use proc_macro::TokenStream as TokenStream1;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use proc_macro_error::{abort, proc_macro_error};
use std::collections::HashMap;
use syn::parse::Parse;
use syn::spanned::Spanned;
use syn::*;
use template_quote::quote;

#[derive(Default)]
struct Arguments {
    map: HashMap<Ident, Type>,
    krate: Option<Path>,
}

impl Parse for Arguments {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let mut ret: Self = Default::default();
        while input.peek(Ident) {
            let ident: Ident = input.parse()?;
            let ty: Type = if let Ok(_) = input.parse::<Token![:]>() {
                input.parse()?
            } else {
                parse_quote!(#ident)
            };
            match ty {
                Type::Path(TypePath { qself, path }) if ident == "krate" && qself.is_none() => {
                    ret.krate = Some(path);
                }
                ty if ident.to_string().len() == 1 => {
                    ret.map.insert(ident, ty);
                }
                _ => {
                    abort!(ident.span(), "it should be ident of one character")
                }
            }
            if let Err(_) = input.parse::<Token![,]>() {
                break;
            }
        }
        if !input.is_empty() {
            Err(syn::parse::Error::new(input.span(), "Unparsed args"))
        } else {
            Ok(ret)
        }
    }
}

fn map_type(ty: &mut Type, from_ty: &Type, to_ty: &Type) -> bool {
    use syn::visit_mut::VisitMut;
    struct Visitor<'a>(&'a Type, &'a Type, bool);
    impl<'a> VisitMut for Visitor<'a> {
        fn visit_type_mut(&mut self, ty: &mut Type) {
            if &ty == &self.0 {
                *ty = self.1.clone();
                self.2 = true;
            } else {
                syn::visit_mut::visit_type_mut(self, ty)
            }
        }
    }
    let mut visitor = Visitor(from_ty, to_ty, false);
    visitor.visit_type_mut(ty);
    visitor.2
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Generator {
    MaxLen,
    MinLen,
    Len,
    Iter,
    IterMut,
    IntoIter,
    Map(Ident, Ident),
}

impl Generator {
    fn generate(
        &self,
        krate: &Path,
        replacing_ty: &Type,
        ty: &Type,
        expr: &TokenStream,
    ) -> std::result::Result<Option<TokenStream>, Type> {
        if ty == replacing_ty {
            match self {
                Generator::MinLen => return Ok(Some(quote! {1usize})),
                Generator::MaxLen => {
                    return Ok(Some(quote! {::core::option::Option::Some(1usize)}))
                }
                Generator::Len => return Ok(Some(quote! {1usize})),
                Generator::Iter => return Ok(Some(quote! {&#expr})),
                Generator::IterMut => return Ok(Some(quote! {&mut #expr})),
                Generator::IntoIter => return Ok(Some(quote! {::core::iter::once(#expr)})),
                Generator::Map(map_fn, _) => return Ok(Some(quote! {#map_fn(#expr)})),
            }
        }
        let indexed_ty_args = match ty {
            Type::Slice(TypeSlice { elem, .. }) | Type::Array(TypeArray { elem, .. }) => {
                vec![(0, elem.as_ref())]
            }
            Type::Group(TypeGroup { elem, .. }) | Type::Paren(TypeParen { elem, .. }) => {
                return self.generate(krate, replacing_ty, elem.as_ref(), expr);
            }
            Type::Path(TypePath { path, .. }) => {
                if let Some(last_seg) = path.segments.iter().last() {
                    let generic_args = match &last_seg.arguments {
                        PathArguments::None => vec![],
                        PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                            args,
                            ..
                        }) => args.iter().collect(),
                        PathArguments::Parenthesized(_) => return Err(ty.clone()),
                    };
                    generic_args
                        .iter()
                        .enumerate()
                        .filter_map(|(idx, ga)| {
                            if let GenericArgument::Type(inner_ty) = ga {
                                Some((idx, inner_ty))
                            } else {
                                None
                            }
                        })
                        .collect()
                } else {
                    return Ok(None);
                }
            }
            Type::Reference(TypeReference {
                mutability, elem, ..
            }) => match (mutability, self) {
                (_, Self::MaxLen)
                | (_, Self::MinLen)
                | (_, Self::Len)
                | (_, Self::Iter)
                | (Some(_), Self::IterMut) => vec![(0, elem.as_ref())],
                _ => return Err(ty.clone()),
            },
            Type::Tuple(TypeTuple { elems, .. }) => elems.iter().enumerate().collect(),
            Type::Never(_) => return Ok(None),
            _ => return Err(ty.clone()),
        };
        let map_arg = quote!(__parametric_type_arg);
        if let Generator::Map(map_fn, map_param) = self {
            let mut ret = quote! {#expr};
            for (index, inner_ty) in indexed_ty_args.into_iter() {
                if let Some(generated) = self.generate(krate, replacing_ty, inner_ty, &map_arg)? {
                    ret = quote! {
                        <
                            _ as #krate::type_argument::MapOfNthArgument<#index>
                        >::map_of_param(#ret, |#map_arg| {#generated})
                    };
                }
            }
            return Ok(Some(ret));
        }
        let mut indexed = Vec::new();
        for (index, inner_ty) in indexed_ty_args.into_iter() {
            if let Some(generated) = self.generate(krate, replacing_ty, inner_ty, &map_arg)? {
                indexed.push((index, generated));
            }
        }
        if indexed.len() == 0 {
            return Ok(None);
        }
        match self {
             Generator::MinLen => {
                Ok(Some(
                    indexed.into_iter().fold(quote!(0usize), |acc, (idx, inner)| {
                        quote! {
                            #acc + <#ty as #krate::type_argument::IntoIteratorOfNthArgument<#idx>>::MIN_LEN * #inner
                        }
                    })
                ))
            }
            Generator::MaxLen => {
                Ok(Some(
                    indexed.into_iter().fold(quote!(::core::option::Option::Some(0usize)), |acc, (idx, inner)| {
                        quote! {
                            if let (Some(l), Some(m), Some(r)) = (#acc, <#ty as #krate::type_argument::IntoIteratorOfNthArgument<#idx>>::MAX_LEN, #inner) {
                                Some(l + m * r)
                            } else { None }
                        }
                    })
                ))
            }
            Generator::Len => {
                Ok(Some(indexed.into_iter().fold(quote!(0usize), |acc, (idx, inner)| {
                    quote! {
                        #acc + <
                            & #ty as #krate::type_argument::IntoIteratorOfNthArgument<#idx>
                        >::into_iter_of_arg(#expr)
                            .map(|#map_arg| #inner)
                            .sum::<::core::primitive::usize>()

                    }
                })))
            }
            Generator::Iter | Generator::IterMut | Generator::IntoIter => {
                Ok(Some(indexed.into_iter().fold(quote!(::core::iter::empty()), |acc, (idx, inner)| {
                    let and = match self {
                        Generator::Iter => quote!{&},
                        Generator::IterMut => quote!{&mut},
                        _ => quote!{}
                    };
                    quote! {
                        #acc.chain(
                            <#and #ty as #krate::type_argument::IntoIteratorOfNthArgument<#idx>>::into_iter_of_arg(#expr)
                                .map(|#map_arg| #inner)
                                .flatten()
                        )
                    }
                })))
            }
            Generator::Map(map_fn, map_param) if indexed.len() == 1 => {
                Ok(Some(quote! {
                    <#ty as #krate::type_argument::MapOfNthArgument<#{&indexed[0].0}, _>>::map_of_param(#expr, |#map_arg| #map_fn(#{&indexed[0].1}))
                }))
            }
            _ => Err(ty.clone())
        }
    }
}

fn inner(arg: Arguments, input: Item) -> TokenStream {
    let krate = arg.krate.unwrap_or(parse_quote!(::parametric_type));
    fn generate_with_generator(
        krate: &Path,
        generators: &[Generator],
        replacing_ty: &Type,
        items: &[(Type, TokenStream)],
    ) -> std::result::Result<Vec<TokenStream>, Type> {
        generators
            .iter()
            .map(|generator| {
                let acc = match generator {
                    Generator::MaxLen => quote!(Some(0usize)),
                    Generator::MinLen | Generator::Len => quote!(0usize),
                    Generator::Iter | Generator::IterMut | Generator::IntoIter => {
                        quote!(::core::iter::empty())
                    }
                    Generator::Map(_, _) => todo!(),
                };
                let and = if let Generator::Len = generator {
                    quote!(&)
                } else {
                    quote!()
                };
                Ok(items
                    .iter()
                    .filter_map(|(ty, expr)| {
                        match generator.generate(krate, replacing_ty, ty, &quote!(#and #expr)) {
                            Ok(Some(v)) => Some(Ok(v)),
                            Ok(None) => None,
                            Err(e) => Some(Err(e)),
                        }
                    })
                    .collect::<std::result::Result<Vec<_>, _>>()?
                    .into_iter()
                    .fold(acc, |acc, out| match generator {
                        Generator::MinLen | Generator::Len => quote! {#acc + #out},
                        Generator::MaxLen => quote! {if let (Some(l), Some(r)) = (#acc, #out) { Some(l + r) } else { None }},
                        Generator::Iter | Generator::IterMut | Generator::IntoIter => {
                            quote! {#acc.chain(#out)}
                        }
                        Generator::Map(map_fn, _) => todo!(),
                    }))
            })
            .collect()
    }
    let mut out = quote!();
    match &input {
        Item::Enum(_) => todo!(),
        Item::Struct(item_struct) => {
            let (impl_generics, ty_generics, where_clause) = item_struct.generics.split_for_impl();
            for (i, par) in
                item_struct
                    .generics
                    .params
                    .iter()
                    .enumerate()
                    .filter_map(|(i, param)| {
                        if let GenericParam::Type(TypeParam { ident, .. }) = param {
                            Some((i, ident))
                        } else {
                            None
                        }
                    })
            {
                let items: Vec<_> = item_struct
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        let ty = field.ty.clone();
                        if let Some(ident) = &field.ident {
                            (ty, quote! {self.#ident})
                        } else {
                            let i = Index {
                                index: i as u32,
                                span: Span::call_site(),
                            };
                            (ty, quote! {self.#i})
                        }
                    })
                    .collect();
                if let [out_minlen, out_maxlen, out_iter, out_len] = generate_with_generator(
                    &krate,
                    &[
                        Generator::MinLen,
                        Generator::MaxLen,
                        Generator::IntoIter,
                        Generator::Len,
                    ],
                    &parse_quote!(#par),
                    items.as_ref(),
                )
                .unwrap_or_else(|e| abort!(e.span(), "Cannot implement IntoIteratorOfNthArgument"))
                .as_slice()
                {
                    out.extend(quote! {
                        impl #impl_generics #krate::type_argument::IntoIteratorOfNthArgument<#i> for #{&item_struct.ident} #ty_generics #where_clause {
                            type Item = #par;
                            const MIN_LEN: usize = #out_minlen;
                            const MAX_LEN: Option<usize> = #out_maxlen;
                            fn into_iter_of_arg(self) -> impl ::core::iter::Iterator<Item = Self::Item> { #out_iter }
                            fn len_of_arg(&self) -> usize { #out_len }
                        }
                    })
                } else {
                    unreachable!()
                }
            }
            quote! {
                #input
                #out
            }
        }
        _ => abort!(
            input.span(),
            "Unsuported item; Only supported enums or structs"
        ),
    }
}

#[proc_macro_error]
#[proc_macro_attribute]
pub fn parametric_type(attr: TokenStream1, input: TokenStream1) -> TokenStream1 {
    inner(
        parse(attr).unwrap_or_else(|e| abort!(e.span(), &format!("{}", e))),
        parse_macro_input!(input as Item),
    )
    .into()
}
