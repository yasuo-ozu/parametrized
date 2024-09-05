mod generator;
use proc_macro::TokenStream as TokenStream1;

use proc_macro2::Span;
use proc_macro2::TokenStream;
use proc_macro_error::{abort, proc_macro_error};
use std::collections::{HashMap, HashSet};
use syn::parse::Parse;
use syn::spanned::Spanned;
use syn::*;
use template_quote::{quote, ToTokens};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum TraitTarget {
    Default,
    IterMut,
    IntoIter,
    Map,
}

fn squash_minlens(outs: &[Expr]) -> Expr {
    if outs.len() == 0 {
        abort!(Span::call_site(), "needs one or more variants");
    }
    let mut acc = outs[outs.len() - 1].clone();
    if outs.len() >= 2 {
        for out in outs[0..(outs.len() - 2)].iter().rev() {
            acc = parse_quote! {__parametric_type_min(#out, #acc)};
        }
    }
    parse_quote! {
        {
            const fn __parametric_type_min(a: usize, b: usize) -> usize {
                if a < b { a } else { b }
            }
            #acc
        }
    }
}
fn squash_maxlens(outs: &[Expr]) -> Expr {
    if outs.len() == 0 {
        abort!(Span::call_site(), "needs one or more variants");
    }
    let mut acc = outs[outs.len() - 1].clone();
    if outs.len() >= 2 {
        for out in outs[0..(outs.len() - 2)].iter().rev() {
            acc = parse_quote! {__parametric_type_max(#out, #acc)};
        }
    }
    parse_quote! {
        {
            const fn __parametric_type_max(a: Option<usize>, b: Option<usize>) -> Option<usize> {
                match (a, b) {
                    (Some(a), Some(b)) => if a > b { Some(a) } else { Some(b) }
                    _ => None,
                }
            }
            #acc
        }
    }
}

impl TraitTarget {
    fn make_enough(mut set: HashSet<Self>) -> HashSet<Self> {
        if set.contains(&Self::Map) {
            set.insert(Self::IntoIter);
        }
        if set.contains(&Self::IntoIter) {
            set.insert(Self::Default);
        }
        if set.contains(&Self::IterMut) {
            set.insert(Self::Default);
        }
        set
    }

    fn emit(
        &self,
        krate: &Path,
        ident: &Ident,
        generics: &Generics,
        param_index: usize,
        replacing_ty: &Type,
        self_val: &Ident,
        tys_exprs: &[Vec<(Type, Expr)>],
        mut f: impl FnMut(&[Expr]) -> TokenStream,
    ) -> Result<TokenStream> {
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
        match self {
            Self::Default => {
                eprintln!("len");
                let out_len = tys_exprs
                    .iter()
                    .map(|item| {
                        let ret = generator::EmitContext {
                            kind: generator::EmitLen,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(
                            item.iter().map(|(a, b)| (a.clone(), parse_quote! {&#b})),
                        );
                        ret
                    })
                    .collect::<Result<Option<Vec<_>>>>()?
                    .unwrap_or_else(|| abort!(Span::call_site(), "Cannot implement len method"));
                eprintln!("max_len");
                let out_max_len = tys_exprs
                    .iter()
                    .map(|item| {
                        generator::EmitContext {
                            kind: generator::EmitMaxLen,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(
                            item.iter().map(|(a, b)| (a.clone(), parse_quote!(&#b))),
                        )
                    })
                    .collect::<Result<Option<Vec<_>>>>()?
                    .unwrap_or_else(|| abort!(Span::call_site(), "Cannot implement maxlen method"));
                eprintln!("min_len");
                let out_min_len = tys_exprs
                    .iter()
                    .map(|item| {
                        generator::EmitContext {
                            kind: generator::EmitMinLen,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(
                            item.iter().map(|(a, b)| (a.clone(), parse_quote!(&#b))),
                        )
                    })
                    .collect::<Result<Option<Vec<_>>>>()?
                    .unwrap_or_else(|| abort!(Span::call_site(), "Cannot implement minlen method"));
                eprintln!("iter");
                let out_iter = tys_exprs
                    .iter()
                    .map(|item| {
                        generator::EmitContext {
                            kind: generator::EmitIter,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(
                            item.iter().map(|(a, b)| (a.clone(), parse_quote!(&#b))),
                        )
                    })
                    .collect::<Result<Option<Vec<_>>>>()?
                    .unwrap_or_else(|| abort!(Span::call_site(), "Cannot implement iter method"));
                Ok(quote! {
                    impl #impl_generics #krate::Parametrized<#param_index> for #ident
                    #ty_generics #where_clause {
                        type Item = #replacing_ty;
                        const MIN_LEN: usize = #{squash_minlens(out_min_len.as_slice())};
                        const MAX_LEN: Option<usize> = #{squash_maxlens(out_max_len.as_slice())};
                        fn param_len(&#self_val) -> usize {
                            #{f(out_len.as_slice())}
                        }
                        type Iter<'a> = todo!() where (Self, Self::Item): 'a;
                        fn param_iter<'a>(&'a #self_val) -> Self::Iter<'a>
                        where
                            Self::Item: 'a
                        {
                            #{f(out_iter.as_slice())}
                        }
                    }
                })
            }
            Self::IterMut => {
                let out_iter_mut = tys_exprs
                    .iter()
                    .map(|item| {
                        generator::EmitContext {
                            kind: generator::EmitIterMut,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(
                            item.iter().map(|(a, b)| (a.clone(), parse_quote!(&mut #b))),
                        )
                    })
                    .collect::<Result<Option<Vec<_>>>>()?
                    .unwrap_or_else(|| {
                        abort!(Span::call_site(), "Cannot implement iter_mut method")
                    });
                Ok(quote! {
                    impl #impl_generics #krate::ParametrizedIterMut<#param_index> for #ident #ty_generics #where_clause {
                        type IterMut<'a> = todo!() where (Self, Self::Item): 'a;
                        fn param_iter_mut<'a>(&'a mut #self_val) -> Self::IterMut<'a>
                        where
                            Self::Item: 'a
                        {
                            #{f(out_iter_mut.as_slice())}
                        }
                    }
                })
            }
            Self::IntoIter => {
                let out_into_iter = tys_exprs
                    .iter()
                    .map(|item| {
                        generator::EmitContext {
                            kind: generator::EmitIntoIter,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(item.iter().map(|(a, b)| (a.clone(), b.clone())))
                    })
                    .collect::<Result<Option<Vec<_>>>>()?
                    .unwrap_or_else(|| {
                        abort!(Span::call_site(), "Cannot implement into_iter method")
                    });
                Ok(quote! {
                    impl #impl_generics #krate::ParametrizedIntoIter<#param_index> for #ident #ty_generics #where_clause {
                        type IntoIter = todo!();
                        fn param_into_iter(#self_val) -> Self::IntoIter
                        {
                            #{f(out_into_iter.as_slice())}
                        }
                    }
                })
            }
            Self::Map => {
                let out_map = tys_exprs
                    .iter()
                    .map(|item| {
                        generator::EmitContext {
                            kind: generator::EmitMap,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(item.iter().map(|(a, b)| (a.clone(), b.clone())))
                    })
                    .collect::<Result<Option<Vec<_>>>>()?
                    .unwrap_or_else(|| abort!(Span::call_site(), "Cannot implement map method"));
                Ok(quote! {
                    impl #impl_generics #krate::ParametrizedIntoIter<#param_index> for #ident #ty_generics #where_clause {
                        type IntoIter = todo!();
                        fn param_into_iter(#self_val) -> Self::IntoIter
                        {
                            #{f(out_map.as_slice())}
                        }
                    }
                })
            }
        }
    }
}

impl Parse for TraitTarget {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let ident: Ident = input.fork().parse()?;
        let r = match ident.to_string().as_str() {
            "default" => Self::Default,
            "iter_mut" => Self::IterMut,
            "into_iter" => Self::IntoIter,
            "map" => Self::Map,
            _ => return Err(input.error("Require one of `iter`, `iter_mut`, `into_iter`, `map`")),
        };
        input.parse::<Ident>()?;
        Ok(r)
    }
}

#[derive(Debug, Default)]
struct Arguments {
    trait_impls: HashMap<usize, HashSet<TraitTarget>>,
    krate: Option<Path>,
}

impl Parse for Arguments {
    fn parse(input: parse::ParseStream) -> Result<Self> {
        let mut ret: Self = Default::default();
        while input.peek(Ident) {
            if let Ok(tr) = input.parse::<TraitTarget>() {
                // parse number or array
                let param_indices = if input.parse::<Token![=]>().is_ok() {
                    if let Ok(expr_arr) = input.parse::<ExprArray>() {
                        expr_arr
                            .elems
                            .into_iter()
                            .map(|expr| {
                                if let Expr::Lit(ExprLit {
                                    lit: Lit::Int(lit), ..
                                }) = expr
                                {
                                    lit.base10_parse::<usize>()
                                } else {
                                    Err(Error::new(expr.span(), "Bad integer"))
                                }
                            })
                            .collect::<Result<Vec<_>>>()?
                    } else {
                        vec![input.parse::<LitInt>()?.base10_parse::<usize>()?]
                    }
                } else {
                    vec![0]
                };
                for param_index in param_indices {
                    ret.trait_impls
                        .entry(param_index)
                        .or_insert(HashSet::new())
                        .insert(tr.clone());
                }
            } else {
                let ident: Ident = input.parse()?;
                if &ident == "krate" {
                    input.parse::<Token![=]>()?;
                    ret.krate = Some(input.parse()?);
                } else {
                    return Err(Error::new(ident.span(), "Bad option"));
                }
            }
            if input.parse::<Token![,]>().is_err() {
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

trait ImplTarget {
    fn emit_impl(&self, krate: &Path, tr: &TraitTarget, param_index: usize) -> Result<TokenStream>;
}

fn get_replacing_ty(generics: &Generics, param_index: usize) -> Type {
    generics
        .params
        .get(param_index)
        .and_then(|g| {
            if let GenericParam::Type(TypeParam { ident, .. }) = g {
                Some(parse_quote!(#ident))
            } else {
                None
            }
        })
        .unwrap_or_else(|| {
            abort!(
                Span::call_site(),
                format!("Cannot implement for index {}", param_index)
            )
        })
}

impl ImplTarget for ItemStruct {
    fn emit_impl(&self, krate: &Path, tr: &TraitTarget, param_index: usize) -> Result<TokenStream> {
        let self_val = Ident::new("self", Span::call_site());
        let replacing_ty = get_replacing_ty(&self.generics, param_index);
        let tys_exprs = self
            .fields
            .iter()
            .enumerate()
            .map(|(i, field)| {
                let ty = field.ty.clone();
                if let Some(ident) = &field.ident {
                    (ty, parse_quote! {#self_val.#ident})
                } else {
                    let i = Index {
                        index: i as u32,
                        span: Span::call_site(),
                    };
                    (ty, parse_quote! {#self_val.#i})
                }
            })
            .collect::<Vec<_>>();
        tr.emit(
            krate,
            &self.ident,
            &self.generics,
            param_index,
            &replacing_ty,
            &self_val,
            &[tys_exprs],
            |inner| {
                quote! {
                    #(#inner)*
                }
            },
        )
    }
}

impl ImplTarget for ItemEnum {
    fn emit_impl(&self, krate: &Path, tr: &TraitTarget, param_index: usize) -> Result<TokenStream> {
        let self_val: Ident = parse_quote!(self);
        let replacing_ty = get_replacing_ty(&self.generics, param_index);
        let variant_idents = self
            .variants
            .iter()
            .map(|variant| {
                variant
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        field.ident.clone().unwrap_or(Ident::new(
                            &format!("__parametric_type_id_{}", i),
                            Span::call_site(),
                        ))
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let variant_items = self
            .variants
            .iter()
            .zip(&variant_idents)
            .map(|(var, idents)| {
                var.fields
                    .iter()
                    .zip(idents)
                    .map(|(field, ident)| {
                        let ty = field.ty.clone();
                        (ty, parse_quote! {#ident})
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        tr.emit(
            krate,
            &self.ident,
            &self.generics,
            param_index,
            &replacing_ty,
            &self_val,
            variant_items.as_slice(),
            |inner| {
                quote! {
                    match #self_val {
                        #(for ((variant, inner), idents) in self
                            .variants.iter().zip(inner).zip(&variant_idents)
                        ) {
                            #{&self.ident}::#{&variant.ident}
                                #(if let Fields::Named(_) = &variant.fields) {
                                    { #(#idents),*  }
                                }
                                #(if let Fields::Unnamed(_) = &variant.fields) {
                                    ( #(#idents),* )
                                }
                            => { #inner }
                        }
                    }
                }
            },
        )
    }
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
    fn and(&self) -> TokenStream {
        match self {
            Self::Iter | Self::Len | Self::MinLen | Self::MaxLen => quote!(&),
            Self::IterMut => quote!(&mut),
            _ => quote!(),
        }
    }
    fn generate_if_pure(
        &self,
        replacing_ty: &Type,
        ty: &Type,
        expr: &TokenStream,
    ) -> Option<TokenStream> {
        if ty == replacing_ty {
            match self {
                Generator::MinLen => Some(quote! {1usize}),
                Generator::MaxLen => Some(quote! {::core::option::Option::Some(1usize)}),
                Generator::Len => Some(quote! {1usize}),
                Generator::Iter | Generator::IterMut | Generator::IntoIter => {
                    Some(quote! {::core::iter::once(#expr)})
                }
                Generator::Map(map_fn, _) => Some(quote! {#map_fn(#expr)}),
            }
        } else if let Type::Reference(TypeReference {
            mutability, elem, ..
        }) = ty
        {
            match (self, mutability.is_some()) {
                (Self::MinLen | Self::MaxLen | Self::Len | Self::Iter, _)
                | (Self::IterMut, true) => {
                    self.generate_if_pure(replacing_ty, elem, &quote!(*#expr))
                }
                _ => None,
            }
        } else {
            None
        }
    }
    fn generate_fold(
        &self,
        krate: &Path,
        replacing_ty: &Type,
        tys_exprs: &[(Type, Expr)],
    ) -> Result<TokenStream> {
        let acc = match self {
            Generator::MaxLen => quote!(Some(0usize)),
            Generator::MinLen | Generator::Len => quote!(0usize),
            Generator::Iter | Generator::IterMut | Generator::IntoIter => {
                quote!(::core::iter::empty())
            }
            Generator::Map(_, _) => todo!(),
        };
        let and = self.and();
        let out = tys_exprs
            .iter()
            .filter_map(|(ty, expr)| {
                match self.generate(krate, replacing_ty, ty, &quote!(#and #expr)) {
                    Ok(Some(v)) => Some(Ok(v)),
                    Ok(None) => None,
                    Err(e) => Some(Err(e)),
                }
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .fold(acc, |acc, out| match self {
                Generator::MinLen | Generator::Len => quote! {#acc + #out},
                Generator::MaxLen => {
                    quote! {if let (Some(l), Some(r)) = (#acc, #out) { Some(l + r) } else { None }}
                }
                Generator::Iter | Generator::IterMut | Generator::IntoIter => {
                    quote! {#acc.chain(#out)}
                }
                Generator::Map(_map_fn, _) => todo!(),
            });
        Ok(out)
    }
    fn generate(
        &self,
        krate: &Path,
        replacing_ty: &Type,
        ty: &Type,
        expr: &TokenStream,
    ) -> Result<Option<TokenStream>> {
        if let Some(out) = self.generate_if_pure(replacing_ty, ty, expr) {
            return Ok(Some(out));
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
                        PathArguments::Parenthesized(_) => {
                            return Err(Error::new(
                                ty.span(),
                                "Cannot infer Parametrized of closures",
                            ))
                        }
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
                | (Some(_), Self::IterMut) => {
                    return self.generate(krate, replacing_ty, elem.as_ref(), expr);
                }
                _ => {
                    return Err(Error::new(
                        ty.span(),
                        format!("Cannot implement {:?} over this reference", self),
                    ))
                }
            },
            Type::Tuple(TypeTuple { elems, .. }) => elems.iter().enumerate().collect(),
            Type::Never(_) => return Ok(None),
            _ => {
                return Err(Error::new(
                    ty.span(),
                    "Cannot infer Parametrized for this type",
                ))
            }
        };
        let map_arg = quote!(__parametric_type_arg);
        if let Generator::Map(_map_fn, _map_param) = self {
            let mut ret = quote! {#expr};
            for (index, inner_ty) in indexed_ty_args.into_iter() {
                if let Some(generated) = self.generate(krate, replacing_ty, inner_ty, &map_arg)? {
                    ret = quote! {
                        < _ as #krate::ParametrizedMap<#index, _>>::map_of_param(#ret, |#map_arg| {#generated})
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
                            #acc + <#ty as #krate::Parametrized<#idx>>::MIN_LEN * #inner
                        }
                    })
                ))
            }
            Generator::MaxLen => {
                Ok(Some(
                    indexed.into_iter().fold(quote!(::core::option::Option::Some(0usize)), |acc, (idx, inner)| {
                        quote! {
                            if let (Some(l), Some(m), Some(r)) = (#acc, <#ty as #krate::Parametrized<#idx>>::MAX_LEN, #inner) {
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
                            #ty as #krate::ParametrizedIter<#idx>
                        >::param_iter(#expr)
                            .map(|#map_arg| #inner)
                            .sum::<::core::primitive::usize>()
                    }
                })))
            }
            Generator::Iter | Generator::IterMut | Generator::IntoIter => {
                Ok(Some(indexed.into_iter().fold(quote!(::core::iter::empty()), |acc, (idx, inner)| {
                    let and = self.and();
                    quote! {
                        #acc.chain( // TODO! 
                            <#ty as #krate::ParametrizedIter<#idx>>::into_iter_of_arg(#expr)
                                .map(|#map_arg| #inner)
                                .flatten()
                        )
                    }
                })))
            }
            Generator::Map(map_fn, _map_param) if indexed.len() == 1 => {
                Ok(Some(quote! {
                    <#ty as #krate::type_argument::MapOfNthArgument<#{&indexed[0].0}, _>>::map_of_param(#expr, |#map_arg| #map_fn(#{&indexed[0].1}))
                }))
            }
            _ => Err(Error::new(ty.span(), "general error"))
        }
    }
}

fn inner_target<T: ImplTarget>(target: &T, arg: Arguments) -> TokenStream {
    let krate = arg.krate.unwrap_or(parse_quote!(::parametrized));
    let mut out = quote!();
    for (param_index, impl_traits) in &arg.trait_impls {
        let impl_traits = TraitTarget::make_enough(impl_traits.clone());
        for impl_trait in &impl_traits {
            let ret = target
                .emit_impl(&krate, impl_trait, *param_index)
                .unwrap_or_else(|e| {
                    abort!(
                        e.span(),
                        format!(
                            "Cannot implement {:?} for parameter {}: {}",
                            &impl_trait, param_index, e
                        )
                    )
                });
            out.extend(ret);
        }
    }
    out
}

fn inner(arg: Arguments, input: Item) -> TokenStream {
    match input {
        Item::Enum(item_enum) => inner_target(&item_enum, arg),
        Item::Struct(item_struct) => inner_target(&item_struct, arg),
        _ => abort!(input.span(), "Bad item"),
    }
}

#[proc_macro_error]
#[proc_macro_attribute]
pub fn parametrized(attr: TokenStream1, input: TokenStream1) -> TokenStream1 {
    inner(
        parse(attr).unwrap_or_else(|e| abort!(e.span(), &format!("{}", e))),
        parse_macro_input!(input as Item),
    )
    .into()
}
