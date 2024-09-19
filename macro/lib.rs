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

fn replace_type(mut ty: Type, from: Type, to: Type) -> Type {
    use syn::visit_mut::VisitMut;
    struct Visitor(Type, Type);
    impl VisitMut for Visitor {
        fn visit_type_mut(&mut self, ty: &mut Type) {
            if ty == &self.0 {
                *ty = self.1.clone();
            } else {
                syn::visit_mut::visit_type_mut(self, ty)
            }
        }
    }
    Visitor(from, to).visit_type_mut(&mut ty);
    ty
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
        mut f: impl FnMut(&[TokenStream]) -> TokenStream,
        mut emit_map_f: impl FnMut(&[Vec<Expr>]) -> TokenStream,
        needs_ref: bool,
    ) -> Result<TokenStream> {
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
        match self {
            Self::Default => {
                let out_len = tys_exprs
                    .iter()
                    .map(|item| {
                        Ok(generator::EmitContext {
                            kind: generator::EmitLen,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(item.iter().map(|(a, b)| {
                            (
                                a.clone(),
                                if needs_ref {
                                    parse_quote! {&#b}
                                } else {
                                    parse_quote! {#b}
                                },
                            )
                        }))?
                        .unwrap_or(parse_quote!(0usize)))
                    })
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .map(|expr| quote!(#expr))
                    .collect::<Vec<_>>();
                let out_max_len = tys_exprs
                    .iter()
                    .map(|item| {
                        Ok(generator::EmitContext {
                            kind: generator::EmitMaxLen,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(item.iter().map(|(a, b)| {
                            (
                                a.clone(),
                                if needs_ref {
                                    parse_quote!(&#b)
                                } else {
                                    parse_quote!(#b)
                                },
                            )
                        }))?
                        .unwrap_or(parse_quote!(::core::option::Option::Some(0usize))))
                    })
                    .collect::<Result<Vec<_>>>()?;
                let out_min_len = tys_exprs
                    .iter()
                    .map(|item| {
                        Ok(generator::EmitContext {
                            kind: generator::EmitMinLen,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(item.iter().map(|(a, b)| {
                            (
                                a.clone(),
                                if needs_ref {
                                    parse_quote!(&#b)
                                } else {
                                    parse_quote!(#b)
                                },
                            )
                        }))?
                        .unwrap_or(parse_quote!(0usize)))
                    })
                    .collect::<Result<Vec<_>>>()?;
                let iter_ty_lt: Lifetime = parse_quote!('__parametrized_lt);
                let out_iter_ty = tys_exprs
                    .iter()
                    .map(|item| {
                        Ok(generator::EmitContext {
                            kind: generator::EmitIterTy(iter_ty_lt.clone(), replacing_ty.clone()),
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(
                            item.iter().map(|(a, _)| (a.clone(), replacing_ty.clone())),
                        )?
                        .unwrap_or(parse_quote!(::core::iter::Empty<&#iter_ty_lt #replacing_ty>)))
                    })
                    .collect::<Result<Vec<_>>>()?;
                let out_iter = tys_exprs
                    .iter()
                    .map(|item| {
                        Ok(generator::EmitContext {
                            kind: generator::EmitIter,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(
                            item.iter().map(|(a, b)| (a.clone(), if needs_ref{parse_quote!(&#b)}else{parse_quote!(#b)})),
                        )?
                        .unwrap_or(parse_quote!(::core::iter::empty())))
                    })
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .zip(&out_iter_ty)
                    .map(|(expr, ty)| {
                        if tys_exprs.len() > 1 {
                            quote!(sumtype!(#expr, for<#iter_ty_lt> #ty where #replacing_ty: #iter_ty_lt))
                        } else {
                            quote!(#expr)
                        }
                    })
                    .collect::<Vec<_>>();
                Ok(quote! {
                    #(if tys_exprs.len() > 1) {
                        #[#krate::_imp::sumtype]
                    }
                    impl #impl_generics #krate::Parametrized<#param_index> for #ident
                    #ty_generics #where_clause {
                        type Item = #replacing_ty;
                        const MIN_LEN: usize = #{squash_minlens(out_min_len.as_slice())};
                        const MAX_LEN: Option<usize> = #{squash_maxlens(out_max_len.as_slice())};
                        fn param_len(&#self_val) -> usize {
                            #{f(out_len.as_slice())}
                        }
                        #(if tys_exprs.len() > 1) {
                            type Iter<#iter_ty_lt> = sumtype![#iter_ty_lt] where (Self, Self::Item): #iter_ty_lt;
                        } #(else) {
                            type Iter<#iter_ty_lt> = #(#out_iter_ty)* where (Self, Self::Item): #iter_ty_lt;
                        }
                        fn param_iter<'__parametrized_lt>(&'__parametrized_lt #self_val) -> Self::Iter<'__parametrized_lt>
                        where
                            Self::Item: '__parametrized_lt
                        {
                            #{f(out_iter.as_slice())}
                        }
                    }
                })
            }
            Self::IterMut => {
                let iter_ty_lt: Lifetime = parse_quote!('__parametrized_lt);
                let out_iter_mut_ty = tys_exprs
                    .iter()
                    .map(|item| {
                        Ok(generator::EmitContext {
                            kind: generator::EmitIterMutTy(
                                iter_ty_lt.clone(),
                                replacing_ty.clone(),
                            ),
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(
                            item.iter().map(|(a, _)| (a.clone(), replacing_ty.clone())),
                        )?
                        .unwrap_or(
                            parse_quote!(::core::iter::Empty<& #iter_ty_lt mut #replacing_ty>),
                        ))
                    })
                    .collect::<Result<Vec<_>>>()?;
                let out_iter_mut = tys_exprs
                    .iter()
                    .map(|item| {
                        Ok(generator::EmitContext {
                            kind: generator::EmitIterMut,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(
                            item.iter().map(|(a, b)| (a.clone(), if needs_ref{parse_quote!(&mut #b)}else{parse_quote!(#b)})),
                        )?
                        .unwrap_or(parse_quote!(::core::iter::empty())))
                    })
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .zip(&out_iter_mut_ty)
                    .map(|(expr, ty)| {
                        if tys_exprs.len() > 1 {
                            quote!(sumtype!(#expr, for<#iter_ty_lt> #ty where #replacing_ty: #iter_ty_lt))
                        } else {
                            quote!(#expr)
                        }
                    })
                    .collect::<Vec<_>>();
                Ok(quote! {
                    #(if tys_exprs.len() > 1) {
                        #[#krate::_imp::sumtype]
                    }
                    impl #impl_generics #krate::ParametrizedIterMut<#param_index> for #ident #ty_generics #where_clause {
                        #(if tys_exprs.len() > 1) {
                            type IterMut<#iter_ty_lt> = sumtype![#iter_ty_lt] where (Self, Self::Item): #iter_ty_lt;
                        } #(else) {
                            type IterMut<#iter_ty_lt> = #(#out_iter_mut_ty)* where (Self, Self::Item): #iter_ty_lt;
                        }
                        fn param_iter_mut<'__parametrized_lt>(&'__parametrized_lt mut #self_val) -> Self::IterMut<'__parametrized_lt>
                        where
                            Self::Item: '__parametrized_lt
                        {
                            #{f(out_iter_mut.as_slice())}
                        }
                    }
                })
            }
            Self::IntoIter => {
                let out_into_iter_ty = tys_exprs
                    .iter()
                    .map(|item| {
                        Ok(generator::EmitContext {
                            kind: generator::EmitIntoIterTy(replacing_ty.clone()),
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(
                            item.iter().map(|(a, _)| (a.clone(), replacing_ty.clone())),
                        )?
                        .unwrap_or(parse_quote!(::core::iter::Empty<#replacing_ty>)))
                    })
                    .collect::<Result<Vec<_>>>()?;
                let out_into_iter = tys_exprs
                    .iter()
                    .map(|item| {
                        Ok(generator::EmitContext {
                            kind: generator::EmitIntoIter,
                            krate: krate.clone(),
                            replacing_ty: replacing_ty.clone(),
                        }
                        .emit_for_tys_exprs(item.iter().map(|(a, b)| (a.clone(), b.clone())))?
                        .unwrap_or(parse_quote!(::core::iter::empty())))
                    })
                    .collect::<Result<Vec<_>>>()?
                    .into_iter()
                    .zip(&out_into_iter_ty)
                    .map(|(expr, ty)| {
                        if tys_exprs.len() > 1 {
                            quote!(sumtype!(#expr, #ty))
                        } else {
                            quote!(#expr)
                        }
                    })
                    .collect::<Vec<_>>();
                Ok(quote! {
                    #(if tys_exprs.len() > 1) {
                        #[#krate::_imp::sumtype]
                    }
                    impl #impl_generics #krate::ParametrizedIntoIter<#param_index> for #ident #ty_generics #where_clause {
                        #(if tys_exprs.len() > 1) {
                            type IntoIter = sumtype![];
                        } #(else) {
                            type IntoIter = #(#out_into_iter_ty)*;
                        }
                        fn param_into_iter(#self_val) -> Self::IntoIter
                        {
                            #{f(out_into_iter.as_slice())}
                        }
                    }
                })
            }
            Self::Map => {
                let map_fn: Ident = parse_quote!(__parametrized_map_fn);
                let mapped_param: Ident = parse_quote!(__PARAMETRIZED_MAP_PARAM);
                let out_map = tys_exprs
                    .iter()
                    .map(|item| {
                        item.iter()
                            .map(|(a, b)| {
                                Ok(generator::EmitContext {
                                    kind: generator::EmitMap(map_fn.clone(), mapped_param.clone()),
                                    krate: krate.clone(),
                                    replacing_ty: replacing_ty.clone(),
                                }
                                .emit(a, &(b.clone(), a.clone()))?
                                .map(|a| a.0)
                                .unwrap_or(b.clone()))
                            })
                            .collect::<Result<Vec<_>>>()
                    })
                    .collect::<Result<Vec<_>>>()?;
                let mapped = replace_type(
                    parse_quote!(#ident #ty_generics),
                    replacing_ty.clone(),
                    parse_quote!(#mapped_param),
                );
                eprintln!("emit_map_f = [{}]", emit_map_f(out_map.as_slice()));
                Ok(quote! {
                    impl <#(for p in &generics.params){ #p, } #mapped_param> #krate::ParametrizedMap<#param_index, #mapped_param> for #ident #ty_generics #where_clause {
                        type Mapped = #mapped;
                        fn param_map(#self_val, mut #map_fn: impl FnMut(Self::Item) -> #mapped_param) -> Self::Mapped
                        where
                            Self::Item: ::core::marker::Sized
                        {
                            #{emit_map_f(out_map.as_slice())}
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
                quote! { #(#inner)* }
            },
            |items| {
                quote! {
                    #{&self.ident}
                    #(if let Fields::Named(_) = &self.fields) {
                        {#(for (inner, field) in items[0].iter().zip(&self.fields)) {
                            #{&field.ident} : #inner,
                        }}
                    } #(else) {
                        ( #(for inner in items[0].iter()), { #inner })
                    }
                }
            },
            true,
        )
    }
}

impl ImplTarget for ItemEnum {
    fn emit_impl(&self, krate: &Path, tr: &TraitTarget, param_index: usize) -> Result<TokenStream> {
        let self_val: Ident = Ident::new("self", Span::call_site());
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
            |items| {
                quote! {
                    match #self_val {
                        #(for ((variant, inner), idents) in self
                            .variants.iter().zip(items).zip(&variant_idents)
                        ) {
                            #{&self.ident}::#{&variant.ident}
                                #(if let Fields::Named(_) = &variant.fields) {
                                    { #(#idents),*  }
                                }
                                #(if let Fields::Unnamed(_) = &variant.fields) {
                                    ( #(#idents),* )
                                }
                            => {
                                #{&self.ident}::#{&variant.ident}
                                #(if let Fields::Named(_) = &variant.fields) {
                                    { #(#inner),*  }
                                }
                                #(if let Fields::Unnamed(_) = &variant.fields) {
                                    ( #(#inner),* )
                                }
                            }
                        }
                    }
                }
            },
            false,
        )
    }
}

fn inner_target<T: ImplTarget + ToTokens>(target: &T, arg: Arguments) -> TokenStream {
    let krate = arg.krate.unwrap_or(parse_quote!(::parametrized));
    let mut out = quote!(#target);
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
