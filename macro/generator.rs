use core::any::Any;
use core::fmt::Debug;
use core::hash::Hash;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use syn::spanned::Spanned;
use syn::*;
use template_quote::quote;

pub trait Emitter: PartialEq + Debug + Hash + Any {
    type Elem: Clone;
    fn native_reference(&self) -> TokenStream;
    fn item(
        &self,
        base_ty: &Type,
        index: usize,
        ty: &Type,
        elem: &Self::Elem,
    ) -> Result<Option<Self::Elem>>;
    fn fold(&self, acc: &Self::Elem, item: &Self::Elem) -> Self::Elem;

    fn emit_pure(&self, ty: &Type, elem: &Self::Elem) -> Self::Elem;

    fn access_over_ref(&self) -> bool;
    fn access_over_ref_mut(&self) -> bool;

    fn do_deref(&self, elem: &Self::Elem) -> Self::Elem;

    fn fold_item(
        &self,
        base_ty: Type,
        base_elem: &<Self as Emitter>::Elem,
        ty: &Type,
        elem: Option<<Self as Emitter>::Elem>,
        index: usize,
    ) -> Result<Option<<Self as Emitter>::Elem>> {
        match (elem, self.item(&base_ty, index, ty, base_elem)?) {
            (Some(elem), Some(item)) => Ok(Some(self.fold(&elem, &item))),
            (Some(o), None) | (None, Some(o)) => Ok(Some(o)),
            _ => Ok(None),
        }
    }
}

#[derive(PartialEq, Debug, Hash)]
pub struct EmitContext<K> {
    pub kind: K,
    pub krate: Path,
    pub replacing_ty: Type,
}

pub trait ParseQuote<T> {
    fn parse_quote(self) -> T;
}

impl ParseQuote<Expr> for TokenStream {
    fn parse_quote(self) -> Expr {
        parse_quote!(#self)
    }
}

impl ParseQuote<Type> for TokenStream {
    fn parse_quote(self) -> Type {
        parse_quote!(#self)
    }
}

impl<K> EmitContext<K>
where
    Self: Emitter,
{
    fn check_pure_and_emit(
        &self,
        ty: &Type,
        expr: &<Self as Emitter>::Elem,
    ) -> Option<<Self as Emitter>::Elem> {
        if &self.replacing_ty == ty {
            Some(self.emit_pure(ty, expr))
        } else if let Type::Reference(TypeReference {
            mutability, elem, ..
        }) = ty
        {
            if self.access_over_ref() || self.access_over_ref_mut() && mutability.is_some() {
                if self.native_reference().to_string().as_str() == "" {
                    self.check_pure_and_emit(elem, expr)
                } else {
                    self.check_pure_and_emit(elem, &self.do_deref(expr))
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    fn emit_with_tys<'a>(
        &self,
        base_ty: &Type,
        tys: impl IntoIterator<Item = (usize, &'a Type)>,
        expr: &<Self as Emitter>::Elem,
    ) -> Result<Option<<Self as Emitter>::Elem>> {
        let base_expr = expr.clone();
        Ok(tys.into_iter().fold(Ok(None), |acc, (index, ty)| {
            self.fold_item(base_ty.clone(), &base_expr, ty, acc?, index)
        })?)
    }
    pub fn emit_for_tys_exprs<'a>(
        &self,
        tys_exprs: impl IntoIterator<Item = (Type, <Self as Emitter>::Elem)>,
    ) -> Result<Option<<Self as Emitter>::Elem>> {
        tys_exprs.into_iter().fold(Ok(None), |acc, (ty, expr)| {
            match (acc?, self.emit(&ty, &expr)?) {
                (Some(acc), Some(item)) => Ok(Some(self.fold(&acc, &item))),
                (Some(o), None) | (None, Some(o)) => Ok(Some(o)),
                _ => Ok(None),
            }
        })
    }
    pub fn emit(
        &self,
        ty: &Type,
        expr: &<Self as Emitter>::Elem,
    ) -> Result<Option<<Self as Emitter>::Elem>> {
        if let Some(out) = self.check_pure_and_emit(ty, expr) {
            return Ok(Some(out));
        }
        match ty {
            Type::Slice(TypeSlice { elem, .. }) | Type::Array(TypeArray { elem, .. }) => {
                self.emit_with_tys(ty, core::iter::once((0, elem.as_ref())), expr)
            }
            Type::Group(TypeGroup { elem, .. }) | Type::Paren(TypeParen { elem, .. }) => {
                self.emit(elem.as_ref(), expr)
            }
            Type::Path(TypePath { path, .. }) => {
                if let Some(last_seg) = path.segments.iter().last() {
                    match &last_seg.arguments {
                        PathArguments::None => Ok(None),
                        PathArguments::AngleBracketed(abga) => self.emit_with_tys(
                            ty,
                            abga.args
                                .iter()
                                .filter_map(|ga| {
                                    if let GenericArgument::Type(ty) = ga {
                                        Some(ty)
                                    } else {
                                        None
                                    }
                                })
                                .enumerate(),
                            expr,
                        ),
                        PathArguments::Parenthesized(parenthesized) => {
                            if let Some(_) = self.emit_with_tys(
                                ty,
                                parenthesized.inputs.iter().enumerate(),
                                expr,
                            )? {
                                Err(Error::new(
                                    ty.span(),
                                    "Cannot infer Parametrized of closures",
                                ))
                            } else {
                                Ok(None)
                            }
                        }
                    }
                } else {
                    Ok(None)
                }
            }
            Type::Reference(TypeReference {
                mutability, elem, ..
            }) => {
                if let Some(ret) = self.emit(elem.as_ref(), expr)? {
                    if self.access_over_ref() || self.access_over_ref_mut() && mutability.is_some()
                    {
                        Ok(Some(ret))
                    } else {
                        Err(Error::new(
                            mutability.span(),
                            format!("Cannot implement {:?} over this reference", self),
                        ))
                    }
                } else {
                    Ok(None)
                }
            }
            Type::Tuple(TypeTuple { elems, .. }) => {
                self.emit_with_tys(ty, elems.iter().enumerate(), expr)
            }
            Type::Never(_) => return Ok(None),
            Type::ImplTrait(TypeImplTrait { bounds, .. }) => {
                if let Some(_) = self.emit_with_tys(
                    ty,
                    bounds
                        .iter()
                        .filter_map(|tpb| {
                            if let TypeParamBound::Trait(tb) = tpb {
                                Some(
                                    tb.path
                                        .segments
                                        .iter()
                                        .map(|seg| match &seg.arguments {
                                            PathArguments::None => vec![],
                                            PathArguments::AngleBracketed(ab) => ab
                                                .args
                                                .iter()
                                                .filter_map(|ga| {
                                                    if let GenericArgument::Type(ty) = ga {
                                                        Some(ty)
                                                    } else {
                                                        None
                                                    }
                                                })
                                                .collect(),
                                            PathArguments::Parenthesized(pg) => pg
                                                .inputs
                                                .iter()
                                                .chain(
                                                    if let ReturnType::Type(_, ty) = &pg.output {
                                                        Some(ty.as_ref())
                                                    } else {
                                                        None
                                                    },
                                                )
                                                .collect(),
                                        })
                                        .flatten(),
                                )
                            } else {
                                None
                            }
                        })
                        .flatten()
                        .enumerate(),
                    expr,
                )? {
                    Err(Error::new(ty.span(), "Cannot parametrize over impl trait"))
                } else {
                    Ok(None)
                }
            }
            _ => Err(Error::new(
                ty.span(),
                "Cannot infer Parametrized for this type",
            )),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct EmitMaxLen;

impl Emitter for EmitContext<EmitMaxLen> {
    type Elem = Expr;

    fn item(&self, base_ty: &Type, index: usize, ty: &Type, expr: &Expr) -> Result<Option<Expr>> {
        let krate = &self.krate;
        if let Some(inner) = self.emit(ty, expr)? {
            Ok(Some(parse_quote! {
                if let (Some(l), Some(r)) = (
                    <#base_ty as #krate::Parametrized<#index>>::MAX_LEN,
                    #inner
                ) {
                    Some(l * r)
                } else {
                    None
                }
            }))
        } else {
            Ok(None)
        }
    }

    fn fold(&self, acc: &Expr, item: &Expr) -> Expr {
        parse_quote! {
            if let (Some(l), Some(r)) = (#acc, #item) {
                Some(l + r)
            } else {
                None
            }
        }
    }

    fn emit_pure(&self, _ty: &Type, _expr: &Expr) -> Expr {
        parse_quote!(::core::option::Option::Some(0usize))
    }

    fn access_over_ref(&self) -> bool {
        true
    }

    fn access_over_ref_mut(&self) -> bool {
        true
    }

    fn native_reference(&self) -> TokenStream {
        quote!(&)
    }
    fn do_deref(&self, elem: &Self::Elem) -> Self::Elem {
        parse_quote!(*#elem)
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct EmitMinLen;

impl Emitter for EmitContext<EmitMinLen> {
    type Elem = Expr;

    fn item(&self, base_ty: &Type, index: usize, ty: &Type, expr: &Expr) -> Result<Option<Expr>> {
        if let Some(inner) = self.emit(ty, expr)? {
            let krate = &self.krate;
            Ok(Some(
                parse_quote!(<#base_ty as #krate::Parametrized<#index>>::MIN_LEN * #inner),
            ))
        } else {
            Ok(None)
        }
    }

    fn fold(&self, acc: &Expr, item: &Expr) -> Expr {
        parse_quote!((#acc + #item))
    }

    fn emit_pure(&self, _ty: &Type, _expr: &Expr) -> Expr {
        parse_quote!(1usize)
    }

    fn access_over_ref(&self) -> bool {
        true
    }

    fn access_over_ref_mut(&self) -> bool {
        true
    }

    fn native_reference(&self) -> TokenStream {
        quote!(&)
    }
    fn do_deref(&self, elem: &Self::Elem) -> Self::Elem {
        parse_quote!(*#elem)
    }
}

fn fold_iter_like<T>(
    ctx: &EmitContext<T>,
    base_ty: &Type,
    index: usize,
    ty: &Type,
    expr: &Expr,
    trait_name: &TokenStream,
    fn_name: &TokenStream,
    and: &TokenStream,
) -> Result<Option<Expr>>
where
    EmitContext<T>: Emitter<Elem = Expr>,
    TokenStream: ParseQuote<<EmitContext<T> as Emitter>::Elem>,
{
    let arg = Ident::new("__parametrized_arg", Span::call_site());
    if let Some(inner) = ctx.emit(ty, &quote!(#arg).parse_quote())? {
        let krate = &ctx.krate;
        Ok(Some(parse_quote! {
            {
                let __parametrized_fn: fn(#and #ty) -> _ = |#arg| {#inner};
                <#base_ty as #krate::#trait_name<#index>>::#fn_name(#expr)
                    .map(__parametrized_fn)
                    .flatten()
            }
        }))
    } else {
        Ok(None)
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct EmitLen;

impl Emitter for EmitContext<EmitLen> {
    type Elem = Expr;

    fn item(&self, base_ty: &Type, index: usize, ty: &Type, expr: &Expr) -> Result<Option<Expr>> {
        let krate = &self.krate;
        let arg = Ident::new("__parametrized_arg", Span::call_site());
        if let Some(inner) = self.emit(ty, &parse_quote!(#arg))? {
            Ok(Some(parse_quote!(
                <#base_ty as #krate::Parametrized<#index>>::param_iter(#expr)
                .map(|#arg| #inner)
                .sum::<::core::primitive::usize>()
            )))
        } else {
            Ok(None)
        }
    }

    fn fold(&self, acc: &Expr, item: &Expr) -> Expr {
        parse_quote! { (#acc + #item) }
    }

    fn emit_pure(&self, _ty: &Type, _expr: &Expr) -> Expr {
        parse_quote!(1usize)
    }

    fn access_over_ref(&self) -> bool {
        true
    }

    fn access_over_ref_mut(&self) -> bool {
        true
    }

    fn native_reference(&self) -> TokenStream {
        quote!(&)
    }
    fn do_deref(&self, elem: &Self::Elem) -> Self::Elem {
        parse_quote!(*#elem)
    }
}

fn fold_iter_ty_like<T>(
    ctx: &EmitContext<T>,
    lt: &Lifetime,
    base_ty: &Type,
    index: usize,
    ty: &Type,
    expr: &Type,
    trait_name: &TokenStream,
    assoc_ty_name: &TokenStream,
    and: &TokenStream,
) -> Result<Option<Type>>
where
    EmitContext<T>: Emitter<Elem = Type>,
    TokenStream: ParseQuote<Type>,
{
    if let Some(inner) = ctx.emit(ty, expr)? {
        let krate = &ctx.krate;
        Ok(Some(parse_quote! {
            ::core::iter::Flatten<
                ::core::iter::Map<
                <#base_ty as #krate::#trait_name<#index>>::#assoc_ty_name<#lt>,
                fn(#and #ty) -> #inner
                    >
                        >
        }))
    } else {
        Ok(None)
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct EmitIterTy(pub Lifetime, pub Type);

impl Emitter for EmitContext<EmitIterTy> {
    type Elem = Type;

    fn item(&self, base_ty: &Type, index: usize, ty: &Type, expr: &Type) -> Result<Option<Type>> {
        let lt = &self.kind.0;
        fold_iter_ty_like(
            self,
            lt,
            base_ty,
            index,
            ty,
            expr,
            &quote!(Parametrized),
            &quote!(Iter),
            &quote!(&#lt),
        )
    }

    fn fold(&self, acc: &Type, item: &Type) -> Type {
        parse_quote!(::core::iter::Chain<#acc, #item>)
    }

    fn emit_pure(&self, _ty: &Type, _expr: &Type) -> Type {
        let lt = &self.kind.0;
        let iter_ty = &self.kind.1;
        parse_quote!(::core::iter::Once<&#lt #iter_ty>)
    }

    fn access_over_ref(&self) -> bool {
        true
    }

    fn access_over_ref_mut(&self) -> bool {
        true
    }

    fn native_reference(&self) -> TokenStream {
        quote!()
    }
    fn do_deref(&self, _elem: &Self::Elem) -> Self::Elem {
        unreachable!()
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct EmitIter;

impl Emitter for EmitContext<EmitIter> {
    type Elem = Expr;

    fn item(&self, base_ty: &Type, index: usize, ty: &Type, expr: &Expr) -> Result<Option<Expr>> {
        fold_iter_like(
            self,
            base_ty,
            index,
            ty,
            expr,
            &quote! {Parametrized},
            &quote!(param_iter),
            &quote!(& '__parametrized_lt),
        )
    }

    fn fold(&self, acc: &Expr, item: &Expr) -> Expr {
        parse_quote!(#acc.chain(#item))
    }

    fn emit_pure(&self, _ty: &Type, expr: &Expr) -> Expr {
        parse_quote!(::core::iter::once(#expr))
    }

    fn access_over_ref(&self) -> bool {
        true
    }

    fn access_over_ref_mut(&self) -> bool {
        true
    }

    fn native_reference(&self) -> TokenStream {
        quote!(&)
    }
    fn do_deref(&self, elem: &Self::Elem) -> Self::Elem {
        parse_quote!(*#elem)
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct EmitIterMutTy(pub Lifetime, pub Type);

impl Emitter for EmitContext<EmitIterMutTy> {
    type Elem = Type;

    fn item(&self, base_ty: &Type, index: usize, ty: &Type, expr: &Type) -> Result<Option<Type>> {
        let lt = &self.kind.0;
        fold_iter_ty_like(
            self,
            &self.kind.0,
            base_ty,
            index,
            ty,
            expr,
            &quote!(ParametrizedIterMut),
            &quote!(IterMut),
            &quote!(&#lt mut),
        )
    }

    fn fold(&self, acc: &Type, item: &Type) -> Type {
        parse_quote!(::core::iter::Chain<#acc, #item>)
    }

    fn emit_pure(&self, _ty: &Type, _expr: &Type) -> Type {
        let lt = &self.kind.0;
        let iter_ty = &self.kind.1;
        parse_quote!(::core::iter::Once<&#lt mut #iter_ty>)
    }

    fn access_over_ref(&self) -> bool {
        false
    }

    fn access_over_ref_mut(&self) -> bool {
        true
    }

    fn native_reference(&self) -> TokenStream {
        quote!()
    }
    fn do_deref(&self, _elem: &Self::Elem) -> Self::Elem {
        unreachable!()
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct EmitIterMut;

impl Emitter for EmitContext<EmitIterMut> {
    type Elem = Expr;

    fn item(&self, base_ty: &Type, index: usize, ty: &Type, expr: &Expr) -> Result<Option<Expr>> {
        fold_iter_like(
            self,
            base_ty,
            index,
            ty,
            expr,
            &quote!(ParametrizedIterMut),
            &quote!(param_iter_mut),
            &quote!(& '__parametrized_lt mut),
        )
    }

    fn fold(&self, acc: &Expr, item: &Expr) -> Expr {
        parse_quote!(#acc.chain(#item))
    }

    fn emit_pure(&self, _ty: &Type, expr: &Expr) -> Expr {
        parse_quote!(::core::iter::once(#expr))
    }

    fn access_over_ref(&self) -> bool {
        false
    }

    fn access_over_ref_mut(&self) -> bool {
        true
    }

    fn native_reference(&self) -> TokenStream {
        quote!(&mut)
    }
    fn do_deref(&self, elem: &Self::Elem) -> Self::Elem {
        parse_quote!(*#elem)
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct EmitIntoIterTy(pub Type);

impl Emitter for EmitContext<EmitIntoIterTy> {
    type Elem = Type;

    fn item(&self, base_ty: &Type, index: usize, ty: &Type, expr: &Type) -> Result<Option<Type>> {
        if let Some(inner) = self.emit(ty, expr)? {
            let krate = &self.krate;
            Ok(Some(parse_quote! {
                ::core::iter::Flatten<
                    ::core::iter::Map<
                        <#base_ty as #krate::ParametrizedIntoIter<#index>>::IntoIter,
                        fn(#ty) -> #inner
                    >
                >
            }))
        } else {
            Ok(None)
        }
    }

    fn fold(&self, acc: &Type, item: &Type) -> Type {
        parse_quote!(::core::iter::Chain<#acc, #item>)
    }

    fn emit_pure(&self, _ty: &Type, _expr: &Type) -> Type {
        let iter_ty = &self.kind.0;
        parse_quote!(::core::iter::Once<#iter_ty>)
    }

    fn access_over_ref(&self) -> bool {
        false
    }

    fn access_over_ref_mut(&self) -> bool {
        false
    }

    fn native_reference(&self) -> TokenStream {
        quote!()
    }
    fn do_deref(&self, _elem: &Self::Elem) -> Self::Elem {
        unreachable!()
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct EmitIntoIter;
impl Emitter for EmitContext<EmitIntoIter> {
    type Elem = Expr;
    fn item(&self, base_ty: &Type, index: usize, ty: &Type, expr: &Expr) -> Result<Option<Expr>> {
        fold_iter_like(
            self,
            base_ty,
            index,
            ty,
            expr,
            &quote!(ParametrizedIntoIter),
            &quote!(param_into_iter),
            &quote!(),
        )
    }

    fn fold(&self, acc: &Expr, item: &Expr) -> Expr {
        parse_quote!(#acc.chain(#item))
    }

    fn emit_pure(&self, _ty: &Type, expr: &Expr) -> Expr {
        parse_quote!(::core::iter::once(#expr))
    }

    fn access_over_ref(&self) -> bool {
        false
    }

    fn access_over_ref_mut(&self) -> bool {
        false
    }

    fn native_reference(&self) -> TokenStream {
        quote!()
    }
    fn do_deref(&self, _elem: &Self::Elem) -> Self::Elem {
        unreachable!()
    }
}
#[derive(PartialEq, Eq, Hash, Debug)]
pub struct EmitMap(pub Ident, pub Ident);
impl Emitter for EmitContext<EmitMap> {
    type Elem = (Expr, Type);

    fn emit_pure(&self, _ty: &Type, expr: &(Expr, Type)) -> (Expr, Type) {
        let map_fn = &self.kind.0;
        let expr = expr.clone().0;
        let map_param = &self.kind.1;
        (parse_quote!(#map_fn(#expr)), parse_quote!(#map_param))
    }

    fn access_over_ref(&self) -> bool {
        false
    }

    fn access_over_ref_mut(&self) -> bool {
        false
    }
    fn native_reference(&self) -> TokenStream {
        quote!()
    }

    fn item(
        &self,
        base_ty: &Type,
        index: usize,
        ty: &Type,
        (expr, acc_ty): &Self::Elem,
    ) -> Result<Option<Self::Elem>> {
        panic!()
        // let krate = &self.krate;
        // let map_param = &self.kind.1;
        // let arg = Ident::new("__parametrized_arg", Span::call_site());
        // if let Some((inner_exp, inner_ty)) = self.emit(acc_ty, &(parse_quote!(#arg), ty.clone()))? {
        //     Ok(Some((
        //         parse_quote!(
        //             <#base_ty as #krate::ParametrizedMap<#index, #map_param>>::param_map(
        //                 #expr,
        //                 |#arg| { #inner_exp }
        //             )
        //         ),
        //         inner_ty,
        //     )))
        // } else {
        //     Ok(None)
        // }
    }

    fn fold_item(
        &self,
        base_ty: Type,
        (expr0, ty0): &<Self as Emitter>::Elem,
        ty: &Type,
        elem: Option<<Self as Emitter>::Elem>,
        index: usize,
    ) -> Result<Option<<Self as Emitter>::Elem>> {
        let krate = &self.krate;
        let map_param = &self.kind.1;
        let replaced_ty = super::replace_type(
            ty.clone(),
            self.replacing_ty.clone(),
            parse_quote!(#map_param),
        );
        let arg = Ident::new("__parametrized_arg", Span::call_site());
        if let Some((inner_exp, inner_ty)) = self.emit(ty, &(parse_quote!(#arg), ty.clone()))? {
            let expr = if let Some((expr1, _)) = elem {
                expr1
            } else {
                expr0.clone()
            };
            Ok(Some((
                parse_quote!(
                    <#base_ty as #krate::ParametrizedMap<
                        #index,
                        #replaced_ty
                    >>::param_map(
                        #expr,
                        |#arg| { #inner_exp }
                    )
                ),
                inner_ty,
            )))
        } else {
            Ok(None)
        }
    }

    fn fold(&self, _acc: &Self::Elem, _item: &Self::Elem) -> Self::Elem {
        unreachable!()
    }
    fn do_deref(&self, (elem, ty): &Self::Elem) -> Self::Elem {
        (parse_quote!(*#elem), ty.clone())
    }
}
