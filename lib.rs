#![doc = include_str!("README.md")]

/// Implement traits defined in [`parametrized`] crate, specifified by
/// comma-separated arguments to this attribute macro `#[parametrized(<args>)]`.
///
/// - `default` ... implements [`Parametrized`]
/// - `iter_mut` ... implements [`ParametrizedIterMut`]
/// - `into_iter` ... implements [`ParametrizedIntoIter`]
/// - `map` ... implements [`ParametrizedMap`]
///
/// You can specify `PARAM` index by using `<arg> = [<PARAM>, ..]` syntax.
pub use parametrized_macro::parametrized;
use std::hash::Hash;

/// Provide method to iterate about `PARAM`-th type parameter. For user-defined types,
/// this trait is implemented by [`parametrized`] macro with `default` argument.
///
/// ```
/// # use parametrized::*;
/// #[parametrized(default)]
/// struct S<T>(Vec<T>, T);
/// let s = S(vec![1usize, 2usize], 3usize);
/// assert_eq!(<S<usize>>::MIN_LEN, 1);
/// assert_eq!(<S<usize>>::MAX_LEN, None);
/// assert_eq!(s.param_len(), 3);
/// assert_eq!(s.param_iter().collect::<Vec<_>>(), vec![&1usize, &2, &3]);
/// ```
pub trait Parametrized<const PARAM: usize> {
    type Item: ?Sized;
    const MIN_LEN: usize;
    const MAX_LEN: Option<usize>;
    fn param_len(&self) -> usize;

    type Iter<'a>: Iterator<Item = &'a Self::Item>
    where
        (Self, Self::Item): 'a;

    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::Item: 'a;
}

/// Provide [`ParametrizedIterMut::param_iter_mut()`] method to return mutable
/// iterator, that iterates the `PARAM`-th type parameter of given type.
///
/// ```
/// # use parametrized::*;
/// #[parametrized(iter_mut)]
/// enum E<T> {
///     E1(T),
///     E2([T; 3], T)
/// }
/// assert_eq!(<E<usize>>::MIN_LEN, 1);
/// assert_eq!(<E<usize>>::MAX_LEN, Some(4));
/// let mut e1 = E::E1(1usize);
/// e1.param_iter_mut().for_each(|i| {*i *= 3;});
/// assert_eq!(e1.param_iter().collect::<Vec<_>>(), vec![&3usize]);
/// let mut e2 = E::E2([1usize, 2, 3], 4);
/// e2.param_iter_mut().for_each(|i| {*i *= 3;});
/// assert_eq!(e2.param_iter().collect::<Vec<_>>(), vec![&3usize, &6, &9, &12]);
/// ```
pub trait ParametrizedIterMut<const PARAM: usize>: Parametrized<PARAM> {
    type IterMut<'a>: Iterator<Item = &'a mut Self::Item>
    where
        (Self, Self::Item): 'a;
    fn param_iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        Self::Item: 'a;
}

/// Provide [`ParametrizedIntoIter::param_into_iter()`] method to return iterator that
/// consumes and iterates the `PARAM`-th type parameter of given type.
///
/// ```
/// # use parametrized::*;
/// #[derive(PartialEq, Clone, Debug)]
/// struct Elem(usize);
/// #[parametrized(into_iter)]
/// struct S<T>(Vec<T>);
/// 
/// let v = vec![Elem(1), Elem(2), Elem(3)];
/// let s = S(v.clone());
/// assert_eq!(s.param_into_iter().collect::<Vec<_>>(), v);
/// ```
pub trait ParametrizedIntoIter<const PARAM: usize>: Parametrized<PARAM> + Sized {
    type IntoIter: Iterator<Item = Self::Item>
    where
        Self::Item: Sized;
    fn param_into_iter(self) -> Self::IntoIter
    where
        Self::Item: Sized;
}

/// Provide [`ParametrizedMap::param_map()`] method to map values specified by
/// `PARAM`-th type parameter of given type.
///
/// ```
/// # use parametrized::*;
/// #[parametrized(map)]
/// struct S<T>(Vec<T>);
/// 
/// let s = S(vec![1usize, 2, 3]).param_map(|s| s.to_string());
/// assert_eq!(s.param_iter().collect::<Vec<_>>(), vec![
///     &"1".to_string(),
///     &"2".to_string(),
///     &"3".to_string(),
/// ]);
/// ```
pub trait ParametrizedMap<const PARAM: usize, K>: ParametrizedIntoIter<PARAM> + Sized {
    type Mapped: ParametrizedIntoIter<PARAM, Item = K>;
    fn param_map(self, f: impl FnMut(Self::Item) -> K) -> Self::Mapped
    where
        Self::Item: Sized;
}

impl<'a, const PARAM: usize, T> Parametrized<PARAM> for &'a T
where
    T: Parametrized<PARAM>,
{
    type Item = <T as Parametrized<PARAM>>::Item;
    const MIN_LEN: usize = <T as Parametrized<PARAM>>::MIN_LEN;
    const MAX_LEN: Option<usize> = <T as Parametrized<PARAM>>::MAX_LEN;
    fn param_len(&self) -> usize {
        <T as Parametrized<PARAM>>::param_len(self)
    }
    type Iter<'b> = <T as Parametrized<PARAM>>::Iter<'b>
    where
        (Self, Self::Item): 'b;

    fn param_iter<'b>(&'b self) -> Self::Iter<'b>
    where
        Self::Item: 'b,
    {
        <T as Parametrized<PARAM>>::param_iter(self)
    }
}

impl<'a, const PARAM: usize, T> Parametrized<PARAM> for &'a mut T
where
    T: Parametrized<PARAM>,
{
    type Item = <T as Parametrized<PARAM>>::Item;
    const MIN_LEN: usize = <T as Parametrized<PARAM>>::MIN_LEN;
    const MAX_LEN: Option<usize> = <T as Parametrized<PARAM>>::MAX_LEN;
    fn param_len(&self) -> usize {
        <T as Parametrized<PARAM>>::param_len(self)
    }
    type Iter<'b> = <T as Parametrized<PARAM>>::Iter<'b>
    where
        (Self, Self::Item): 'b;

    fn param_iter<'b>(&'b self) -> Self::Iter<'b>
    where
        Self::Item: 'b,
    {
        <T as Parametrized<PARAM>>::param_iter(self)
    }
}

impl<'a, const PARAM: usize, T> ParametrizedIterMut<PARAM> for &'a mut T
where
    T: ParametrizedIterMut<PARAM>,
{
    type IterMut<'b> = <T as ParametrizedIterMut<PARAM>>::IterMut<'b>
    where
        (Self, Self::Item): 'b;

    fn param_iter_mut<'b>(&'b mut self) -> Self::IterMut<'b>
    where
        Self::Item: 'b,
    {
        <T as ParametrizedIterMut<PARAM>>::param_iter_mut(self)
    }
}

macro_rules! impl_for_tuple {
    (@wrap_f $fn:ident[] [] [$($_:expr),*] {$($out:expr),*}) => {($($out,)*)};
    (@wrap_f $fn:ident[] [$_:ident$(,$params1:ident)*] [$rhs:expr $(,$t:expr)*] {$($out:expr),*}) => {
        impl_for_tuple!(@wrap_f $fn[] [$($params1),*] [$($t),*] {$($out,)*$rhs})
    };
    (@wrap_f $fn:ident[] $param:ident [$($params1:ident),*] [$rhs:expr $(,$t:expr)*] {$($out:expr),*}) => {
        impl_for_tuple!(@wrap_f $fn[] [$($params1),*] [$($t),*] {$($out,)*($fn($rhs))})
    };
    (@wrap_f $fn:ident[$_:ident $(,$params0:ident)*] $param:ident [$($params1:ident),*] [$rhs:expr $(,$t:expr)*] {$($out:expr),*} ) => {
        impl_for_tuple!(@wrap_f $fn[$($params0),*] $param [$($params1),*] [$($t),*] {$($out,)*$rhs})
    };
    (@nth [] [$rhs:expr$(,$_:expr)*]) => { $rhs };
    (@nth [$_:expr $(,$lhs:expr)*] [$__:expr $(,$rhs:expr)*]) => {
        impl_for_tuple!(@nth [$($lhs),*] [$($rhs),*])
    };
    (@count) => {0usize};
    (@count $_:ident $(,$t:ident)*) => {
        impl_for_tuple!(@count $($t),*) + 1
    };
    (
        [$($params0:ident),*] $param:ident [$($params1:ident),*]
    ) => {
        impl<$($params0,)* $param $(,$params1)*> Parametrized<{impl_for_tuple!(@count $($params0),*)}>
        for ($($params0,)* $param, $($params1),*)
        {
            type Item = $param;
            const MIN_LEN: usize = 1;
            const MAX_LEN: Option<usize> = Some(1);
            fn param_len(&self) -> usize {
                1
            }
            type Iter<'a> = ::core::iter::Once<&'a Self::Item>
            where
                (Self, Self::Item): 'a;
            fn param_iter<'a>(&'a self) -> Self::Iter<'a> where Self::Item: 'a {
                ::core::iter::once(impl_for_tuple!(
                    @nth [$($params0),*]
                    [
                        &self.0, &self.1, &self.2, &self.3, &self.4, &self.5, &self.6,
                        &self.7, &self.8, &self.9, &self.10, &self.11
                    ]
                ))
            }
        }
        impl<$($params0,)* $param $(,$params1)*>
            ParametrizedIterMut<{impl_for_tuple!(@count $($params0),*)}>
        for ($($params0,)* $param, $($params1),*) {
            type IterMut<'a> = ::core::iter::Once<&'a mut Self::Item>
            where
                (Self, Self::Item): 'a;
            fn param_iter_mut<'a>(&'a mut self) -> Self::IterMut<'a> where Self::Item: 'a {
                core::iter::once(impl_for_tuple!(
                    @nth [$($params0),*]
                    [
                        &mut self.0, &mut self.1, &mut self.2, &mut self.3, &mut self.4,
                        &mut self.5, &mut self.6, &mut self.7, &mut self.8, &mut self.9,
                        &mut self.10, &mut self.11
                    ]
                ))
            }
        }
        impl<$($params0,)* $param $(,$params1)*>
            ParametrizedIntoIter<{impl_for_tuple!(@count $($params0),*)}>
        for ($($params0,)* $param, $($params1),*) {
            type IntoIter = ::core::iter::Once<Self::Item>
            where
                Self::Item: Sized;
            fn param_into_iter(self) -> Self::IntoIter where Self::Item: Sized {
                core::iter::once(impl_for_tuple!(
                    @nth [$($params0),*]
                    [
                        self.0, self.1, self.2, self.3, self.4,
                        self.5, self.6, self.7, self.8, self.9,
                        self.10, self.11
                    ]
                ))
            }
        }

        impl<U, $($params0,)* $param $(,$params1)*>
            ParametrizedMap<{impl_for_tuple!(@count $($params0),*)}, U>
            for ($($params0,)* $param, $($params1),*)
        {
            type Mapped = ($($params0,)* U, $($params1),*);
            fn param_map(self, mut f: impl FnMut(Self::Item) -> U) -> Self::Mapped
            where Self::Item: Sized
            {
                impl_for_tuple!(@wrap_f f[$($params0),*] $param [$($params1),*] [
                    self.0, self.1, self.2, self.3, self.4, self.5, self.6,
                    self.7, self.8, self.9, self.10, self.11
                ] {})
            }
        }
    };
}
impl_for_tuple!([] T []);
impl_for_tuple!([] T [R0]);
impl_for_tuple!([] T [R0, R1]);
impl_for_tuple!([L0] T []);
impl_for_tuple!([L0] T [R0]);
impl_for_tuple!([L0, L1] T []);

#[cfg(feature = "large-tuples")]
mod large_tuples {
    impl_for_tuple!([] T [R0, R1, R2]);
    impl_for_tuple!([] T [R0, R1, R2, R3]);
    impl_for_tuple!([] T [R0, R1, R2, R3, R4]);
    impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5]);
    impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5, R6]);
    impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5, R6, R7]);
    impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5, R6, R7, R8]);
    impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]);
    impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10]);
    impl_for_tuple!([L0] T [R0, R1]);
    impl_for_tuple!([L0] T [R0, R1, R2]);
    impl_for_tuple!([L0] T [R0, R1, R2, R3]);
    impl_for_tuple!([L0] T [R0, R1, R2, R3, R4]);
    impl_for_tuple!([L0] T [R0, R1, R2, R3, R4, R5]);
    impl_for_tuple!([L0] T [R0, R1, R2, R3, R4, R5, R6]);
    impl_for_tuple!([L0] T [R0, R1, R2, R3, R4, R5, R6, R7]);
    impl_for_tuple!([L0] T [R0, R1, R2, R3, R4, R5, R6, R7, R8]);
    impl_for_tuple!([L0] T [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]);
    impl_for_tuple!([L0, L1] T [R0]);
    impl_for_tuple!([L0, L1] T [R0, R1]);
    impl_for_tuple!([L0, L1] T [R0, R1, R2]);
    impl_for_tuple!([L0, L1] T [R0, R1, R2, R3]);
    impl_for_tuple!([L0, L1] T [R0, R1, R2, R3, R4]);
    impl_for_tuple!([L0, L1] T [R0, R1, R2, R3, R4, R5]);
    impl_for_tuple!([L0, L1] T [R0, R1, R2, R3, R4, R5, R6]);
    impl_for_tuple!([L0, L1] T [R0, R1, R2, R3, R4, R5, R6, R7]);
    impl_for_tuple!([L0, L1] T [R0, R1, R2, R3, R4, R5, R6, R7, R8]);
    impl_for_tuple!([L0, L1, L2] T []);
    impl_for_tuple!([L0, L1, L2] T [R0]);
    impl_for_tuple!([L0, L1, L2] T [R0, R1]);
    impl_for_tuple!([L0, L1, L2] T [R0, R1, R2]);
    impl_for_tuple!([L0, L1, L2] T [R0, R1, R2, R3]);
    impl_for_tuple!([L0, L1, L2] T [R0, R1, R2, R3, R4]);
    impl_for_tuple!([L0, L1, L2] T [R0, R1, R2, R3, R4, R5]);
    impl_for_tuple!([L0, L1, L2] T [R0, R1, R2, R3, R4, R5, R6]);
    impl_for_tuple!([L0, L1, L2] T [R0, R1, R2, R3, R4, R5, R6, R7]);
    impl_for_tuple!([L0, L1, L2, L3] T []);
    impl_for_tuple!([L0, L1, L2, L3] T [R0]);
    impl_for_tuple!([L0, L1, L2, L3] T [R0, R1]);
    impl_for_tuple!([L0, L1, L2, L3] T [R0, R1, R2]);
    impl_for_tuple!([L0, L1, L2, L3] T [R0, R1, R2, R3]);
    impl_for_tuple!([L0, L1, L2, L3] T [R0, R1, R2, R3, R4]);
    impl_for_tuple!([L0, L1, L2, L3] T [R0, R1, R2, R3, R4, R5]);
    impl_for_tuple!([L0, L1, L2, L3] T [R0, R1, R2, R3, R4, R5, R6]);
    impl_for_tuple!([L0, L1, L2, L3, L4] T []);
    impl_for_tuple!([L0, L1, L2, L3, L4] T [R0]);
    impl_for_tuple!([L0, L1, L2, L3, L4] T [R0, R1]);
    impl_for_tuple!([L0, L1, L2, L3, L4] T [R0, R1, R2]);
    impl_for_tuple!([L0, L1, L2, L3, L4] T [R0, R1, R2, R3]);
    impl_for_tuple!([L0, L1, L2, L3, L4] T [R0, R1, R2, R3, R4]);
    impl_for_tuple!([L0, L1, L2, L3, L4] T [R0, R1, R2, R3, R4, R5]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5] T []);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5] T [R0]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5] T [R0, R1]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5] T [R0, R1, R2]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5] T [R0, R1, R2, R3]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5] T [R0, R1, R2, R3, R4]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6] T []);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6] T [R0]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6] T [R0, R1]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6] T [R0, R1, R2]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6] T [R0, R1, R2, R3]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6, L7] T []);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6, L7] T [R0]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6, L7] T [R0, R1]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6, L7] T [R0, R1, R2]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6, L7, L8] T []);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6, L7, L8] T [R0]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6, L7, L8] T [R0, R1]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6, L7, L8, L9] T []);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6, L7, L8, L9] T [R0]);
    impl_for_tuple!([L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10] T []);
}

macro_rules! emit_impl_trait {
    (
        [$(,)?]
        impl_generics = [$($tpar: tt)*],
        PARAM = $n:literal,
        Self = $self_ty:ty,
        self = $self_val:ident,
        {
            Item = $item_ty:ty,
            MIN_LEN = $min_len:expr,
            MAX_LEN = $max_len:expr,
            param_len = { $($param_len:tt)* },
        }
        {
            lt = $lt:lifetime,
            Iter = $iter_ty:ty,
            param_iter = {$($param_iter:tt)*},
        }
        $($_:tt)*
    ) => {
        impl<$($tpar)*> Parametrized<$n> for $self_ty
        {
            type Item = $item_ty;
            const MIN_LEN: usize = $min_len;
            const MAX_LEN: Option<usize> = $max_len;
            fn param_len(&$self_val) -> usize { $($param_len)* }
            type Iter<$lt> = $iter_ty where (Self, Self::Item): $lt;
            fn param_iter<$lt>(& $lt $self_val) -> Self::Iter<$lt> where Self::Item: $lt {
                $($param_iter)*
            }
        }

    };
    (
        [iter_mut, $($acc:tt)*]
        impl_generics = [$($tpar: tt)*],
        PARAM = $n:literal,
        Self = $self_ty:ty,
        self = $self_val:ident,
        { $($t0:tt)* }
        { lt = $lt:lifetime, $($t1:tt)* }
        {
            IterMut = $iter_mut_ty:ty,
            param_iter_mut = {$($param_iter_mut:tt)*},
        }
        $($_:tt)*
    ) => {
        impl<$($tpar)*> ParametrizedIterMut<$n> for $self_ty
        {
            type IterMut<$lt> = $iter_mut_ty where (Self, Self::Item): $lt;
            fn param_iter_mut<$lt>(& $lt mut $self_val) -> Self::IterMut<$lt> where Self::Item: $lt {
                $($param_iter_mut)*
            }
        }
        emit_impl_trait!(
            [$($acc)*]
            impl_generics = [$($tpar)*],
            PARAM = $n,
            Self = $self_ty,
            self = $self_val,
            { $($t0)* }
            { lt = $lt, $($t1)* }
        );
    };
    (
        [into_iter, $($acc:tt)*]
        impl_generics = [$($tpar: tt)*],
        PARAM = $n:literal,
        Self = $self_ty:ty,
        self = $self_val:ident,
        { $($t0:tt)* }
        { $($t1:tt)* }
        { $($t2:tt)* }
        {
            IntoIter = $into_iter_ty:ty,
            param_into_iter = {$($param_into_iter:tt)*},
        }
        $($_:tt)*
    ) => {
        impl<$($tpar)*> ParametrizedIntoIter<$n> for $self_ty
        {
            type IntoIter = $into_iter_ty;
            fn param_into_iter($self_val) -> Self::IntoIter {
                $($param_into_iter)*
            }
        }
        emit_impl_trait!(
            [$($acc)*]
            impl_generics = [$($tpar)*],
            PARAM = $n,
            Self = $self_ty,
            self = $self_val,
            { $($t0)* }
            { $($t1)* }
            { $($t2)* }
        );
    };
    (
        [map, $($acc:tt)*]
        impl_generics = [$($tpar: tt)*],
        PARAM = $n:literal,
        Self = $self_ty:ty,
        self = $self_val:ident,
        { $($t0:tt)* }
        { $($t1:tt)* }
        { $($t2:tt)* }
        { $($t3:tt)* }
        {
            f = $f_val:ident,
            T = $arg_ty:ident,
            Mapped = $mapped_ty:ty,
            param_map = {$($param_map:tt)*},
        }
    ) => {
        impl<$($tpar)*,$arg_ty> ParametrizedMap<$n, $arg_ty> for $self_ty
        {
            type Mapped = $mapped_ty;
            fn param_map($self_val, $f_val: impl FnMut(Self::Item) -> $arg_ty) -> Self::Mapped {
                $($param_map)*
            }
        }
        emit_impl_trait!(
            [$($acc)*]
            impl_generics = [$($tpar)*],
            PARAM = $n,
            Self = $self_ty,
            self = $self_val,
            { $($t0)* }
            { $($t1)* }
            { $($t2)* }
            { $($t3)* }
        );
    };
}

macro_rules! impl_all {
    ($(
        [$($tpar:tt)*]
        $($fn:ident),*
        for $self_ty:ty $(,T = $arg_ty:ident, Mapped = $mapped_ty:ty)? ;
    )*) => {
        $(
            emit_impl_trait!(
                [$($fn,)*]
                impl_generics = [$($tpar)*],
                PARAM = 0,
                Self = $self_ty,
                self = self,
                {
                    Item = <Self as IntoIterator>::Item,
                    MIN_LEN = 0,
                    MAX_LEN = None,
                    param_len = { self.len() },
                }
                {
                    lt = 'a,
                    Iter = <&'a Self as IntoIterator>::IntoIter,
                    param_iter = {<&'a Self as IntoIterator>::into_iter(self)},
                }
                {
                    IterMut = <&'a mut Self as IntoIterator>::IntoIter,
                    param_iter_mut = {<&'a mut Self as IntoIterator>::into_iter(self)},
                }
                {
                    IntoIter = <Self as IntoIterator>::IntoIter,
                    param_into_iter = { <Self as IntoIterator>::into_iter(self) },
                }
                $({
                    f = f,
                    T = $arg_ty,
                    Mapped = $mapped_ty,
                    param_map = { <Self as IntoIterator>::into_iter(self).map(f).collect() },
                })?
            );
        )*
    };
}

impl_all! {
    [T] map, into_iter, iter_mut for Vec<T>, T = M, Mapped = Vec<M>;
    [T] into_iter for std::collections::BTreeSet<T>;
    [T] into_iter for std::collections::HashSet<T>;
    [T] into_iter for std::collections::BinaryHeap<T>;
    [T] map, into_iter, iter_mut for std::collections::LinkedList<T>,
        T = M, Mapped = std::collections::LinkedList<M>;
    [T] map, into_iter, iter_mut for std::collections::VecDeque<T>,
        T = M, Mapped = std::collections::VecDeque<M>;
}

impl<const N: usize, T> ParametrizedIntoIter<0> for [T; N] {
    type IntoIter = <Self as IntoIterator>::IntoIter;
    fn param_into_iter(self) -> Self::IntoIter {
        <Self as IntoIterator>::into_iter(self)
    }
}
impl<const N: usize, T> ParametrizedIterMut<0> for [T; N] {
    type IterMut<'a> = <&'a mut Self as IntoIterator>::IntoIter
    where
        (Self, Self::Item): 'a;
    fn param_iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        Self::Item: 'a,
    {
        <&'a mut Self as IntoIterator>::into_iter(self)
    }
}
impl<const N: usize, T> Parametrized<0> for [T; N] {
    type Item = <Self as IntoIterator>::Item;
    const MIN_LEN: usize = N;
    const MAX_LEN: Option<usize> = Some(N);
    fn param_len(&self) -> usize {
        self.len()
    }
    type Iter<'a> = <&'a Self as IntoIterator>::IntoIter where (Self, Self::Item): 
'a;
    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::Item: 'a,
    {
        <&'a Self as IntoIterator>::into_iter(self)
    }
}

impl<T> ParametrizedIntoIter<0> for Box<T> {
    type IntoIter = core::iter::Once<T>;
    fn param_into_iter(self) -> Self::IntoIter {
        core::iter::once(*self)
    }
}
impl<T> ParametrizedIterMut<0> for Box<T> {
    type IterMut<'a> = core::iter::Once<&'a mut T>
    where
        (Self, Self::Item): 'a;
    fn param_iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        Self::Item: 'a,
    {
        core::iter::once(&mut *self)
    }
}
impl< T> Parametrized<0> for Box<T> {
    type Item = T;
    const MIN_LEN: usize = 1;
    const MAX_LEN: Option<usize> = Some(1);
    fn param_len(&self) -> usize {
        1
    }
    type Iter<'a> = core::iter::Once<&'a T> where (Self, Self::Item): 
'a;
    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::Item: 'a,
    {
        core::iter::once(self.as_ref())
    }
}

impl<T, M: Ord> ParametrizedMap<0, M> for std::collections::BTreeSet<T> {
    type Mapped = std::collections::BTreeSet<M>;
    fn param_map(self, f: impl FnMut(Self::Item) -> M) -> Self::Mapped
    where
        Self::Item: Sized,
    {
        self.into_iter().map(f).collect()
    }
}
impl<T, M: Eq + Hash> ParametrizedMap<0, M> for std::collections::HashSet<T> {
    type Mapped = std::collections::HashSet<M>;

    fn param_map(self, f: impl FnMut(Self::Item) -> M) -> Self::Mapped
    where
        Self::Item: Sized,
    {
        self.into_iter().map(f).collect()
    }
}
impl<T, M: Ord> ParametrizedMap<0, M> for std::collections::BinaryHeap<T> {
    type Mapped = std::collections::BinaryHeap<M>;

    fn param_map(self, f: impl FnMut(Self::Item) -> M) -> Self::Mapped
    where
        Self::Item: Sized,
    {
        self.into_iter().map(f).collect()
    }
}
impl<T, E> Parametrized<0> for Result<T, E> {
    type Item = T;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = Some(1);
    fn param_len(&self) -> usize {
        self.is_ok() as usize
    }
    type Iter<'a> = std::result::Iter<'a, T> where (T,E):'a;
    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::Item: 'a,
    {
        self.iter()
    }
}
impl<T, E> ParametrizedIterMut<0> for Result<T, E> {
    type IterMut<'a> = std::result::IterMut<'a,T>
    where
        (Self, Self::Item): 'a;

    fn param_iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        Self::Item: 'a,
    {
        self.iter_mut()
    }
}
impl<T, E> ParametrizedIntoIter<0> for Result<T, E> {
    type IntoIter = std::result::IntoIter<T>
    where
        Self::Item: Sized;

    fn param_into_iter(self) -> Self::IntoIter
    where
        Self::Item: Sized,
    {
        self.into_iter()
    }
}
impl<T, E, M> ParametrizedMap<0, M> for Result<T, E> {
    type Mapped = Result<M, E>;

    fn param_map(self, f: impl FnMut(Self::Item) -> M) -> Self::Mapped
    where
        Self::Item: Sized,
    {
        self.map(f)
    }
}

impl<T, E> Parametrized<1> for Result<T, E> {
    type Item = E;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = Some(1);
    fn param_len(&self) -> usize {
        self.is_err() as usize
    }
    type Iter<'a> = std::option::IntoIter<&'a E> where (T, E): 'a;

    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        (T, E): 'a,
    {
        self.as_ref().err().into_iter()
    }
}
impl<T, E> ParametrizedIterMut<1> for Result<T, E> {
    type IterMut<'a> = std::option::IntoIter<&'a mut E> where (T,E):'a;

    fn param_iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        Self::Item: 'a,
    {
        self.as_mut().err().into_iter()
    }
}
impl<T, E> ParametrizedIntoIter<1> for Result<T, E> {
    type IntoIter = std::option::IntoIter<E>;
    fn param_into_iter(self) -> Self::IntoIter
    where
        Self::Item: Sized,
    {
        self.err().into_iter()
    }
}
impl<T, E, M> ParametrizedMap<1, M> for Result<T, E> {
    type Mapped = Result<T, M>;
    fn param_map(self, f: impl FnMut(Self::Item) -> M) -> Self::Mapped
    where
        Self::Item: Sized,
    {
        self.map_err(f)
    }
}
impl<const N: usize, T, M> ParametrizedMap<0, M> for [T; N] {
    type Mapped = [M; N];

    fn param_map(self, f: impl FnMut(Self::Item) -> M) -> Self::Mapped
    where
        Self::Item: Sized,
    {
        self.map(f)
    }
}
impl<T> ParametrizedIterMut<0> for [T] {
    type IterMut<'a> = std::slice::IterMut<'a, T> where T: 'a;
    fn param_iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        T: 'a,
    {
        self.iter_mut()
    }
}
impl<T> Parametrized<0> for [T] {
    type Item = T;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn param_len(&self) -> usize {
        self.len()
    }
    type Iter<'a> = std::slice::Iter<'a, T> where T: 'a;
    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::Item: 'a,
    {
        <&'a Self as IntoIterator>::into_iter(self)
    }
}
impl<T> ParametrizedIntoIter<0> for Option<T> {
    type IntoIter = core::option::IntoIter<T>;
    fn param_into_iter(self) -> Self::IntoIter {
        <Self as IntoIterator>::into_iter(self)
    }
}
impl<T> ParametrizedIterMut<0> for Option<T> {
    type IterMut<'a> = core::option::IterMut<'a,T> where T:'a;
    fn param_iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        T: 'a,
    {
        <&'a mut Self as IntoIterator>::into_iter(self)
    }
}
impl<T> Parametrized<0> for Option<T> {
    type Item = T;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn param_len(&self) -> usize {
        self.is_some() as usize
    }
    type Iter<'a> = core::option::Iter<'a,T> where T:'a;
    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::Item: 'a,
    {
        <&'a Self as IntoIterator>::into_iter(self)
    }
}

impl<K, V> Parametrized<0> for std::collections::BTreeMap<K, V> {
    type Item = K;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn param_len(&self) -> usize {
        self.len()
    }
    type Iter<'a> = std::collections::btree_map::Keys<'a, K, V> where (K, V): 'a;
    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::Item: 'a,
    {
        self.keys()
    }
}

impl<K, V> ParametrizedIntoIter<0> for std::collections::BTreeMap<K, V> {
    type IntoIter = std::collections::btree_map::IntoKeys<K, V>;
    fn param_into_iter(self) -> Self::IntoIter
    where
        Self::Item: Sized,
    {
        self.into_keys()
    }
}
impl<L: Ord, K, V> ParametrizedMap<0, L> for std::collections::BTreeMap<K, V> {
    type Mapped = std::collections::BTreeMap<L, V>;
    fn param_map(self, mut f: impl FnMut(Self::Item) -> L) -> Self::Mapped {
        self.into_iter().map(|(k, v)| (f(k), v)).collect()
    }
}
impl<K, V> Parametrized<1> for std::collections::BTreeMap<K, V> {
    type Item = V;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn param_len(&self) -> usize {
        self.len()
    }
    type Iter<'a> = std::collections::btree_map::Values<'a, K, V> where (K, V): 'a;
    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        (K, V): 'a,
    {
        self.values()
    }
}
impl<K, V> ParametrizedIterMut<1> for std::collections::BTreeMap<K, V> {
    type IterMut<'a> = std::collections::btree_map::ValuesMut<'a, K, V> where (K, V): 'a;
    fn param_iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        (K, V): 'a,
    {
        self.values_mut()
    }
}
impl<K, V> ParametrizedIntoIter<1> for std::collections::BTreeMap<K, V> {
    type IntoIter = std::collections::btree_map::IntoValues<K, V>;
    fn param_into_iter(self) -> Self::IntoIter
    where
        Self::Item: Sized,
    {
        self.into_values()
    }
}
impl<L, K: Ord, V> ParametrizedMap<1, L> for std::collections::BTreeMap<K, V> {
    type Mapped = std::collections::BTreeMap<K, L>;
    fn param_map(self, mut f: impl FnMut(Self::Item) -> L) -> Self::Mapped {
        self.into_iter().map(|(k, v)| (k, f(v))).collect()
    }
}
impl<K, V> Parametrized<0> for std::collections::HashMap<K, V> {
    type Item = K;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn param_len(&self) -> usize {
        self.len()
    }
    type Iter<'a> = std::collections::hash_map::Keys<'a, K, V> where (K, V): 'a;
    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::Item: 'a,
    {
        self.keys()
    }
}

impl<K, V> ParametrizedIntoIter<0> for std::collections::HashMap<K, V> {
    type IntoIter = std::collections::hash_map::IntoKeys<K, V>;
    fn param_into_iter(self) -> Self::IntoIter
    where
        Self::Item: Sized,
    {
        self.into_keys()
    }
}
impl<L: Hash + Eq, K, V> ParametrizedMap<0, L> for std::collections::HashMap<K, V> {
    type Mapped = std::collections::HashMap<L, V>;
    fn param_map(self, mut f: impl FnMut(Self::Item) -> L) -> Self::Mapped {
        self.into_iter().map(|(k, v)| (f(k), v)).collect()
    }
}
impl<K, V> Parametrized<1> for std::collections::HashMap<K, V> {
    type Item = V;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn param_len(&self) -> usize {
        self.len()
    }
    type Iter<'a> = std::collections::hash_map::Values<'a, K, V> where (K, V): 'a;
    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        (K, V): 'a,
    {
        self.values()
    }
}
impl<K, V> ParametrizedIterMut<1> for std::collections::HashMap<K, V> {
    type IterMut<'a> = std::collections::hash_map::ValuesMut<'a, K, V> where (K, V): 'a;
    fn param_iter_mut<'a>(&'a mut self) -> Self::IterMut<'a>
    where
        (K, V): 'a,
    {
        self.values_mut()
    }
}
impl<K, V> ParametrizedIntoIter<1> for std::collections::HashMap<K, V> {
    type IntoIter = std::collections::hash_map::IntoValues<K, V>;
    fn param_into_iter(self) -> Self::IntoIter
    where
        Self::Item: Sized,
    {
        self.into_values()
    }
}
impl<L: Hash + Eq, K: Hash + Eq, V> ParametrizedMap<1, L> for std::collections::HashMap<K, V> {
    type Mapped = std::collections::HashMap<K, L>;
    fn param_map(self, mut f: impl FnMut(Self::Item) -> L) -> Self::Mapped {
        self.into_iter().map(|(k, v)| (k, f(v))).collect()
    }
}

#[doc(hidden)]
pub mod _imp {
    pub use sumtype::sumtype;
}
