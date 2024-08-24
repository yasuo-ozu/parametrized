/// Iterate over the `INDEX`th type argument of implemented type.
/// It is like [`IntoIterator`], but of the specific type arguments, indexed by `INDEX`.
///
/// For example:
/// - The 0th type argument of `Vec<T>` is `T`.
/// - The 0th type argument of `Vec<[(usize, bool)]>` is `[(usize, bool)]`.
/// - The 1st type argument of `HashMap<K, (usize, &str)>` is `(usize, &str)`.
/// - The 2nd type argument of `(T0, T1, T2, T3)` is `T2`.
pub trait IntoIteratorOfNthArgument<const INDEX: usize> {
    type Item;
    const MIN_LEN: usize;
    const MAX_LEN: Option<usize>;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item>;
    fn len_of_arg(&self) -> usize;
}

/// Map the `INDEX`th type argument of implemented type. See [`IntoIteratorOfNthArgument`].
pub trait MapOfNthArgument<const INDEX: usize, T>: IntoIteratorOfNthArgument<INDEX> {
    type Output;
    fn map_of_param(self, _: impl FnMut(Self::Item) -> T) -> Self::Output;
}

impl<'a, const INDEX: usize, T> IntoIteratorOfNthArgument<INDEX> for &'a &'a T
where
    &'a T: IntoIteratorOfNthArgument<INDEX>,
{
    type Item = <&'a T as IntoIteratorOfNthArgument<INDEX>>::Item;
    const MIN_LEN: usize = <&'a T as IntoIteratorOfNthArgument<INDEX>>::MIN_LEN;
    const MAX_LEN: Option<usize> = <&'a T as IntoIteratorOfNthArgument<INDEX>>::MAX_LEN;

    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <&'a T as IntoIteratorOfNthArgument<INDEX>>::into_iter_of_arg(*self)
    }

    fn len_of_arg(&self) -> usize {
        <&'a T as IntoIteratorOfNthArgument<INDEX>>::len_of_arg(self)
    }
}

impl<'a, const INDEX: usize, T> IntoIteratorOfNthArgument<INDEX> for &'a mut &'a mut T
where
    &'a mut T: IntoIteratorOfNthArgument<INDEX>,
{
    type Item = <&'a mut T as IntoIteratorOfNthArgument<INDEX>>::Item;
    const MIN_LEN: usize = <&'a mut T as IntoIteratorOfNthArgument<INDEX>>::MIN_LEN;
    const MAX_LEN: Option<usize> = <&'a mut T as IntoIteratorOfNthArgument<INDEX>>::MAX_LEN;

    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <&'a mut T as IntoIteratorOfNthArgument<INDEX>>::into_iter_of_arg(*self)
    }

    fn len_of_arg(&self) -> usize {
        <&'a mut T as IntoIteratorOfNthArgument<INDEX>>::len_of_arg(self)
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
        impl<$($params0,)* $param $(,$params1)*>
            IntoIteratorOfNthArgument<{impl_for_tuple!(@count $($params0),*)}>
        for ($($params0,)* $param, $($params1),*) {
            type Item = $param;
            // type IntoIter = std::iter::Once<$param>;
            const MIN_LEN: usize = 1;
            const MAX_LEN: Option<usize> = Some(1);
            fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
                core::iter::once(impl_for_tuple!(
                    @nth [$($params0),*]
                    [
                        self.0, self.1, self.2, self.3, self.4, self.5, self.6,
                        self.7, self.8, self.9, self.10, self.11
                    ]
                ))
            }
            fn len_of_arg(&self) -> usize {
                1
            }
        }
        impl<'a$(,$params0)* ,$param $(,$params1)*>
            IntoIteratorOfNthArgument<{impl_for_tuple!(@count $($params0),*)}>
        for &'a ($($params0,)* $param, $($params1),*) {
            type Item = &'a $param;
            // type IntoIter = std::iter::Once<$param>;
            const MIN_LEN: usize = 1;
            const MAX_LEN: Option<usize> = Some(1);
            fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
                core::iter::once(impl_for_tuple!(
                    @nth [$($params0),*]
                    [
                        &self.0, &self.1, &self.2, &self.3, &self.4, &self.5, &self.6,
                        &self.7, &self.8, &self.9, &self.10, &self.11
                    ]
                ))
            }
            fn len_of_arg(&self) -> usize {
                1
            }
        }
        impl<'a$(,$params0)* ,$param $(,$params1)*>
            IntoIteratorOfNthArgument<{impl_for_tuple!(@count $($params0),*)}>
        for &'a mut ($($params0,)* $param, $($params1),*) {
            type Item = &'a mut $param;
            // type IntoIter = std::iter::Once<$param>;
            const MIN_LEN: usize = 1;
            const MAX_LEN: Option<usize> = Some(1);
            fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
                core::iter::once(impl_for_tuple!(
                    @nth [$($params0),*]
                    [
                        &mut self.0, &mut self.1, &mut self.2, &mut self.3, &mut self.4,
                        &mut self.5, &mut self.6, &mut self.7, &mut self.8, &mut self.9,
                        &mut self.10, &mut self.11
                    ]
                ))
            }
            fn len_of_arg(&self) -> usize {
                1
            }
        }

        impl<U, $($params0,)* $param $(,$params1)*>
            MapOfNthArgument<{impl_for_tuple!(@count $($params0),*)}, U>
            for ($($params0,)* $param, $($params1),*)
        {
            type Output = ($($params0,)* U, $($params1),*);
            fn map_of_param(self, mut f: impl FnMut(Self::Item) -> U) -> Self::Output {
                impl_for_tuple!(@wrap_f f[$($params0),*] $param [$($params1),*] [
                    self.0, self.1, self.2, self.3, self.4, self.5, self.6,
                    self.7, self.8, self.9, self.10, self.11
                ] {})
            }
        }
    };
    () => {
        impl_for_tuple!([] T []);
        impl_for_tuple!([] T [R0]);
        impl_for_tuple!([] T [R0, R1]);
        impl_for_tuple!([] T [R0, R1, R2]);
        impl_for_tuple!([] T [R0, R1, R2, R3]);
        impl_for_tuple!([] T [R0, R1, R2, R3, R4]);
        impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5]);
        impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5, R6]);
        impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5, R6, R7]);
        impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5, R6, R7, R8]);
        impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]);
        impl_for_tuple!([] T [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10]);
        impl_for_tuple!([L0] T []);
        impl_for_tuple!([L0] T [R0]);
        impl_for_tuple!([L0] T [R0, R1]);
        impl_for_tuple!([L0] T [R0, R1, R2]);
        impl_for_tuple!([L0] T [R0, R1, R2, R3]);
        impl_for_tuple!([L0] T [R0, R1, R2, R3, R4]);
        impl_for_tuple!([L0] T [R0, R1, R2, R3, R4, R5]);
        impl_for_tuple!([L0] T [R0, R1, R2, R3, R4, R5, R6]);
        impl_for_tuple!([L0] T [R0, R1, R2, R3, R4, R5, R6, R7]);
        impl_for_tuple!([L0] T [R0, R1, R2, R3, R4, R5, R6, R7, R8]);
        impl_for_tuple!([L0] T [R0, R1, R2, R3, R4, R5, R6, R7, R8, R9]);
        impl_for_tuple!([L0, L1] T []);
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
    };
}
impl_for_tuple!();

macro_rules! impl_into_iter {
    ($(
        [$($tpar:tt)*]
        for $self_ty:ty ;
    )*) => {
        $(
            impl<$($tpar)*>
            IntoIteratorOfNthArgument<0>
            for $self_ty
            where Self: IntoIterator
            {
                type Item = <Self as IntoIterator>::Item;
                // type IntoIter = <Self as IntoIterator>::IntoIter;
                const MIN_LEN: usize = 0;
                const MAX_LEN: Option<usize> = None;
                fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
                    <Self as IntoIterator>::into_iter(self)
                }
                fn len_of_arg(&self) -> usize {
                    self.len()
                }
            }
        )*
    };
}

macro_rules! impl_map {
    ($(
        $map_to_par:ident [$($tpar:tt)*]
        for $self_ty:ty => $out_ty:ty ;
    )*) => {
        $(
            impl<$map_to_par, $($tpar)*>
            MapOfNthArgument<0, $map_to_par>
            for $self_ty
            where $out_ty: FromIterator<$map_to_par>
            {
                type Output = $out_ty;
                fn map_of_param(
                    self,
                    mut f: impl FnMut(Self::Item) -> $map_to_par
                ) -> Self::Output {
                    self.into_iter().map(|item| f(item)).collect()
                }
            }
        )*
    };
}

impl_into_iter! {
    ['a, T] for &'a Vec<T>;
    ['a, T] for &'a mut Vec<T>;
    [T] for Vec<T>;
    ['a, T] for &'a [T];
    ['a, T] for &'a mut [T];
    ['a, T] for &'a std::collections::BTreeSet<T>;
    [T] for std::collections::BTreeSet<T>;
    ['a, T] for &'a std::collections::HashSet<T>;
    [T] for std::collections::HashSet<T>;
    ['a, T] for &'a std::collections::BinaryHeap<T>;
    [T] for std::collections::BinaryHeap<T>;
    ['a, T] for &'a std::collections::LinkedList<T>;
    ['a, T] for &'a mut std::collections::LinkedList<T>;
    [T] for std::collections::LinkedList<T>;
    ['a, T] for &'a std::collections::VecDeque<T>;
    ['a, T] for &'a mut std::collections::VecDeque<T>;
    [T] for std::collections::VecDeque<T>;
}

impl_map! {
    U [T] for Vec<T> => Vec<U>;
    U [T] for std::collections::BTreeSet<T> => std::collections::BTreeSet<U>;
    U [T] for std::collections::HashSet<T> => std::collections::HashSet<U>;
    U [T] for std::collections::BinaryHeap<T> => std::collections::BinaryHeap<U>;
    U [T] for std::collections::LinkedList<T> => std::collections::LinkedList<U>;
    U [T] for std::collections::VecDeque<T> => std::collections::VecDeque<U>;
    U [T, E] for Result<T, E> => Result<U, E>;
    U [T] for Option<T> => Option<U>;
    U [const N: usize, T] for [T; N] => [U; N];
}

impl<'a, const N: usize, T> IntoIteratorOfNthArgument<0> for &'a [T; N] {
    type Item = <Self as IntoIterator>::Item;
    // type IntoIter = <Self as IntoIterator>::IntoIter;
    const MIN_LEN: usize = N;
    const MAX_LEN: Option<usize> = Some(N);
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <Self as IntoIterator>::into_iter(self)
    }
    fn len_of_arg(&self) -> usize {
        N
    }
}
impl<'a, const N: usize, T> IntoIteratorOfNthArgument<0> for &'a mut [T; N] {
    type Item = <Self as IntoIterator>::Item;
    // type IntoIter = <Self as IntoIterator>::IntoIter;
    const MIN_LEN: usize = N;
    const MAX_LEN: Option<usize> = Some(N);
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <Self as IntoIterator>::into_iter(self)
    }
    fn len_of_arg(&self) -> usize {
        N
    }
}
impl<const N: usize, T> IntoIteratorOfNthArgument<0> for [T; N] {
    type Item = <Self as IntoIterator>::Item;
    // type IntoIter = <Self as IntoIterator>::IntoIter;
    const MIN_LEN: usize = N;
    const MAX_LEN: Option<usize> = Some(N);
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <Self as IntoIterator>::into_iter(self)
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<'a, T> IntoIteratorOfNthArgument<0> for &'a Option<T> {
    type Item = <Self as IntoIterator>::Item;
    // type IntoIter = <Self as IntoIterator>::IntoIter;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = Some(1);
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <Self as IntoIterator>::into_iter(self)
    }
    fn len_of_arg(&self) -> usize {
        if self.is_none() {
            0
        } else {
            1
        }
    }
}
impl<'a, T> IntoIteratorOfNthArgument<0> for &'a mut Option<T> {
    type Item = <Self as IntoIterator>::Item;
    // type IntoIter = <Self as IntoIterator>::IntoIter;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = Some(1);
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <Self as IntoIterator>::into_iter(self)
    }
    fn len_of_arg(&self) -> usize {
        if self.is_none() {
            0
        } else {
            1
        }
    }
}
impl<T> IntoIteratorOfNthArgument<0> for Option<T> {
    type Item = <Self as IntoIterator>::Item;
    // type IntoIter = <Self as IntoIterator>::IntoIter;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = Some(1);
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <Self as IntoIterator>::into_iter(self)
    }
    fn len_of_arg(&self) -> usize {
        if self.is_none() {
            0
        } else {
            1
        }
    }
}
impl<'a, T, E> IntoIteratorOfNthArgument<0> for &'a Result<T, E> {
    type Item = <Self as IntoIterator>::Item;
    // type IntoIter = <Self as IntoIterator>::IntoIter;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = Some(1);
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <Self as IntoIterator>::into_iter(self)
    }
    fn len_of_arg(&self) -> usize {
        if self.is_ok() {
            1
        } else {
            0
        }
    }
}
impl<'a, T, E> IntoIteratorOfNthArgument<0> for &'a mut Result<T, E> {
    type Item = <Self as IntoIterator>::Item;
    // type IntoIter = <Self as IntoIterator>::IntoIter;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <Self as IntoIterator>::into_iter(self)
    }
    fn len_of_arg(&self) -> usize {
        if self.is_ok() {
            1
        } else {
            0
        }
    }
}
impl<T, E> IntoIteratorOfNthArgument<0> for Result<T, E> {
    type Item = <Self as IntoIterator>::Item;
    // type IntoIter = <Self as IntoIterator>::IntoIter;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        <Self as IntoIterator>::into_iter(self)
    }
    fn len_of_arg(&self) -> usize {
        if self.is_ok() {
            1
        } else {
            0
        }
    }
}
impl<'a, T, E> IntoIteratorOfNthArgument<1> for &'a Result<T, E> {
    type Item = &'a E;
    // type IntoIter = core::option::IntoIter<&'a E>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = Some(1);
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.as_ref().err().into_iter()
    }
    fn len_of_arg(&self) -> usize {
        if self.is_ok() {
            0
        } else {
            1
        }
    }
}
impl<'a, T, E> IntoIteratorOfNthArgument<1> for &'a mut Result<T, E> {
    type Item = &'a mut E;
    // type IntoIter = core::option::IntoIter<&'a mut E>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = Some(1);
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.as_mut().err().into_iter()
    }
    fn len_of_arg(&self) -> usize {
        if self.is_ok() {
            0
        } else {
            1
        }
    }
}
impl<T, E> IntoIteratorOfNthArgument<1> for Result<T, E> {
    type Item = E;
    // type IntoIter = core::option::IntoIter<E>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = Some(1);
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.err().into_iter()
    }
    fn len_of_arg(&self) -> usize {
        if self.is_ok() {
            0
        } else {
            1
        }
    }
}
impl<'a, K, V> IntoIteratorOfNthArgument<0> for &'a std::collections::BTreeMap<K, V> {
    type Item = &'a K;
    // type IntoIter = std::collections::hash_map::Keys<'a, K, V>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.keys()
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<K, V> IntoIteratorOfNthArgument<0> for std::collections::BTreeMap<K, V> {
    type Item = K;
    // type IntoIter = std::collections::hash_map::IntoKeys<K, V>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.into_keys()
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<'a, K, V> IntoIteratorOfNthArgument<1> for &'a std::collections::BTreeMap<K, V> {
    type Item = &'a V;
    // type IntoIter = std::collections::hash_map::Values<'a, K, V>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.values()
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<'a, K, V> IntoIteratorOfNthArgument<1> for &'a mut std::collections::BTreeMap<K, V> {
    type Item = &'a mut V;
    // type IntoIter = std::collections::hash_map::ValuesMut<'a, K, V>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.values_mut()
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<K, V> IntoIteratorOfNthArgument<1> for std::collections::BTreeMap<K, V> {
    type Item = V;
    // type IntoIter = std::collections::hash_map::IntoValues<K, V>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.into_values()
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<'a, K, V> IntoIteratorOfNthArgument<0> for &'a std::collections::HashMap<K, V> {
    type Item = &'a K;
    // type IntoIter = std::collections::hash_map::Keys<'a, K, V>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.keys()
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<K, V> IntoIteratorOfNthArgument<0> for std::collections::HashMap<K, V> {
    type Item = K;
    // type IntoIter = std::collections::hash_map::IntoKeys<K, V>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.into_keys()
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<'a, K, V> IntoIteratorOfNthArgument<1> for &'a std::collections::HashMap<K, V> {
    type Item = &'a V;
    // type IntoIter = std::collections::hash_map::Values<'a, K, V>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.values()
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<'a, K, V> IntoIteratorOfNthArgument<1> for &'a mut std::collections::HashMap<K, V> {
    type Item = &'a mut V;
    // type IntoIter = std::collections::hash_map::ValuesMut<'a, K, V>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.values_mut()
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<K, V> IntoIteratorOfNthArgument<1> for std::collections::HashMap<K, V> {
    type Item = V;
    // type IntoIter = std::collections::hash_map::IntoValues<K, V>;
    const MIN_LEN: usize = 0;
    const MAX_LEN: Option<usize> = None;
    fn into_iter_of_arg(self) -> impl Iterator<Item = Self::Item> {
        self.into_values()
    }
    fn len_of_arg(&self) -> usize {
        self.len()
    }
}
impl<U, T, E> MapOfNthArgument<1, U> for Result<T, E> {
    type Output = Result<T, U>;
    fn map_of_param(self, mut f: impl FnMut(Self::Item) -> U) -> Self::Output {
        match self {
            Ok(o) => Ok(o),
            Err(e) => Err(f(e)),
        }
    }
}
