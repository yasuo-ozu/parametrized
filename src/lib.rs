pub unsafe trait ParametricType<const LABEL: char> {
    type Variable;

    fn variables_len(&self) -> usize;
    fn variables<'a>(&'a self) -> impl Iterator<Item = &'a Self::Variable>;
    fn variables_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut Self::Variable>;
    fn into_variables(self) -> impl Iterator<Item = Self::Variable>;
}

pub unsafe trait Map<const LABEL: char, P>: ParametricType<LABEL> {
    type Mapped: ParametricType<LABEL, Variable = P>;
    fn map(self, f: impl FnMut(Self::Variable) -> P) -> Self::Mapped;
}

pub unsafe trait ParametricEnum<const LABEL: char>: Sized {
    type Discriminant: Discriminant
        + From<core::mem::Discriminant<Self>>
        + Into<core::mem::Discriminant<Self>>;
    fn discriminant(&self) -> Self::Discriminant;
}

pub unsafe trait Discriminant:
    core::fmt::Display + core::fmt::Debug + core::hash::Hash + PartialEq + Eq + PartialOrd + Ord
{
    fn iter_all() -> impl Iterator<Item = Self>
    where
        Self: Sized;
}

pub mod imp {
    pub trait IntoIteratorOfNthArgument<const INDEX: usize> {
        type Item;
        type IntoIter: Iterator<Item = Self::Item>;
        const MIN_LEN: usize;
        const MAX_LEN: Option<usize>;
        fn into_iter_of_arg(self) -> Self::IntoIter;
        fn len_of_arg(&self) -> usize;
    }

    pub trait MapOfNthArgument<const INDEX: usize, T>: IntoIteratorOfNthArgument<INDEX> {
        type Output;
        fn map_of_param(self, _: impl FnMut(Self::Item) -> T) -> Self::Output;
    }

    macro_rules! impl_into_iter {
        ($(
            [$($tpar:tt)*]
            for $self_ty:ty  ;
        )*) => {
            $(
                impl<$($tpar)*>
                IntoIteratorOfNthArgument<0>
                for $self_ty
                where Self: IntoIterator
                {
                    type Item = <Self as IntoIterator>::Item;
                    type IntoIter = <Self as IntoIterator>::IntoIter;
                    const MIN_LEN: usize = 0;
                    const MAX_LEN: Option<usize> = None;
                    fn into_iter_of_arg(self) -> Self::IntoIter {
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
        type IntoIter = <Self as IntoIterator>::IntoIter;
        const MIN_LEN: usize = N;
        const MAX_LEN: Option<usize> = Some(N);
        fn into_iter_of_arg(self) -> Self::IntoIter {
            <Self as IntoIterator>::into_iter(self)
        }
        fn len_of_arg(&self) -> usize {
            N
        }
    }
    impl<'a, const N: usize, T> IntoIteratorOfNthArgument<0> for &'a mut [T; N] {
        type Item = <Self as IntoIterator>::Item;
        type IntoIter = <Self as IntoIterator>::IntoIter;
        const MIN_LEN: usize = N;
        const MAX_LEN: Option<usize> = Some(N);
        fn into_iter_of_arg(self) -> Self::IntoIter {
            <Self as IntoIterator>::into_iter(self)
        }
        fn len_of_arg(&self) -> usize {
            N
        }
    }
    impl<const N: usize, T> IntoIteratorOfNthArgument<0> for [T; N] {
        type Item = <Self as IntoIterator>::Item;
        type IntoIter = <Self as IntoIterator>::IntoIter;
        const MIN_LEN: usize = N;
        const MAX_LEN: Option<usize> = Some(N);
        fn into_iter_of_arg(self) -> Self::IntoIter {
            <Self as IntoIterator>::into_iter(self)
        }
        fn len_of_arg(&self) -> usize {
            self.len()
        }
    }
    impl<'a, T> IntoIteratorOfNthArgument<0> for &'a Option<T> {
        type Item = <Self as IntoIterator>::Item;
        type IntoIter = <Self as IntoIterator>::IntoIter;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = Some(1);
        fn into_iter_of_arg(self) -> Self::IntoIter {
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
        type IntoIter = <Self as IntoIterator>::IntoIter;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = Some(1);
        fn into_iter_of_arg(self) -> Self::IntoIter {
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
        type IntoIter = <Self as IntoIterator>::IntoIter;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = Some(1);
        fn into_iter_of_arg(self) -> Self::IntoIter {
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
        type IntoIter = <Self as IntoIterator>::IntoIter;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = Some(1);
        fn into_iter_of_arg(self) -> Self::IntoIter {
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
        type IntoIter = <Self as IntoIterator>::IntoIter;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = None;
        fn into_iter_of_arg(self) -> Self::IntoIter {
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
        type IntoIter = <Self as IntoIterator>::IntoIter;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = None;
        fn into_iter_of_arg(self) -> Self::IntoIter {
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
        type IntoIter = core::option::IntoIter<&'a E>;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = Some(1);
        fn into_iter_of_arg(self) -> Self::IntoIter {
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
        type IntoIter = core::option::IntoIter<&'a mut E>;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = Some(1);
        fn into_iter_of_arg(self) -> Self::IntoIter {
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
        type IntoIter = core::option::IntoIter<E>;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = Some(1);
        fn into_iter_of_arg(self) -> Self::IntoIter {
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
    impl<'a, K, V> IntoIteratorOfNthArgument<0> for &'a std::collections::HashMap<K, V> {
        type Item = &'a K;
        type IntoIter = std::collections::hash_map::Keys<'a, K, V>;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = None;
        fn into_iter_of_arg(self) -> Self::IntoIter {
            self.keys()
        }
        fn len_of_arg(&self) -> usize {
            self.len()
        }
    }
    impl<K, V> IntoIteratorOfNthArgument<0> for std::collections::HashMap<K, V> {
        type Item = K;
        type IntoIter = std::collections::hash_map::IntoKeys<K, V>;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = None;
        fn into_iter_of_arg(self) -> Self::IntoIter {
            self.into_keys()
        }
        fn len_of_arg(&self) -> usize {
            self.len()
        }
    }
    impl<'a, K, V> IntoIteratorOfNthArgument<1> for &'a std::collections::HashMap<K, V> {
        type Item = &'a V;
        type IntoIter = std::collections::hash_map::Values<'a, K, V>;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = None;
        fn into_iter_of_arg(self) -> Self::IntoIter {
            self.values()
        }
        fn len_of_arg(&self) -> usize {
            self.len()
        }
    }
    impl<'a, K, V> IntoIteratorOfNthArgument<1> for &'a mut std::collections::HashMap<K, V> {
        type Item = &'a mut V;
        type IntoIter = std::collections::hash_map::ValuesMut<'a, K, V>;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = None;
        fn into_iter_of_arg(self) -> Self::IntoIter {
            self.values_mut()
        }
        fn len_of_arg(&self) -> usize {
            self.len()
        }
    }
    impl<K, V> IntoIteratorOfNthArgument<1> for std::collections::HashMap<K, V> {
        type Item = V;
        type IntoIter = std::collections::hash_map::IntoValues<K, V>;
        const MIN_LEN: usize = 0;
        const MAX_LEN: Option<usize> = None;
        fn into_iter_of_arg(self) -> Self::IntoIter {
            self.into_values()
        }
        fn len_of_arg(&self) -> usize {
            self.len()
        }
    }
    impl<U, T, E> MapOfNthArgument<1, U> for Result<T, E>
    where
        Result<U, E>: FromIterator<U>,
    {
        type Output = Result<T, U>;
        fn map_of_param(self, mut f: impl FnMut(Self::Item) -> U) -> Self::Output {
            match self {
                Ok(o) => Ok(o),
                Err(e) => Err(f(e)),
            }
        }
    }
}
