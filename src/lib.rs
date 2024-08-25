pub mod type_argument;

pub use parametric_type_macro::parametric_type;

/// Main trait to cooperate with parametric types, which defines iterations over annotated type.
///
/// This trait is implemented by [`parametric_type`] macro.
pub unsafe trait ParametricType<const LABEL: char> {
    type Item;

    const MIN_LEN: usize;
    const MAX_LEN: Option<usize>;

    fn len(&self) -> usize;
    fn iter<'a>(&'a self) -> impl Iterator<Item = &'a Self::Item>;
    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut Self::Item>
    where
        &'a Self: IntoIterOfLabel<LABEL, Item = &'a mut Self::Item>;
    fn into_iter(self) -> impl Iterator<Item = <Self as IntoIterOfLabel<LABEL>>::Item>
    where
        Self: IntoIterOfLabel<LABEL> + Sized;

    type Mapped<P>
    where
        Self: MapOfLabel<LABEL, P>;
    fn map<P>(self, f: impl FnMut(<Self as IntoIterOfLabel<LABEL>>::Item) -> P) -> Self::Mapped<P>
    where
        Self: MapOfLabel<LABEL, P, Output = Self::Mapped<P>> + Sized;
}

#[doc(hidden)]
pub unsafe trait IntoIterOfLabel<const LABEL: char> {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;
    const MIN_LEN: usize;
    const MAX_LEN: Option<usize>;
    fn into_iter_of_label(self) -> Self::IntoIter;
    fn len_of_label(&self) -> usize;
}

#[doc(hidden)]
pub unsafe trait MapOfLabel<const LABEL: char, P>: IntoIterOfLabel<LABEL> {
    type Output;
    fn map(self, f: impl FnMut(Self::Item) -> P) -> Self::Output;
}

#[doc(hidden)]
pub mod _imp {
    pub use sumtype::sumtype;
}
