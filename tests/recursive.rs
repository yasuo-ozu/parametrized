use parametrized::parametrized;

#[parametrized(map)]
pub enum E<T> {
    E0(S<T>),
    E1,
}

#[parametrized(map)]
pub struct S<T>(T);

#[parametrized(map)]
pub enum E1<A, B> {
    E1A(A),
    E1B(B),
}

#[parametrized(map)]
pub enum E2<A, B, C> {
    E2A(E1<A, B>),
    E2B(C),
}

#[parametrized(map)]
pub enum E3<A, B, C> {
    E3A(E2<A, B, C>),
    E3B,
}
