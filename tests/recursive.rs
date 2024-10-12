use parametrized::parametrized;

#[parametrized(map)]
pub enum E<T> {
    E0(S<T>),
    E1,
}

#[parametrized(map)]
pub struct S<T>(T);
