use parametrized::*;

#[allow(unused)]
#[parametrized(default, iter_mut, map)]
enum MyEnum<A> {
    E1(A),
    E2((A,)),
}
