use parametrized::*;

#[allow(unused)]
#[parametrized(default, iter_mut, into_iter)]
struct MyStruct<T>((T, Vec<T>));
