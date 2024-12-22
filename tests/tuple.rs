use parametrized::*;

#[allow(unused)]
#[parametrized(default)]
struct MyStruct<T>((T, Vec<T>));
