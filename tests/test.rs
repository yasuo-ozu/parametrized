use parametric_type::parametric_type;

#[parametric_type(krate: parametric_type, K)]
struct S<K>(usize, Vec<(usize, K)>);
