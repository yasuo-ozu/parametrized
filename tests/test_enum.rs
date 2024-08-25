use parametric_type::parametric_type;
use parametric_type::type_argument::IntoIteratorOfNthArgument;

#[parametric_type(K, iter, iter_mut, into_iter)]
enum Enum1<K> {
    V1,
    V2(K),
    V3 { _f1: usize, _f2: K },
}

#[test]
fn test1() {
    let e1: Enum1<()> = Enum1::V1;
    assert_eq!((&e1).len_of_arg(), 0);
    assert_eq!(
        (&e1).into_iter_of_arg().collect::<Vec<_>>(),
        vec![] as Vec<&()>
    );
    let mut e2 = Enum1::V2(123usize);
    assert_eq!((&e2).len_of_arg(), 1);
    assert_eq!((&e2).into_iter_of_arg().collect::<Vec<_>>(), vec![&123]);
    (&mut e2).into_iter_of_arg().for_each(|a| {
        *a *= 2;
    });
    assert_eq!((&e2).into_iter_of_arg().collect::<Vec<_>>(), vec![&246]);
    assert_eq!(e2.into_iter_of_arg().collect::<Vec<_>>(), vec![246]);
    let e3 = Enum1::V3 {
        _f1: 1,
        _f2: 2usize,
    };
    assert_eq!((&e3).len_of_arg(), 1);
}
