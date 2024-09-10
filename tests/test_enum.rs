use parametrized::*;

#[parametrized(default, iter_mut, into_iter)]
enum Enum1<K> {
    V1,
    V2(K),
    V3 { _f1: usize, _f2: K },
}
#[test]
fn test1() {
    let e1: Enum1<()> = Enum1::V1;
    assert_eq!(e1.param_len(), 0);
    assert_eq!(e1.param_iter().collect::<Vec<_>>(), vec![] as Vec<&()>);
    let mut e2 = Enum1::V2(123usize);
    assert_eq!(e2.param_len(), 1);
    assert_eq!(e2.param_iter().collect::<Vec<_>>(), vec![&123]);
    e2.param_iter_mut().for_each(|a| {
        *a *= 2;
    });
    assert_eq!(e2.param_iter().collect::<Vec<_>>(), vec![&246]);
    assert_eq!(e2.param_into_iter().collect::<Vec<_>>(), vec![246]);
    let e3 = Enum1::V3 {
        _f1: 1,
        _f2: 2usize,
    };
    assert_eq!(e3.param_len(), 1);
}
