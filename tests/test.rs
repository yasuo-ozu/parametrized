use parametrized::*;

#[allow(unused)]
#[parametrized(default, iter_mut)]
struct Struct1<K>(usize, Vec<(usize, K)>);

#[test]
fn test1() {
    let mut s = Struct1(123, vec![(456, "hello"), (789, "world")]);
    assert_eq!(s.param_len(), 2);
    assert_eq!(s.param_iter().collect::<Vec<_>>(), vec![&"hello", &"world"]);
    for item in s.param_iter_mut() {
        *item = "konnichiwa";
    }
    assert_eq!(
        s.param_iter().collect::<Vec<_>>(),
        vec![&"konnichiwa", &"konnichiwa"]
    );
    // let s = s.map_of_param(|s| s.len());
    // assert_eq!(s.into_iter_of_arg().collect::<Vec<_>>(), vec![10, 10]);
}

#[parametrized(default = 1)]
struct Struct2<'a, K> {
    f1: K,
    f2: Option<(&'a K, isize)>,
}

#[test]
fn test2() {
    let s = Struct2 {
        f1: "hello",
        f2: Some((&"world", 123)),
    };
    assert_eq!(s.param_len(), 2);
    assert_eq!(s.param_iter().collect::<Vec<_>>(), vec![&"hello", &"world"]);
}

#[parametrized(default = 1, iter_mut = 1)]
struct Struct3<'a, K>(&'a mut std::collections::BTreeMap<usize, K>);

#[test]
fn test3() {
    let mut m: std::collections::BTreeMap<_, _> =
        vec![(123, "hello"), (456, "world")].into_iter().collect();
    let mut s = Struct3(&mut m);
    assert_eq!((&s).param_len(), 2);
    assert_eq!(s.param_iter().collect::<Vec<_>>(), vec![&"hello", &"world"]);
    for item in s.param_iter_mut() {
        *item = "konnichiwa";
    }
    assert_eq!(
        s.param_iter().collect::<Vec<_>>(),
        vec![&"konnichiwa", &"konnichiwa"]
    );
}

#[parametrized(default = 1, iter_mut = 1)]
struct Struct4<'a, K>(&'a mut Vec<[K; 3]>);

#[test]
fn test4() {
    let mut v = vec![[2usize, 3, 5], [7, 11, 13], [17, 19, 23]];
    let mut s = Struct4(&mut v);
    assert_eq!(s.param_len(), 9);
    assert_eq!(
        s.param_iter().collect::<Vec<_>>(),
        vec![&2, &3, &5, &7, &11, &13, &17, &19, &23]
    );
    for item in s.param_iter_mut() {
        *item *= 2;
    }
    assert_eq!(
        s.param_iter().collect::<Vec<_>>(),
        vec![&4, &6, &10, &14, &22, &26, &34, &38, &46]
    );
}
