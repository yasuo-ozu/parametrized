use parametric_type::parametric_type;
use parametric_type::type_argument::{IntoIteratorOfNthArgument, MapOfNthArgument};

#[allow(unused)]
#[parametric_type(K, into_iter, iter, iter_mut, map)]
struct Struct1<K>(usize, Vec<(usize, K)>);

#[test]
fn test1() {
    let mut s = Struct1(123, vec![(456, "hello"), (789, "world")]);
    assert_eq!(s.len_of_arg(), 2);
    assert_eq!(
        (&s).into_iter_of_arg().collect::<Vec<_>>(),
        vec![&"hello", &"world"]
    );
    for item in (&mut s).into_iter_of_arg() {
        *item = "konnichiwa";
    }
    assert_eq!(
        (&s).into_iter_of_arg().collect::<Vec<_>>(),
        vec![&"konnichiwa", &"konnichiwa"]
    );
    // let s = s.map_of_param(|s| s.len());
    // assert_eq!(s.into_iter_of_arg().collect::<Vec<_>>(), vec![10, 10]);
}

#[parametric_type(K, iter)]
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
    assert_eq!((&s).len_of_arg(), 2);
    assert_eq!(
        (&s).into_iter_of_arg().collect::<Vec<_>>(),
        vec![&"hello", &"world"]
    );
}

#[parametric_type(K, iter, iter_mut)]
struct Struct3<'a, K>(&'a mut std::collections::HashMap<usize, K>);

#[test]
fn test3() {
    let mut m: std::collections::HashMap<_, _> =
        vec![(123, "hello"), (456, "world")].into_iter().collect();
    let mut s = Struct3(&mut m);
    assert_eq!((&s).len_of_arg(), 2);
    assert_eq!(
        (&s).into_iter_of_arg().collect::<Vec<_>>(),
        vec![&"hello", &"world"]
    );
    for item in (&mut s).into_iter_of_arg() {
        *item = "konnichiwa";
    }
    assert_eq!(
        (&s).into_iter_of_arg().collect::<Vec<_>>(),
        vec![&"konnichiwa", &"konnichiwa"]
    );
}

#[parametric_type(K, iter, iter_mut)]
struct Struct4<'a, K>(&'a mut Vec<[K; 3]>);

#[test]
fn test4() {
    let mut v = vec![[2usize, 3, 5], [7, 11, 13], [17, 19, 23]];
    let mut s = Struct4(&mut v);
    assert_eq!((&s).len_of_arg(), 9);
    assert_eq!(
        (&s).into_iter_of_arg().collect::<Vec<_>>(),
        vec![&2, &3, &5, &7, &11, &13, &17, &19, &23]
    );
    for item in (&mut s).into_iter_of_arg() {
        *item *= 2;
    }
    assert_eq!(
        (&s).into_iter_of_arg().collect::<Vec<_>>(),
        vec![&4, &6, &10, &14, &22, &26, &34, &38, &46]
    );
}
