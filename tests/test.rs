use parametrized::*;

#[allow(unused)]
//#[parametrized(default)]
struct Struct1<K>(usize, Vec<(usize, K)>);
impl<K> ::parametrized::Parametrized<0usize> for Struct1<K> {
    type Item = K;
    const MIN_LEN: usize = {
        const fn __parametric_type_min(a: usize, b: usize) -> usize {
            if a < b {
                a
            } else {
                b
            }
        }
        (<Vec<(usize, K)> as ::parametrized::Parametrized<0usize>>::MIN_LEN
            * (<(usize, K) as ::parametrized::Parametrized<1usize>>::MIN_LEN * 1usize))
    };
    const MAX_LEN: Option<usize> = {
        const fn __parametric_type_max(a: Option<usize>, b: Option<usize>) -> Option<usize> {
            match (a, b) {
                (Some(a), Some(b)) => {
                    if a > b {
                        Some(a)
                    } else {
                        Some(b)
                    }
                }
                _ => None,
            }
        }
        if let (Some(l), Some(r)) = (
            <Vec<(usize, K)> as ::parametrized::Parametrized<0usize>>::MAX_LEN,
            if let (Some(l), Some(r)) = (
                <(usize, K) as ::parametrized::Parametrized<1usize>>::MAX_LEN,
                ::core::option::Option::Some(0usize),
            ) {
                Some(l * r)
            } else {
                None
            },
        ) {
            Some(l * r)
        } else {
            None
        }
    };
    fn param_len(&self) -> usize {
        <Vec<(usize, K)> as ::parametrized::Parametrized<0usize>>::param_iter(self.1)
            .map(|__parametrized_arg| {
                <(usize, K) as ::parametrized::Parametrized<1usize>>::param_iter(__parametrized_arg)
                    .map(|__parametrized_arg| 1usize)
                    .sum::<::core::primitive::usize>()
            })
            .sum::<::core::primitive::usize>()
    }
    type Iter<'a> = () where (Self, Self::Item): 'a;
    fn param_iter<'a>(&'a self) -> Self::Iter<'a>
    where
        Self::Item: 'a,
    {
        <Vec<(usize, K)> as ::parametrized::Parametrized<0usize>>::param_iter(&self.1)
            .map(|__parametrized_arg| {
                <(usize, K) as ::parametrized::Parametrized<1usize>>::param_iter(__parametrized_arg)
                    .map(|__parametrized_arg| ::core::iter::once(__parametrized_arg))
                    .flatten()
            })
            .flatten();
        todo!()
    }
}

// #[test]
// fn test1() {
//     let mut s = Struct1(123, vec![(456, "hello"), (789, "world")]);
//     assert_eq!(s.param_len(), 2);
//     assert_eq!(s.param_iter().collect::<Vec<_>>(), vec![&"hello", &"world"]);
//     for item in s.param_iter_mut() {
//         *item = "konnichiwa";
//     }
//     assert_eq!(
//         s.param_iter().collect::<Vec<_>>(),
//         vec![&"konnichiwa", &"konnichiwa"]
//     );
//     // let s = s.map_of_param(|s| s.len());
//     // assert_eq!(s.into_iter_of_arg().collect::<Vec<_>>(), vec![10, 10]);
// }
//
// #[parametrized(iter)]
// struct Struct2<'a, K> {
//     f1: K,
//     f2: Option<(&'a K, isize)>,
// }
//
// #[test]
// fn test2() {
//     let s = Struct2 {
//         f1: "hello",
//         f2: Some((&"world", 123)),
//     };
//     assert_eq!(s.param_len(), 2);
//     assert_eq!(s.param_iter().collect::<Vec<_>>(), vec![&"hello", &"world"]);
// }
//
// #[parametrized(K, iter, iter_mut)]
// struct Struct3<'a, K>(&'a mut std::collections::BTreeMap<usize, K>);
//
// #[test]
// fn test3() {
//     let mut m: std::collections::BTreeMap<_, _> =
//         vec![(123, "hello"), (456, "world")].into_iter().collect();
//     let mut s = Struct3(&mut m);
//     assert_eq!((&s).param_len(), 2);
//     assert_eq!(s.param_iter().collect::<Vec<_>>(), vec![&"hello", &"world"]);
//     for item in s.param_iter_mut() {
//         *item = "konnichiwa";
//     }
//     assert_eq!(
//         s.param_iter().collect::<Vec<_>>(),
//         vec![&"konnichiwa", &"konnichiwa"]
//     );
// }
//
// #[parametrized(iter, iter_mut)]
// struct Struct4<'a, K>(&'a mut Vec<[K; 3]>);
//
// #[test]
// fn test4() {
//     let mut v = vec![[2usize, 3, 5], [7, 11, 13], [17, 19, 23]];
//     let mut s = Struct4(&mut v);
//     assert_eq!(s.param_iter(), 9);
//     assert_eq!(
//         s.param_iter().collect::<Vec<_>>(),
//         vec![&2, &3, &5, &7, &11, &13, &17, &19, &23]
//     );
//     for item in s.param_iter_mut() {
//         *item *= 2;
//     }
//     assert_eq!(
//         s.param_iter().collect::<Vec<_>>(),
//         vec![&4, &6, &10, &14, &22, &26, &34, &38, &46]
//     );
// }
