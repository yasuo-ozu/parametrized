# parametrized crate [![Latest Version]][crates.io] [![Documentation]][docs.rs] [![GitHub Actions]][actions]

[Latest Version]: https://img.shields.io/crates/v/parametrized.svg
[crates.io]: https://crates.io/crates/parametrized
[Documentation]: https://img.shields.io/docsrs/parametrized
[docs.rs]: https://docs.rs/parametrized/latest/parametrized/
[GitHub Actions]: https://github.com/yasuo-ozu/parametrized/actions/workflows/rust.yml/badge.svg
[actions]: https://github.com/yasuo-ozu/parametrized/actions/workflows/rust.yml

This Rust library provides a procedural macro attribute `#[parametrized]` that automatically implements methods like [`Parametrized::param_iter()`], [`ParametrizedIntoIter::param_into_iter()`], [`ParametrizedIterMut::param_iter_mut()`], and [`ParametrizedMap::param_map()`] for user-defined struct and enum types. The primary purpose of the library is to enable seamless traversal and transformation of complex data structures containing various nested collection types.

## Motivation

The parametrized library is particularly well-suited for handling complex data structures commonly found in compiler development and systems programming, such as Abstract Syntax Trees (ASTs) and Instruction Set Architectures (ISAs). These data structures often involve deeply nested collections and varying node types, making manual implementation of methods like iter, iter_mut, and map both tedious and error-prone.

### ISA example

```rust
# use parametrized::*;
# use std::collections::BTreeSet;
# #[allow(unused)]
#[parametrized(default, into_iter, map)]
enum Instruction<Operand: Ord> {
    BinaryOp {
        _op: String,
        _src: Operand,
        _dest: BTreeSet<Operand>,
    },
    LoadStore {
        _op: String,
        _address: Vec<(Operand, bool)>,
        _value: Operand,
    },
    Branch {
        _condition: String,
        _target: String,
    },
}
```
