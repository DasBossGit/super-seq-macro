Supercharged `seq!` macro
=========================

<br>

This crate provides a `seq!` macro to repeat a fragment of source code and
substitute into each repetition a value of your choosing,
drawn from an iterable [RHAI](https://rhai.rs/) expression.

This is a fork of the [seq-macro](https://github.com/dtolnay/seq-macro) crate
and is backwards-compatible for simple usage.

```rust
use super_seq_macro::seq;

seq!(A in 0..3 {#(
    const WITHOUT_~A: [u32; 2] = seq!(B in (0..3).collect().filter(|x| x != A) {
        [ #( B, )* ]
    });
)*});

assert_eq!(WITHOUT_0, [1, 2]);
assert_eq!(WITHOUT_1, [0, 2]);
assert_eq!(WITHOUT_2, [0, 1]);
```

#### License

<sup>
Licensed under either of <a href="LICENSE-APACHE">Apache License, Version
2.0</a> or <a href="LICENSE-MIT">MIT license</a> at your option.
</sup>

<br>

<sub>
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
</sub>
