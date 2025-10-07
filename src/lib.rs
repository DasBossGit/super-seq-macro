//! [![github]](https://github.com/ervanalb/super-seq-macro)&ensp;[![crates-io]](https://crates.io/crates/super-seq-macro)&ensp;[![docs-rs]](https://docs.rs/super-seq-macro)
//!
//! [github]: https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//! [crates-io]: https://img.shields.io/badge/crates.io-fc8d62?style=for-the-badge&labelColor=555555&logo=rust
//! [docs-rs]: https://img.shields.io/badge/docs.rs-66c2a5?style=for-the-badge&labelColor=555555&logo=docs.rs
//!
//! <br>
//!
//! # For-loops over any iterable in a macro
//!
//! This crate provides a `seq!` macro to repeat a fragment of source code and
//! substitute into each repetition a value of your choosing,
//! drawn from an iterable [RHAI](https://rhai.rs/) expression.
//!
//! This is mostly compatible with the [seq-macro](https://github.com/dtolnay/seq-macro) crate.
//!
//! ```
//! use super_seq_macro::seq;
//!
//! fn main() {
//!     let tuple = (1000, 100, 10);
//!     let mut sum = 0;
//!
//!     // Expands to:
//!     //
//!     //     sum += tuple.0;
//!     //     sum += tuple.1;
//!     //     sum += tuple.2;
//!     //
//!     // This cannot be written using an ordinary for-loop because elements of
//!     // a tuple can only be accessed by their integer literal index, not by a
//!     // variable.
//!     seq!(N in 0..=2 {
//!         sum += tuple.N;
//!     });
//!
//!     assert_eq!(sum, 1110);
//! }
//! ```
//!
//! - If the input tokens contain a section surrounded by `#(` ... `)*` then
//!   only that part is repeated.
//!
//! - The numeric counter can be pasted onto the end of some prefix to form
//!   sequential identifiers.
//!
//! ```
//! use super_seq_macro::seq;
//!
//! seq!(N in 64..=127 {
//!     #[derive(Debug)]
//!     enum Demo {
//!         // Expands to Variant64, Variant65, ...
//!         #(
//!             Variant~N,
//!         )*
//!     }
//! });
//!
//! fn main() {
//!     assert_eq!("Variant99", format!("{:?}", Demo::Variant99));
//! }
//! ```
//!
//! - RHAI provides functional tools like `.filter()` and `.map()` on arrays.
//!
//! ```
//! use super_seq_macro::seq;
//!
//! seq!(A in 0..3 {#(
//!     const WITHOUT_~A: [u32; 2] = seq!(B in (0..3).collect().filter(|x| x != A) {
//!         [ #( B, )* ]
//!     });
//! )*});
//!
//! assert_eq!(WITHOUT_0, [1, 2]);
//! assert_eq!(WITHOUT_1, [0, 2]);
//! assert_eq!(WITHOUT_2, [0, 1]);
//! ```
//!
//! - Since the backtick character is not available, the syntax `&"..."&` is provided for string
//!   interpolation.
//!
//! ```
//! use super_seq_macro::seq;
//!
//! seq!(P in (0x000..0x00F).collect()
//!     .map(|x| x.to_hex().to_upper()) // Convert to uppercase hex
//!     .map(|x| "000".sub_string(&"${x}"&.len()) + &"${x}"&) // Pad on the left with zeros
//!     {
//!     // expands to structs Pin000, ..., Pin009, Pin00A, ..., Pin00F
//!     struct Pin~P;
//! });
//! ```
//!
//! - If the input tokens contain a section surrounded by `#(` ... `)#` then
//!   that part is taken verbatim and not repeated.
//!   Markers such as`#(`...`)*` within that segment are ignored
//!   (this can be useful for nesting `seq!` invocations.)

#![doc(html_root_url = "https://docs.rs/seq-macro/0.3.5")]
#![allow(
    clippy::cast_lossless,
    clippy::cast_possible_truncation,
    clippy::derive_partial_eq_without_eq,
    clippy::into_iter_without_iter,
    clippy::let_underscore_untyped,
    clippy::needless_doctest_main,
    clippy::single_match_else,
    clippy::wildcard_imports
)]

use ::super_seq_macro_types::SeqInput;
use ::syn::{parse::Parse, spanned::Spanned};
use proc_macro2::{Delimiter, Group, Ident, Spacing, TokenStream, TokenTree};
use std::iter::{self, FromIterator};
use syn::{Error, Result, parse_macro_input};

#[proc_macro]
pub fn seq(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as SeqInput);

    let output = seq_impl(input).unwrap_or_else(Error::into_compile_error);
    proc_macro::TokenStream::from(output)
}

fn seq_impl(
    SeqInput {
        ident,
        script,
        block,
    }: SeqInput,
) -> Result<TokenStream> {
    // Run script
    let script_span = script.span();
    let script = rewrite_script(script);

    if let SciptType::Rhai(script) = script {
        let mut engine = rhai::Engine::new();

        fn rhai_collect<T: IntoIterator<Item: Into<rhai::Dynamic>>>(inp: T) -> rhai::Array {
            inp.into_iter().map(|x| x.into()).collect()
        }
        engine.register_fn("collect", rhai_collect::<std::ops::Range<i64>>);
        engine.register_fn("collect", rhai_collect::<std::ops::RangeInclusive<i64>>);
        let output: rhai::Dynamic = engine
            .eval(&script)
            .map_err(|e| Error::new(script_span, e.to_string()))?;

        // See if output is a range of int
        let list: Vec<_> = if let Some(mut r) = output.clone().try_cast::<std::ops::Range<i64>>() {
            if r.start > r.end {
                r = r.end + 1..r.start + 1; // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::RangeInclusive<i64>>() {
            if r.start() > r.end() {
                r = *r.end()..=*r.start(); // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::Range<i32>>() {
            if r.start > r.end {
                r = r.end + 1..r.start + 1; // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::RangeInclusive<i32>>() {
            if r.start() > r.end() {
                r = *r.end()..=*r.start(); // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::Range<i16>>() {
            if r.start > r.end {
                r = r.end + 1..r.start + 1; // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::RangeInclusive<i16>>() {
            if r.start() > r.end() {
                r = *r.end()..=*r.start(); // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::Range<i8>>() {
            if r.start > r.end {
                r = r.end + 1..r.start + 1; // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::RangeInclusive<i8>>() {
            if r.start() > r.end() {
                r = *r.end()..=*r.start(); // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::Range<u64>>() {
            if r.start > r.end {
                r = r.end + 1..r.start + 1; // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::RangeInclusive<u64>>() {
            if r.start() > r.end() {
                r = *r.end()..=*r.start(); // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::Range<u32>>() {
            if r.start > r.end {
                r = r.end + 1..r.start + 1; // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::RangeInclusive<u32>>() {
            if r.start() > r.end() {
                r = *r.end()..=*r.start(); // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::Range<u16>>() {
            if r.start > r.end {
                r = r.end + 1..r.start + 1; // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::RangeInclusive<u16>>() {
            if r.start() > r.end() {
                r = *r.end()..=*r.start(); // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::Range<u8>>() {
            if r.start > r.end {
                r = r.end + 1..r.start + 1; // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(mut r) = output.clone().try_cast::<std::ops::RangeInclusive<u8>>() {
            if r.start() > r.end() {
                r = *r.end()..=*r.start(); // Reverse the range
            }
            r.map(|x| x.to_string()).collect()
        } else if let Some(a) = output.clone().try_cast::<Vec<rhai::Dynamic>>() {
            a.into_iter().map(|d| d.to_string()).collect()
        } else {
            return Err(Error::new(script_span, "Bad expression type"));
        };
        let mut found_repetition = false;
        let expanded = expand_repetitions(&ident, &list, block.clone(), &mut found_repetition);
        if found_repetition {
            Ok(expanded)
        } else {
            // If no `#(...)*`, repeat the entire body.
            Ok(repeat(&ident, &list, &block))
        }
    } else if let SciptType::Enum(list) = script {
        let str_list = &list.into_iter().map(|v| v.to_string()).collect::<Vec<_>>();

        let mut found_repetition = false;
        let expanded = expand_repetitions(
            &ident,
            str_list.as_slice(),
            block.clone(),
            &mut found_repetition,
        );
        if found_repetition {
            Ok(expanded)
        } else {
            // If no `#(...)*`, repeat the entire body.
            Ok(repeat(&ident, str_list.as_slice(), &block))
        }
    } else {
        unreachable!();
    }
}

#[derive(Debug, Clone)]
enum SciptType {
    Rhai(String),
    Enum(Vec<TokenTree>),
}
impl PartialEq for SciptType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Rhai(s1), Self::Rhai(s2)) => s1 == s2,
            (Self::Enum(t1), Self::Enum(t2)) => {
                t1.len() == t2.len()
                    && t1.iter().zip(t2.iter()).all(|(a, b)| match (a, b) {
                        (TokenTree::Group(group_a), TokenTree::Group(group_b)) => {
                            group_a.delimiter() == group_b.delimiter()
                                && group_a.span().source_text() == group_b.span().source_text()
                        }
                        (TokenTree::Ident(ident_a), TokenTree::Ident(ident_b)) => {
                            ident_a == ident_b
                        }
                        (TokenTree::Punct(punct_a), TokenTree::Punct(punct_b)) => {
                            punct_a.as_char() == punct_b.as_char()
                                && punct_a.spacing() == punct_b.spacing()
                        }
                        (TokenTree::Literal(literal_a), TokenTree::Literal(literal_b)) => {
                            literal_a.to_string() == literal_b.to_string()
                        }
                        _ => false,
                    })
            }
            _ => false,
        }
    }
}
impl ToString for SciptType {
    fn to_string(&self) -> String {
        match self {
            Self::Rhai(s) => s.clone(),
            Self::Enum(t) => t
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<_>>()
                .join(" "),
        }
    }
}

impl SciptType {
    fn is_rhai(&self) -> bool {
        matches!(self, SciptType::Rhai(_))
    }
    fn push(&mut self, c: char) {
        match self {
            Self::Rhai(str) => str.push(c),
            Self::Enum(token_trees) => {
                let ts: TokenStream = c.to_string().parse().unwrap();
                token_trees.extend(ts.into_iter());
            }
        }
    }
    fn push_str<A: AsRef<str>>(&mut self, s: A) {
        match self {
            Self::Rhai(str) => str.push_str(s.as_ref()),
            Self::Enum(token_trees) => {
                let ts: TokenStream = s.as_ref().parse().unwrap();
                token_trees.extend(ts.into_iter());
            }
        }
    }
    fn push_self(&mut self, other: &Self) {
        match (self, other) {
            (Self::Rhai(s1), Self::Rhai(s2)) => s1.push_str(s2),
            (Self::Enum(t1), Self::Enum(t2)) => t1.extend(t2.iter().cloned()),
            (Self::Rhai(se), Self::Enum(token_trees)) => {
                let mut s = String::new();
                for tt in token_trees {
                    s.push_str(&tt.to_string());
                    s.push(' ');
                }
                se.push_str(&s);
            }
            (Self::Enum(token_trees), Self::Rhai(se)) => {
                let ts: TokenStream = se.parse().unwrap();
                token_trees.extend(ts.into_iter());
            }
        }
    }
}

fn rewrite_script(script: TokenStream) -> SciptType {
    fn and_str(tokens: &[TokenTree]) -> Option<String> {
        assert!(tokens.len() == 3);
        match &tokens[0] {
            TokenTree::Punct(punct) if punct.as_char() == '&' => {}
            _ => return None,
        }
        match &tokens[2] {
            TokenTree::Punct(punct) if punct.as_char() == '&' => {}
            _ => return None,
        }
        match &tokens[1] {
            TokenTree::Literal(lit) => {
                let content = lit.to_string();
                let mut chars = content.chars();
                match chars.next() {
                    Some('"') => {}
                    _ => return None,
                }
                match chars.next_back() {
                    Some('"') => {}
                    _ => return None,
                }
                Some(format!("`{}`", chars.as_str()))
            }
            _ => None,
        }
    }

    // Look for `&"..."&`.
    let tokens = Vec::from_iter(script);

    if let Some((pos, _)) = tokens
        .get(0..=1)
        .map(|t| {
            t.iter().enumerate().find(|(_, tt)| {
                if let TokenTree::Ident(i) = tt {
                    i == "enum"
                } else {
                    false
                }
            })
        })
        .flatten()
    {
        // This is expected to be only one TokenTree::Group after the "enum" ident.
        let variants = tokens.into_iter().skip(pos + 1).collect::<Vec<_>>();

        if variants.len() == 1 {
            if let TokenTree::Group(group) = variants.into_iter().next().unwrap() {
                let enum_variants = group.stream().into_iter().filter(
                |tt| !matches!(tt, TokenTree::Punct(p) if p.as_char() == ',' || p.as_char() == ';'),
            ).collect::<Vec<_>>();
                return SciptType::Enum(enum_variants);
            }
        }
        panic!("Bad enum syntax");
    }

    let mut output: SciptType = SciptType::Rhai(String::new());
    let mut i = 0;
    while i < tokens.len() {
        if let TokenTree::Group(group) = &tokens[i] {
            match group.delimiter() {
                Delimiter::Parenthesis => {
                    output.push('(');
                }
                Delimiter::Brace => {
                    output.push('{');
                }
                Delimiter::Bracket => {
                    output.push('[');
                }
                Delimiter::None => {}
            }
            output.push(' ');
            output.push_self(&rewrite_script(group.stream()));
            match group.delimiter() {
                Delimiter::Parenthesis => {
                    output.push(')');
                }
                Delimiter::Brace => {
                    output.push('}');
                }
                Delimiter::Bracket => {
                    output.push(']');
                }
                Delimiter::None => {}
            }
            output.push(' ');
            i += 1;
            continue;
        }
        if i + 3 <= tokens.len() {
            if let Some(backtick_str) = and_str(&tokens[i..i + 3]) {
                output.push_str(&backtick_str);
                output.push(' ');
                i += 3;
                continue;
            }
        }

        match &tokens[i] {
            TokenTree::Group(_) => {
                unreachable!();
            }
            TokenTree::Ident(i) => {
                output.push_str(&i.to_string());
                output.push(' ');
            }
            TokenTree::Punct(p) => {
                output.push_str(&p.to_string());
                match p.spacing() {
                    Spacing::Alone => {
                        output.push(' ');
                    }
                    Spacing::Joint => {}
                }
            }
            TokenTree::Literal(l) => {
                output.push_str(&l.to_string());
                output.push(' ');
            }
        }
        i += 1;
    }
    dbg!(output)
}

fn repeat(var: &Ident, list: &[String], body: &TokenStream) -> TokenStream {
    let mut repeated = TokenStream::new();
    for value in list {
        repeated.extend(substitute_value(var, value, body.clone()));
    }
    repeated
}

fn substitute_value(var: &Ident, value: &str, body: TokenStream) -> TokenStream {
    let mut tokens = Vec::from_iter(body);

    let mut i = 0;
    while i < tokens.len() {
        // Substitute our variable by itself, e.g. `N`.
        let replace = match &tokens[i] {
            TokenTree::Ident(ident) => ident.to_string() == var.to_string(),
            _ => false,
        };
        if replace {
            let original_span = tokens[i].span();

            let new_tokens = value.parse::<TokenStream>().unwrap();

            tokens.splice(
                i..i + 1,
                new_tokens.into_iter().map(|mut t| {
                    t.set_span(original_span);
                    t
                }),
            );

            continue;
        }

        // Substitute our variable concatenated onto some prefix, `Prefix~N`.
        if i + 3 <= tokens.len() {
            let prefix = match &tokens[i..i + 3] {
                [first, TokenTree::Punct(tilde), TokenTree::Ident(ident)]
                    if tilde.as_char() == '~' && ident.to_string() == var.to_string() =>
                {
                    match first {
                        TokenTree::Ident(ident) => Some(ident.clone()),
                        TokenTree::Group(group) => {
                            let mut iter = group.stream().into_iter().fuse();
                            match (iter.next(), iter.next()) {
                                (Some(TokenTree::Ident(ident)), None) => Some(ident),
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(prefix) = prefix {
                let concat = format!("{}{}", prefix, value);
                let ident = Ident::new(&concat, prefix.span());
                tokens.splice(i..i + 3, iter::once(TokenTree::Ident(ident)));
                i += 1;
                continue;
            }
        }

        // Recursively substitute content nested in a group.
        if let TokenTree::Group(group) = &mut tokens[i] {
            let original_span = group.span();
            let content = substitute_value(var, value, group.stream());
            *group = Group::new(group.delimiter(), content);
            group.set_span(original_span);
        }

        i += 1;
    }

    TokenStream::from_iter(tokens)
}

fn enter_repetition(tokens: &[TokenTree]) -> Option<TokenStream> {
    assert!(tokens.len() == 3);
    match &tokens[0] {
        TokenTree::Punct(punct) if punct.as_char() == '#' => {}
        _ => return None,
    }
    match &tokens[2] {
        TokenTree::Punct(punct) if punct.as_char() == '*' => {}
        _ => return None,
    }
    match &tokens[1] {
        TokenTree::Group(group) if group.delimiter() == Delimiter::Parenthesis => {
            Some(group.stream())
        }
        _ => None,
    }
}

fn enter_single(tokens: &[TokenTree]) -> Option<TokenStream> {
    assert!(tokens.len() == 3);
    match &tokens[0] {
        TokenTree::Punct(punct) if punct.as_char() == '#' => {}
        _ => return None,
    }
    match &tokens[2] {
        TokenTree::Punct(punct) if punct.as_char() == '#' => {}
        _ => return None,
    }
    match &tokens[1] {
        TokenTree::Group(group) if group.delimiter() == Delimiter::Parenthesis => {
            Some(group.stream())
        }
        _ => None,
    }
}

fn expand_repetitions(
    var: &Ident,
    range: &[String],
    body: TokenStream,
    found_repetition: &mut bool,
) -> TokenStream {
    let mut tokens = Vec::from_iter(body);

    // Look for `#(...)*` or `#(...)#`.
    let mut i = 0;
    while i < tokens.len() {
        if let TokenTree::Group(group) = &mut tokens[i] {
            let content = expand_repetitions(var, range, group.stream(), found_repetition);
            let original_span = group.span();
            *group = Group::new(group.delimiter(), content);
            group.set_span(original_span);
            i += 1;
            continue;
        }
        if i + 3 > tokens.len() {
            i += 1;
            continue;
        }
        if let Some(template) = enter_repetition(&tokens[i..i + 3]) {
            *found_repetition = true;
            let mut repeated = Vec::new();
            for value in range {
                repeated.extend(substitute_value(var, &value, template.clone()));
            }
            let repeated_len = repeated.len();
            tokens.splice(i..i + 3, repeated);
            i += repeated_len;
            continue;
        }
        if let Some(template) = enter_single(&tokens[i..i + 3]) {
            tokens.splice(i..i + 3, template);
            *found_repetition = true;
            i += 1;
            continue;
        }
        // Normal token
        i += 1;
        continue;
    }

    TokenStream::from_iter(tokens)
}

#[cfg(test)]
mod test {
    use crate::{SciptType, rewrite_script, seq_impl};
    use quote::quote;

    #[test]
    fn test_string_rewrite() {
        let inp = quote! {
            let a = (
                $"${x}"$
            );
        };

        let result = rewrite_script(inp);
        assert_eq!(result, SciptType::Rhai("let a = ( `${x}` ) ; ".to_string()));
    }

    #[test]
    fn test_range() {
        let inp = quote! {
            A in 0..3 {
                println("{}", A);
            }
        };

        let result = seq_impl(syn::parse2(inp).unwrap()).unwrap();
        assert_eq!(
            result.to_string(),
            "println (\"{}\" , 0) ; println (\"{}\" , 1) ; println (\"{}\" , 2) ;"
        );
    }
    #[test]
    fn test_range_neg() {
        let inp = quote! {
            A in -3..-1 {
                println("{}", A);
            }
        };
        let result = seq_impl(syn::parse2(inp).unwrap()).unwrap();
        assert_eq!(
            result.to_string(),
            "println (\"{}\" , 0) ; println (\"{}\" , - 1) ; println (\"{}\" , - 2) ;"
        );
    }
    #[test]
    fn test_range_ops() {
        let inp = quote! {
            A in 3+1..=1+5 {
                println("{}", A);
            }
        };
        let result = seq_impl(syn::parse2(inp).unwrap()).unwrap();
        assert_eq!(
            result.to_string(),
            "println (\"{}\" , 0) ; println (\"{}\" , - 1) ; println (\"{}\" , - 2) ;"
        );
    }

    #[test]
    fn test_int_array() {
        let inp = quote! {
            A in [0,1,2] {
                println("{}", A);
            }
        };

        let result = seq_impl(syn::parse2(inp).unwrap()).unwrap();
        assert_eq!(
            result.to_string(),
            "println (\"{}\" , 0) ; println (\"{}\" , 1) ; println (\"{}\" , 2) ;"
        );
    }
    #[test]
    fn test_int_array_neg() {
        let inp = quote! {
            A in [-0,-1,-2] {
                println("{}", A);
            }
        };

        let result = seq_impl(syn::parse2(inp).unwrap()).unwrap();
        assert_eq!(
            result.to_string(),
            "println (\"{}\" , 0) ; println (\"{}\" , - 1) ; println (\"{}\" , - 2) ;"
        );
    }
    #[test]
    fn test_enum_variant_array_neg() {
        let inp = quote! {
            N in enum[A, B, C] {
                let _ = E::N;
            }
        };

        let result = seq_impl(syn::parse2(inp).unwrap());

        if let Ok(result) = result {
            println!("{}", result.to_string());
        }

        /* assert_eq!(
            result.to_string(),
            "println (\"{}\" , 0) ; println (\"{}\" , - 1) ; println (\"{}\" , - 2) ;"
        ); */
    }

    #[test]
    fn test_str_array() {
        let inp = quote! {
            A in (0..3).collect().map(|x| &"${x}"&) {
                println("{}", A);
            }
        };

        let result = seq_impl(syn::parse2(inp).unwrap()).unwrap();
        assert_eq!(
            result.to_string(),
            "println (\"{}\" , 0) ; println (\"{}\" , 1) ; println (\"{}\" , 2) ;"
        );
    }
}
