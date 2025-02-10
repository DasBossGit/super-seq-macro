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
//! - Since the backtick character is not available, the syntax `$"..."$` is provided for string
//!   interpolation.
//!
//! ```
//! use super_seq_macro::seq;
//!
//! seq!(P in (0x000..0x00F).collect()
//!     .map(|x| x.to_hex().to_upper()) // Convert to uppercase hex
//!     .map(|x| "000".sub_string($"${x}"$.len()) + $"${x}"$) // Pad on the left with zeros
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

use proc_macro2::{Delimiter, Group, Ident, Spacing, Span, TokenStream, TokenTree};
use std::iter::{self, FromIterator};
use std::mem;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input, Error, Result, Token,
};

#[derive(Debug)]
struct SeqInput {
    ident: Ident,
    script: TokenStream,
    block: TokenStream,
}

impl Parse for SeqInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident: Ident = input.parse()?;
        input.parse::<Token![in]>()?;
        let (script, block) = input.step(|cursor| {
            let mut cur = *cursor;
            let mut script = TokenStream::new();
            let mut block: Option<TokenTree> = None;

            while let Some((tt, next)) = cur.token_tree() {
                if let Some(ref mut block) = block {
                    let old_block = mem::replace(block, tt.clone());
                    script.extend(std::iter::once(old_block));
                } else {
                    block = Some(tt.clone());
                }
                cur = next;
            }
            Ok(((script, block), cur))
        })?;

        let Some(block) = block else {
            return Err(Error::new(Span::call_site(), "Expected block"));
        };
        let TokenTree::Group(block) = block else {
            return Err(Error::new(block.span(), "Expected block"));
        };

        Ok(SeqInput {
            ident,
            script,
            block: block.stream(),
        })
    }
}

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
    let script = rewrite_script(script);
    let script_span = Span::call_site(); //script.span(); TODO

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
    let list: Vec<_> = if let Some(r) = output.clone().try_cast::<std::ops::Range<i64>>() {
        r.map(|x| x.to_string()).collect()
    } else if let Some(r) = output.clone().try_cast::<std::ops::RangeInclusive<i64>>() {
        r.map(|x| x.to_string()).collect()
    } else if let Some(a) = output.clone().try_cast::<Vec<rhai::Dynamic>>() {
        a.into_iter().map(|d| d.to_string()).collect()
    } else {
        return Err(Error::new(script_span, "Bad expression type"));
    };

    //let list = list
    //    .into_iter()
    //    .map(|x| x.into_string())
    //    .collect::<std::result::Result<Vec<_>, _>>()
    //    .map_err(|e| Error::new(script_span, e))?;

    let mut found_repetition = false;
    let expanded = expand_repetitions(&ident, &list, block.clone(), &mut found_repetition);
    if found_repetition {
        Ok(expanded)
    } else {
        // If no `#(...)*`, repeat the entire body.
        Ok(repeat(&ident, &list, &block))
    }
}

fn rewrite_script(script: TokenStream) -> String {
    fn dollar_str(tokens: &[TokenTree]) -> Option<String> {
        assert!(tokens.len() == 3);
        match &tokens[0] {
            TokenTree::Punct(punct) if punct.as_char() == '$' => {}
            _ => return None,
        }
        match &tokens[2] {
            TokenTree::Punct(punct) if punct.as_char() == '$' => {}
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
                return Some(format!("`{}`", chars.as_str()));
            }
            _ => return None,
        }
    }

    // Look for `$"..."$`.
    let tokens = Vec::from_iter(script);
    let mut output = String::new();
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
            output.push_str(&rewrite_script(group.stream()));
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
            if let Some(backtick_str) = dollar_str(&tokens[i..i + 3]) {
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
        //let template = match enter_repetition(&tokens[i..i + 3]) {
        //    Some(template) => template,
        //    None => {
        //        i += 1;
        //        continue;
        //    }
        //};
        //*found_repetition = true;
        //let mut repeated = Vec::new();
        //for value in range {
        //    repeated.extend(substitute_value(var, &value, template.clone()));
        //}
        //let repeated_len = repeated.len();
        //tokens.splice(i..i + 3, repeated);
        //i += repeated_len;
    }

    //let script = TokenStream::from_iter(tokens);

    output
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

            //let mut iter = new_tokens.into_iter();
            //let mut t = match iter.next() {
            //    Some(t) => t,
            //    None => panic!("Empty token"),
            //};
            //assert!(iter.next().is_none(), "Multiple tokens");

            //t.set_span(original_span);
            //tokens[i] = t;
            //i += 1;
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
    use crate::{rewrite_script, seq_impl};
    use quote::quote;

    #[test]
    fn test_string_rewrite() {
        let inp = quote! {
            let a = (
                $"${x}"$
            );
        };

        let result = rewrite_script(inp);
        assert_eq!(result, "let a = ( `${x}` ) ; ");
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
    fn test_str_array() {
        let inp = quote! {
            A in (0..3).collect().map(|x| $"${x}"$) {
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
