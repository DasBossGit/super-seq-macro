use proc_macro2::{Ident, Span, TokenStream, TokenTree};
use std::mem;
use syn::{
    Error, Result, Token,
    parse::{Parse, ParseStream},
};

#[derive(Debug)]
#[repr(C)]
pub struct SeqInput {
    pub ident: Ident,
    pub script: TokenStream,
    pub block: TokenStream,
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
