# parse-more

Parse-more is an extension of the [Parse](https://docs.rs/syn/latest/syn/parse/trait.Parse.html) trait from the [syn](https://docs.rs/syn/) crate, allowing to parse input from procedural macros directly, without having to create a custom structure and implementing the Parse trait on it.

It provides classic [syn](https://docs.rs/syn/) macros and functions variant, using the [ParseMore](https://docs.rs/parse-more/latest/parse-more/trait.ParseMore.html) trait instead.

## Example

```rust
use quote::quote;
use parse_more::{parse_more_macro_input, Concat, Braced};
use proc_macro::TokenStream;
use syn::{Expr, Ident, Token, punctuated::Punctuated};

#[proc_macro]
pub fn complex_args(input: TokenStream) -> TokenStream {
   let content = parse_more_macro_input!(
       input as Punctuated<Concat<(Ident, Token![=>], Braced<(Ident, Expr)>)>, Token![,]>
   );
   content
       .into_iter()
       .map(|concat| {
           // Second item is discarded (it's the => arrow)
           let (ident, _, Braced((other_ident, literal))) = concat.value();
           quote! {
            println!("{}: {} versus other type {}", #literal, (-1i8) as #ident, (-1i8) as #other_ident);
           }
       })
       .collect::<proc_macro2::TokenStream>()
       .into()
}
```

And then :

```rust
complex_args! {
    u8 => {
        (i8, "u8 integer")
    },
    u16 => {
        (i16, "u16 integer")
    },
    Foo => {
        (Bar, 8 + 42)
    }
}
```

## Installation

Add to your `Cargo.toml` file:

```toml
[dependencies]
parse-more = "0.1"
```

## Contribution

Contributions are welcome! Open an issue or a pull request.

## License

This project is licensed under the MIT License.
