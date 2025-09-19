use parse_more::{parse_more, Braced, Bracketed, Concat, Parenthesized};
use proc_macro::TokenStream;
use quote::quote;
use syn::{punctuated::Punctuated, Expr, Ident, Token};

macro_rules! proc_assert {
    ($cond:expr, $message:expr) => {
        if !$cond {
            return syn::Error::new(
                proc_macro2::Span::call_site(),
                format!(
                    "assertion failed at {}:{}:{} -> {}",
                    file!(),
                    line!(),
                    column!(),
                    $message
                ),
            )
            .into_compile_error()
            .into();
        }
    };
    ($cond:expr) => {
        proc_assert! {
            $cond, stringify! { $cond }
        }
    };
}

macro_rules! proc_assert_eq {
    ($a:expr, $b:expr) => {{
        let __a = $a;
        let __b = $b;
        proc_assert! {
            __a == __b,
            format!(
                "{} == {}\nleft: {}\nright: {}",
                stringify! { $a },
                stringify! { $b },
                __a,
                __b
            )
        }
    }};
}

#[proc_macro]
pub fn test_array(_: TokenStream) -> TokenStream {
    let input = quote! {
        [a, b, c, d]
    }
    .into();
    proc_assert!(parse_more::<[Ident; 4]>(input).is_ok());
    let input = quote! {
        [a, b, c, d,]
    }
    .into();
    proc_assert!(parse_more::<[Ident; 4]>(input).is_ok());
    let input = quote! {
        [a, b, c]
    }
    .into();
    proc_assert!(parse_more::<[Ident; 4]>(input).is_err());
    let input = quote! {
        [a, b, c,]
    }
    .into();
    proc_assert!(parse_more::<[Ident; 4]>(input).is_err());
    let input = quote! {
        []
    }
    .into();
    proc_assert!(parse_more::<[Ident; 0]>(input).is_ok());
    let input = quote! {
        a, b
    }
    .into();
    proc_assert!(parse_more::<[Ident; 2]>(input).is_err());

    quote! {}.into()
}

#[proc_macro]
pub fn test_tuple(_: TokenStream) -> TokenStream {
    let input = quote! {
        (a, b, c, d)
    }
    .into();
    proc_assert!(parse_more::<(Ident, Ident, Ident, Ident)>(input).is_ok());
    let input = quote! {
        (a, b, c, d,)
    }
    .into();
    proc_assert!(parse_more::<(Ident, Ident, Ident, Ident)>(input).is_ok());
    let input = quote! {
        (a, b, c)
    }
    .into();
    proc_assert!(parse_more::<(Ident, Ident, Ident, Ident)>(input).is_err());
    let input = quote! {
        (a, b, c,)
    }
    .into();
    proc_assert!(parse_more::<(Ident, Ident, Ident, Ident)>(input).is_err());
    let input = quote! {
        (a,)
    }
    .into();
    proc_assert!(parse_more::<(Ident,)>(input).is_ok());
    let input = quote! {
        (a)
    }
    .into();
    proc_assert!(parse_more::<(Ident,)>(input).is_err());

    quote! {}.into()
}

#[proc_macro]
pub fn test_punctuated(_: TokenStream) -> TokenStream {
    let input = quote! {
        a, b, c, d
    }
    .into();
    let parsed = parse_more::<Punctuated<Ident, Token![,]>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert_eq!(parsed.as_ref().unwrap().len(), 4);
    proc_assert!(!parsed.unwrap().trailing_punct());
    let input = quote! {
        a, b, c, d,
    }
    .into();
    let parsed = parse_more::<Punctuated<Ident, Token![,]>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert_eq!(parsed.as_ref().unwrap().len(), 4);
    proc_assert!(parsed.unwrap().trailing_punct());
    let input = quote! {
        a
    }
    .into();
    let parsed = parse_more::<Punctuated<Ident, Token![,]>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert_eq!(parsed.as_ref().unwrap().len(), 1);
    proc_assert!(!parsed.unwrap().trailing_punct());
    quote! {}.into()
}

#[proc_macro]
pub fn test_concat(_: TokenStream) -> TokenStream {
    let input = quote! {
        a b
    }
    .into();
    let parsed = parse_more::<Concat<(Ident, Ident)>>(input);
    proc_assert!(parsed.is_ok());
    let input = quote! {
        a 0u8 c
    }
    .into();
    let parsed = parse_more::<Concat<(Ident, Expr, Ident)>>(input);
    proc_assert!(parsed.is_ok());
    let input = quote! {
        a
    }
    .into();
    let parsed = parse_more::<Concat<(Ident,)>>(input);
    proc_assert!(parsed.is_ok());
    let input = quote! {
        a b
    }
    .into();
    let parsed = parse_more::<Concat<(Ident,)>>(input);
    proc_assert!(parsed.is_err());
    let input = quote! {
        a b
    }
    .into();
    let parsed = parse_more::<Concat<(Ident, Ident, Ident)>>(input);
    proc_assert!(parsed.is_err());
    quote! {}.into()
}

#[proc_macro]
pub fn test_braced(_: TokenStream) -> TokenStream {
    let input = quote! {
        { a }
    }
    .into();
    let parsed = parse_more::<Braced<Ident>>(input);
    proc_assert!(parsed.is_ok());
    let input = quote! {
        a
    }
    .into();
    let parsed = parse_more::<Braced<Ident>>(input);
    proc_assert!(parsed.is_err());

    quote! {}.into()
}
#[proc_macro]
pub fn test_parenthesized(_: TokenStream) -> TokenStream {
    let input = quote! {
        ( a )
    }
    .into();
    let parsed = parse_more::<Parenthesized<Ident>>(input);
    proc_assert!(parsed.is_ok());
    let input = quote! {
        a
    }
    .into();
    let parsed = parse_more::<Parenthesized<Ident>>(input);
    proc_assert!(parsed.is_err());

    quote! {}.into()
}
#[proc_macro]
pub fn test_bracketed(_: TokenStream) -> TokenStream {
    let input = quote! {
        [ a ]
    }
    .into();
    let parsed = parse_more::<Bracketed<Ident>>(input);
    proc_assert!(parsed.is_ok());
    let input = quote! {
        a
    }
    .into();
    let parsed = parse_more::<Bracketed<Ident>>(input);
    proc_assert!(parsed.is_err());

    quote! {}.into()
}
