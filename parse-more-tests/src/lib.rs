use parse_more::{filler, parse_more, Braced, Bracketed, Concat, Either, Parenthesized};
use proc_macro::TokenStream;
use quote::quote;
use syn::{punctuated::Punctuated, Abi, Expr, ExprBlock, Ident, Token};

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
    let parsed = parse_more::<Concat<Ident, Ident>>(input);
    proc_assert!(parsed.is_ok());
    let input = quote! {
        a 0u8 c
    }
    .into();
    let parsed = parse_more::<Concat<Ident, Expr, Ident>>(input);
    proc_assert!(parsed.is_ok());
    let input = quote! {
        a
    }
    .into();
    let parsed = parse_more::<Concat<Ident, Ident, Ident>>(input);
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
#[proc_macro]
pub fn test_option(_: TokenStream) -> TokenStream {
    let input = quote! {
        u8
    }
    .into();
    let parsed = parse_more::<Option<Ident>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(parsed.unwrap().is_some());
    let input = quote! {}.into();
    let parsed = parse_more::<Option<Ident>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(parsed.unwrap().is_none());
    let input = quote! {
        (u8, { 0u8 })
    }
    .into();
    let parsed = parse_more::<Concat<Option<(Ident, Ident)>, (Ident, ExprBlock)>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(parsed.clone().unwrap().into_tuple2().0.is_none());
    proc_assert_eq!("u8", parsed.unwrap().into_tuple2().1 .0.to_string());
    let input = quote! {
        (Foo, Bar)(u8, { 0u8 })
    }
    .into();
    let parsed = parse_more::<Concat<Option<(Ident, Ident)>, (Ident, ExprBlock)>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(parsed.unwrap().into_tuple2().0.is_some());

    let input = quote! {
        extern "C" fn
    }
    .into();
    let parsed = parse_more::<Concat<Option<Abi>, Token![fn]>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(parsed.unwrap().into_tuple2().0.is_some());

    let input = quote! {
        fn
    }
    .into();
    let parsed = parse_more::<Concat<Option<Abi>, Token![fn]>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(parsed.unwrap().into_tuple2().0.is_none());

    quote! {}.into()
}
#[proc_macro]
pub fn test_either(_: TokenStream) -> TokenStream {
    let input = quote! {
        u8
    }
    .into();
    let parsed = parse_more::<Either<Ident, Token![=>]>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(parsed.unwrap().is_first());
    let input = quote! {
        =>
    }
    .into();
    let parsed = parse_more::<Either<Ident, Token![=>]>>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(parsed.unwrap().is_second());

    quote! {}.into()
}

#[allow(unused)]
#[parse_more]
struct TestDerivation {
    first: Ident,
    #[filler(Token![=>])]
    tuple: (Expr, Expr),
}

#[allow(unused, clippy::large_enum_variant)]
#[parse_more]
enum TestDerivationEnum {
    Maybe(Ident),
    Another(Token![=>]),
    Tuple((Expr, Expr)),
}

#[proc_macro]
pub fn test_derivation(_: TokenStream) -> TokenStream {
    let input = quote! {
        u8
    }
    .into();
    let parsed = parse_more::<TestDerivation>(input);
    proc_assert!(parsed.is_err());
    let input = quote! {
        u8 => (8, 8 + 4)
    }
    .into();
    let parsed = parse_more::<TestDerivation>(input);
    proc_assert!(parsed.is_ok());
    let input = quote! {
        u8
    }
    .into();
    let parsed = parse_more::<TestDerivationEnum>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(matches!(parsed.unwrap(), TestDerivationEnum::Maybe(_)));
    let input = quote! {
        =>
    }
    .into();
    let parsed = parse_more::<TestDerivationEnum>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(matches!(parsed.unwrap(), TestDerivationEnum::Another(_)));
    let input = quote! {
        (9, 9 + 5)
    }
    .into();
    let parsed = parse_more::<TestDerivationEnum>(input);
    proc_assert!(parsed.is_ok());
    proc_assert!(matches!(parsed.unwrap(), TestDerivationEnum::Tuple(_)));
    let input = quote! {
        (9,)
    }
    .into();
    let parsed = parse_more::<TestDerivationEnum>(input);
    proc_assert!(parsed.is_err());

    quote! {}.into()
}

#[proc_macro]
pub fn test_primitives(_: TokenStream) -> TokenStream {
    let input = quote! {
        0
    }
    .into();
    let parsed = parse_more::<u8>(input);
    proc_assert!(parsed.is_ok());
    proc_assert_eq!(parsed.unwrap(), 0);
    let input = quote! {
        0u8
    }
    .into();
    let parsed = parse_more::<u8>(input);
    proc_assert!(parsed.is_ok());
    proc_assert_eq!(parsed.unwrap(), 0);
    let input = quote! {
        0i8
    }
    .into();
    let parsed = parse_more::<u8>(input);
    proc_assert!(parsed.is_ok());
    proc_assert_eq!(parsed.unwrap(), 0);
    let input = quote! {
        256u8
    }
    .into();
    let parsed = parse_more::<u8>(input);
    proc_assert!(parsed.is_err());
    let input = quote! {
        -1i8
    }
    .into();
    let parsed = parse_more::<u8>(input);
    proc_assert!(parsed.is_err());

    let input = quote! {
        18446744073709551615
    }
    .into();
    let parsed = parse_more::<u64>(input);
    proc_assert!(parsed.is_ok());
    proc_assert_eq!(parsed.unwrap(), u64::MAX);
    let input = quote! {
        18446744073709551616
    }
    .into();
    let parsed = parse_more::<u64>(input);
    proc_assert!(parsed.is_err());

    let input = quote! {
        200u8
    }
    .into();
    let parsed = parse_more::<i8>(input);
    proc_assert!(parsed.is_err());

    let input = quote! {
        "Hello World !"
    }
    .into();
    let parsed = parse_more::<String>(input);
    proc_assert!(parsed.is_ok());
    proc_assert_eq!(parsed.unwrap(), "Hello World !");

    quote! {}.into()
}
