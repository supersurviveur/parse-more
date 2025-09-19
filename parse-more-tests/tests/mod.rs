macro_rules! tests_wrapper {
    ($($test:ident),*) => {
        $(#[test]
        fn $test() {
            parse_more_tests::$test!()
        })*
    };
}

tests_wrapper! {
    test_array,
    test_tuple,
    test_punctuated,
    test_concat,
    test_braced,
    test_parenthesized,
    test_bracketed
}
