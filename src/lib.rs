use crate::compile::compile;
use crate::execute::execute;
use crate::parse::parse;

mod compile;
mod execute;
mod lexer;
mod parse;

pub fn matches(input: &str, expr: &str) -> bool {
    let parsed = parse(expr).unwrap();
    let compiled = compile(parsed).unwrap();
    execute(input, &compiled)
}
