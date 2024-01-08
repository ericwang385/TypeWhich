use parser::parse;
use type_migrate::{type_infer, type_check};

mod parser;
mod pretty;
mod syntax;
mod type_migrate;


fn main() -> Result<(), String> {
    let prog = "1";
    let mut parsed = parse(prog).unwrap();
    let env = Default::default();
    parsed.fresh_types();
    let infered = type_infer(parsed, &env).unwrap();
    let t = type_check(&infered).expect("failed to typecheck");

    Ok(())
}

#[cfg(test)]
mod test{
    use crate::type_migrate::{type_infer, type_check};
    use super::syntax::{Exp, Typ};
    use super::parser::parse;

    fn compile_verbose(mut orig: Exp) -> (Typ, Exp) {
        let env = Default::default();
        orig.fresh_types();
        println!("\nOriginal program:\n{}", &orig);
        let e = type_infer(orig, &env).unwrap();
        println!("\nAfter type inference:\n{}", e);
        let t = type_check(&e).expect("failed to typecheck");
        println!("\nProgram type:\n{}", t);
        (t, e)
    }

    fn test_migrate(mut orig: &str) -> Typ {
        let parsed = parse(orig).unwrap();
        let (t, e) = compile_verbose(parsed);
        t
    }

    #[test]
    fn int_lit() {
        test_migrate("1");
    }
}