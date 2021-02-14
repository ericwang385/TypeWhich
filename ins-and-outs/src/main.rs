mod collect_coercions;
mod decorate;
mod flow;
mod parser;
mod pretty;
mod solve;
mod syntax;
//mod type_check;

use std::io::*;

lrlex::lrlex_mod!("lexer.l"); // effectively mod `lexer_l`
lrpar::lrpar_mod!("parser.y"); // effectively mod `parser_y`

type Closure = im_rc::HashSet<(syntax::Typ, syntax::Typ)>;

fn main() -> Result<()> {
    let mut args = std::env::args();
    args.next();
    let source = match args.next() {
        Some(file) => std::fs::read_to_string(file)?,
        None => {
            let mut out = String::new();
            stdin().read_to_string(&mut out)?;
            out
        }
    };
    let parsed = parser::parse(source);
    typeinf(parsed);
    Ok(())
}

pub fn typeinf(parsed: syntax::Exp) -> syntax::Exp {
    let (mut coerced, coercions) = collect_coercions::compile_coercions(parsed);
    println!(
        "{}\ncoercions:\n{}",
        coerced,
        pretty::DisplayClosure(&coercions)
    );
    let coercions_closure = flow::compute_closure(coercions);
    println!("closure:\n{}", pretty::DisplayClosure(&coercions_closure));
    let solution = solve::solve_closure(coercions_closure);
    println!("solution:\n{:?}", solution);
    decorate::decorate(&mut coerced, &solution);
    println!("annotated:\n{}", coerced);
    coerced
}

#[cfg(test)]
mod tests {
    use super::parser::parse;
    use super::syntax::*;
    use super::typeinf;
    //use super::type_check::type_check;
    pub fn contains_coercions(e: Exp) -> bool {
        match e {
            Exp::Coerce(..) => true,
            Exp::Lit(..) | Exp::Var(..) => false,
            Exp::Fun(_, _, e, _) | Exp::Assign(_, e) => contains_coercions(*e),
            Exp::App(e1, e2) | Exp::Seq(e1, e2) => {
                contains_coercions(*e1) || contains_coercions(*e2)
            }
            Exp::If(e1, e2, e3) => {
                contains_coercions(*e1) || contains_coercions(*e2) || contains_coercions(*e3)
            }
        }
    }
    pub fn succeeds(program: &str) {
        let orig = parse(program);
        println!("\nOriginal program:\n{}", &orig);
        let e = typeinf(orig);
        println!("\nAfter type inference:\n{}", e);
        let coercions = contains_coercions(e);
        assert!(!coercions);
    }
    pub fn coerces(program: &str) {
        let orig = parse(program);
        println!("\nOriginal program:\n{}", &orig);
        let e = typeinf(orig);
        println!("\nAfter type inference:\n{}", e);
        let coercions = contains_coercions(e);
        assert!(coercions);
    }
    #[test]
    fn an_int() {
        succeeds("5");
    }
    #[test]
    fn fun_app_int() {
        succeeds("(fun x.x) 5");
    }
    #[test]
    fn fun_fun_app_int_int() {
        succeeds("(fun x.fun y.y) 5 8");
    }
    #[test]
    fn indir_int_equal_bool() {
        coerces(
            "fun p .
                (fun foo . foo 10 p true)
                    (fun x . fun y . fun z .
                        if true then z
                        else
                            (fun w . w) (if true then y else (fun w0 . w0) x))",
        );
    }
    #[test]
    fn key_is_bool_and_int() {
        // previously ended in else key > 10 which would yield bool and
        // constrain key to int, so we make something similar type-wise without
        // adding comparisons
        coerces(
            "let elim_int = fun i: int.i in
            fun key . if true then if true then key else true else
                (fun i . true) (elim_int key)",
        );
    }
    #[test]
    fn identity_polymorphic() {
        coerces(
            "let id = fun x . x in
            let f = fun anid .
                let n = anid 10 in
                let b = anid true in
                5 in
            f id",
        );
    }
    #[test]
    fn bool_const() {
        succeeds("true");
    }
    #[test]
    fn local_variables_having_base_types() {
        // we don't worry about elimination forms since ins and outs doesn't
        // even use them!
        succeeds(
            "fun n:int.
                let index = 0 in
                let sum = index in
                // while (index < sum) { <- index |> int, sum |> int aren't used (outflows)
                       index = index; // was index + 1 which produces index |> int (outflow)
                       sum = sum; // was sum + index which produces outflows, and int |> sum (already there)
                // }
                sum",
        );
    }
    #[test]
    fn conditional_int_arr_int() {
        succeeds(
            "let b = null in
            let elim_int = fun x: int. x in // an elimanation form for int, for use rather than +
            let foo = fun x.
                if b then
                    elim_int x
                else
                    0 in
            foo 1",
        )
    }
    #[test]
    fn callable_by_existing_code() {
        coerces(
            "let b = null in
            let foo = fun x.
                if b then
                    (fun i: int. i) x // an elimanation form for int, for use rather than +
                else
                    0 in
            let app1 = foo 1 in
            foo",
        )
    }
    #[test]
    fn identity_twice() {
        succeeds("(fun i.i) ((fun i.i) null)");
    }
    #[test]
    fn identity_public() {
        let e = typeinf(parse("(fun i . i)"));
        match e {
            Exp::Fun(_, Typ::Any, _, Typ::Any) => (),
            _ => panic!(),
        }
    }
    #[test]
    fn call_identity() {
        succeeds("(fun i.i null) (fun x.x)");
    }
    #[test]
    fn i_on_f() {
        // probly (fun i:(any->any)->any->any.(i (fun y:any.y:any))) (fun x:any->any.x:any->any)
        succeeds("(fun i.(i (fun y.y))) (fun x.x)");
    }
    #[test]
    fn i_on_f_twice() {
        succeeds("(fun i.(fun a.a) (i (fun y.y))) (fun x.x)");
    }
    #[test]
    fn broke_migeed() {
        coerces("(fun i.(fun a.fun b.b) (i 5) (i true)) (fun x.x)");
    }
    // =======================================
    // ~~~~~~~~~ migeed and palsberg ~~~~~~~~~
    #[test]
    fn apply_add() {
        coerces(
            "let elim_add = fun x: int.x in
            fun x . x (elim_add x)",
        );
    }
    #[test]
    fn add_applied() {
        coerces(
            "let elim_add = fun x: int.x in
            fun x             . x (elim_add (x true))",
        );
    }
    #[test]
    fn add_two_applies() {
        coerces(
            "let elim_add = fun x: int. x in
            fun x             . elim_add (x 4); elim_add (x true)",
        );
    }
    #[test]
    fn identity_four() {
        succeeds("(fun x . x) 4");
    }
    #[test]
    fn succ_id_id() {
        coerces(
            "let elim_int = fun x: int. x in
            elim_int ((fun y    .y) ((fun x    .x) true))",
        );
    }
    #[test]
    fn identity() {
        succeeds("fun x.x");
    }
    #[test]
    fn apply2() {
        coerces("fun x    .fun y                    .y x x");
    }
    #[test]
    fn indirect_apply_self() {
        coerces("fun x    .(fun y    .x)           x  x");
    }
    #[test]
    fn the_long_one() {
        succeeds("fun x    .(fun f    .(fun x    .fun y    .x)          f (f x))(fun z    .1)");
    }
    /// this benchmark has no maximal migration, which means that x could be
    /// given an infinity recursive arrow type (t -> t -> t -> ...). we will
    /// give it... something
    #[test]
    fn apply_self() {
        coerces("fun x.x x");
    }
    /// this benchmark has an unknown maximal migration. because Migeed's
    /// algorithm is incomplete, it sometimes does not report whether a maximal
    /// solution exists. in practice, this probably means that there is no maximal
    /// migration. we still give it some migration
    /// TODO(luna): this test hangs fsr
    #[test]
    #[ignore]
    fn untypable_in_sys_f() {
        coerces("(fun x.fun y.y(x(fun x.x))(x(fun b.fun c.b)))(fun d.d d)");
    }
    #[test]
    fn self_apply_applied() {
        coerces("(fun x.x x) (fun i.i)");
        coerces("(fun x: any.<any |> any -> any>x x) (fun i: any.i)");
    }
    /// unknown to Migeed and Parsberg. self interpreter for the lambda calculus
    /// TODO(luna): this test hangs adding a bunch of ?!?!?!s fsr
    #[test]
    #[ignore]
    fn self_interpreter() {
        coerces(
            "(fun h.(fun x.h(x x))(fun x.h x x))
             (fun e.fun m.m(fun x.x)(fun m.fun n.(e m)(e n))(fun m.fun v.e (m v)))",
        );
    }
    // =======================================
}