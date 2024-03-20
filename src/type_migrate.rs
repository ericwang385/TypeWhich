use either::Either::{self, Left, Right};
use im::{HashMap, HashSet};
use crate::constraint_solve::csolve;
use crate::syntax::{Any, GroundTyp};
use super::syntax::{Exp, Typ, MetaVar};
use super::syntax::Exp::*;
use super::constraint_gen::cgen;
use std::boxed::Box;

#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum Constraint {
    Consistent(CTyp, CTyp),
    Precious(CTyp, CTyp)
}
pub type Env = HashMap<String, MetaVar>;
pub type CTyp = Either<MetaVar, GroundTyp>;
pub type CSet = HashSet<Constraint>;
pub type HIndex = HashSet<MetaVar>;
pub type ATyp = Either<Any, GroundTyp>;
pub type Ans = HashMap<MetaVar, ATyp>;

// Entry Point
pub fn type_infer(mut exp: Exp, env: &Env) -> Result<Exp, String> {
    let (mut phi, psi) = cgen(&mut exp, env);
    let sigma = csolve(&mut phi, &psi);
    annotate(&sigma, &mut exp, &psi);
    Ok(exp)
}

fn annotate_metavar(sigma: &Ans, t: &MetaVar, psi: &HIndex) -> Typ {
    match sigma.get(t) {
        Some(Left(_)) => Typ::Any,
        Some(Right(t)) => t.to_typ(),
        None if psi.contains(t) => {
            let dom = annotate_metavar(sigma, &t.dom(), psi);
            let cod = annotate_metavar(sigma, &t.cod(), psi);
            Typ::Arr(Box::new(dom), Box::new(cod))
        }
        None => Typ::Any 
    }
}

fn annotate_typ(sigma: &Ans, t: &mut Typ, psi: &HIndex) {
    match t {
        Typ::Metavar(i) => *t = annotate_metavar(sigma, &MetaVar::Atom(*i), psi),
        Typ::Arr(t1, t2) | Typ::Pair(t1, t2) => {
            annotate_typ(sigma, t1, psi);
            annotate_typ(sigma, t2, psi);
        }
        Typ::List(t) | Typ::Box(t) | Typ::Vect(t) => {
            annotate_typ(sigma, t, psi);
        }
        Typ::Unit | Typ::Int | Typ::Float | Typ::Bool | Typ::Str | Typ::Char | Typ::Any => (),
    }
}

fn annotate(sigma: &Ans, exp: &mut Exp, psi: &HIndex) {
    match &mut *exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(..) | Var(..) => {}
        Exp::Fun(_, t, e) | Exp::Fix(_, t, e) | Exp::Ann(e, t) => {
            annotate_typ(sigma, t, psi);
            annotate(sigma, e, psi);
        }
        Exp::Coerce(t1, t2, e) => {
            annotate(sigma, e, psi);
            annotate_typ(sigma, t1, psi);
            annotate_typ(sigma, t2, psi);
            if t1 == t2 {
                *exp = e.take();
            }
        }
        Exp::App(e1, e2) 
        | Exp::Let(_, e1, e2)
        | Exp::BinaryOp(_, e1, e2)
        | Exp::AddOverload(e1, e2) => {
            annotate(sigma, e1, psi);
            annotate(sigma, e2, psi);
        }
        _ => {}
    }
}

// #[cfg(test)]
mod test {
    use crate::constraint_gen::cgen;
    use crate::constraint_solve::csolve;
    use crate::syntax::Exp;
    use crate::parser::parse;

    use super::annotate;

    fn test_migrate(orig: &str) -> Exp {
        let mut exp = parse(orig).unwrap();
        exp.fresh_types();
        let (mut phi, psi) = cgen(&mut exp, &Default::default());
        println!("Constraint: {:?}", phi);
        let sigma = csolve(&mut phi, &psi);
        println!("Answer Set:\n{:?}", sigma);
        println!("Before Annotation:\n{:?}\n", exp);
        annotate(&sigma, &mut exp, &psi);
        println!("After Annotation \n {:?} \n", exp);
        println!("After Annotation Pretty:\n{}\n", exp);
        exp
    }

    #[test]
    fn bool_add() {
        test_migrate("true + false");
    }

    #[test]
    fn simple_arith() {
        test_migrate("(fun x . x + 1) 10");
    }

    #[test]
    fn bool_app() {
        test_migrate("(fun x . x + 1) true");
    }

    #[test]
    fn fun_app() {
        test_migrate("(fun f . f true) (fun x . x + 100)");
    }

    #[test]
    fn y_combinator() {
        test_migrate("(fun x . x x) 5");
    }

    #[test]
    fn precision() {
       test_migrate("(fun f. f true + (fun g.g 5) f) (fun x.5)");
    }
    #[test]
    fn rank2_poly() {
        test_migrate("(fun i.(fun a. (i true)) (i 5) ) (fun x.x)");
    }

    #[test]
    fn unreachable() {
        test_migrate("(fun b . 
            b (fun c . 
                 ((fun x . x x) 5) 5) 
              (fun d . 0)) 
            (fun t . fun f . f)
          ");
    }
}
