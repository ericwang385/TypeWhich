use either::Either::{self, Left, Right};
use im::{HashMap, HashSet};
use crate::constraint_solve::csolve;
use crate::fgraph::{is_fun, FGraph};
use crate::syntax::{Any, GroundTyp};
use super::syntax::{Exp, Typ, MetaVar};
use super::syntax::Exp::*;
use super::constraint_gen::cgen;
use std::boxed::Box;
use std::collections::BTreeSet;

#[derive(Debug, PartialEq, Clone, Eq, Hash, PartialOrd, Ord)]
pub enum Constraint {
    Consistent(CTyp, CTyp),
    Precious(CTyp, CTyp)
}
pub type Env = HashMap<String, MetaVar>;
pub type CTyp = Either<MetaVar, GroundTyp>;
pub type CSet = BTreeSet<Constraint>;
pub type ATyp = Either<Any, GroundTyp>;
pub type Ans = HashMap<MetaVar, ATyp>;

// Entry Point
pub fn type_infer(mut exp: Exp, env: &Env) -> Result<Exp, String> {
    let cmode = false;
    let (phi, g) = cgen(&mut exp, env);
    let mut sigma = csolve(&phi, &g, &exp, cmode);
    annotate(&mut sigma, &mut exp, &g, cmode);
    Ok(exp)
}

fn annotate_metavar(sigma: &Ans, t: &MetaVar, g: &FGraph, flag: bool) -> Typ {
    match sigma.get(t) {
        Some(Left(_)) => Typ::Any,
        Some(Right(g)) => {
            // if flag {
            //     Typ::Any
            // } else {
            //     g.to_typ()
            // }
            g.to_typ()
        },
        None if is_fun(t, g).is_some() => {
            let dom = annotate_metavar(sigma, &t.dom(), g, flag);
            let cod = annotate_metavar(sigma, &t.cod(), g, flag);
            Typ::Arr(Box::new(dom), Box::new(cod))
        }
        None => Typ::Any 
    }
}

fn annotate_typ(sigma: &Ans, t: &mut Typ, g: &FGraph, flag: bool) {
    match t {
        Typ::Metavar(i) => *t = annotate_metavar(sigma, &MetaVar::Atom(*i), g, flag),
        Typ::Arr(t1, t2) | Typ::Pair(t1, t2) => {
            annotate_typ(sigma, t1, g, flag);
            annotate_typ(sigma, t2, g, false);
        }
        Typ::List(t) | Typ::Box(t) | Typ::Vect(t) => {
            annotate_typ(sigma, t, g, false);
        }
        Typ::Unit | Typ::Int | Typ::Float | Typ::Bool | Typ::Str | Typ::Char | Typ::Any => (),
    }
}

fn annotate(sigma: &Ans, exp: &mut Exp, g: &FGraph, flag: bool) {
    match &mut *exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(..) | Var(..) => {}
        Exp::Fun(_, t, e) | Exp::Fix(_, t, e) | Exp::Ann(e, t) => {
            annotate_typ(sigma, t, g, flag);
            annotate(sigma, e, g, flag);
        }
        Exp::Coerce(t1, t2, e) => {
            annotate(sigma, e, g, flag);
            annotate_typ(sigma, t1, g, false);
            annotate_typ(sigma, t2, g, false);
            if t1 == t2 {
                *exp = e.take();
            }
        }
        Exp::App(e1, e2) 
        | Exp::Let(_, e1, e2)
        | Exp::BinaryOp(_, e1, e2)
        | Exp::AddOverload(e1, e2) => {
            annotate(sigma, e1, g, false);
            annotate(sigma, e2, g, false);
        }
        Exp::If(e1, e2, e3) => {
            annotate(sigma, e1, g, false);
            annotate(sigma, e2, g, false);
            annotate(sigma, e3, g, false);
        }
        _ => {}
    }
}

mod test {
    use crate::constraint_gen::cgen;
    use crate::constraint_solve::csolve;
    use crate::syntax::Exp;
    use crate::parser::parse;

    use super::annotate;

    fn test_migrate(orig: &str) -> Exp {
        let mut exp = parse(orig).unwrap();
        exp.fresh_types();
        let (phi, g) = cgen(&mut exp, &Default::default());
        println!("Constraint: {:?}", phi);
        let sigma = csolve(&phi, &g, &exp, true);
        println!("Answer Set:\n{:?}", sigma);
        println!("Before Annotation:\n{:?}\n", exp);
        annotate(&sigma, &mut exp, &g, true);
        println!("After Annotation \n {:?} \n", exp);
        println!("After Annotation Pretty:\n{}\n", exp);
        exp
    }

    #[test]
    fn bool_add() {
        test_migrate("(fun y. if (y true) then 2 else y + 1) (fun x. if x then true else 3)");
    }

    #[test]
    fn simple_arith() {
        test_migrate("(fun x. x 5 + x) 5");
    }

    #[test]
    fn bool_app() {
        test_migrate("(fun x.(x 5) + x) 5");
    }

    #[test]
    fn fun_app() {
        test_migrate("(fun f. f true + (fun g.g 5) f) (fun x.5)");
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
    fn if_tag() {
        test_migrate("fun tag. fun x. if tag then x + 1 else 2");
    }

    #[test]
    fn if_tag_eta() {
        test_migrate("(fun u. fun y. ((fun tag. fun x. if tag then x + 1 else 2) u) y)");
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
