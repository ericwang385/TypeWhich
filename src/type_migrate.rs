use either::Either;
use im::{HashMap, HashSet};
use crate::constraint_solve::csolve;
use crate::syntax::GroundTyp;
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
pub type Ans = HashMap<MetaVar, Typ>;

// Entry Point
pub fn type_infer(mut exp: Exp, env: &Env) -> Result<Exp, String> {
    let (mut phi, psi) = cgen(&mut exp, env);
    let mut sigma = csolve(&mut phi, &psi);
    fun_assign(&mut sigma, &psi);
    annotate(&sigma, &mut exp, &psi);
    Ok(exp)
}

fn fun_assign(sigma: &mut Ans, psi: &HIndex) {
    for t in psi {
        if sigma.get(t) == None {
            sigma.insert(t.clone(), Typ::Arr(Box::new(sigma.get(&t.dom()).unwrap_or(&Typ::Any).clone()),
                                Box::new(sigma.get(&t.cod()).unwrap_or(&Typ::Any).clone())));
        }
    }
}

fn annotate_typ(sigma: &Ans, t: &mut Typ, psi: &HIndex) {
    match t {
        Typ::Metavar(i) => {
            *t = match sigma.get(&MetaVar::Atom(*i)) {
                Some(s) => match s {
                    Typ::Metavar(_) => panic!("Type variable in answer set at {}", i),
                    _ => s.clone(),
                },
                None => Typ::Any,
            }
        }
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
    use crate::syntax::Exp;
    use crate::parser::parse;

    fn test_migrate(orig: &str) -> Exp {
        // let mut exp = parse(orig).unwrap();
        // exp.fresh_types();
        // let (_, mut phi) = constraint_gen(&mut exp, &Default::default());
        // // let n = curr_metavar();
        // let mut sigma = Default::default();
        // let mut psi = Default::default();
        // // println!("Before rewrite: {:?}", phi);
        // // println!("Expression: {:?}", exp);
        // constraint_rewrite(&mut phi, &mut psi);
        // // println!("After rewrite: {:?}", phi);
        // constraint_solve(&mut phi, &mut sigma, &psi);
        // fun_assign(&mut sigma, &psi);
        // // println!("Constraint:\n{:?}", phi);
        // println!("Answer Set:\n{:?}", sigma);
        // println!("Higher-Order Set:\n{:?}", psi);
        // println!("Before Annotation:\n{:?}\n", exp);
        // annotate(&sigma, &mut exp, &psi);
        // println!("After Annotation \n {:?} \n", exp);
        // println!("After Annotation Pretty:\n{}\n", exp);
        // exp
        todo!()
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
