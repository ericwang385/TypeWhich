use crate::parser::{next_metavar, curr_metavar};
use crate::syntax::GroundTyp;

use super::syntax::{Exp, Typ};
use super::syntax::Exp::*;
use im::{HashSet, HashMap};
use std::boxed::Box;
use either::Either::{self, Left, Right};

type Env = HashMap<String, Typ>;
type Hom = HashMap<Typ, (Typ, Typ)>;
type Constraint = HashSet<(Either<Typ, GroundTyp>, Either<Typ, GroundTyp>, bool)>;

// Entry Point
pub fn type_infer(mut exp: Exp, env: &Env) -> Result<Exp, String> {
    let (_, mut cst, mut hom) = constraint_gen(&mut exp, env);
    let n = curr_metavar();
    let mut ans = (0..n).map(|x| (x, Typ::Metavar(x))).collect::<HashMap<u32, Typ>>();
    constraint_rewrite(&mut cst, &mut ans);
    annotate(&ans, &mut exp);
    Ok(exp)
}

pub fn type_check(exp: &Exp) -> Result<Typ, String> {
    todo!()
}

fn constraint_gen(exp: &mut Exp, env: &Env) -> (Typ, Constraint, Hom) {
    match exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(lit) => {
            let t1 = lit.typ();
            outer_coerce(t1, exp, Default::default(), Default::default())
        },
        Var(x) => {
            let t1 = env.get(x)
                .unwrap_or_else(|| panic!("unbound identifier {}", x))
                .clone();
            outer_coerce(t1, exp, Default::default(), Default::default())
        },
        Fun(f, t1, body) => {
            let mut env = env.clone();
            env.insert(f.clone(), t1.clone());
            let (t2, phi, hom) = constraint_gen(body, &env);
            let funt = Typ::Arr(Box::new(t1.clone()), Box::new(t2));
            outer_coerce(funt, exp, phi, hom)
        },
        App(e1, e2) => {
            let (t1, phi1, hom1) = constraint_gen(e1, &env);
            let (t2, phi2, hom2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2);
            let mut hom = hom1.union(hom2);
            let alpha = next_metavar();
            let beta = next_metavar();
            let dom = next_metavar();
            let cod = next_metavar();
            let funt = Typ::Arr(Box::new(alpha.clone()), Box::new(beta.clone()));
            coerce(t1.clone(), funt.clone(), e1);
            coerce(t2.clone(), alpha.clone(), e2);
            hom.insert(alpha.clone(), (dom.clone(), cod.clone()));
            phi.insert((Left(t1), Left(funt), false));
            phi.insert((Left(alpha.clone()), Left(t2), false));
            phi.insert((Left(alpha), Left(dom), true));
            phi.insert((Left(cod), Left(beta.clone()), false));
            (beta, phi, hom)
        },
        UnaryOp(op, e) => {
            let (t1, ret) = op.typ();
            let t11 = t1.to_groundtyp().unwrap_or_else(|| panic!("UnaryOp with higher-order behavior"));
            let (t2, mut phi, hom) = constraint_gen(e, &env);
            coerce(t2.clone(), t1, e);
            phi.insert((Left(t2), Right(t11), false));
            outer_coerce(ret, e, phi, hom)
        },
        BinaryOp(op, e1, e2) => {
            let (t1, t2, ret) = op.typ();
            let t11 = t1.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior"));
            let t22 = t2.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior"));
            let (t3, phi1, hom1) = constraint_gen(e1, &env);
            let (t4, phi2, hom2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2);
            let hom = hom1.union(hom2);
            coerce(t3.clone(), t1, e1);
            coerce(t4.clone(), t2, e2);
            phi.insert((Left(t3), Right(t11), false));
            phi.insert((Left(t4), Right(t22), false));
            outer_coerce(ret, exp, phi, hom)
        },
        Let(x, e1, e2) => {
            let (t1, phi1, hom1) = constraint_gen(e1, &env);
            let mut env = env.clone();
            env.insert(x.clone(), t1);
            let (t2, phi2, hom2) = constraint_gen(e2, &env);
            (t2, phi1.union(phi2), hom1.union(hom2))
        }
        If(cond, e1, e2) => {
            let (t1, phi1, hom1) = constraint_gen(cond, &env);
            let (t2, phi2, hom2) = constraint_gen(e1, &env);
            let (t3, phi3, hom3) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2).union(phi3);
            let hom = hom1.union(hom2).union(hom3);
            let alpha = next_metavar();
            coerce(t1.clone(), Typ::Bool, cond);
            coerce(t2.clone(), alpha.clone(), e1);
            coerce(t3.clone(), alpha.clone(), e2);
            phi.insert((Left(t1), Right(GroundTyp::Bool), false));
            phi.insert((Left(t2), Left(alpha.clone()), true));
            phi.insert((Left(t3), Left(alpha.clone()), true));
            (alpha, phi, hom)
        }
        _ => todo!()
    }
}

fn outer_coerce(t: Typ, exp: &mut Exp, mut cst: Constraint, mut hom: Hom) -> (Typ, Constraint, Hom) {
    let alpha = next_metavar();
    coerce(t.clone(), alpha.clone(), exp);
    match t {
        Typ::Int | Typ::Bool => {
            cst.insert((Right(t.to_groundtyp().unwrap()), Left(alpha.clone()), true));
        }
        Typ::Arr(t1, t2) => {
            let beta = next_metavar();
            let gamma = next_metavar();
            hom.insert(alpha.clone(), (beta.clone(), gamma.clone()));
            cst.insert((Right(GroundTyp::Fun), Left(alpha.clone()), true));
            cst.insert((Left(beta), Left(*t1), false));
            cst.insert((Left(*t2), Left(gamma), true));
        }
        _ => {
            cst.insert((Left(t), Left(alpha.clone()), true));
        }
    }
    (alpha, cst, hom)
}

fn coerce(t1: Typ, t2: Typ, exp: &mut Exp) {
    *exp = Exp::Coerce(t1, t2, Box::new(exp.take()))
}

fn constraint_rewrite(cst: &mut Constraint, ans: &mut HashMap<u32, Typ>) {
    todo!()
}

// fn ans_dif(orig: HashMap<u32, Typ>, cst: &mut Constraint, ans: &mut HashMap<u32, Typ>) {
//     if !orig.symmetric_difference(ans.clone()).is_empty() {
//         constraint_rewrite(cst, ans);
//     }
// }

// fn constraint_dif(orig: Constraint, cst: &mut Constraint, ans: &mut HashMap<u32, Typ>) {
//     if !orig.symmetric_difference(cst.clone()).is_empty() {
//         constraint_rewrite(cst, ans);
//     }
// }

// fn check_ans(t: &Typ, ans: &HashMap<u32, Typ>) -> Typ {
//     match t {
//         Typ::Metavar(i) => match ans.get(i) {
//             Some(t1) => t1.clone(),
//             None => t.clone()
//         }
//         Typ::Arr(t1, t2) => 
//             Typ::Arr(Box::new(check_ans(t1, &ans)), Box::new(check_ans(t2, &ans))),
//         _ => t.clone()
//     }
// }

// fn union_typ(t1: &Typ, t2: &Typ, ans: &HashMap<u32, Typ>) -> Typ {
//     match (t1, t2) {
//         (Typ::Metavar(i), Typ::Metavar(j)) => {if i<j {Typ::Metavar(*i)} else {Typ::Metavar(*j)}}
//         (Typ::Metavar(_), t) | (t, Typ::Metavar(_)) => {
//             if occur(t1, t2) {Typ::Any} else {t.clone()}
//         }
//         (Typ::Arr(t11, t12), Typ::Arr(t21, t22)) =>
//             Typ::Arr(
//                 Box::new(union_typ(t11, t21, &ans)), 
//                 Box::new(union_typ(t12, t22, &ans))
//             ),
//         (t3, t4) => {
//             if t3==t4 {t3.clone()} else {Typ::Any}
//         }
//     }
// }

// fn occur(t1: &Typ, t2: &Typ) -> bool {
//     match t2 {
//         Typ::Metavar(_) => if t1==t2 {true} else {false},
//         Typ::Arr(t21, t22) => occur(t1, t21) || occur(t1, t22),
//         _ => false
//     }
// }

fn annotate_metatyp(ans: &HashMap<u32, Typ>, t: &Typ) -> Typ {
    match t {
        Typ::Metavar(i) => match ans.get(i) {
            Some(Typ::Metavar(_)) => Typ::Any,
            Some(t) => t.clone(),
            None => panic!("panic in annotate_metatyp"),
        }
        _ => t.clone()

    }
}

fn annotate_typ(ans: &HashMap<u32, Typ>, t: &mut Typ) {
    match t {
        Typ::Metavar(i) => {
            match ans.get(i) {
                Some(s) => *t = match s {
                    Typ::Metavar(_) => annotate_metatyp(ans, s),
                    Typ::Arr(t1, t2) => {
                        Typ::Arr(Box::new(annotate_metatyp(ans, t1)), Box::new(annotate_metatyp(ans, t2)))
                    }
                    t => t.clone()
                },
                None => ()
            }
        }
        Typ::Arr(t1, t2) | Typ::Pair(t1, t2) => {
            annotate_typ(ans, t1);
            annotate_typ(ans, t2);
        }
        Typ::List(t) | Typ::Box(t) | Typ::Vect(t) => {
            annotate_typ(ans, t);
        }
        Typ::Unit | Typ::Int | Typ::Float | Typ::Bool | Typ::Str | Typ::Char | Typ::Any => (),
    }
}

fn annotate(ans: &HashMap<u32, Typ>, exp: &mut Exp) {
    match &mut *exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(..) | Var(..) => {}
        Exp::Fun(_, t, e) | Exp::Fix(_, t, e) | Exp::Ann(e, t) => {
            annotate_typ(ans, t);
            annotate(ans, e);
        }
        Exp::Coerce(t1, t2, e) => {
            annotate(ans, e);
            annotate_typ(ans, t1);
            annotate_typ(ans, t2);
            if t1 == t2 {
                *exp = e.take();
            }
        }
        Exp::App(e1, e2) 
        | Exp::Let(_, e1, e2)
        | Exp::BinaryOp(_, e1, e2)
        | Exp::AddOverload(e1, e2) => {
            annotate(ans, e1);
            annotate(ans, e2);
        }
        _ => {}
    }
}

#[cfg(test)]
mod test {
    use crate::{parser::parse, syntax::Exp};

    use super::type_infer;

    fn test_migrate(mut orig: &str) -> Exp {
        let mut parsed = parse(orig).unwrap();
        parsed.fresh_types();
        let e = type_infer(parsed, &Default::default()).unwrap();
        e
    }

    #[test]
    fn simple_arith() {
        test_migrate("(fun x . x + 1) 10");
    }

    #[test]
    fn bool_add() {
        test_migrate("(fun x . x + 1) true");
    }

    #[test]
    fn fun_app() {
        test_migrate("(fun f . f true) (fun x . x + 100)");
    }

    #[test]
    fn rank2_poly() {
        test_migrate("(fun i.(fun a. (i true)) (i 5) ) (fun x.x)");
    }
}