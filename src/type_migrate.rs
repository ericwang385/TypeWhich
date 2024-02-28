use crate::parser::{curr_metavar, next_metavar, parse};
use crate::syntax::GroundTyp;

use super::syntax::{Exp, Typ};
use super::syntax::Exp::*;
use im::{HashSet, HashMap};
use std::boxed::Box;
use either::Either::{self, Left, Right};

type Env = HashMap<String, Typ>;
type Hom = HashMap<Typ, (Typ, Typ)>;
type Ans = HashMap<u32, Typ>;
type Constraint = HashSet<(Typ, Typ)>;

// Entry Point
pub fn type_infer(mut exp: Exp, env: &Env) -> Result<Exp, String> {
    let (_, mut cst) = constraint_gen(&mut exp, env);
    let n = curr_metavar();
    let mut ans = (0..n).map(|x| (x, Typ::Metavar(x))).collect::<Ans>();
    let mut hom = Default::default();
    constraint_rewrite(&mut cst, &mut hom);
    constraint_solve(&mut cst, &mut ans, &hom);
    annotate(&ans, &mut exp, &hom);
    Ok(exp)
}

pub fn type_check(exp: &Exp) -> Result<Typ, String> {
    todo!()
}

fn constraint_gen(exp: &mut Exp, env: &Env) -> (Typ, Constraint) {
    match exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(lit) => {
            let t1 = lit.typ();
            outer_coerce(t1, exp, Default::default())
        },
        Var(x) => {
            let t1 = env.get(x)
                .unwrap_or_else(|| panic!("unbound identifier {}", x))
                .clone();
            outer_coerce(t1, exp, Default::default())
        },
        Fun(f, t1, body) => {
            let mut env = env.clone();
            env.insert(f.clone(), t1.clone());
            let (t2, phi) = constraint_gen(body, &env);
            let funt = Typ::Arr(Box::new(t1.clone()), Box::new(t2));
            outer_coerce(funt, exp, phi)
        },
        App(e1, e2) => {
            let (t1, phi1) = constraint_gen(e1, &env);
            let (t2, phi2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2);
            let alpha = next_metavar();
            let beta = next_metavar();
            let funt = Typ::Arr(Box::new(alpha.clone()), Box::new(beta.clone()));
            coerce(t1.clone(), funt.clone(), e1);
            coerce(t2.clone(), alpha.clone(), e2);
            phi.insert((t1, funt));
            phi.insert((t2, alpha));
            (beta, phi)
        },
        UnaryOp(op, e) => {
            let (t1, ret) = op.typ();
            // let t11 = t1.to_groundtyp().unwrap_or_else(|| panic!("UnaryOp with higher-order behavior"));
            let (t2, mut phi) = constraint_gen(e, &env);
            coerce(t2.clone(), t1.clone(), e);
            phi.insert((t2, t1));
            outer_coerce(ret, e, phi)
        },
        BinaryOp(op, e1, e2) => {
            let (t1, t2, ret) = op.typ();
            // let t11 = t1.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior"));
            // let t22 = t2.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior"));
            let (t3, phi1) = constraint_gen(e1, &env);
            let (t4, phi2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2);
            coerce(t3.clone(), t1.clone(), e1);
            coerce(t4.clone(), t2.clone(), e2);
            phi.insert((t3, t1));
            phi.insert((t4, t2));
            outer_coerce(ret, exp, phi)
        },
        Let(x, e1, e2) => {
            let (t1, phi1) = constraint_gen(e1, &env);
            let mut env = env.clone();
            env.insert(x.clone(), t1);
            let (t2, phi2) = constraint_gen(e2, &env);
            (t2, phi1.union(phi2))
        }
        If(cond, e1, e2) => {
            let (t1, phi1) = constraint_gen(cond, &env);
            let (t2, phi2) = constraint_gen(e1, &env);
            let (t3, phi3) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2).union(phi3);
            let alpha = next_metavar();
            coerce(t1.clone(), Typ::Bool, cond);
            coerce(t2.clone(), alpha.clone(), e1);
            coerce(t3.clone(), alpha.clone(), e2);
            phi.insert((t1, Typ::Bool));
            phi.insert((alpha.clone(), t2));
            phi.insert((alpha.clone(), t3));
            (alpha, phi)
        }
        _ => todo!()
    }
}

fn outer_coerce(t: Typ, exp: &mut Exp, mut cst: Constraint) -> (Typ, Constraint) {
    let alpha = next_metavar();
    coerce(t.clone(), alpha.clone(), exp);
    cst.insert((alpha.clone(), t));
    (alpha, cst)
}

fn coerce(t1: Typ, t2: Typ, exp: &mut Exp) {
    *exp = Exp::Coerce(t1, t2, Box::new(exp.take()))
}

fn constraint_rewrite(cst: &mut Constraint, hom: &mut Hom) {
    let iterator = cst.clone();
    let orig_hom = hom.clone();
    for (t1, t2) in iterator.iter() {
        match (t1, t2) {
            // a < b < G => a < G 
            (Typ::Metavar(_), Typ::Int)
            | (Typ::Metavar(_), Typ::Bool) => {
                for (t3, t4) in iterator.iter() {
                    if t2 == t3 && t1 != t4 {
                        cst.insert((t3.clone(), t1.clone()));
                    }
                }
            }
            (Typ::Metavar(_), Typ::Metavar(_)) => {
                if hom.contains_key(t1) && !hom.contains_key(t2) {
                    // a < b && a = c -> d && b != _ -> _
                    let alpha = next_metavar();
                    let beta = next_metavar();
                    hom.insert(t2.clone(), (alpha.clone(), beta.clone()));
                    cst.insert((t1.clone(), Typ::Arr(Box::new(alpha), Box::new(beta))));
                } else if hom.contains_key(t2) && ! hom.contains_key(t1){
                    // a < b && b = c -> d && a != _ -> _
                    let alpha = next_metavar();
                    let beta = next_metavar();
                    hom.insert(t1.clone(), (alpha.clone(), beta.clone()));
                    cst.insert((Typ::Arr(Box::new(alpha), Box::new(beta)), t2.clone()));
                }
                // a < b < c => a < c
                for (t3, t4) in iterator.iter() {
                    if t2 == t3 && t1 != t4 {
                        cst.insert((t3.clone(), t1.clone()));
                    }
                }
            }
            // a -> b < c -> d => a < c & b < d
            (Typ::Arr(t11, t12), Typ::Arr(t21, t22)) => {
                cst.insert((*t11.clone(), *t21.clone()));
                cst.insert((*t12.clone(), *t22.clone()));
            }
            // a < b -> c
            (Typ::Metavar(_), Typ::Arr(_, _)) => {
                let (alpha, beta) = match hom.get(t1) {
                    Some((a, b)) => (a.clone(), b.clone()),
                    None => {
                        let a = next_metavar();
                        let b = next_metavar();
                        (a, b)
                    },
                };
                cst.insert((Typ::Arr(Box::new(alpha.clone()), Box::new(beta.clone())), t2.clone()));
                hom.insert(t1.clone(), (alpha, beta));
            }
            // b -> c < a
            (Typ::Arr(_, _), Typ::Metavar(_)) => {
                let (alpha, beta) = match hom.get(t2) {
                    Some((a, b)) => (a.clone(), b.clone()),
                    None => {
                        let a = next_metavar();
                        let b = next_metavar();
                        (a, b)
                    },
                };
                cst.insert((t1.clone(), Typ::Arr(Box::new(alpha.clone()), Box::new(beta.clone()))));
                hom.insert(t2.clone(), (alpha, beta));
            }
            _ => {}
        }
    }
    if !iterator.difference(cst.clone()).is_empty() || !orig_hom.difference(hom.clone()).is_empty() {
        constraint_rewrite(cst, hom);
    }
}

fn constraint_solve(cst: &mut Constraint, ans: &mut Ans, hom: &Hom) {
    let iterator = cst.clone();
    let orig_ans = ans.clone();
    for (t1, t2) in iterator.iter() {
        match (t1, t2) {
            // G < a => a = G
            (Typ::Int, Typ::Metavar(i))
            | (Typ::Bool, Typ::Metavar(i)) => {
                match ans.get(i).unwrap() {
                    t => {
                        if t1 != t {
                            ans.insert(i.clone(), Typ::Any);
                            check_fun(i, ans, &hom);
                        }
                    }
                    Typ::Metavar(i) => {
                        ans.insert(i.clone(), t1.clone());
                    }
                    _ => panic!("Error at first case while solving constraints"),
                }
            }
            // a < G1 & a < G2 => a = ?      
            
            _ => {}
        }
    }
    if !iterator.difference(cst.clone()).is_empty() {
        constraint_solve(cst, ans, hom);
    } else if !orig_ans.difference(ans.clone()).is_empty() {
        constraint_solve(cst, ans, hom);
    }
}

fn check_fun(i: &u32, ans: &mut Ans, hom: &Hom) {
    match hom.get(&Typ::Metavar(*i)) {
        Some((Typ::Metavar(j), Typ::Metavar(k))) => {
            ans.insert(j.clone(), Typ::Any);
            ans.insert(k.clone(), Typ::Any);
        }
        // None => {}
        _ => {}
    }
}

fn annotate_typ(ans: &Ans, t: &mut Typ, hom: &Hom) {
    match t {
        Typ::Metavar(i) => {
            match ans.get(i) {
                Some(s) => *t = match s {
                    Left(Typ::Metavar(_)) => Typ::Any,
                    Right(GroundTyp::Fun) => {
                        match hom.get(&Typ::Metavar(*i)) {
                            Some((t1, t2)) => {
                                annotate_typ(ans, &mut t1.clone(), hom);
                                annotate_typ(ans, &mut t2.clone(), hom);
                                Typ::Arr(Box::new(t1.clone()), Box::new(t2.clone()))
                            }
                            None => {Typ::Arr(Box::new(Typ::Any), Box::new(Typ::Any))}
                        }
                        
                    }
                    Right(GroundTyp::Bool) => Typ::Bool,
                    Right(GroundTyp::Int) => Typ::Int,
                    _ => {panic!("Error when annotate type")}
                },
                None => ()
            }
        }
        Typ::Arr(t1, t2) | Typ::Pair(t1, t2) => {
            annotate_typ(ans, t1, hom);
            annotate_typ(ans, t2, hom);
        }
        Typ::List(t) | Typ::Box(t) | Typ::Vect(t) => {
            annotate_typ(ans, t, hom);
        }
        Typ::Unit | Typ::Int | Typ::Float | Typ::Bool | Typ::Str | Typ::Char | Typ::Any => (),
    }
}

fn annotate(ans: &Ans, exp: &mut Exp, hom: &Hom) {
    match &mut *exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(..) | Var(..) => {}
        Exp::Fun(_, t, e) | Exp::Fix(_, t, e) | Exp::Ann(e, t) => {
            annotate_typ(ans, t, hom);
            annotate(ans, e, hom);
        }
        Exp::Coerce(t1, t2, e) => {
            annotate(ans, e, hom);
            annotate_typ(ans, t1, hom);
            annotate_typ(ans, t2, hom);
            if t1 == t2 {
                *exp = e.take();
            }
        }
        Exp::App(e1, e2) 
        | Exp::Let(_, e1, e2)
        | Exp::BinaryOp(_, e1, e2)
        | Exp::AddOverload(e1, e2) => {
            annotate(ans, e1, hom);
            annotate(ans, e2, hom);
        }
        _ => {}
    }
}

#[cfg(test)]
mod test {
    use either::Either::Left;
    use crate::syntax::{Exp, Typ};
    use crate::parser::{curr_metavar, parse};
    use crate::type_migrate::{annotate, constraint_gen, constraint_rewrite, constraint_solve, Ans};

    fn test_migrate(orig: &str) -> Exp {
        let mut exp = parse(orig).unwrap();
        exp.fresh_types();
        let (_, mut cst) = constraint_gen(&mut exp, &Default::default());
        let n = curr_metavar();
        let mut ans = (0..n).map(|x| (x, Left(Typ::Metavar(x)))).collect::<Ans>();
        let hom = Default::default();
        constraint_rewrite(&mut cst);
        println!("Constraint:\n{:?}", cst);
        constraint_solve(&mut cst, &mut ans, &hom);
        println!("Answer Set:\n{:?}", ans);
        println!("Higher-Order Set:\n{:?}", hom);
        println!("Before Annotation:\n{:?}\n", exp);
        annotate(&ans, &mut exp, &hom);
        println!("After Annotation Pretty:\n{}\n", exp);
        exp
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