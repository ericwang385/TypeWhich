use crate::parser::{curr_metavar, next_metavar, parse};
use crate::syntax::GroundTyp;

use super::syntax::{Exp, Typ};
use super::syntax::Exp::*;
use im::{HashSet, HashMap};
use std::boxed::Box;
use either::Either::{self, Left, Right};

type Env = HashMap<String, Typ>;
type Hom = HashMap<Typ, (Typ, Typ)>;
type Ans = HashMap<u32, Either<Typ, GroundTyp>>;
type Constraint = HashSet<(Either<Typ, GroundTyp>, Either<Typ, GroundTyp>, bool)>;

// Entry Point
pub fn type_infer(mut exp: Exp, env: &Env) -> Result<Exp, String> {
    let (_, mut cst, hom) = constraint_gen(&mut exp, env);
    let n = curr_metavar();
    let mut ans = (0..n).map(|x| (x, Left(Typ::Metavar(x)))).collect::<Ans>();
    constraint_rewrite(&mut cst);
    constraint_solve(&mut cst, &mut ans, &hom);
    annotate(&ans, &mut exp, &hom);
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
            let (dom, cod) = match hom.clone().get(&t1) {
                Some(t) => t.clone(),
                None => {
                    let a = next_metavar();
                    let b = next_metavar();
                    (a, b)
                }
            };
            let funt = Typ::Arr(Box::new(alpha.clone()), Box::new(beta.clone()));
            coerce(t1.clone(), funt, e1);
            coerce(t2.clone(), alpha.clone(), e2);
            hom.insert(t1.clone(), (dom.clone(), cod.clone()));
            phi.insert((Left(t1), Right(GroundTyp::Fun), false));
            phi.insert((Left(t2), Left(alpha.clone()), false));
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

fn constraint_rewrite(cst: &mut Constraint) {
    let iterator = cst.clone();
    for (t1, t2, sign) in iterator.iter() {
        match (t1, t2, sign) {
            // a ~+ b ~+ c => a ~+ c
            (Left(_), Left(_), true) => {
                for (t3, t4, sigm) in iterator.iter() {
                    if *sigm && t2 == t3 && t1 != t4 {
                        cst.insert((t1.clone(), t4.clone(), true));
                    }
                }
            }
            // a ~- b ~- c => a ~- c
            (Left(_), Left(_), false) => {
                for (t3, t4, sigm) in iterator.iter() {
                    if !sigm && t2 == t3 && t1 != t4 {
                        cst.insert((t1.clone(), t4.clone(), false));
                    } 
                }
            }
            _ => {}
        }
    }
    if !iterator.difference(cst.clone()).is_empty() {
        constraint_rewrite(cst);
    }
}

fn constraint_solve(cst: &mut Constraint, ans: &mut Ans, hom: &Hom) {
    let iterator = cst.clone();
    let orig_ans = ans.clone();
    for constraint in iterator.iter() {
        match constraint {
            // G ~- a => a = G
            // a ~+ G => a = G
            // a = G1 & a = G2 => a = ?
            (Right(t), Left(Typ::Metavar(i)), false)
            | (Left(Typ::Metavar(i)), Right(t), true) => {
                println!("Test Flag");
                match ans.get(i).unwrap() {
                    Right(t1) => {
                        if t != t1 {
                            ans.insert(i.clone(), Left(Typ::Any));
                            cst.remove(constraint);
                            check_fun(i, ans, &hom);
                        }
                    }
                    Left(Typ::Metavar(_)) => {
                        ans.insert(i.clone(), Right(t.clone()));
                    }
                    _ => panic!("Error at first case while solving constraints"),
                }
            }
            
            (Left(Typ::Metavar(i)), Left(Typ::Metavar(j)), true) => {
                let t1 = ans.get(i).unwrap();
                let t2 = ans.get(j).unwrap();
                match (t1, t2) {
                    // ? ~+ a => a = ?
                    (Left(Typ::Any), _) => {
                        ans.insert(j.clone(), Left(Typ::Any));
                        cst.remove(constraint);
                        check_fun(i, ans, &hom);
                    }
                    // a ~+ b & b = G => a = G
                    (Left(Typ::Metavar(_)), Right(_)) => {
                        ans.insert(i.clone(), t2.clone());
                    }
                    // a ~- b & a = G => b = G
                    (Right(_), Left(Typ::Metavar(_))) => {
                        ans.insert(j.clone(), t1.clone());
                    }
                    _ => {}
                }
            }
            // a ~- G => a = G
            (Left(Typ::Metavar(i)), Right(t), false) => {
                match ans.get(i).unwrap() {
                    Left(Typ::Metavar(_)) => {
                        ans.insert(i.clone(), Right(t.clone()));
                    }
                    // a ~- G1 & a ~- G2 => a = ?
                    Right(t1) => {
                        if t != t1 {
                            ans.insert(i.clone(), Left(Typ::Any));
                            cst.remove(constraint);
                            check_fun(i, ans, &hom);
                        }
                    }
                    _ => {}
                }
            }
            
            (Right(t1), Left(Typ::Metavar(i)), true) => {
                for cc in iterator.iter() {
                    match cc {
                        // G1 ~+ a & G2 ~+ a => a = ?
                        (Right(t2), Left(Typ::Metavar(j)), true) => {
                            if i == j && t1 != t2 {
                                ans.insert(i.clone(), Left(Typ::Any));
                                cst.remove(constraint);
                                check_fun(i, ans, &hom);
                            }
                        }
                        // G1 ~+ a & a ~- G2 => a = ?
                        (Left(Typ::Metavar(j)), Right(t2), false) => {
                            if i == j && t1 != t2 {
                                ans.insert(i.clone(), Left(Typ::Any));
                                cst.remove(constraint);
                                check_fun(i, ans, &hom);
                            }
                        }
                        _ => {}
                    }
                }
            }
                     
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
            ans.insert(j.clone(), Left(Typ::Any));
            ans.insert(k.clone(), Left(Typ::Any));
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

fn test_migrate(orig: &str) -> Exp {
    let mut exp = parse(orig).unwrap();
    exp.fresh_types();
    let (_, mut cst, hom) = constraint_gen(&mut exp, &Default::default());
    let n = curr_metavar();
    let mut ans = (0..n).map(|x| (x, Left(Typ::Metavar(x)))).collect::<Ans>();
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

#[cfg(test)]
mod test {
    use super::test_migrate;


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