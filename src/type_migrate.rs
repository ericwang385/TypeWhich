use crate::parser::{curr_metavar, inc_metavar, parse};
use crate::syntax::{GroundTyp, MetaVar};

use super::syntax::{Exp, Typ};
use super::syntax::Exp::*;
use im::{HashSet, HashMap};
use std::boxed::Box;
use either::Either::{self, Left, Right};

type Env = HashMap<String, MetaVar>;
type CTyp = Either<MetaVar, GroundTyp>;
type Hom = HashMap<u32, (u32, u32)>;
type Ans = HashMap<u32, Typ>;
type Constraint = HashSet<(CTyp, CTyp)>;

fn next_metavar() -> MetaVar {
    MetaVar::Atom(inc_metavar())
}

// Entry Point
pub fn type_infer(mut exp: Exp, env: &Env) -> Result<Exp, String> {
    let (_, mut phi) = constraint_gen(&mut exp, env);
    let mut psi = Default::default();
    let mut sigma = Default::default();
    // let n = curr_metavar();
    // let mut sigma = (0..n).map(|x| (x, Typ::Metavar(x))).collect::<Ans>();
    constraint_rewrite(&mut phi, &mut psi);
    constraint_solve(&mut phi, &mut sigma, &psi);
    annotate(&sigma, &mut exp, &psi);
    Ok(exp)
}

// pub fn type_check(exp: &Exp) -> Result<Typ, String> {
//     todo!()
// }

fn constraint_gen(exp: &mut Exp, env: &Env) -> (MetaVar, Constraint) {
    match exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(lit) => {
            let t = lit.typ().to_groundtyp().unwrap();
            outer_coerce(Right(t), exp, Default::default())
        },
        Var(x) => {
            let t = env.get(x)
                .unwrap_or_else(|| panic!("unbound identifier {}", x))
                .clone();
            outer_coerce(Left(t), exp, Default::default())
        },
        Fun(f, t, body) => {
            let mut env = env.clone();
            let t1 = t.to_metavar();
            env.insert(f.clone(), t1.clone());
            let (t2, phi) = constraint_gen(body, &env);
            let funt = MetaVar::Arr(Box::new(t1), Box::new(t2));
            outer_coerce(Left(funt), exp, phi)
        },
        App(e1, e2) => {
            let (t1, phi1) = constraint_gen(e1, &env);
            let (t2, phi2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2);
            let alpha = next_metavar();
            let beta = next_metavar();
            let funt = MetaVar::Arr(Box::new(alpha.clone()), Box::new(beta.clone()));
            coerce(t1.to_typ(), funt.to_typ(), e1);
            coerce(t2.to_typ(), alpha.to_typ(), e2);
            phi.insert((Left(t1), Left(funt)));
            phi.insert((Left(t2), Left(alpha)));
            (beta, phi)
        },
        UnaryOp(op, e) => {
            let (t1, ret) = op.typ();
            let t11 = t1.to_groundtyp().unwrap_or_else(|| panic!("UnaryOp with higher-order behavior"));
            let rett = ret.to_groundtyp().unwrap_or_else(|| panic!("UnaryOp with higher-order behavior"));
            let (t2, mut phi) = constraint_gen(e, &env);
            coerce(t2.to_typ(), t1, e);
            phi.insert((Left(t2), Right(t11)));
            outer_coerce(Right(rett), e, phi)
        },
        BinaryOp(op, e1, e2) => {
            let (t1, t2, ret) = op.typ();
            let t11 = t1.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior"));
            let t22 = t2.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior"));
            let rett = ret.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior"));
            let (t3, phi1) = constraint_gen(e1, &env);
            let (t4, phi2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2);
            coerce(t3.to_typ(), t1, e1);
            coerce(t4.to_typ(), t2, e2);
            phi.insert((Left(t3), Right(t11)));
            phi.insert((Left(t4), Right(t22)));
            outer_coerce(Right(rett), exp, phi)
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
            coerce(t1.to_typ(), Typ::Bool, cond);
            coerce(t2.to_typ(), alpha.to_typ(), e1);
            coerce(t3.to_typ(), alpha.to_typ(), e2);
            phi.insert((Left(t1), Right(GroundTyp::Bool)));
            phi.insert((Left(alpha.clone()), Left(t2)));
            phi.insert((Left(alpha.clone()), Left(t3)));
            (alpha, phi)
        }
        _ => todo!()
    }
}

fn outer_coerce(t: CTyp, exp: &mut Exp, mut cst: Constraint) -> (MetaVar, Constraint) {
    let alpha = next_metavar();
    match t {
        Left(a) => {
            coerce(a.to_typ(), alpha.to_typ(), exp);
            cst.insert((Left(alpha.clone()), Left(a)))
        },
        Right(a) => {
            coerce(a.to_typ(), alpha.to_typ(), exp);
            cst.insert((Left(alpha.clone()), Right(a)))
        }
    };
    (alpha, cst)
}

fn coerce(t1: Typ, t2: Typ, exp: &mut Exp) {
    *exp = Exp::Coerce(t1, t2, Box::new(exp.take()))
}

fn constraint_rewrite(phi: &mut Constraint, psi: &mut Hom) {
    let iterator = phi.clone();
    let orig_hom = psi.clone();
    for (t1, t2) in iterator.iter() {
        match (t1, t2) {
            (Left(MetaVar::Atom(i)), Left(MetaVar::Atom(j))) => {
                if psi.contains_key(i) && !psi.contains_key(j) {
                    // a < b & a = fun & b != fun
                    let (dom, cod) = (next_metavar(), next_metavar());
                    let (a1, a2) = psi.get(i).unwrap();
                    let funt = MetaVar::Arr(Box::new(MetaVar::Atom(*a1)), Box::new(MetaVar::Atom(*a2)));
                    psi.insert(*j, (dom.index(), cod.index()));
                    phi.insert((Left(funt), Left(MetaVar::Arr(Box::new(dom), Box::new(cod)))));

                } else if !psi.contains_key(i) && psi.contains_key(j) {
                    // a < b & a != fun & b = fun
                    let (dom, cod) = (next_metavar(), next_metavar());
                    let (b1, b2) = psi.get(j).unwrap();
                    let funt = MetaVar::Arr(Box::new(MetaVar::Atom(*b1)), Box::new(MetaVar::Atom(*b2)));
                    psi.insert(*i, (dom.index(), cod.index()));
                    phi.insert((Left(MetaVar::Arr(Box::new(dom), Box::new(cod))), Left(funt)));
                } else if psi.contains_key(i) && psi.contains_key(j) {
                    // a < b & a = fun & b = fun
                    let (a1, a2) = psi.get(i).unwrap();
                    let (b1, b2) = psi.get(j).unwrap();
                    let funta = MetaVar::Arr(Box::new(MetaVar::Atom(*a1)), Box::new(MetaVar::Atom(*a2)));
                    let funtb = MetaVar::Arr(Box::new(MetaVar::Atom(*b1)), Box::new(MetaVar::Atom(*b2)));
                    phi.insert((Left(funta), Left(funtb)));
                    phi.remove(&(t1.clone(), t2.clone()));
                }
                for (t3, t4) in iterator.iter() {
                    match (t3, t4) {
                        // a < b & b < G => a < G
                        // a < b & b < c => a < c
                        (Left(MetaVar::Atom(_)), Right(_))
                        | (Left(MetaVar::Atom(_)), Left(MetaVar::Atom(_))) => {
                            if t2 == t3 && t1 != t4 {
                                phi.insert((t1.clone(), t4.clone()));
                            }
                        }
                        _ => {}
                    }
                }
            }
            // a -> b < c -> d => a < c & b < d
            (Left(MetaVar::Arr(t11, t12)), Left(MetaVar::Arr(t21, t22))) => {
                phi.remove(&(t1.clone(), t2.clone()));
                phi.insert((Left(*t11.clone()), Left(*t21.clone())));
                phi.insert((Left(*t12.clone()), Left(*t22.clone())));
            }
            // a < b -> c
            (Left(MetaVar::Atom(i)), Left(MetaVar::Arr(_,_))) => {
                phi.remove(&(t1.clone(), t2.clone()));
                if psi.contains_key(i) {
                    let (dom, cod) = psi.get(i).unwrap();
                    phi.insert((Left(MetaVar::Arr(Box::new(MetaVar::Atom(*dom)), Box::new(MetaVar::Atom(*cod)))), t2.clone()));
                } else {
                    let (dom, cod) = (next_metavar(), next_metavar());
                    phi.insert((Left(MetaVar::Arr(Box::new(dom.clone()), Box::new(cod.clone()))), t2.clone()));
                    psi.insert(*i, (dom.index(), cod.index()));
                }
            }
            // b -> c < a
            (Left(MetaVar::Arr(_, _)), Left(MetaVar::Atom(j))) => {
                phi.remove(&(t1.clone(), t2.clone()));
                if psi.contains_key(j) {
                    let (dom, cod) = psi.get(j).unwrap();
                    phi.insert((t1.clone(), Left(MetaVar::Arr(Box::new(MetaVar::Atom(*dom)), Box::new(MetaVar::Atom(*cod))))));
                } else {
                    let (dom, cod) = (next_metavar(), next_metavar());
                    phi.insert((t1.clone(), Left(MetaVar::Arr(Box::new(dom.clone()), Box::new(cod.clone())))));
                    psi.insert(*j, (dom.index(), cod.index()));
                }
            }
            _ => {}
        }
    }
    if !iterator.difference(phi.clone()).is_empty() || !orig_hom.difference(psi.clone()).is_empty() {
        constraint_rewrite(phi, psi);
    }
}

fn constraint_solve(phi: &mut Constraint, sigma: &mut Ans, psi: &Hom) {
    // conflict_solve(phi, sigma, psi);
    println!("Original Constraint{:?} \n", phi);
    loop {
        if sigma.len() as u32 == curr_metavar() {
            return;
        }
        // println!("Answer Set: {:?}", sigma);
        let orig_sigma = sigma.clone();
        let orig_phi = phi.clone();
        try_assign(phi, sigma);
        conflict_solve(phi, sigma, psi);
        println!("Constraint{:?} \n", phi);
        println!("orig_sigma{:?}, sigma{:?} \n", orig_sigma, sigma);
        if orig_sigma.difference(sigma.clone()).is_empty() && orig_phi.difference(phi.clone()).is_empty() {
            return;
        }
    }
}

fn conflict_solve(phi: &Constraint, sigma: &mut Ans, psi: &Hom) {
    let iterator = phi.clone();
    let orig_sigma = sigma.clone();
    let n = curr_metavar();
    for (t1, t2) in iterator.iter() {
        match (t1, t2) {
            // G < a => a = G
            (Right(a), Left(MetaVar::Atom(i))) => {
                match sigma.get(i) {
                    Some(b) => {
                        if a.to_typ() != b.clone() {
                            sigma.insert(i.clone(), Typ::Any);
                        }
                    }
                    None => {
                        sigma.insert(i.clone(), a.to_typ());
                    }
                }
            }
            // a < G1 & a < G2 => a = ?      
            (Left(MetaVar::Atom(_)), Right(_)) => {
                for (t3, t4) in iterator.iter() {
                    match (t3, t4) {
                        (Left(MetaVar::Atom(i)), Right(_)) if t1 == t3 && t2 != t4 => {
                            sigma.insert(i.clone(), Typ::Any);
                        }
                        _ => {}
                    }
                }
            }
            // b = ? & a < b => a = ?
            (Left(MetaVar::Atom(i)), Left(MetaVar::Atom(j))) => {
                if sigma.get(j) == Some(&Typ::Any){
                    sigma.insert(i.clone(), Typ::Any);
                }
            }
            _ => {}
        }
    }
    for i in 0..n {
        match sigma.get(&i) {
            Some(Typ::Int) 
            | Some(Typ::Bool) if psi.contains_key(&i)=> {
                let (dom, cod) = psi.get(&i).unwrap();
                sigma.insert(i, Typ::Any);
                sigma.insert(*dom, Typ::Any);
                sigma.insert(*cod, Typ::Any);
            }
            Some(Typ::Arr(t1, t2)) => {
                let (dom, cod) = psi.get(&i).unwrap();
                let (t11, t22) = (*t1.clone(), *t2.clone());
                match (sigma.get(dom), sigma.get(cod)) {
                    (Some(t3), Some(t4)) => {
                        if t11 != t3.clone() && t22 != t4.clone() {
                            sigma.insert(i, Typ::Arr(Box::new(Typ::Any), Box::new(Typ::Any)));
                            sigma.insert(*dom, Typ::Any);
                            sigma.insert(*cod, Typ::Any);
                        } else if t11 != t3.clone() && t22 == t4.clone() {
                            sigma.insert(i, Typ::Arr(Box::new(Typ::Any), t2.clone()));
                            sigma.insert(*dom, Typ::Any);
                        } else if t11 == t3.clone() && t22 != t4.clone() {
                            sigma.insert(i, Typ::Arr(t1.clone(), Box::new(Typ::Any)));
                            sigma.insert(*cod, Typ::Any);
                        }
                    }
                    (Some(t3), None) => {
                        if t11 != t3.clone() {
                            sigma.insert(i, Typ::Arr(Box::new(Typ::Any), t2.clone()));
                            sigma.insert(*dom, Typ::Any);
                        }
                        sigma.insert(*cod, t22);
                    }
                    (None, Some(t4)) => {
                        if t22 != t4.clone() {
                            sigma.insert(i, Typ::Arr(t1.clone(), Box::new(Typ::Any)));
                            sigma.insert(*cod, Typ::Any);
                        }
                        sigma.insert(*dom, t11);
                    }
                    (None, None) => {
                        sigma.insert(*cod, t22);
                        sigma.insert(*dom, t11);
                    }
                }
            }
            None if psi.contains_key(&i) => {
                let (dom, cod) = psi.get(&i).unwrap();
                match (sigma.get(dom), sigma.get(cod)) {
                    (Some(a), Some(b)) => {
                        sigma.insert(i, Typ::Arr(Box::new(a.clone()), 
                                            Box::new(b.clone())));
                    }
                    // (Some(a), None) => {
                    //     sigma.insert(i, Typ::Arr((), ()))
                    // }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    if !orig_sigma.difference(sigma.clone()).is_empty() {
        conflict_solve(phi, sigma, psi);
    }
}

fn try_assign(phi: &mut Constraint, sigma: &mut Ans) {
    // let iterator = phi.clone();
    for (t1, t2) in phi.clone().iter() {
        match (t1, t2) {
            (Left(MetaVar::Atom(i)), Right(t)) if sigma.get(&i) == None => {
                sigma.insert(*i, t.to_typ());
            }
            _ => {}
        }
    }
    for i in 0..curr_metavar() {
        match sigma.get(&i) {
            Some(t @ Typ::Int) 
            | Some(t @ Typ::Bool) => substitute(i, t.to_groundtyp().unwrap(), phi),
            _ => {}
        };
    }
}

fn substitute(i: u32, t: GroundTyp, phi: &mut Constraint) {
    let iterator = phi.clone();
    for (t1, t2) in iterator.iter() {
        if t1 == &Left(MetaVar::Atom(i)) {
            phi.remove(&(t1.clone(), t2.clone()));
            phi.insert((Right(t.clone()), t2.clone()));
        } else if t2 == &Left(MetaVar::Atom(i)) {
            phi.remove(&(t1.clone(), t2.clone()));
            phi.insert((t2.clone(), Right(t.clone())));
        }
    }
}

fn annotate_typ(ans: &Ans, t: &mut Typ, hom: &Hom) {
    match t {
        Typ::Metavar(i) => {
            *t = match ans.get(i) {
                Some(s) => match s {
                    Typ::Metavar(_) => panic!("Type variable in answer set at {}", i),
                    _ => s.clone(),
                },
                None => Typ::Any,
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

fn annotate(sigma: &Ans, exp: &mut Exp, psi: &Hom) {
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
    use crate::syntax::{Exp, Typ};
    use crate::parser::{curr_metavar, parse};
    use crate::type_migrate::{annotate, constraint_gen, constraint_rewrite, constraint_solve};

    fn test_migrate(orig: &str) -> Exp {
        let mut exp = parse(orig).unwrap();
        exp.fresh_types();
        let (_, mut phi) = constraint_gen(&mut exp, &Default::default());
        // let n = curr_metavar();
        let mut sigma = Default::default();
        let mut psi = Default::default();
        constraint_rewrite(&mut phi, &mut psi);
        constraint_solve(&mut phi, &mut sigma, &psi);
        // println!("Constraint:\n{:?}", phi);
        // println!("Answer Set:\n{:?}", sigma);
        // println!("Higher-Order Set:\n{:?}", psi);
        // println!("Before Annotation:\n{:?}\n", exp);
        annotate(&sigma, &mut exp, &psi);
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
