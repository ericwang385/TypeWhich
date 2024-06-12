use crate::parser::inc_metavar;
use std::boxed::Box;
use either::Either::{Left, Right};
use im::HashSet;
use crate::syntax::{Exp, GroundTyp, MetaVar, Typ};
use super::type_migrate::{Env, CSet, HIndex, CTyp, Constraint, FGraph};
use super::syntax::Exp::*;
use super::type_migrate::Constraint::*;

fn next_metavar() -> MetaVar {
    MetaVar::Atom(inc_metavar())
}

fn constraint_gen(exp: &mut Exp, env: &Env) -> (MetaVar, CSet, FGraph) {
    match exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(lit) => {
            let t = lit.typ().to_groundtyp().unwrap();
            outer_coerce(Right(t), exp, Default::default(), Default::default())
        },
        Var(x) => {
            let t = env.get(x)
                .unwrap_or_else(|| panic!("unbound identifier {}", x))
                .clone();
            outer_coerce(Left(t), exp, Default::default(), Default::default())
        },
        Fun(f, t, body) => {
            let mut env = env.clone();
            let t1 = t.to_metavar();
            env.insert(f.clone(), t1.clone());
            let (t2, phi, g) = constraint_gen(body, &env);
            let funt = MetaVar::Arr(Box::new(t1), Box::new(t2));
            outer_coerce(Left(funt), exp, phi, g)
        },
        App(e1, e2) => {
            let (t1, phi1, g1) = constraint_gen(e1, &env);
            let (t2, phi2, g2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2);
            let mut g = g1.union(g2);
            let alpha = next_metavar();
            let beta = next_metavar();
            let funt = MetaVar::Arr(Box::new(alpha.clone()), Box::new(beta.clone()));
            coerce(t1.to_typ(), funt.to_typ(), e1);
            coerce(t2.to_typ(), alpha.to_typ(), e2);
            phi.insert(Precious(Left(MetaVar::Dom(Box::new(t1.clone()))), Left(alpha.clone())));
            phi.insert(Precious(Left(MetaVar::Cod(Box::new(t2.clone()))), Left(beta.clone())));
            phi.insert(Precious(Left(t2), Left(alpha)));
            g.insert((funt.clone(), t1.clone()));
            (beta, phi, g)
        },
        UnaryOp(op, e) => {
            let (t1, ret) = op.typ();
            let t11 = t1.to_groundtyp().unwrap_or_else(|| panic!("UnaryOp with higher-order behavior"));
            let rett = ret.to_groundtyp().unwrap_or_else(|| panic!("UnaryOp with higher-order behavior"));
            let (t2, mut phi, g) = constraint_gen(e, &env);
            coerce(t2.to_typ(), t1, e);
            phi.insert(Precious(Left(t2), Right(t11)));
            outer_coerce(Right(rett), e, phi, g)
        },
        BinaryOp(op, e1, e2) => {
            let (t1, t2, ret) = op.typ();
            let t11 = t1.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior"));
            let t22 = t2.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior"));
            let rett = ret.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior"));
            let (t3, phi1, g1) = constraint_gen(e1, &env);
            let (t4, phi2, g2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2);
            let mut g = g1.union(g2);
            coerce(t3.to_typ(), t1, e1);
            coerce(t4.to_typ(), t2, e2);
            phi.insert(Precious(Left(t3), Right(t11)));
            phi.insert(Precious(Left(t4), Right(t22)));
            outer_coerce(Right(rett), exp, phi, g)

        },
        Let(x, e1, e2) => {
            let (t1, phi1, g1) = constraint_gen(e1, &env);
            let mut env = env.clone();
            env.insert(x.clone(), t1);
            let (t2, phi2, g2) = constraint_gen(e2, &env);
            (t2, phi1.union(phi2), g1.union(g2))
        },
        If(cond, e1, e2) => {
            let (t1, phi1, g1) = constraint_gen(cond, &env);
            let (t2, phi2, g2) = constraint_gen(e1, &env);
            let (t3, phi3, g3) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2).union(phi3);
            let g = g1.union(g2).union(g3);
            let alpha = next_metavar();
            coerce(t1.to_typ(), Typ::Bool, cond);
            coerce(t2.to_typ(), alpha.to_typ(), e1);
            coerce(t3.to_typ(), alpha.to_typ(), e2);
            phi.insert(Precious(Left(t1), Right(GroundTyp::Bool)));
            phi.insert(Precious(Left(alpha.clone()), Left(t2)));
            phi.insert(Precious(Left(alpha.clone()), Left(t3)));
            (alpha, phi, g)
        },
        _ => todo!()
    }
}

fn constraint_rewrite(phi: &mut CSet, psi: &mut HIndex) {
    let iterator = phi.clone();
    let orig_hom = psi.clone();
    for c1 in iterator.iter() {
        match c1 {
            Precious(Left(t1), Left(t2)) 
            if !t1.is_arr() && !t2.is_arr() => {
                // a < b & (a = fun | b = fun)
                match (t1, t2) {
                    (MetaVar::Atom(_), _) | (_, MetaVar::Atom(_))
                    if psi.contains(t1) ^ psi.contains(t2) => {
                        phi.insert(Precious(Left(MetaVar::Arr(Box::new(t1.dom()), Box::new(t1.cod()))), 
                                            Left(MetaVar::Arr(Box::new(t2.dom()), Box::new(t2.cod())))));
                        psi.insert(t1.clone());
                        psi.insert(t2.clone());
                    }
                    (MetaVar::Dom(a), MetaVar::Dom(b)) 
                    | (MetaVar::Cod(a), MetaVar::Cod(b))
                    | (MetaVar::Dom(a), MetaVar::Cod(b)) 
                    | (MetaVar::Cod(a), MetaVar::Dom(b)) 
                    if (psi.contains(t1) ^ psi.contains(t2)) && 
                    !phi.contains(&Precious(Left(*a.clone()), Left(*b.clone()))) => {
                        phi.insert(Precious(Left(MetaVar::Arr(Box::new(t1.dom()), Box::new(t1.cod()))), 
                                            Left(MetaVar::Arr(Box::new(t2.dom()), Box::new(t2.cod())))));
                        psi.insert(t1.clone());
                        psi.insert(t2.clone());
                    }
                    _ => {}
                }
                
                for c2 in iterator.iter() {
                    match c2 {
                        // a < b & b < G => a < G
                        // a < b & b < c => a < c
                        Constraint::Precious(Left(t3), Right(t4))
                        if !t3.is_arr() => {
                            if t2 == t3 {
                                phi.insert(Constraint::Precious(Left(t1.clone()), Right(t4.clone())));
                            } else if t1 == t3 {
                                phi.insert(Constraint::Consistent(Left(t2.clone()), Right(t4.clone())));
                            }
                        }
                        Constraint::Precious(Left(t3), Left(t4)) 
                        if !t3.is_arr() && !t4.is_arr() => {
                            if t2 == t3 && t1 != t4 {
                                phi.insert(Constraint::Precious(Left(t1.clone()), Left(t4.clone())));
                            } else if t1 == t3 && t2 != t4 {
                                phi.insert(Constraint::Consistent(Left(t2.clone()), Left(t4.clone())));
                            }
                        }
                        _ => {}
                    }
                }
            }
            // a -> b < c -> d => a < c & b < d
            Precious(Left(MetaVar::Arr(t11, t12)), Left(MetaVar::Arr(t21, t22))) => {
                // phi.remove(&(t1.clone(), t2.clone()));
                phi.insert(Precious(Left(*t11.clone()), Left(*t21.clone())));
                phi.insert(Precious(Left(*t12.clone()), Left(*t22.clone())));
            }
            // a < b -> c
            Precious(Left(t), t2 @ Left(MetaVar::Arr(_,_))) 
            if !t.is_arr() => {
                psi.insert(t.clone());
                phi.insert(Precious(
                    Left(MetaVar::Arr(Box::new(t.dom()), Box::new(t.cod()))), 
                    t2.clone()
                ));
            }
            // b -> c < a
            Constraint::Precious(t1 @ Left(MetaVar::Arr(_, _)), Left(t))
            if !t.is_arr() => {
                psi.insert(t.clone());
                phi.insert(Precious(
                    t1.clone(),
                    Left(MetaVar::Arr(Box::new(t.dom()), Box::new(t.cod())))
                ));
            }
            _ => {}
        }
    }

    let phi_diff = iterator.difference(phi.clone());
    let psi_diff = orig_hom.difference(psi.clone());
    
    if !phi_diff.is_empty() || !psi_diff.is_empty() {
        constraint_rewrite(phi, psi);
    }
}

fn coerce(t1: Typ, t2: Typ, exp: &mut Exp) {
    *exp = Exp::Coerce(t1, t2, Box::new(exp.take()))
}

fn outer_coerce(t: CTyp, exp: &mut Exp, mut phi: CSet, mut g: FGraph) -> (MetaVar, CSet, FGraph) {
    let alpha = next_metavar();
    match t {
        Left(a @ MetaVar::Atom(_)) => {
            coerce(a.to_typ(), alpha.to_typ(), exp);
            phi.insert(Constraint::Precious(Left(alpha.clone()), Left(a)));
        },
        Left(MetaVar::Arr(t1, t2)) => {
            coerce(MetaVar::Arr(t1.clone(), t2.clone()).to_typ(), alpha.to_typ(), exp);
            phi.insert(Constraint::Precious(Left(MetaVar::Dom(Box::new(alpha.clone()))), Left(*t1.clone())));
            phi.insert(Constraint::Precious(Left(MetaVar::Cod(Box::new(alpha.clone()))), Left(*t2.clone())));
            g.insert((MetaVar::Arr(Box::new(*t1.clone()), Box::new(*t2.clone())), alpha.clone()));
        },
        Left(_) => panic!("Panic at outer coerce"),
        Right(a) => {
            coerce(a.to_typ(), alpha.to_typ(), exp);
            phi.insert(Constraint::Precious(Left(alpha.clone()), Right(a)));
        }
    };
    (alpha, phi, g)
}

pub fn cgen(exp: &mut Exp, env: &Env) -> (CSet, HIndex) {
    let (_, mut phi, mut g) = constraint_gen(exp, env);
    let mut psi = Default::default();
    constraint_rewrite(&mut phi, &mut psi);
    (phi, psi)
}