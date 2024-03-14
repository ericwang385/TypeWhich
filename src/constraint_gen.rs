use im::{HashMap, HashSet};
use crate::parser::inc_metavar;
use std::boxed::Box;
use either::Either::{Left, Right};
use crate::syntax::{Exp, GroundTyp, MetaVar, Typ};
use super::type_migrate::{Env, CSet, HIndex, CTyp, Constraint};
use super::syntax::Exp::*;

fn next_metavar() -> MetaVar {
    MetaVar::Atom(inc_metavar())
}

fn constraint_gen(exp: &mut Exp, env: &Env) -> (MetaVar, CSet) {
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
            phi.insert(Constraint::Precious(Left(t1), Left(funt)));
            phi.insert(Constraint::Precious(Left(t2), Left(alpha)));
            (beta, phi)
        },
        UnaryOp(op, e) => {
            let (t1, ret) = op.typ();
            let t11 = t1.to_groundtyp().unwrap_or_else(|| panic!("UnaryOp with higher-order behavior"));
            let rett = ret.to_groundtyp().unwrap_or_else(|| panic!("UnaryOp with higher-order behavior"));
            let (t2, mut phi) = constraint_gen(e, &env);
            coerce(t2.to_typ(), t1, e);
            phi.insert(Constraint::Precious(Left(t2), Right(t11)));
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
            phi.insert(Constraint::Precious(Left(t3), Right(t11)));
            phi.insert(Constraint::Precious(Left(t4), Right(t22)));
            outer_coerce(Right(rett), exp, phi)
        },
        Let(x, e1, e2) => {
            let (t1, phi1) = constraint_gen(e1, &env);
            let mut env = env.clone();
            env.insert(x.clone(), t1);
            let (t2, phi2) = constraint_gen(e2, &env);
            (t2, phi1.union(phi2))
        },
        If(cond, e1, e2) => {
            let (t1, phi1) = constraint_gen(cond, &env);
            let (t2, phi2) = constraint_gen(e1, &env);
            let (t3, phi3) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2).union(phi3);
            let alpha = next_metavar();
            coerce(t1.to_typ(), Typ::Bool, cond);
            coerce(t2.to_typ(), alpha.to_typ(), e1);
            coerce(t3.to_typ(), alpha.to_typ(), e2);
            phi.insert(Constraint::Precious(Left(t1), Right(GroundTyp::Bool)));
            phi.insert(Constraint::Precious(Left(alpha.clone()), Left(t2)));
            phi.insert(Constraint::Precious(Left(alpha.clone()), Left(t3)));
            (alpha, phi)
        },
        _ => todo!()
    }
}

fn constraint_rewrite(phi: &mut CSet, psi: &mut HIndex) {
    let iterator = phi.clone();
    let orig_hom = psi.clone();
    for c1 in iterator.iter() {
        match c1 {
            Constraint::Precious(t1 @ Left(t11), t2 @ Left(t22)) 
            if !t11.is_arr() && !t22.is_arr() => {
                // a < b & (a = fun | b = fun)
                match (t11, t22) {
                    (MetaVar::Atom(_), _) | (_, MetaVar::Atom(_)) 
                    if psi.contains(t11) || psi.contains(t22) => {
                        phi.insert(Constraint::Precious(
                            Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t11.clone()))), Box::new(MetaVar::Cod(Box::new(t11.clone()))))), 
                            Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t22.clone()))), Box::new(MetaVar::Cod(Box::new(t22.clone())))))
                        ));
                        psi.insert(t11.clone());
                        psi.insert(t22.clone());
                    }
                    (MetaVar::Dom(a), MetaVar::Dom(b)) | (MetaVar::Cod(a), MetaVar::Cod(b))
                    | (MetaVar::Dom(a), MetaVar::Cod(b)) | (MetaVar::Cod(a), MetaVar::Dom(b))
                    if (psi.contains(t11) || psi.contains(t22)) && !phi.contains(&Constraint::Precious(Left(*a.clone()), Left(*b.clone()))) => {
                        phi.insert(Constraint::Precious(
                            Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t11.clone()))), Box::new(MetaVar::Cod(Box::new(t11.clone()))))), 
                            Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t22.clone()))), Box::new(MetaVar::Cod(Box::new(t22.clone())))))
                        ));
                        psi.insert(t11.clone());
                        psi.insert(t22.clone());
                    }
                    _ => {}
                }
                for c2 in iterator.iter() {
                    match c2 {
                        // a < b & b < G => a < G
                        // a < b & b < c => a < c
                        Constraint::Precious(t3 @ Left(MetaVar::Atom(_)), t4 @ Right(_))
                        | Constraint::Precious(t3 @ Left(MetaVar::Atom(_)), t4 @ Left(MetaVar::Atom(_))) => {
                            if t2 == t3 && t1 != t4 {
                                phi.insert(Constraint::Precious(t1.clone(), t4.clone()));
                            } else if t1 == t3 && t2 != t4 {
                                phi.insert(Constraint::Consistent(t2.clone(), t4.clone()));
                            }
                        }
                        _ => {}
                    }
                }
            }
            // a -> b < c -> d => a < c & b < d
            Constraint::Precious(Left(MetaVar::Arr(t11, t12)), Left(MetaVar::Arr(t21, t22))) => {
                // phi.remove(&(t1.clone(), t2.clone()));
                phi.insert(Constraint::Precious(Left(*t11.clone()), Left(*t21.clone())));
                phi.insert(Constraint::Precious(Left(*t12.clone()), Left(*t22.clone())));
            }
            // a < b -> c
            Constraint::Precious(Left(t @ MetaVar::Atom(_)), t2 @ Left(MetaVar::Arr(_,_)))
            | Constraint::Precious(Left(t @ MetaVar::Dom(_)), t2 @ Left(MetaVar::Arr(_,_)))
            | Constraint::Precious(Left(t @ MetaVar::Cod(_)), t2 @ Left(MetaVar::Arr(_,_))) => {
                psi.insert(t.clone());
                phi.insert(Constraint::Precious(
                    Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t.clone()))), Box::new(MetaVar::Cod(Box::new(t.clone()))))), 
                    t2.clone()
                ));
            }
            // b -> c < a
            Constraint::Precious(t1 @ Left(MetaVar::Arr(_, _)), Left(t @ MetaVar::Atom(_)))
            | Constraint::Precious(t1 @ Left(MetaVar::Arr(_, _)), Left(t @ MetaVar::Dom(_)))
            | Constraint::Precious(t1 @ Left(MetaVar::Arr(_, _)), Left(t @ MetaVar::Cod(_))) => {
                psi.insert(t.clone());
                phi.insert(Constraint::Precious(
                    t1.clone(),
                    Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t.clone()))), Box::new(MetaVar::Cod(Box::new(t.clone())))))
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

fn outer_coerce(t: CTyp, exp: &mut Exp, mut phi: CSet) -> (MetaVar, CSet) {
    let alpha = next_metavar();
    match t {
        Left(a) => {
            coerce(a.to_typ(), alpha.to_typ(), exp);
            phi.insert(Constraint::Precious(Left(alpha.clone()), Left(a)))
        },
        Right(a) => {
            coerce(a.to_typ(), alpha.to_typ(), exp);
            phi.insert(Constraint::Precious(Left(alpha.clone()), Right(a)))
        }
    };
    (alpha, phi)
}

pub fn cgen(exp: &mut Exp, env: &Env) -> (CSet, HIndex) {
    let (_, mut phi) = constraint_gen(exp, env);
    let mut psi = Default::default();
    constraint_rewrite(&mut phi, &mut psi);
    (phi, psi)
}