use crate::fgraph::{acyclic, fgraph_union, is_fun, FGraph};
use crate::parser::inc_metavar;
use std::boxed::Box;
use std::collections::BTreeSet;
use either::Either::{Left, Right};
use im::hashset;
use crate::syntax::{Exp, GroundTyp, MetaVar, Typ};
use super::type_migrate::{Env, CSet};
use super::syntax::Exp::*;
use super::type_migrate::Constraint::*;

fn next_metavar() -> MetaVar {
    MetaVar::Atom(inc_metavar())
}

fn constraint_gen(exp: &mut Exp, env: &Env) -> (MetaVar, CSet, FGraph) {
    match exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(lit) => {
            let t = lit.typ();
            let alpha = next_metavar();
            coerce(t.clone(), alpha.to_typ(), exp);
            let mut phi = BTreeSet::new();
            phi.insert(Precious(Left(alpha.clone()), Right(t.to_groundtyp().unwrap())));
            (alpha, phi, Default::default())
        },
        Var(x) => {
            let t = env.get(x)
                .unwrap_or_else(|| panic!("unbound identifier {}", x));
            let alpha = next_metavar();
            coerce(t.to_typ(), alpha.to_typ(), exp);
            let mut phi = BTreeSet::new();
            phi.insert(Precious(Left(alpha.clone()), Left(t.clone())));
            (alpha, phi, Default::default())
        },
        Fun(f, t, body) => {
            let mut env = env.clone();
            let t1 = t.to_metavar();
            let alpha = next_metavar();
            env.insert(f.clone(), t1.clone());
            let (t2, mut phi, mut g) = constraint_gen(body, &env);
            let funt = MetaVar::Arr(Box::new(t1.clone()), Box::new(t2.clone()));
            coerce(funt.to_typ(), alpha.to_typ(), exp);
            phi.insert(Precious(Left(alpha.dom()), Left(t1)));
            phi.insert(Precious(Left(alpha.cod()), Left(t2)));
            g.insert(g.len(), hashset![funt.clone(), alpha.clone()]);
            (alpha, phi, g)
        },
        App(e1, e2) => {
            let (t1, phi1, g1) = constraint_gen(e1, &env);
            let (t2, phi2, g2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(&phi2).cloned().collect::<CSet>();
            let mut g = fgraph_union(g1, g2);
            let alpha = next_metavar();
            let beta = next_metavar();
            let funt = MetaVar::Arr(Box::new(alpha.clone()), Box::new(beta.clone()));
            coerce(t1.to_typ(), funt.to_typ(), e1);
            coerce(t2.to_typ(), alpha.to_typ(), e2);
            phi.insert(Precious(Left(t1.dom()), Left(alpha.clone())));
            phi.insert(Precious(Left(t1.cod()), Left(beta.clone())));
            phi.insert(Precious(Left(t2.clone()), Left(alpha.clone())));
            g.insert(g.len(), hashset![funt.clone(), t1.clone()]);
            (beta, phi, g)
        },
        UnaryOp(op, e) => {
            let (t1, ret) = op.typ();
            let (alpha, mut phi, g) = constraint_gen(e, &env);
            let beta = next_metavar();
            coerce(alpha.to_typ(), t1.clone(), e);
            coerce(ret.clone(), beta.to_typ(), exp);
            phi.insert(Precious(Left(alpha), Right(t1.to_groundtyp().unwrap_or_else(|| panic!("UnaryOp with higher-order behavior")))));
            phi.insert(Precious(Left(beta.clone()), Right(ret.to_groundtyp().unwrap_or_else(|| panic!("UnaryOp with higher-order behavior")))));
            (beta, phi, g)
        },
        BinaryOp(op, e1, e2) => {
            let (t1, t2, ret) = op.typ();
            let (t3, phi1, g1) = constraint_gen(e1, &env);
            let (t4, phi2, g2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(&phi2).cloned().collect::<CSet>();
            let alpha = next_metavar();
            let g = fgraph_union(g1, g2);
            coerce(t3.to_typ(), t1.clone(), e1);
            coerce(t4.to_typ(), t2.clone(), e2);
            coerce(ret.clone(), alpha.to_typ(), exp);
            phi.insert(Precious(Left(t3), Right(t1.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior")))));
            phi.insert(Precious(Left(t4), Right(t2.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior")))));
            phi.insert(Precious(Left(alpha.clone()), Right(ret.to_groundtyp().unwrap_or_else(|| panic!("BinaryOp with higher-order behavior")))));
            (alpha, phi, g)
        },
        Let(x, e1, e2) => {
            let (t1, phi1, g1) = constraint_gen(e1, &env);
            let mut env = env.clone();
            env.insert(x.clone(), t1);
            let (t2, phi2, g2) = constraint_gen(e2, &env);
            let phi = phi1.union(&phi2).cloned().collect::<CSet>();
            (t2, phi, fgraph_union(g1, g2))
        },
        If(cond, e1, e2) => {
            let (t1, phi1, g1) = constraint_gen(cond, &env);
            let (t2, phi2, g2) = constraint_gen(e1, &env);
            let (t3, phi3, g3) = constraint_gen(e2, &env);
            let mut phi = phi1.union(&phi2).cloned().collect::<CSet>().union(&phi3).cloned().collect::<CSet>();
            let g = fgraph_union(g1, fgraph_union(g2, g3));
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

fn constraint_rewrite(phi: &mut CSet, g: &mut FGraph) {
    let iterator = phi.clone();
    for c1 in iterator.iter() {
        match c1 {
            Precious(Left(t1), Left(t2)) 
            if !t1.is_arr() && !t2.is_arr() => {
                // a < b & (a = fun | b = fun)
                //Fun FunctionalizeLR
                match (is_fun(t1, g), is_fun(t2, g)) {
                    (Some(_), Some(_)) 
                    if !phi.contains(&Precious(Left(t1.dom()), Left(t2.dom()))) => {
                        phi.insert(Precious(Left(t1.dom()), Left(t2.dom())));
                        phi.insert(Precious(Left(t1.cod()), Left(t2.cod())));
                    }
                    (None, Some(i))
                    if !acyclic(t2, t1, g) => {
                        let mut path = g.get(&i).unwrap().clone();
                        phi.insert(Precious(Left(t1.dom()), Left(t2.dom())));
                        phi.insert(Precious(Left(t1.cod()), Left(t2.cod())));
                        path.insert(t1.clone());
                        g.insert(i, path);
                    }
                    (Some(i), None)
                    if !acyclic(t1, t2, g) => {
                        let mut path = g.get(&i).unwrap().clone();
                        phi.insert(Precious(Left(t1.dom()), Left(t2.dom())));
                        phi.insert(Precious(Left(t1.cod()), Left(t2.cod())));
                        path.insert(t2.clone());
                        g.insert(i, path);
                    }
                    _ => {}
                }
                
                // a < b & a < c => b ~ c
                // Consistent
                for c2 in iterator.iter() {
                    match c2 {
                        Precious(Left(t3), Right(t4)) => {
                            if t1 == t3 {
                                phi.insert(Consistent(Left(t2.clone()), Right(t4.clone())));
                            } 
                        }
                        Precious(Left(t3), Left(t4)) 
                        if !t4.is_arr() && t2 != t4 => {
                            if t1 == t3 {
                                phi.insert(Consistent(Left(t2.clone()), Left(t4.clone())));
                            } 
                        }
                        _ => {}
                    }
                }
            }
            // Consistent(t1, t2) => {
            //     for c2 in iterator.iter() {
            //         match c2 {
            //             Consistent(t3, t4) 
            //             if (t2 == t3 && t1 != t4) => {
            //                 phi.insert(Consistent(t1.clone(), t4.clone()));
            //             }
            //             _ => {}
            //         }
            //     }
            // }
            _ => {}
        }
    }

    let phi_diff = phi.difference(&iterator).cloned().collect::<CSet>();
    
    if !phi_diff.is_empty() {
        constraint_rewrite(phi, g);
    }
}

fn coerce(t1: Typ, t2: Typ, exp: &mut Exp) {
    *exp = Exp::Coerce(t1, t2, Box::new(exp.take()))
}

pub fn cgen(exp: &mut Exp, env: &Env) -> (CSet, FGraph) {
    let (_, mut phi, mut g) = constraint_gen(exp, env);
    constraint_rewrite(&mut phi, &mut g);
    (phi, g)
}