use either::Either::{Left, Right};
use crate::fgraph::{is_fun, FGraph};
use crate::syntax::Any;
use crate::type_migrate::ATyp;

use super::syntax::{MetaVar, Typ};
use super::type_migrate::{Ans, CSet, Constraint};
use super::type_migrate::Constraint::*;

fn conflict_solve(phi: &CSet, g: &FGraph, sigma: &mut Ans) {
    let iterator = phi.clone();
    let orig_sigma = sigma.clone();
    for c1 in iterator.iter() {
        match c1 {
            //CBase
            Precious(Left(t1), Right(t2)) => {
                match sigma.get(t1) {
                    Some(Right(t)) => {
                        if t != t2 {
                            sigma.insert(t1.clone(), Left(Any::Base));
                        }
                    }
                    _ => {}
                }
            }
            //CPrecious & CDyn
            Precious(Left(t1), Left(t2)) => {
                match (sigma.get(t1), sigma.get(t2)) {
                    (Some(Right(t3)), Some(Right(t4))) => {
                        if t3 != t4 {
                            sigma.insert(t1.clone(), Left(Any::Base));
                        }
                    }
                    (Some(Right(t3)), None) => {
                        sigma.insert(t2.clone(), Right(t3.clone()));
                    }
                    (_, Some(Left(_))) => {
                        sigma.insert(t1.clone(), Left(Any::Base));
                    }
                    _ => {}
                }
            }
            //CConsistentBase
            Consistent(Left(t1), Right(t2)) => {
                match sigma.get(t1) {
                    Some(t ) => {
                        if !consistent(t, &Right(t2.clone())) {
                            sigma.insert(t1.clone(), Left(Any::Base));
                        }
                    }
                    _ => {}
                }
            }
            //CConsistent2
            Consistent(Left(t1), Left(t2)) => {
                match (sigma.get(t1), sigma.get(t2)) {
                    (Some(t3), Some(t4)) => {
                        if !consistent(t3, t4) {
                            sigma.insert(t1.clone(), Left(Any::Base));
                            sigma.insert(t2.clone(), Left(Any::Base));
                        }
                    }
                    _ => {}
                }
            }
            
            _ => {}
        }
    }
    
    let diff = orig_sigma.difference(sigma.clone());

    if !diff.is_empty() {
        //CFunBase & CFunDyn
        for (i, t) in diff.iter() {
            match is_fun(i, g) {
                Some(_) => {
                    sigma.insert(i.dom(), Left(Any::Base));
                    sigma.insert(i.cod(), Left(Any::Base));
                    if t.is_right() {
                        sigma.insert(i.clone(), Left(Any::Base));
                    }
                }
                _ => {}
            }
        }
        conflict_solve(phi, g, sigma);
    }
}

fn consistent(t1: &ATyp, t2: &ATyp) -> bool {
    match (t1, t2) {
        (_, Left(_)) | (Left(_), _) => true,
        _ => {
            if t1 == t2 {true} else {false}
        }
    }
}

fn try_assign(phi: &CSet, sigma: &mut Ans) {
    let iterator = phi.clone();
    for c1 in iterator.iter() {
        match c1 {
            // a < G => a = G
            Precious(Left(t1), Right(t2)) 
            if !sigma.contains_key(t1) && !t1.is_arr() => {
                sigma.insert(t1.clone(), Right(t2.clone()));
                // return;
            },
            // a < b & b = G => a = G
            Precious(Left(t1), Left(t2)) 
            if !sigma.contains_key(t1) && sigma.contains_key(t2) && !t1.is_arr() && !t2.is_arr() => {
                match sigma.get(t2).unwrap() {
                    Right(t) => {
                        sigma.insert(t1.clone(), Right(t.clone()));
                        // return;
                    }
                    Left(_) => panic!("Should not have a < ? in try_assign"),
                };
            }
            _ => {}
        }
    }
}

pub fn csolve(phi: &CSet, g: &FGraph) -> Ans {
    let mut sigma : Ans = Default::default();
    loop {
        let orig_sigma = sigma.clone();
        let orig_phi = phi.clone();
        conflict_solve(phi, g, &mut sigma);
        try_assign(phi, &mut sigma);
        let sigma_diff = orig_sigma.difference(sigma.clone());
        let phi_diff = orig_phi.difference(phi.clone());
        if sigma_diff.is_empty() && phi_diff.is_empty() {
            return sigma;
        }
    }
}
