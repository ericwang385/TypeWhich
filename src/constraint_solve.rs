use either::Either::{Left, Right};
use crate::syntax::Any;
use crate::type_migrate::ATyp;

use super::syntax::{MetaVar, Typ};
use super::type_migrate::{Ans, CSet, Constraint, HIndex};
use super::type_migrate::Constraint::*;

fn conflict_solve(phi: &CSet, sigma: &mut Ans, psi: &HIndex) {
    let iterator = phi.clone();
    let orig_sigma = sigma.clone();
    for c1 in iterator.iter() {
        match c1 {
            // G < a => a = G | a = ?
            Precious(Right(_), Left(t )) 
            if !t.is_arr() => {
                panic!("Should not generate G < a in conflict solve");
            }
            // a < G1 & a < G2 => a = ?    
            Precious(t1 @ Left(t ), t2 @ Right(_))
            if !t.is_arr() => {
                for c2 in iterator.iter() {
                    match c2 {
                        Precious(t3, t4) => {
                            if t1 == t3 && t2 != t4 && t4.is_right() {
                                sigma.insert(t.clone(), Left(Any::Base));
                            }
                        }
                        _ => {}
                    }
                }
            }
            // b = ? & a < b => a = ?
            // a = G & a < b => b = G
            Precious(Left(t1), Left(t2)) => {
                match (sigma.get(t1), sigma.get(t2)) {
                    (_, Some(Left(Any::Base))) => {
                        sigma.insert(t1.clone(), Left(Any::Base));
                    }
                    (Some(Right(t)), None) => {
                        sigma.insert(t2.clone(), Right(t.clone()));
                    }
                    _ => {}
                };
            }
            // a = G1 & b = G2 & a ~ b => a = b = ? 
            Consistent(Left(t1), Left(t2)) 
            if sigma.contains_key(t1) && sigma.contains_key(t2) && 
            !consistent(sigma.get(t1).unwrap(), sigma.get(t2).unwrap()) => {
                sigma.insert(t1.clone(), Left(Any::Base));
                sigma.insert(t2.clone(), Left(Any::Base));
            }
            // a = G1 & a ~ G2 => a = ?
            Consistent(Left(t1), Right(t2))
            | Consistent(Right(t2), Left(t1)) 
            if sigma.contains_key(t1) && !consistent(sigma.get(t1).unwrap(), &Right(t2.clone())) => {
                sigma.insert(t1.clone(), Left(Any::Base));
            }
            _ => {}
        }
    }
    
    for t in psi.iter() {
        match sigma.get(t) {
            Some(_) => {
                sigma.insert(t.clone(), Left(Any::Base));
                sigma.insert(t.dom(), Left(Any::Base));
                sigma.insert(t.cod(), Left(Any::Base));
            }
            _ => {}
        }
    }
    
    if !orig_sigma.difference(sigma.clone()).is_empty() {
        conflict_solve(phi, sigma, psi);
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

fn try_assign(phi: &mut CSet, sigma: &mut Ans) {
    let iterator = phi.clone();
    for c1 in iterator.iter() {
        match c1 {
            // a < G => a = G
            Precious(Left(t1), Right(t2)) 
            if !sigma.contains_key(t1) && !t1.is_arr() => {
                sigma.insert(t1.clone(), Right(t2.clone()));
            },
            // a < b & b = G => a = G
            Precious(Left(t1), Left(t2)) 
            if !sigma.contains_key(t1) && sigma.contains_key(t2) && !t1.is_arr() && !t2.is_arr() => {
                match sigma.get(t2).unwrap() {
                    Right(t) => sigma.insert(t1.clone(), Right(t.clone())),
                    Left(_) => panic!("Should not have a < ? in try_assign"),
                };
            }
            _ => {}
        }
    }
}

pub fn csolve(phi: &mut CSet, psi: &HIndex) -> Ans {
    let mut sigma : Ans = Default::default();
    loop {
        let orig_sigma = sigma.clone();
        let orig_phi = phi.clone();
        conflict_solve(phi, &mut sigma, psi);
        try_assign(phi, &mut sigma);
        let sigma_diff = orig_sigma.difference(sigma.clone());
        let phi_diff = orig_phi.difference(phi.clone());
        if sigma_diff.is_empty() && phi_diff.is_empty() {
            return sigma;
        }
    }
}
