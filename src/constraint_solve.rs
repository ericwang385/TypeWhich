use either::Either::{Left, Right};
use super::syntax::{MetaVar, Typ};
use super::type_migrate::{Ans, CSet, Constraint, HIndex};
use super::type_migrate::Constraint::*;

fn conflict_solve(phi: &CSet, sigma: &mut Ans, psi: &HIndex) {
    let iterator = phi.clone();
    let orig_sigma = sigma.clone();
    for c1 in iterator.iter() {
        match c1 {
            // G < a => a = G | a = ?
            Constraint::Precious(Right(a), Left(t @ MetaVar::Atom(_)))
            | Constraint::Precious(Right(a), Left(t @ MetaVar::Dom(_)))
            | Constraint::Precious(Right(a), Left(t @ MetaVar::Cod(_))) => {
                match sigma.get(t) {
                    Some(b) => {
                        if a.to_typ() != b.clone() {
                            sigma.insert(t.clone(), Typ::Any);
                        }
                    }
                    None => {
                        sigma.insert(t.clone(), a.to_typ());
                    }
                }
            }
            // a < G1 & a < G2 => a = ?    
            Constraint::Precious(t1 @ Left(t @ MetaVar::Atom(_)), t2 @ Right(_))
            | Constraint::Precious(t1 @ Left(t @ MetaVar::Dom(_)), t2 @ Right(_))
            | Constraint::Precious(t1 @ Left(t @ MetaVar::Cod(_)), t2 @ Right(_)) => {
                for c2 in iterator.iter() {
                    match c2 {
                        Constraint::Precious(t3, t4) => {
                            if t1 == t3 && t2 != t4 && t4.is_right() {
                                sigma.insert(t.clone(), Typ::Any);
                            }
                        }
                        _ => {}
                    }
                    
                }
            }
            // b = ? & a < b => a = ?
            Constraint::Precious(Left(t1), Left(t2)) => {
                if sigma.get(t2) == Some(&Typ::Any){
                    sigma.insert(t1.clone(), Typ::Any);
                }
            }
            Constraint::Consistent(Left(t1), Left(t2))  => {
                if sigma.contains_key(t1) && sigma.contains_key(t2) && 
                    !consistent(sigma.get(t1).unwrap(), sigma.get(t2).unwrap()) {
                        sigma.insert(t1.clone(), Typ::Any);
                        sigma.insert(t2.clone(), Typ::Any);
                }
            }
            Constraint::Consistent(Left(t1), Right(t2))
            | Constraint::Consistent(Right(t2), Left(t1)) => {
                if sigma.contains_key(t1) && !consistent(sigma.get(t1).unwrap(), &t2.to_typ()) {
                    sigma.insert(t1.clone(), Typ::Any);
                }
            }
            _ => {}
        }
    }
    
    for t in psi.iter() {
        match sigma.get(t) {
            Some(Typ::Int) | Some(Typ::Bool) | Some(Typ::Float) | Some(Typ::Char) | Some(Typ::Any) => {
                sigma.insert(t.clone(), Typ::Any);
                sigma.insert(t.dom(), Typ::Any);
                sigma.insert(t.cod(), Typ::Any);
            }
            Some(Typ::Arr(t1, t2)) => {
                let dom = sigma.get(&t.dom()).unwrap();
                let cod = sigma.get(&t.cod()).unwrap();
                if dom.clone() != *t1.clone() {
                    sigma.insert(t.clone(), Typ::Arr(Box::new(Typ::Any), t2.clone()));
                    sigma.insert(t.dom(), Typ::Any);
                } else if cod.clone() != *t2.clone() {
                    sigma.insert(t.clone(), Typ::Arr(t1.clone(), Box::new(Typ::Any)));
                    sigma.insert(t.cod(), Typ::Any);
                }
            }
            None if sigma.contains_key(&t.dom()) && sigma.contains_key(&t.cod()) => {
                sigma.insert(t.clone(), Typ::Arr(Box::new(sigma.get(&t.dom()).unwrap().clone()),
                                Box::new(sigma.get(&t.cod()).unwrap().clone())));
            }
            _ => {}
        }
    }
    if !orig_sigma.difference(sigma.clone()).is_empty() {
        conflict_solve(phi, sigma, psi);
    }
}

fn consistent(t1: &Typ, t2: &Typ) -> bool {
    match (t1, t2) {
        (_, Typ::Any) | (Typ::Any, _) => true,
        (_, _) => {
            if t1 == t2 {true} else {false}
        }
    }
}

fn try_assign(phi: &mut CSet, sigma: &mut Ans) {
    let iterator = phi.clone();
    for c1 in iterator.iter() {
        match c1 {
            Precious(Left(t1 @ MetaVar::Atom(_)), Right(t2)) if !sigma.contains_key(t1) => {
                sigma.insert(t1.clone(), t2.to_typ());
            },
            Precious(Left(t1 @ MetaVar::Atom(_)), Left(t2 @ MetaVar::Atom(_))) 
            if !sigma.contains_key(t1) && sigma.contains_key(t2) => {
                let t = sigma.get(t2).unwrap();
                if t.is_ground() {
                    sigma.insert(t1.clone(), t.clone());
                }
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
