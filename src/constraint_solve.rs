use either::Either::{Left, Right};
use im::HashMap;
use crate::fgraph::{is_fun, FGraph};
use crate::syntax::{Any, MetaVar};
use crate::type_migrate::ATyp;

use super::type_migrate::{Ans, CSet};
use super::type_migrate::Constraint::*;

fn conflict_solve(phi: &CSet, g: &FGraph, sigma: &mut Ans) -> bool {
    let iterator = phi.clone();
    let mut flag = false;
    for c1 in iterator.iter() {
        match c1 {
            //CBase
            Precious(Left(t1), Right(t2)) => {
                match sigma.get(t1) {
                    Some(Right(t)) => {
                        if t != t2 {
                            sigma.insert(t1.clone(), Left(Any::Base));
                            flag = true;
                        }
                    }
                    _ => {}
                }
            }
            //CPrecious & CDyn
            Precious(Left(t1), Left(t2)) => {
                match (sigma.get(t1), sigma.get(t2)) {
                    (Some(Right(t3)), Some(Right(t4)))
                    if t3 != t4 => {
                        sigma.insert(t1.clone(), Left(Any::Base));
                        flag = true;
                    }
                    (None, Some(Left(_)))
                    | (Some(Right(_)), Some(Left(_))) => {
                        sigma.insert(t1.clone(), Left(Any::Base));
                        flag = true;
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
                            flag = true;
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
                            flag = true;
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    if flag {
        //CFunBase & CFunDyn
        for (i, t) in sigma.clone().iter() {
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
        return true;
    }
    flag
}

fn consistent(t1: &ATyp, t2: &ATyp) -> bool {
    match (t1, t2) {
        (_, Left(_)) | (Left(_), _) => true,
        _ => {
            if t1 == t2 {true} else {false}
        }
    }
}

fn try_assign(phi: &CSet, sigma: &mut Ans) -> bool {
    let iterator = phi.clone();
    let orig = sigma.clone();
    let mut flag = false;
    for c1 in iterator.iter() {
        match c1 {
            // a < G => a = G
            Precious(Left(t1), Right(t2)) 
            if !orig.contains_key(t1) && !t1.is_arr() => {
                sigma.insert(t1.clone(), Right(t2.clone()));
                flag = true;
            },
            // a < b & b = G => a = G
            Precious(Left(t1), Left(t2)) 
            if !orig.contains_key(t1) && orig.contains_key(t2) && !t1.is_arr() && !t2.is_arr() => {
                match sigma.get(t2).unwrap() {
                    Right(t) => {
                        sigma.insert(t1.clone(), Right(t.clone()));
                        flag = true;
                    }
                    Left(_) => panic!("Should not have a < ? in try_assign"),
                };
            }
            _ => {}
        }
    }
    flag
}

// fn commit_assign(phi: &CSet, sigma: &mut Ans) -> bool {
//     let mut counter = 1000;
//     let mut key = (MetaVar::Atom(0), MetaVar::Atom(0));
//     for c1 in phi.iter() {
//         match c1 {
//             Precious(Left(t1), Left(t2)) 
//             if !sigma.contains_key(t2) && 
//             sigma.get(t1).is_some_and(|x| x.is_right()) => {
//                 let mut inner_counter = 0;
//                 for c2 in phi.iter() {
//                     match c2 {
//                         Precious(Left(t3), Left(t4))
//                         if t4 == t2 && !sigma.contains_key(t3) => {
//                             inner_counter += 1;
//                         }
//                         _ => {}
//                     }
//                 }
//                 if inner_counter < counter {
//                     counter = inner_counter;
//                     key = (t2.clone(), t1.clone());
//                 }
//             }
//             _ => {}
//         }
//     }
//     if counter != 1000 {
//         sigma.insert(key.0, sigma.get(&key.1).unwrap().clone());
//         true
//     } else {
//         false
//     }
// }

fn commit_assign(phi: &CSet, sigma: &mut Ans) -> bool {
    for c1 in phi.iter() {
        match c1 {
            Precious(Left(t1), Left(t2)) 
            if !sigma.contains_key(t2) && 
            sigma.get(t1).is_some_and(|x| x.is_right()) => {
                sigma.insert(t2.clone(), sigma.get(t1).unwrap().clone());
                return true;
            }
            _ => {}
        }
    }
    false
}

pub fn csolve(phi: &CSet, g: &FGraph) -> Ans {
    let mut sigma: Ans = Default::default();
    loop{
        let b1 = try_assign(phi, &mut sigma);
        let b2 = conflict_solve(phi, g, &mut sigma);
        if !(b1 || b2) {
            let b3 = commit_assign(phi, &mut sigma);
            conflict_solve(phi, g, &mut sigma);
            if !b3 {
                return sigma;
            }
        }
    }
}

// fn _csolve(phi: &CSet, g: &FGraph, sigma: &mut Ans) {
//     let b1 = conflict_solve(phi, g, sigma);
//     let b2 = try_assign(phi, sigma);
//     if !(b1 || b2) {
//         let b3 = commit_assign(phi, sigma);
//         if b3 {
//             _csolve(phi, g, sigma)
//         } else {
//             return;
//         }
//     } else {
//         _csolve(phi, g, sigma)
//     }
// }

// pub fn csolve(phi: &CSet, g: &FGraph) -> Ans {
//     let mut sigma : Ans = Default::default();
//     _csolve(phi, g, &mut sigma);
//     sigma
// }
