use crate::parser::{curr_metavar, inc_metavar};
use crate::syntax::{GroundTyp, MetaVar};

use super::syntax::{Exp, Typ};
use super::syntax::Exp::*;
use im::{HashMap, HashSet};
use std::boxed::Box;
use either::Either::{self, Left, Right};

type Env = HashMap<String, MetaVar>;
type CTyp = Either<MetaVar, GroundTyp>;
type Hom = HashSet<MetaVar>;
type Ans = HashMap<MetaVar, Typ>;
type Constraint = HashSet<(CTyp, CTyp)>;

fn next_metavar() -> MetaVar {
    MetaVar::Atom(inc_metavar())
}

// Entry Point
pub fn type_infer(mut exp: Exp, env: &Env) -> Result<Exp, String> {
    let (_, mut phi) = constraint_gen(&mut exp, env);
    let mut sigma = Default::default();
    let mut psi = Default::default();
    constraint_rewrite(&mut phi, &mut psi);
    constraint_solve(&mut phi, &mut sigma, &psi);
    fun_assign(&mut sigma, &psi);
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
            
            (Left(t11), Left(t22)) if !t11.is_arr() && !t22.is_arr() => {
                // a < b & (a = fun | b = fun)
                match (t11, t22) {
                    (MetaVar::Atom(_), _) | (_, MetaVar::Atom(_)) 
                    if psi.contains(t11) || psi.contains(t22) => {
                        phi.insert((Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t11.clone()))), Box::new(MetaVar::Cod(Box::new(t11.clone()))))), 
                                    Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t22.clone()))), Box::new(MetaVar::Cod(Box::new(t22.clone())))))));
                        psi.insert(t11.clone());
                        psi.insert(t22.clone());
                    }
                    (MetaVar::Dom(a), MetaVar::Dom(b)) | (MetaVar::Cod(a), MetaVar::Cod(b))
                    | (MetaVar::Dom(a), MetaVar::Cod(b)) | (MetaVar::Cod(a), MetaVar::Dom(b))
                    if (psi.contains(t11) || psi.contains(t22)) && !phi.contains(&(Left(*a.clone()), Left(*b.clone()))) => {
                        phi.insert((Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t11.clone()))), Box::new(MetaVar::Cod(Box::new(t11.clone()))))), 
                                    Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t22.clone()))), Box::new(MetaVar::Cod(Box::new(t22.clone())))))));
                        psi.insert(t11.clone());
                        psi.insert(t22.clone());
                    }
                    _ => {}
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
                // phi.remove(&(t1.clone(), t2.clone()));
                phi.insert((Left(*t11.clone()), Left(*t21.clone())));
                phi.insert((Left(*t12.clone()), Left(*t22.clone())));
            }
            // a < b -> c
            (Left(t @ MetaVar::Atom(_)), Left(MetaVar::Arr(_,_)))
            | (Left(t @ MetaVar::Dom(_)), Left(MetaVar::Arr(_,_)))
            | (Left(t @ MetaVar::Cod(_)), Left(MetaVar::Arr(_,_))) => {
                psi.insert(t.clone());
                phi.insert((Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t.clone()))), Box::new(MetaVar::Cod(Box::new(t.clone()))))), 
                            t2.clone()));
            }
            // b -> c < a
            (Left(MetaVar::Arr(_, _)), Left(t @ MetaVar::Atom(_)))
            | (Left(MetaVar::Arr(_, _)), Left(t @ MetaVar::Dom(_)))
            | (Left(MetaVar::Arr(_, _)), Left(t @ MetaVar::Cod(_))) => {
                psi.insert(t.clone());
                phi.insert((t1.clone(),
                            Left(MetaVar::Arr(Box::new(MetaVar::Dom(Box::new(t.clone()))), Box::new(MetaVar::Cod(Box::new(t.clone())))))));
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

fn constraint_solve(phi: &mut Constraint, sigma: &mut Ans, psi: &Hom) {
    loop {
        if sigma.len() as u32 == curr_metavar() {
            return;
        }
        let orig_sigma = sigma.clone();
        let orig_phi = phi.clone();
        try_assign(phi, sigma);
        conflict_solve(phi, sigma, psi);
        if orig_sigma.difference(sigma.clone()).is_empty() && orig_phi.difference(phi.clone()).is_empty() {
            return;
        }
    }
}

fn fun_assign(sigma: &mut Ans, psi: &Hom) {
    for t in psi {
        if sigma.get(t) == None {
            sigma.insert(t.clone(), Typ::Arr(Box::new(sigma.get(&t.dom()).unwrap_or(&Typ::Any).clone()),
                                Box::new(sigma.get(&t.cod()).unwrap_or(&Typ::Any).clone())));
        }
    }
}

fn conflict_solve(phi: &Constraint, sigma: &mut Ans, psi: &Hom) {
    let iterator = phi.clone();
    let orig_sigma = sigma.clone();
    for (t1, t2) in iterator.iter() {
        match (t1, t2) {
            // G < a => a = G | a = ?
            (Right(a), Left(t @ MetaVar::Atom(_)))
            | (Right(a), Left(t @ MetaVar::Dom(_)))
            | (Right(a), Left(t @ MetaVar::Cod(_))) => {
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
            (Left(t @ MetaVar::Atom(_)), Right(_))
            | (Left(t @ MetaVar::Dom(_)), Right(_))
            | (Left(t @ MetaVar::Cod(_)), Right(_)) => {
                for (t3, t4) in iterator.iter() {
                    if t1 == t3 && t2 != t4 && t4.is_right() {
                        sigma.insert(t.clone(), Typ::Any);
                    }
                }
            }
            // b = ? & a < b => a = ?
            (Left(t1), Left(t2)) => {
                if sigma.get(t2) == Some(&Typ::Any){
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

fn try_assign(phi: &mut Constraint, sigma: &mut Ans) {
    for (k, v) in sigma.iter() {
        match v.to_groundtyp() {
            Some(t) => substitute(k.clone(), t, phi),
            None => {}
        }
    }
    let iterator = phi.clone();
    for (t1, t2) in iterator.iter() {
        match (t1, t2) {
            (Left(a), Right(b)) if sigma.get(a) == None => {
                sigma.insert(a.clone(), b.to_typ());
            }
            _ => {}
        }
    }
}

fn substitute(i: MetaVar, t: GroundTyp, phi: &mut Constraint) {
    let iterator = phi.clone();
    for (t1, t2) in iterator.iter() {
        if t1 == &Left(i.clone()) {
            phi.remove(&(t1.clone(), t2.clone()));
            phi.insert((Right(t.clone()), t2.clone()));
        } else if t2 == &Left(i.clone()) {
            phi.remove(&(t1.clone(), t2.clone()));
            phi.insert((t1.clone(), Right(t.clone())));
        }
    }
}

fn annotate_typ(sigma: &Ans, t: &mut Typ, psi: &Hom) {
    match t {
        Typ::Metavar(i) => {
            *t = match sigma.get(&MetaVar::Atom(*i)) {
                Some(s) => match s {
                    Typ::Metavar(_) => panic!("Type variable in answer set at {}", i),
                    _ => s.clone(),
                },
                None => Typ::Any,
            }
        }
        Typ::Arr(t1, t2) | Typ::Pair(t1, t2) => {
            annotate_typ(sigma, t1, psi);
            annotate_typ(sigma, t2, psi);
        }
        Typ::List(t) | Typ::Box(t) | Typ::Vect(t) => {
            annotate_typ(sigma, t, psi);
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
    use crate::syntax::Exp;
    use crate::parser::parse;
    use crate::type_migrate::{annotate, constraint_gen, constraint_rewrite, constraint_solve, fun_assign};

    fn test_migrate(orig: &str) -> Exp {
        let mut exp = parse(orig).unwrap();
        exp.fresh_types();
        let (_, mut phi) = constraint_gen(&mut exp, &Default::default());
        // let n = curr_metavar();
        let mut sigma = Default::default();
        let mut psi = Default::default();
        // println!("Before rewrite: {:?}", phi);
        // println!("Expression: {:?}", exp);
        constraint_rewrite(&mut phi, &mut psi);
        // println!("After rewrite: {:?}", phi);
        constraint_solve(&mut phi, &mut sigma, &psi);
        fun_assign(&mut sigma, &psi);
        // println!("Constraint:\n{:?}", phi);
        println!("Answer Set:\n{:?}", sigma);
        println!("Higher-Order Set:\n{:?}", psi);
        println!("Before Annotation:\n{:?}\n", exp);
        annotate(&sigma, &mut exp, &psi);
        println!("After Annotation \n {:?} \n", exp);
        println!("After Annotation Pretty:\n{}\n", exp);
        exp
    }

    #[test]
    fn bool_add() {
        test_migrate("true + false");
    }

    #[test]
    fn simple_arith() {
        test_migrate("(fun x . x + 1) 10");
    }

    #[test]
    fn bool_app() {
        test_migrate("(fun x . x + 1) true");
    }

    #[test]
    fn fun_app() {
        test_migrate("(fun f . f true) (fun x . x + 100)");
    }

    #[test]
    fn y_combinator() {
        test_migrate("(fun x . x x) 5");
    }

    #[test]
    fn rank2_poly() {
        test_migrate("(fun i.(fun a. (i true)) (i 5) ) (fun x.x)");
    }

    #[test]
    fn unreachable() {
        test_migrate("(fun b . 
            b (fun c . 
                 ((fun x . x x) 5) 5) 
              (fun d . 0)) 
            (fun t . fun f . f)
          ");
    }
}
