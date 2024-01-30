use crate::parser::{next_metavar, curr_metavar};

use super::syntax::{Exp, Typ};
use super::syntax::Exp::*;
use im::{HashSet, HashMap, hashset, iter};
use std::boxed::Box;

type Env = HashMap<String, Typ>;
type Constraint = HashSet<(Typ, Typ)>;


pub fn type_infer(mut exp: Exp, env: &Env) -> Result<Exp, String> {
    let (t, mut cst) = constraint_gen(&mut exp, env);
    let n = curr_metavar();
    // let mut ans = HashMap::new();
    let mut ans = (0..n).map(|x| (x, Typ::Metavar(x))).collect::<HashMap<u32, Typ>>();
    constraint_rewrite(&mut cst, &mut ans);
    for i in cst.iter() {
        println!("Constraints:\n{:?}\n", i);
    }
    println!("After Unification:\n{:?}\n", ans);
    println!("Before Annotation:\n{:?}\n", exp);
    annotate(&ans, &mut exp);
    println!("After Annotation:\n{:?}\n", exp);
    println!("After Annotation Pretty:\n{}\n", exp);
    Ok(exp)
}

pub fn type_check(exp: &Exp) -> Result<Typ, String> {
    todo!()
}

fn constraint_gen(exp: &mut Exp, env: &Env) -> (Typ, Constraint) {
    match exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(lit) => {
            let t1 = lit.typ();
            outer_coerce(t1, exp, Default::default())
        },
        Var(x) => {
            let t1 = env.get(x)
                .unwrap_or_else(|| panic!("unbound identifier {}", x))
                .clone();
            // (t1, Default::default())
            outer_coerce(t1, exp, Default::default())
        },
        Fun(f, t1, body) => {
            let mut env = env.clone();
            env.insert(f.clone(), t1.clone());
            let (t2, phi) = constraint_gen(body, &env);
            let funt = Typ::Arr(Box::new(t1.clone()), Box::new(t2));
            outer_coerce(funt, exp, phi)
        },
        App(e1, e2) => {
            let (t1, phi1) = constraint_gen(e1, &env);
            let (t2, phi2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2);
            let alpha = next_metavar();
            let beta = next_metavar();
            let funt = Typ::Arr(Box::new(alpha.clone()), Box::new(beta.clone()));
            coerce(t1.clone(), funt.clone(), e1);
            coerce(t2.clone(), alpha.clone(), e2);
            phi.insert((t1, funt));
            phi.insert((alpha, t2));
            (beta, phi)
        },
        UnaryOp(op, e) => {
            let (t1, ret) = op.typ();
            let (t2, mut phi) = constraint_gen(e, &env);
            coerce(t2.clone(), t1.clone(), e);
            phi.insert((t1, t2));
            outer_coerce(ret, e, phi)
        },
        BinaryOp(op, e1, e2) => {
            let (t1, t2, ret) = op.typ();
            let (t3, phi1) = constraint_gen(e1, &env);
            let (t4, phi2) = constraint_gen(e2, &env);
            let mut phi = phi1.union(phi2);
            coerce(t3.clone(), t1.clone(), e1);
            // println!("In BinOp: {:?} Constraint ({},{})", e1, t1, t3);
            coerce(t4.clone(), t2.clone(), e2);
            phi.insert((t3, t1));
            phi.insert((t4, t2));
            outer_coerce(ret, exp, phi)
        },
        Let(x, e1, e2) => {
            let (t1, phi1) = constraint_gen(e1, &env);
            let mut env = env.clone();
            env.insert(x.clone(), t1);
            let (t2, phi2) = constraint_gen(e2, &env);
            (t2, phi1.union(phi2))
        }
        _ => todo!()
    }
}

fn outer_coerce(t: Typ, exp: &mut Exp, mut cst: Constraint) -> (Typ, Constraint) {
    let alpha = next_metavar();
    coerce(t.clone(), alpha.clone(), exp);
    cst.insert((alpha.clone(), t));
    (alpha, cst)
}

fn coerce(t1: Typ, t2: Typ, exp: &mut Exp) {
    *exp = Exp::Coerce(t1, t2, Box::new(exp.take()))
}

fn constraint_rewrite(cst: &mut Constraint, ans: &mut HashMap<u32, Typ>) {
    let iterator = cst.clone();
    //SYM
    for (t1, t2) in iterator.iter() {
        if t1.not_any() && t2.not_any() {
            let orig = cst.clone();
            cst.insert((t2.clone(), t1.clone()));
            constraint_dif(orig, cst, ans);
        }
    }
    
    for (t1, t2) in iterator.iter() {
        match (t1, t2) {
            //EXP
            (Typ::Arr(t11, t12), Typ::Arr(t21, t22)) => {
                if t11.not_any() && t12.not_any() && t21.not_any() && t22.not_any() {
                    let orig = cst.clone();
                    cst.insert((*t11.clone(), *t21.clone()));
                    cst.insert((*t12.clone(), *t22.clone()));
                    constraint_dif(orig, cst, ans);
                }
            }
            //TRANS-VAR
            (Typ::Metavar(_), Typ::Metavar(_)) => {
                let orig = cst.clone();
                for (t3, t4) in iterator.iter() {
                    if t2 == t3 && t2 != t4 && t4.is_metavar() {
                        let orig = cst.clone();
                        cst.insert((t1.clone(), t4.clone()));
                    }
                }
                constraint_dif(orig, cst, ans);
            }
            //TRANS-FUN
            (Typ::Metavar(_), Typ::Arr(t21, t22)) => {
                if t21.is_metavar() && t22.is_metavar() {
                    for (t3, t4) in iterator.iter() {
                        if t1 == t3 && t2 != t4 {
                            match t4 {
                                Typ::Arr(t41, t42) => {
                                    if t41.is_metavar() && t42.is_metavar() {
                                        let orig = cst.clone();
                                        cst.insert((t2.clone(), t4.clone()));
                                        constraint_dif(orig, cst, ans);
                                    }
                                }
                                _ => return,
                            };
                        }
                    }
                }
            }
            _ => {}
        }
    }

    //SUBST
    for (t1, t2) in iterator.iter() {
        match (t1, t2) {
            (Typ::Metavar(i), _) => {
                if t2.not_any() {
                    match ans.get(i) {
                        Some(t3) => ans.insert(*i, union_typ(t3, &check_ans(t2, &ans), &ans)),
                        None => ans.insert(*i, check_ans(t2, &ans)),
                    };
                }
            }
            _ => {}
        }
    }
}

fn ans_dif(orig: HashMap<u32, Typ>, cst: &mut Constraint, ans: &mut HashMap<u32, Typ>) {
    if !orig.symmetric_difference(ans.clone()).is_empty() {
        constraint_rewrite(cst, ans);
    }
}

fn constraint_dif(orig: Constraint, cst: &mut Constraint, ans: &mut HashMap<u32, Typ>) {
    if !orig.symmetric_difference(cst.clone()).is_empty() {
        constraint_rewrite(cst, ans);
    }
}

fn check_ans(t: &Typ, ans: &HashMap<u32, Typ>) -> Typ {
    match t {
        Typ::Metavar(i) => match ans.get(i) {
            Some(t) => t.clone(),
            None => Typ::Metavar(*i)
        },
        _ => t.clone()
    }
}

fn union_typ(t1: &Typ, t2: &Typ, ans: &HashMap<u32, Typ>) -> Typ {
    match (t1, t2) {
        (Typ::Metavar(i), Typ::Metavar(j)) => {if i<j {Typ::Metavar(*i)} else {Typ::Metavar(*j)}}
        (Typ::Any, _) | (_, Typ::Any) => Typ::Any,
        (Typ::Metavar(_), t) | (t, Typ::Metavar(_)) => t.clone(),
        (Typ::Any, t) | (t, Typ::Any) => t.clone(),
        (Typ::Arr(t11, t12), Typ::Arr(t21, t22)) =>
            Typ::Arr(
                Box::new(union_typ(t11, t21, &ans)), 
                Box::new(union_typ(t12, t22, &ans))
            ),
        (t3, t4) => {
            if t3==t4 {t3.clone()} else {Typ::Any}
        }
    }
}

fn annotate_typ(ans: &HashMap<u32, Typ>, t: &mut Typ) {
    match t {
        Typ::Metavar(i) => {
            match ans.get(i) {
                Some(s) => *t = s.clone(),
                None => ()
            }
        }
        Typ::Arr(t1, t2) | Typ::Pair(t1, t2) => {
            annotate_typ(ans, t1);
            annotate_typ(ans, t2);
        }
        Typ::List(t) | Typ::Box(t) | Typ::Vect(t) => {
            annotate_typ(ans, t);
        }
        Typ::Unit | Typ::Int | Typ::Float | Typ::Bool | Typ::Str | Typ::Char | Typ::Any => (),
    }
}

fn annotate(ans: &HashMap<u32, Typ>, exp: &mut Exp) {
    match &mut *exp {
        PrimCoerce(..) => panic!("PrimCoerce should not appear in source"),
        Lit(..) | Var(..) => {}
        Exp::Fun(_, t, e) | Exp::Fix(_, t, e) | Exp::Ann(e, t) => {
            annotate_typ(ans, t);
            annotate(ans, e);
        }
        Exp::Coerce(t1, t2, e) => {
            annotate(ans, e);
            annotate_typ(ans, t1);
            annotate_typ(ans, t2);
            if t1 == t2 {
                *exp = e.take();
            }
        }
        Exp::App(e1, e2) 
        | Exp::Let(_, e1, e2)
        | Exp::BinaryOp(_, e1, e2)
        | Exp::AddOverload(e1, e2) => {
            annotate(ans, e1);
            annotate(ans, e2);
        }
        _ => {}
    }
}

#[cfg(test)]
mod test {
    use crate::{parser::parse, syntax::{Exp, Typ}, type_migrate::annotate};

    use super::type_infer;

    fn test_migrate(mut orig: &str) -> Exp {
        let mut parsed = parse(orig).unwrap();
        parsed.fresh_types();
        let e = type_infer(parsed, &Default::default()).unwrap();
        e
    }

    #[test]
    fn int_lit() {
        test_migrate("1");
    }

    #[test]
    fn int_add() {
        test_migrate("1 + 1");
    }

    #[test]
    fn int_add_bool() {
        test_migrate("1 + true");
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
    fn fun_as_num() {
        test_migrate("let f = fun x . x + 1 in
        f true");
    }
}