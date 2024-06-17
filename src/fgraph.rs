//Definition and some predicates on functionalization graph

use im::{HashMap, HashSet};

use crate::syntax::MetaVar;

pub type FGraph = HashMap<usize, HashSet<MetaVar>>;

pub fn acyclic(t1: &MetaVar, t2: &MetaVar, g: &FGraph) -> bool {
    g.iter().map(|(_, x)| {
        if x.contains(t1) {
            x.iter().map(
                |x| shareroot(x, &t2.root())
            ).fold(false, |acc, x| acc || x)
        } else {
            false
        }
    }).fold(false, |acc, x| acc || x)
}

pub fn is_fun(t: &MetaVar, g: &FGraph) -> Option<usize> {
    g.iter()
    .filter(
        |(_, x)| x.contains(t)
    ).map(|(i, _)| *i).next()
}

pub fn fgraph_union(g1: FGraph, g2: FGraph) -> FGraph {
    g1.union_with(g2, |v1, v2| v1.union(v2))
}

fn shareroot(t1: &MetaVar, t2: &MetaVar) -> bool {
    match t1 {
        MetaVar::Arr(t3, t4) => shareroot(&t3.root(), t2) || shareroot(&t4.root(), t2),
        MetaVar::Atom(_) => t1 == t2,
        MetaVar::Dom(t3)
        | MetaVar::Cod(t3) => shareroot(&t3.root(), t2)
    }
}