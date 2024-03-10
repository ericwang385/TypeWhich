use super::syntax::*;

// it does end up sometimes being useful to print metavariables in programs,
// though usually it's just noise
const PRINT_METAVARS: bool = false;
const PRINT_COERCIONS: bool = false;

// Copied from jankscripten
pub trait Pretty {
    fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        D::Doc: Clone,
        A: Clone;
}

pub const DEFAULT_WIDTH: usize = 72;

// Copied from jankscripten
#[macro_export]
macro_rules! impl_Display_Pretty {
    ($T:ty) => {
        impl std::fmt::Display for $T {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let pp = pretty::BoxAllocator;
                let doc = self.pretty::<_, ()>(&pp);
                doc.1.render_fmt($crate::pretty::DEFAULT_WIDTH, f)
            }
        }
    };
}

////////////////////////////////////////////////////////////////////////////////

fn skip_coercion(e: &Exp) -> &Exp {
    match e {
        Exp::Coerce(_, _, e) => e,
        _ => e,
    }
}

fn parens_if<'b, D, A, T>(pp: &'b D, d: &'b T, b: bool) -> pretty::DocBuilder<'b, D, A>
where
    T: Pretty,
    D: pretty::DocAllocator<'b, A>,
    A: std::clone::Clone,
    <D as pretty::DocAllocator<'b, A>>::Doc: std::clone::Clone,
{
    if b {
        pp.concat(vec![pp.text("("), d.pretty(pp), pp.text(")")])
    } else {
        d.pretty(pp)
    }
}

impl Pretty for Typ {
    fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        A: std::clone::Clone,
        <D as pretty::DocAllocator<'b, A>>::Doc: std::clone::Clone,
    {
        match self {
            Typ::Unit => pp.text("unit"),
            Typ::Int => pp.text("int"),
            Typ::Float => pp.text("float"),
            Typ::Bool => pp.text("bool"),
            Typ::Str => pp.text("str"),
            Typ::Char => pp.text("char"),
            Typ::Arr(t1, t2) => pp.concat(vec![
                parens_if(pp, &**t1, t1.is_arr()),
                pp.space(),
                pp.text("->"),
                pp.space(),
                t2.pretty(pp),
            ]),
            Typ::List(t) => pp.concat(vec![
                pp.text("list"),
                pp.space(),
                parens_if(pp, &**t, t.is_atom()),
            ]),
            Typ::Pair(t1, t2) => pp
                .concat(vec![
                    parens_if(pp, &**t1, t1.is_atom()),
                    pp.text(","),
                    pp.space(),
                    parens_if(pp, &**t2, t2.is_atom()),
                ])
                .parens(),
            Typ::Box(t) => pp.concat(vec![
                pp.text("box"),
                pp.space(),
                parens_if(pp, &**t, t.is_atom()),
            ]),
            Typ::Vect(t) => pp.concat(vec![
                pp.text("vect"),
                pp.space(),
                parens_if(pp, &**t, t.is_atom()),
            ]),
            Typ::Any => pp.text("any"),
            Typ::Metavar(i) => pp.text(alphabet(*i)),
        }
    }
}

/// produces lowercase latin letters in alphabetic order, then produces ⦉i⦊
/// where i begins at 1 after the latin characters
fn alphabet(i: u32) -> String {
    let num_latin_chars = 26;
    if i <= num_latin_chars {
        std::char::from_u32('a' as u32 + i).unwrap().to_string()
    } else {
        format!("⦉{}⦊", i - num_latin_chars)
    }
}

impl Pretty for Lit {
    fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        A: std::clone::Clone,
        <D as pretty::DocAllocator<'b, A>>::Doc: std::clone::Clone,
    {
        match self {
            Lit::Int(n) => pp.as_string(n),
            Lit::Float(f) => pp.as_string(f),
            Lit::Bool(true) => pp.text("true"),
            Lit::Bool(false) => pp.text("false"),
            Lit::Str(s) => pp.text("\"").append(pp.text(s)).append(pp.text("\"")),
            Lit::Char(c) => pp.as_string(c).single_quotes(),
            Lit::Unit => pp.text("()"),
        }
    }
}

impl Pretty for Toplevel {
    fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        A: std::clone::Clone,
        <D as pretty::DocAllocator<'b, A>>::Doc: std::clone::Clone,
    {
        match self {
            Toplevel::Define(x, t, e) => pp
                .concat(vec![
                    pp.text("define"),
                    pp.space(),
                    pp.text(x),
                    pp.space(),
                    pp.text(":"),
                    pp.space(),
                    t.pretty(pp),
                    pp.softline(),
                    e.pretty(pp),
                ])
                .parens(),
            Toplevel::Exp(e) => e.pretty(pp),
        }
    }
}

impl Pretty for Exp {
    fn pretty<'b, D, A>(&'b self, pp: &'b D) -> pretty::DocBuilder<'b, D, A>
    where
        D: pretty::DocAllocator<'b, A>,
        A: std::clone::Clone,
        <D as pretty::DocAllocator<'b, A>>::Doc: std::clone::Clone,
    {
        match self {
            Exp::Lit(l) => l.pretty(pp),
            Exp::Var(x) => pp.text(x),
            Exp::Let(x, e1, e2) => pp.concat(vec![
                pp.text("let"),
                pp.space(),
                pp.text(x),
                pp.space(),
                pp.text("="),
                pp.space(),
                e1.pretty(pp).nest(2),
                pp.space(),
                pp.text("in"),
                pp.line(),
                e2.pretty(pp),
            ]),
            Exp::LetRec(bindings, e) => pp.concat(vec![
                pp.text("let rec"),
                pp.space(),
                pp.intersperse(
                    bindings.iter().map(|(xi, ti, ei)| {
                        pp.intersperse(
                            vec![
                                pp.text(xi),
                                pp.text(":"),
                                ti.pretty(pp),
                                pp.text("="),
                                ei.pretty(pp).nest(2),
                            ],
                            pp.space(),
                        )
                    }),
                    pp.concat(vec![pp.line(), pp.text("and"), pp.space()]),
                ),
                pp.space(),
                pp.text("in"),
                pp.line(),
                e.pretty(pp),
            ]),
            Exp::Ann(e, typ) => pp.intersperse(
                vec![
                    e.pretty(pp),
                    pp.space(),
                    pp.text(":"),
                    pp.space(),
                    typ.pretty(pp),
                ],
                pp.space(),
            ),
            Exp::Fun(x, Typ::Metavar(_), e) if !PRINT_METAVARS => pp
                .concat(vec![
                    pp.text("fun"),
                    pp.space(),
                    pp.text(x),
                    pp.space(),
                    pp.text("."),
                    pp.softline(),
                    e.pretty(pp).nest(2),
                ])
                .group(),
            Exp::Fun(x, t, e) => pp.concat(vec![
                pp.text("fun"),
                pp.space(),
                pp.text(x),
                pp.text(":"),
                t.pretty(pp),
                pp.text("."),
                pp.softline(),
                e.pretty(pp).nest(2),
            ]),
            Exp::Fix(x, t, e) => pp.concat(vec![
                pp.text("fix"),
                pp.space(),
                pp.text(x),
                pp.text(":"),
                t.pretty(pp),
                pp.text("."),
                pp.line(),
                e.pretty(pp),
            ]),
            Exp::App(e1, e2) => {
                let e2 = skip_coercion(&**e2);
                pp.concat(vec![
                    parens_if(pp, &**e1, e1.is_fun_exp()),
                    pp.softline(),
                    parens_if(pp, e2, !(e2.is_atom() || e2.is_coercion())),
                ])
            }
            Exp::BinaryOp(op, e1, e2) => pp.concat(vec![
                // should be pair or looser
                parens_if(pp, &**e1, e1.is_fun_exp()),
                pp.space(),
                match op {
                    BinOp::IntAdd => pp.text("+"),
                    BinOp::IntMul => pp.text("*"),
                    BinOp::IntEq => pp.text("="),
                    _ => pp.text("[op]"),
                },
                pp.space(),
                parens_if(pp, &**e2, e2.is_add_or_looser()),
            ]),
            Exp::AddOverload(e1, e2) => pp.concat(vec![
                // should be pair or looser
                parens_if(pp, &**e1, e1.is_fun_exp()),
                pp.text(" +? "),
                parens_if(pp, &**e2, e2.is_add_or_looser()),
            ]),
            Exp::UnaryOp(op, e1) => pp.concat(vec![
                match op {
                    UnOp::Not => pp.text("not "),
                    _ => pp.text("[op] "),
                },
                parens_if(pp, &**e1, e1.is_mul_or_looser()),
            ]),
            Exp::If(e1, e2, e3) => pp
                .concat(vec![
                    pp.text("if"),
                    pp.space(),
                    e1.pretty(pp).nest(2),
                    pp.line(),
                    pp.concat(vec![pp.text("then"), pp.softline(), e2.pretty(pp)])
                        .nest(2),
                    pp.line(),
                    pp.concat(vec![pp.text("else"), pp.softline(), e3.pretty(pp)])
                        .nest(2),
                ])
                .group(),
            Exp::Pair(e1, e2) => pp.concat(vec![
                // should be is pair or looser (because pair is right associative)
                parens_if(pp, &**e1, e1.is_fun_exp()),
                pp.text(","),
                pp.space(),
                parens_if(pp, &**e2, e2.is_fun_exp()),
            ]),
            Exp::Fst(e) => pp.concat(vec![pp.text("fst"), pp.space(), e.pretty(pp).nest(2)]),
            Exp::Snd(e) => pp.concat(vec![pp.text("snd"), pp.space(), e.pretty(pp).nest(2)]),
            Exp::Cons(e1, e2) => pp.concat(vec![
                parens_if(pp, &**e1, e1.is_app_like()),
                pp.space(),
                pp.text("::"),
                pp.space(),
                e2.pretty(pp).nest(2),
            ]),
            Exp::Empty(Typ::Metavar(_)) if !PRINT_METAVARS => pp.text("empty"),
            Exp::Empty(t) => pp.concat(vec![pp.text("empty:"), pp.space(), t.pretty(pp)]),
            Exp::IsEmpty(e) => {
                pp.concat(vec![pp.text("is_empty"), pp.space(), e.pretty(pp).nest(2)])
            }
            Exp::Head(e) => pp.concat(vec![pp.text("head"), pp.space(), e.pretty(pp).nest(2)]),
            Exp::Tail(e) => pp.concat(vec![
                pp.text("tail"),
                pp.space(),
                parens_if(pp, &**e, e.is_app_like()).nest(2),
            ]),
            Exp::Box(e) => pp.concat(vec![
                pp.text("box "),
                parens_if(pp, &**e, e.is_app_like()).nest(2),
            ]),
            Exp::Unbox(e) => pp.concat(vec![
                pp.text("unbox "),
                parens_if(pp, &**e, e.is_app_like()).nest(2),
            ]),
            Exp::BoxSet(e1, e2) => pp.concat(vec![
                pp.text("boxset! "),
                parens_if(pp, &**e1, e1.is_app_like()).nest(2),
                pp.space(),
                parens_if(pp, &**e2, e2.is_app_like()).nest(2),
            ]),
            Exp::Vector(e1, e2) => pp.concat(vec![
                pp.text("vector "),
                parens_if(pp, &**e1, e1.is_app_like()).nest(2),
                pp.space(),
                parens_if(pp, &**e2, e2.is_app_like()).nest(2),
            ]),
            Exp::VectorRef(e1, e2) => pp.concat(vec![
                pp.text("vector-ref "),
                parens_if(pp, &**e1, e1.is_app_like()).nest(2),
                pp.space(),
                parens_if(pp, &**e2, e2.is_app_like()).nest(2),
            ]),
            Exp::VectorSet(e1, e2, e3) => pp.concat(vec![
                pp.text("vector-set! "),
                parens_if(pp, &**e1, e1.is_app_like()).nest(2),
                pp.space(),
                parens_if(pp, &**e2, e2.is_app_like()).nest(2),
                pp.space(),
                parens_if(pp, &**e3, e3.is_app_like()).nest(2),
            ]),
            Exp::VectorLen(e) => pp.concat(vec![
                pp.text("vector-length "),
                parens_if(pp, &**e, e.is_app_like()).nest(2),
            ]),
            Exp::IsBool(e) => pp.concat(vec![pp.text("is_bool"), pp.space(), e.pretty(pp).nest(2)]),
            Exp::IsInt(e) => pp.concat(vec![pp.text("is_int"), pp.space(), e.pretty(pp).nest(2)]),
            Exp::IsString(e) => {
                pp.concat(vec![pp.text("is_string"), pp.space(), e.pretty(pp).nest(2)])
            }
            Exp::IsList(e) => pp.concat(vec![pp.text("is_list"), pp.space(), e.pretty(pp).nest(2)]),
            Exp::IsFun(e) => pp.concat(vec![pp.text("is_fun"), pp.space(), e.pretty(pp).nest(2)]),
            Exp::Coerce(_, Typ::Any, e) if e.is_atom() => {
                pp.concat(vec![pp.text("("), e.pretty(pp), pp.text(" : any)")])
            }
            // Exp::Coerce(_, to, e) 
            // if e.is_fun_exp() && to.has_any() => {
            //     pp.concat(vec![pp.text("("), e.pretty(pp), pp.text(" : "), to.pretty(pp), pp.text(")")])
            // }
            Exp::Coerce(from, to, e) if PRINT_COERCIONS => pp.concat(vec![
                pp.text("coerce("),
                from.pretty(pp),
                pp.text(", "),
                to.pretty(pp),
                pp.text(")"),
                pp.space(),
                e.pretty(pp).nest(2),
            ]),
            Exp::Coerce(_, _, e) => e.pretty(pp),
            Exp::PrimCoerce(k, e) => {
                pp.concat(vec![pp.text(format!("[{:?}]", k)), e.pretty(pp).nest(2)])
            }
        }
    }
}

impl_Display_Pretty!(Typ);
impl_Display_Pretty!(Lit);
impl_Display_Pretty!(Exp);
impl_Display_Pretty!(Toplevel);
