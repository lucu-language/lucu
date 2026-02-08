use strum::IntoStaticStr;

use crate::ast::{Constant, Grouped, Identifier, Path, Sentinel, Separated, Token, Type};
use crate::span::{HasSpan, Span};
use crate::tokens::{SymbolAssign, SymbolEquality, SymbolInequality};

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum MathOp {
    Add,
    Sub,
    Div,
    Mul,
    Mod,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum AssignOp {
    Assign,
    Math(MathOp),
}

impl From<SymbolAssign> for AssignOp {
    fn from(value: SymbolAssign) -> Self {
        match value {
            SymbolAssign::Equals => Self::Assign,
            SymbolAssign::DashEquals => Self::Math(MathOp::Sub),
            SymbolAssign::PlusEquals => Self::Math(MathOp::Add),
            SymbolAssign::SlashEquals => Self::Math(MathOp::Div),
            SymbolAssign::StarEquals => Self::Math(MathOp::Mul),
            SymbolAssign::PercentEquals => Self::Math(MathOp::Mul),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum EqualityOp {
    Equals,
    NotEquals,
}

impl From<SymbolEquality> for EqualityOp {
    fn from(value: SymbolEquality) -> Self {
        match value {
            SymbolEquality::EqualsEquals => Self::Equals,
            SymbolEquality::BangEquals => Self::NotEquals,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum InequalityOp {
    Greater,
    GreaterEquals,
    Less,
    LessEquals,
}

impl From<SymbolInequality> for InequalityOp {
    fn from(value: SymbolInequality) -> Self {
        match value {
            SymbolInequality::Greater => Self::Greater,
            SymbolInequality::GreaterEquals => Self::GreaterEquals,
            SymbolInequality::Less => Self::Less,
            SymbolInequality::LessEquals => Self::LessEquals,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum BinOp {
    Equality(EqualityOp),
    Inequality(InequalityOp),
    Math(MathOp),
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum UnOp {
    Negate,
    Plus,
}

#[derive(Debug, PartialEq, Eq)]
pub struct LambdaParameter {
    pub name: Identifier,
    pub ty: Option<Box<Type>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Block {
    pub params: Option<(Separated<LambdaParameter>, Token)>,
    pub exprs: Separated<Box<Expression>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Range {
    pub from: Option<Box<Expression>>,
    pub range: Token,
    pub to: Option<Box<Expression>>,
    pub sentinel: Option<Sentinel>,
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Expression::")]
pub enum Expression {
    Constant(Constant),
    Var(Identifier),
    Block(Grouped<Block>),
    Let {
        tk_let: Token,
        var: Identifier,
        ty: Option<Box<Type>>,
        tk_equals: Token,
        value: Box<Self>,
    },
    // integer casting
    Trunc {
        tk_trunc: Token,
        expr: Box<Self>,
    },
    Ext {
        tk_ext: Token,
        expr: Box<Self>,
    },
    // other casting
    Cast {
        tk_cast: Token,
        expr: Box<Self>,
    },
    If {
        tk_if: Token,
        condition: Box<Self>,
        branch_true: (Option<Token>, Box<Self>),
        branch_false: Option<(Token, Box<Self>)>,
    },
    Discard {
        tk_discard: Token,
        expr: Box<Self>,
    },
    AssignOp {
        op: AssignOp,
        lhs: Box<Self>,
        tk_op: Token,
        rhs: Box<Self>,
    },
    BinOp {
        op: BinOp,
        lhs: Box<Self>,
        tk_op: Token,
        rhs: Box<Self>,
    },
    UnOp {
        op: UnOp,
        tk_op: Token,
        expr: Box<Self>,
    },
    Dereference {
        expr: Box<Self>,
        tk_caret: Token,
    },
    Index {
        array: Box<Self>,
        index: Grouped<Box<Self>>,
    },
    IndexRange {
        array: Box<Self>,
        index: Grouped<Range>,
    },
    Array(Grouped<Separated<Box<Self>>>),
    Call {
        fun: Path,
        args: Option<Grouped<Separated<Box<Self>>>>,
        block: Option<Box<Self>>,
    },
    Use {
        params: Option<(Token, Separated<LambdaParameter>, Token)>,
        tk_use: Token,
        fun: Path,
        args: Option<Grouped<Separated<Box<Self>>>>,
        block: Separated<Box<Self>>,
    },
    Try {
        tk_try: Token,
        expr: Box<Self>,
    },
    Break {
        tk_break: Token,
        expr: Option<Box<Self>>,
    },
}

impl HasSpan for Expression {
    fn span(&self) -> Span {
        match self {
            Expression::Constant(c) => c.span(),
            Expression::Var(i) => i.span(),
            Expression::Block(group) => group.span(),
            Expression::Let { tk_let, value, .. } => {
                Span::new(tk_let.span().start, value.span().end)
            }
            Expression::Trunc { tk_trunc, expr, .. } => {
                Span::new(tk_trunc.span().start, expr.span().end)
            }
            Expression::Ext { tk_ext, expr, .. } => Span::new(tk_ext.span().start, expr.span().end),
            Expression::Cast { tk_cast, expr, .. } => {
                Span::new(tk_cast.span().start, expr.span().end)
            }
            Expression::If {
                tk_if,
                branch_true,
                branch_false,
                ..
            } => match branch_false {
                Some(branch_false) => Span::new(tk_if.span().start, branch_false.1.span().end),
                _ => Span::new(tk_if.span().start, branch_true.1.span().end),
            },
            Expression::Discard { tk_discard, expr } => {
                Span::new(tk_discard.span().start, expr.span().end)
            }
            Expression::AssignOp { lhs, rhs, .. } | Expression::BinOp { lhs, rhs, .. } => {
                Span::new(lhs.span().start, rhs.span().end)
            }
            Expression::UnOp { tk_op, expr, .. } => Span::new(tk_op.span().start, expr.span().end),
            Expression::Dereference { expr, tk_caret } => {
                Span::new(expr.span().start, tk_caret.span().end)
            }
            Expression::Index { array, index } => Span::new(array.span().start, index.span().end),
            Expression::IndexRange { array, index } => {
                Span::new(array.span().start, index.span().end)
            }
            Expression::Array(group) => group.span(),
            Expression::Call { fun, args, block } => {
                let start = fun.span().start;
                let end = block
                    .as_ref()
                    .map(HasSpan::span)
                    .or_else(|| args.as_ref().map(HasSpan::span))
                    .unwrap_or_else(|| fun.span())
                    .end;
                Span::new(start, end)
            }
            Expression::Use {
                params,
                tk_use,
                block,
                ..
            } => {
                let start = params
                    .as_ref()
                    .map(|(tk_let, _, _)| tk_let.span())
                    .unwrap_or_else(|| tk_use.span())
                    .start;
                let end = block.span().end;
                Span::new(start, end)
            }
            Expression::Try { tk_try, expr } => Span::new(tk_try.span().start, expr.span().end),
            Expression::Break { tk_break, expr } => match expr {
                Some(expr) => Span::new(tk_break.span().start, expr.span().end),
                None => tk_break.span(),
            },
        }
    }
}
