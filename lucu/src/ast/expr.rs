use strum::IntoStaticStr;

use crate::ast::{
    Constant, Grouped, Identifier, Path, Sentinel, Separated, Token, Type, WithEffects,
};
use crate::span::{HasSpan, Span};
use crate::tokens::{SymbolAssign, SymbolEquality, SymbolInequality};

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum MathOp {
    Add,
    Sub,
    Div,
    Mul,
    Mod,
    And,
    AndNot,
    Or,
    Xor,
    ShiftLeft,
    ShiftRight,
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
            SymbolAssign::AmpersandEquals => Self::Math(MathOp::Add),
            SymbolAssign::BarEquals => Self::Math(MathOp::Or),
            SymbolAssign::TildeEquals => Self::Math(MathOp::Xor),
            SymbolAssign::ShiftLeftEquals => Self::Math(MathOp::ShiftLeft),
            SymbolAssign::ShiftRightEquals => Self::Math(MathOp::ShiftRight),
            SymbolAssign::AmpersandTildeEquals => Self::Math(MathOp::AndNot),
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
pub enum PredicateOp {
    Equality(EqualityOp),
    Inequality(InequalityOp),
}

impl PredicateOp {
    pub fn equals(self) -> bool {
        matches!(
            self,
            Self::Inequality(InequalityOp::GreaterEquals)
                | Self::Inequality(InequalityOp::LessEquals)
                | Self::Equality(EqualityOp::Equals)
        )
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum UnOp {
    Negate,
    Plus,
    Complement,
    Not,
}

#[derive(Debug, PartialEq, Eq)]
pub struct LambdaParameter {
    pub var: Identifier,
    pub ty: Option<Box<Type>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Block {
    pub params: Option<(Separated<LambdaParameter>, Token)>,
    pub stmts: Separated<Box<Expression>>,
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Index::")]
pub enum Index {
    Single(Box<Expression>),
    Range {
        from: Option<Box<Expression>>,
        range: Token,
        to: Option<Box<Expression>>,
        sentinel: Option<Sentinel>,
    },
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Cast {
    Truncate,
    Extend,
    Transmute,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Call {
    pub fun: Path,
    pub args: Option<Grouped<Separated<Box<Expression>>>>,
    pub block: Option<Box<Expression>>,
    pub with_effects: Option<WithEffects>,
}

impl Call {
    pub fn count_args(&self) -> usize {
        self.args
            .as_ref()
            .map(|args| args.inner.elements.len())
            .unwrap_or(0)
            + self.block.is_some() as usize
    }
    pub fn args(&self) -> impl Iterator<Item = &Expression> {
        self.args
            .iter()
            .flat_map(|args| args.inner.iter())
            .chain(self.block.iter())
            .map(|expr| &**expr)
    }
}

impl From<Path> for Call {
    fn from(value: Path) -> Self {
        Self {
            fun: value,
            args: None,
            block: None,
            with_effects: None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, IntoStaticStr)]
#[strum(prefix = "Expression::")]
pub enum Expression {
    Constant(Box<Constant>),
    Uninit(Token),
    /// Could also be a member access
    Path(Path),
    Member {
        lhs: Box<Expression>,
        tk_dot: Token,
        rhs: Identifier,
    },
    Block(Grouped<Block>),
    Enclosed(Grouped<Box<Self>>),
    Let {
        tk_let: Token,
        var: Identifier,
        ty: Option<Box<Type>>,
        tk_equals: Token,
        value: Box<Self>,
    },
    Cast {
        op: Cast,
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
    AssignOp(AssignOp, Box<Self>, Token, Box<Self>),
    PredicateOp(PredicateOp, Box<Self>, Token, Box<Self>),
    MathOp(MathOp, Box<Self>, Token, Box<Self>),
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
        index: Grouped<Index>,
    },
    Array(Grouped<Separated<Box<Self>>>),
    /// Call, type constructor
    Call(Call),
    Use {
        params: Option<(Token, Separated<LambdaParameter>, Token)>,
        tk_use: Token,
        call: Call,
        tk_newline: Token,
        block: Separated<Box<Self>>,
    },
    Handle {
        tk_handle: Token,
        expr: Box<Self>,
    },
    Raise {
        tk_raise: Token,
        expr: Option<Box<Self>>,
    },
}

impl HasSpan for Call {
    fn span(&self) -> Span {
        let start = self.fun.span().start;
        let end = self
            .with_effects
            .as_ref()
            .map(HasSpan::span)
            .or_else(|| self.block.as_ref().map(HasSpan::span))
            .or_else(|| self.args.as_ref().map(HasSpan::span))
            .unwrap_or_else(|| self.fun.span())
            .end;
        Span::new(start, end)
    }
}

impl HasSpan for Expression {
    fn span(&self) -> Span {
        match self {
            Expression::Constant(c) => c.span(),
            Expression::Block(group) => group.span(),
            Expression::Enclosed(group) => group.span(),
            Expression::Uninit(token) => token.span(),
            Expression::Let { tk_let, value, .. } => {
                Span::new(tk_let.span().start, value.span().end)
            }
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
            Expression::AssignOp(_, lhs, _, rhs)
            | Expression::PredicateOp(_, lhs, _, rhs)
            | Expression::MathOp(_, lhs, _, rhs) => Span::new(lhs.span().start, rhs.span().end),
            Expression::UnOp { tk_op, expr, .. } => Span::new(tk_op.span().start, expr.span().end),
            Expression::Dereference { expr, tk_caret } => {
                Span::new(expr.span().start, tk_caret.span().end)
            }
            Expression::Index { array, index } => Span::new(array.span().start, index.span().end),
            Expression::Array(group) => group.span(),
            Expression::Call(call) => call.span(),
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
            Expression::Handle { tk_handle, expr } => {
                Span::new(tk_handle.span().start, expr.span().end)
            }
            Expression::Raise { tk_raise, expr } => match expr {
                Some(expr) => Span::new(tk_raise.span().start, expr.span().end),
                None => tk_raise.span(),
            },
            Expression::Path(path) => path.span(),
            Expression::Member { lhs, rhs, .. } => {
                let start = lhs.span().start;
                let end = rhs.span().end;
                Span::new(start, end)
            }
        }
    }
}

impl HasSpan for LambdaParameter {
    fn span(&self) -> Span {
        let start = self.var.span().start;
        let end = self
            .ty
            .as_ref()
            .map(HasSpan::span)
            .unwrap_or_else(|| self.var.span())
            .end;
        Span::new(start, end)
    }
}

impl HasSpan for Index {
    fn span(&self) -> Span {
        match self {
            Index::Single(expression) => expression.span(),
            Index::Range {
                from,
                range,
                to,
                sentinel,
            } => {
                let start = from
                    .as_deref()
                    .map(HasSpan::span)
                    .unwrap_or_else(|| range.span())
                    .start;
                let end = sentinel
                    .as_ref()
                    .map(HasSpan::span)
                    .or_else(|| to.as_ref().map(HasSpan::span))
                    .unwrap_or_else(|| range.span())
                    .end;
                Span::new(start, end)
            }
        }
    }
}
