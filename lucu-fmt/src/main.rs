use std::any::TypeId;
use std::collections::VecDeque;
use std::env;
use std::fs::read_to_string;
use std::io::{self, Read};
use std::path::Path;

use asta_pretty::{Chunk, Node, Text};
use lucu::ast;
use lucu::module::Module;
use lucu::pass::lexer::Lexer;
use lucu::pass::parser::Parser;
use lucu::span::{HasSpan, Span};

fn main() -> Result<(), io::Error> {
    // get source
    let mut source = String::new();
    if let Some(arg) = env::args().nth(1) {
        source = read_to_string(Path::new(&arg)).expect("could not read file");
    } else {
        let stdin = io::stdin();
        let mut handle = stdin.lock();
        handle.read_to_string(&mut source)?;
    }

    let mut comments = VecDeque::new();
    let tokens = Lexer::new(&source)
        .with_comments(&mut comments)
        .collect::<Box<_>>();
    let ast = Parser::new(&Module::MAIN, &source, &tokens).module();

    if ast.has_error() {
        eprint!("{}", source);
        panic!("ast has errors!");
    }

    // format source
    let mut nodes = Nodes {
        source: &source,
        nodes: Vec::new(),
        comments: comments.clone(),
        last_token: 0,
        no_wrap: false,
    };
    let ast = ast.value().unwrap();
    ast.push_nodes(&mut nodes);
    let text = Text {
        nodes: &nodes.nodes,
        indent_size: 4,
        maximum_width: 100,
    };
    let formatted = format!("{}", text);

    // check if ast is the same
    let mut formatted_comments = VecDeque::new();
    let formatted_tokens = Lexer::new(&formatted)
        .with_comments(&mut formatted_comments)
        .collect::<Box<_>>();
    let formatted_ast = Parser::new(&Module::MAIN, &formatted, &formatted_tokens).module();
    if formatted_ast.has_error()
        || formatted_ast.value().unwrap() != ast
        || !comments
            .into_iter()
            .map(|s| source.as_str()[s][2..].trim())
            .eq(formatted_comments
                .into_iter()
                .map(|s| formatted.as_str()[s][2..].trim()))
    {
        eprint!("{}", formatted);
        panic!("generated different ast!");
    }

    print!("{}", formatted);
    Ok(())
}

struct Nodes<'a> {
    source: &'a str,
    nodes: Vec<Node<'a>>,

    comments: VecDeque<Span>,
    last_token: u32,
    no_wrap: bool,
}

impl<'a> Nodes<'a> {
    fn push(&mut self, node: Node<'a>) {
        self.nodes.push(node);
    }
    fn space(&mut self) {
        self.nodes.push(Node::text(" "));
    }
    fn line(&mut self) {
        self.nodes.push(Node::Line)
    }
    fn line_on_wrap(&mut self) {
        if !self.no_wrap {
            self.nodes.push(Node::LN);
        }
    }
    fn line_or_space(&mut self) {
        if self.no_wrap {
            self.nodes.push(Node::Text(Chunk::SPACE));
        } else {
            self.nodes.push(Node::LN_SPACE)
        }
    }
    fn comma(&mut self) {
        if self.no_wrap {
            self.nodes.push(Node::Text(Chunk::COMMA_SPACE));
        } else {
            self.nodes.push(Node::LN_COMMA_SPACE);
        }
    }
    fn trailing_comma(&mut self) {
        if !self.no_wrap {
            self.nodes.push(Node::LN_TRAILING_COMMA);
        }
    }
    fn group(&mut self, force: bool, f: impl FnOnce(&mut Self)) {
        if self.no_wrap {
            f(self);
        } else {
            self.nodes.push(Node::OpenGroup(force));
            f(self);
            self.nodes.push(Node::CloseGroup)
        }
    }
    fn no_wrap(&mut self, f: impl FnOnce(&mut Self)) {
        if self.no_wrap {
            f(self);
        } else {
            self.no_wrap = true;
            f(self);
            self.no_wrap = false;
        }
    }
    fn indent_on_wrap(&mut self, f: impl FnOnce(&mut Self)) {
        if self.no_wrap {
            f(self);
        } else {
            self.nodes.push(Node::OpenIndentOnWrap);
            f(self);
            self.nodes.push(Node::CloseIndentOnWrap);
        }
    }
    fn indent(&mut self, f: impl FnOnce(&mut Self)) {
        self.nodes.push(Node::OpenIndent);
        f(self);
        self.nodes.push(Node::CloseIndent);
    }
    fn ends_in_whitespace(&self) -> bool {
        !matches!(self.nodes.last(), Some(Node::Text(chunk)) if !chunk.contents.ends_with(' '))
    }
    fn was_just_indented(&self) -> bool {
        matches!(
            self.nodes.last(),
            Some(Node::OpenIndent | Node::OpenIndentOnWrap)
        ) || (matches!(self.nodes.last(), Some(Node::Line | Node::LineOr(_, _)))
            && matches!(
                self.nodes.get(self.nodes.len().saturating_sub(2)),
                Some(Node::OpenIndent | Node::OpenIndentOnWrap)
            ))
    }
    fn was_just_empty_line(&self) -> bool {
        matches!(self.nodes.last(), Some(Node::Line | Node::LineOr(_, _)))
            && matches!(
                self.nodes.get(self.nodes.len().saturating_sub(2)),
                Some(Node::Line | Node::LineOr(_, _))
            )
    }
    fn in_group(&self) -> bool {
        self.nodes
            .iter()
            .map(|n| match n {
                Node::OpenGroup(_) => 1,
                Node::CloseGroup => -1,
                _ => 0,
            })
            .sum::<i32>()
            > 0
    }
    fn comment_line(&mut self) {
        if self.in_group() {
            // make the group always wrap by making the non-wrap variant have a huge size
            self.nodes
                .push(Node::LineOr(Chunk::EMPTY, Chunk::new_sized("", usize::MAX)));
        } else {
            self.line();
        }
    }
    fn contains_comments(&self, span: Span) -> bool {
        self.comments
            .iter()
            .take_while(|s| s.end <= span.end)
            .any(|s| s.start >= span.start)
    }
    fn user_lines(&self, next: Span) -> usize {
        // count the amount of lines the user put between these
        let between = &self.source[Span::new(self.last_token, next.start)];
        between.bytes().filter(|&c| c == b'\n').count()
    }
    fn optional_empty_line(&mut self, next: Span) -> bool {
        if self.was_just_empty_line() {
            return false;
        }
        if self.user_lines(next) > 1 {
            self.line();
            true
        } else {
            false
        }
    }
    fn comments(&mut self, next: Span) {
        while let Some(comment) = self
            .comments
            .pop_front_if(|s| s.start >= self.last_token && s.end <= next.start)
        {
            let mut comment_str = &self.source[comment][2..];
            let doc = comment_str.starts_with('#');
            if doc {
                comment_str = &comment_str[1..];
            }
            comment_str = comment_str.strip_prefix(' ').unwrap_or(comment_str);

            // allow an extra line before this comment starts,
            // unless we just indented, then it needs to hug the line above
            if !self.was_just_indented() {
                self.optional_empty_line(comment);
            }
            // add a space if we currently don't end in a space
            if !self.ends_in_whitespace() {
                self.space();
            }

            if doc {
                self.nodes.push(Node::text("--#"));
            } else {
                self.nodes.push(Node::text("--"));
            }
            if !comment_str.is_empty() {
                self.space();
            }
            self.nodes.push(Node::text(comment_str));
            self.comment_line();

            self.last_token = comment.end;
        }
    }
    fn token(&mut self, token: ast::Token) {
        self.comments(token.span());
        self.nodes.push(Node::text(&self.source[token.0]));
        self.last_token = token.0.end;
    }
}

trait Ast {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>);
}

fn is_heavy(def: &ast::Item) -> bool {
    match def {
        ast::Item::Function(_, def) => def.as_ref().is_some_and(|(_, def)| match def {
            ast::FunctionDefinition::Expression(body) => {
                matches!(**body, ast::Expression::Block(_))
            }
            ast::FunctionDefinition::Intrinsic(_) => false,
        }),
        ast::Item::Type(_, _, _) => false,
        ast::Item::Effect(_, _, def) => def.as_ref().is_some_and(|(_, def)| match def {
            ast::EffectDefinition::Body(_) => true,
            ast::EffectDefinition::Alias(_) => false,
            ast::EffectDefinition::Intrinsic(_) => false,
        }),
        ast::Item::Region(_, _, _) => false,
        ast::Item::Constant(_, _, _, _) => false,
        ast::Item::Handle(_, _, _) => true,
    }
}

impl Ast for ast::Module {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        for (i, import) in self.imports.iter().enumerate() {
            if i > 0 {
                nodes.line();
            }
            import.push_nodes(nodes);
        }

        if !self.imports.elements.is_empty() {
            nodes.line();
            nodes.line();
        }

        let mut last_heavy = false;
        for (i, def) in self.items.iter().enumerate() {
            let this_heavy = is_heavy(def);
            if i > 0 {
                nodes.line();
                if last_heavy || this_heavy {
                    nodes.line();
                }
                nodes.comments(def.span());
                nodes.optional_empty_line(def.span());
            }
            last_heavy = this_heavy;
            def.push_nodes(nodes);
        }

        nodes.line();
        nodes.comments(Span::new(u32::MAX, u32::MAX));
    }
}

impl Ast for ast::Import {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        nodes.token(self.import);
        nodes.space();
        nodes.token(self.path.token);
        if let Some(ident) = &self.ident {
            nodes.space();
            nodes.token(ident.token);
        }
    }
}

impl Ast for ast::Index {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::Index::Single(expr) => expr.push_nodes(nodes),
            ast::Index::Range {
                from,
                range,
                to,
                sentinel,
            } => {
                from.push_nodes(nodes);
                nodes.token(*range);
                to.push_nodes(nodes);
                sentinel.push_nodes(nodes);
            }
        }
    }
}

impl Ast for ast::Grouped<ast::Index> {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        if !nodes.contains_comments(self.span()) {
            nodes.token(self.open);
            self.inner.push_nodes(nodes);
            nodes.token(self.close);
        } else {
            nodes.group(true, |nodes| {
                nodes.token(self.open);
                nodes.indent_on_wrap(|nodes| {
                    nodes.line_on_wrap();
                    self.inner.push_nodes(nodes);
                    nodes.comments(self.close.span());
                });
                nodes.token(self.close);
            });
        }
    }
}

impl Ast for ast::Grouped<Box<ast::Expression>> {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        if !nodes.contains_comments(self.span()) {
            nodes.token(self.open);
            self.inner.push_nodes(nodes);
            nodes.token(self.close);
        } else {
            nodes.group(true, |nodes| {
                nodes.token(self.open);
                nodes.indent_on_wrap(|nodes| {
                    nodes.line_on_wrap();
                    self.inner.push_nodes(nodes);
                    nodes.comments(self.close.span());
                });
                nodes.token(self.close);
            });
        }
    }
}

impl<T: Ast + HasSpan> Ast for ast::Grouped<ast::Separated<T>>
where
    T: 'static,
{
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        if &nodes.source[self.open.0] == "{" {
            nodes.token(self.open);
            nodes.indent(|nodes| {
                for param in self.inner.iter() {
                    nodes.line();
                    param.push_nodes(nodes);
                }
                nodes.line();
                nodes.comments(self.close.span());
            });
            nodes.token(self.close);
        } else if self.inner.elements.len() < 2 && !nodes.contains_comments(self.span()) {
            nodes.token(self.open);
            for param in self.inner.iter() {
                param.push_nodes(nodes);
            }
            if TypeId::of::<T>() == TypeId::of::<ast::GenericArgument>() {
                nodes.push(Node::Text(Chunk::COMMA));
            }
            nodes.token(self.close);
        } else {
            nodes.group(true, |nodes| {
                nodes.token(self.open);
                nodes.indent_on_wrap(|nodes| {
                    nodes.line_on_wrap();
                    for (i, param) in self.inner.iter().enumerate() {
                        if i > 0 {
                            nodes.comma();
                        }
                        param.push_nodes(nodes);
                    }
                    if TypeId::of::<T>() == TypeId::of::<ast::GenericArgument>()
                        && self.inner.elements.len() < 2
                    {
                        nodes.push(Node::Text(Chunk::COMMA));
                        nodes.line_on_wrap();
                    } else {
                        nodes.trailing_comma();
                    }
                    nodes.comments(self.close.span());
                });
                nodes.token(self.close);
            });
        }
    }
}

#[derive(PartialEq, Eq)]
enum Placement {
    Newline,
    Inline,
    Choose,
}

trait Definition: Ast {
    fn placement(&self) -> Placement;
    fn push_definition<'a>(&'a self, nodes: &mut Nodes<'a>, equals: ast::Token) {
        match self.placement() {
            Placement::Newline => {
                nodes.indent(|nodes| {
                    nodes.line();
                    nodes.token(equals);
                    nodes.space();
                    self.push_nodes(nodes);
                });
            }
            Placement::Inline => {
                nodes.space();
                nodes.token(equals);
                nodes.space();
                self.push_nodes(nodes);
            }
            Placement::Choose => {
                nodes.group(false, |nodes| {
                    nodes.indent_on_wrap(|nodes| {
                        nodes.line_or_space();
                        nodes.token(equals);
                        nodes.space();
                        self.push_nodes(nodes);
                    });
                });
            }
        }
    }
}

impl Ast for ast::ConstantDefinition {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::ConstantDefinition::Constant(constant) => constant.push_nodes(nodes),
            ast::ConstantDefinition::Intrinsic(token) => nodes.token(*token),
        }
    }
}

impl Definition for ast::ConstantDefinition {
    fn placement(&self) -> Placement {
        match self {
            ast::ConstantDefinition::Constant(_) => Placement::Choose,
            ast::ConstantDefinition::Intrinsic(_) => Placement::Inline,
        }
    }
}

impl Ast for ast::RegionDefinition {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::RegionDefinition::Alias(path) => path.push_nodes(nodes),
            ast::RegionDefinition::Intrinsic(token) => nodes.token(*token),
        }
    }
}

impl Definition for ast::RegionDefinition {
    fn placement(&self) -> Placement {
        match self {
            ast::RegionDefinition::Alias(_) => Placement::Inline,
            ast::RegionDefinition::Intrinsic(_) => Placement::Inline,
        }
    }
}

impl Ast for ast::Item {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::Item::Function(decl, def) => {
                nodes.token(decl.fun);
                nodes.space();
                decl.name.push_nodes(nodes);

                if let Some(params) = &decl.parameters {
                    params.push_nodes(nodes);
                }

                if let Some(returns) = &decl.returns {
                    nodes.space();
                    returns.push_nodes(nodes);
                }

                if let Some(with_effects) = &decl.effects {
                    if nodes.user_lines(with_effects.span()) > 0 {
                        nodes.indent(|nodes| {
                            nodes.line();
                            with_effects.push_nodes(nodes);
                            if let Some((equals, def)) = def
                                && def.placement() != Placement::Inline
                            {
                                def.push_definition(nodes, *equals);
                            }
                        });
                    } else {
                        nodes.group(false, |nodes| {
                            nodes.indent_on_wrap(|nodes| {
                                nodes.line_or_space();
                                with_effects.push_nodes(nodes);
                                if let Some((equals, def)) = def
                                    && def.placement() != Placement::Inline
                                {
                                    def.push_definition(nodes, *equals);
                                }
                            });
                        });
                    }
                    if let Some((equals, def)) = def
                        && def.placement() == Placement::Inline
                    {
                        def.push_definition(nodes, *equals);
                    }
                } else if let Some((equals, def)) = def {
                    def.push_definition(nodes, *equals);
                }
            }
            ast::Item::Type(token, name, def) => {
                nodes.token(*token);
                nodes.space();
                name.push_nodes(nodes);

                if let Some((equals, def)) = def {
                    def.push_definition(nodes, *equals);
                }
            }
            ast::Item::Effect(token, name, def) => {
                nodes.token(*token);
                nodes.space();
                name.push_nodes(nodes);

                if let Some((equals, def)) = def {
                    def.push_definition(nodes, *equals);
                }
            }
            ast::Item::Region(token, name, def) => {
                nodes.token(*token);
                nodes.space();
                name.push_nodes(nodes);

                if let Some((equals, def)) = def {
                    def.push_definition(nodes, *equals);
                }
            }
            ast::Item::Constant(token, name, ty, def) => {
                nodes.token(*token);
                nodes.space();
                name.push_nodes(nodes);
                nodes.space();
                ty.push_nodes(nodes);

                if let Some((equals, def)) = def {
                    def.push_definition(nodes, *equals);
                }
            }
            ast::Item::Handle(token, generics, def) => {
                nodes.token(*token);
                if let Some(generics) = generics {
                    generics.push_nodes(nodes);
                }
                nodes.space();
                def.push_nodes(nodes);
            }
        }
    }
}

impl Ast for ast::WithEffects {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        nodes.token(self.with);
        nodes.space();
        nodes.no_wrap(|nodes| {
            for (i, path) in self.effects.iter().enumerate() {
                if i > 0 {
                    nodes.space();
                }
                path.push_nodes(nodes);
            }
        });
    }
}

impl Ast for ast::Handler {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        self.effect.push_nodes(nodes);
        if let Some(effects) = &self.with_effects {
            nodes.space();
            effects.push_nodes(nodes);
        }
        nodes.space();
        self.items.push_nodes(nodes);
    }
}

impl Ast for ast::FunctionDeclaration {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        nodes.token(self.fun);
        nodes.space();
        self.name.push_nodes(nodes);

        if let Some(params) = &self.parameters {
            params.push_nodes(nodes);
        }

        if let Some(returns) = &self.returns {
            nodes.space();
            returns.push_nodes(nodes);
        }

        if let Some(with_effects) = &self.effects {
            nodes.space();
            with_effects.push_nodes(nodes);
        }
    }
}

impl Ast for ast::Returns {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::Returns::Path(path) => path.push_nodes(nodes),
            ast::Returns::Type(ty) => ty.push_nodes(nodes),
            ast::Returns::Never(token) => nodes.token(*token),
        }
    }
}

impl Ast for ast::Parameter {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::Parameter::Data(name, ty) => {
                nodes.token(name.token);
                nodes.space();
                ty.push_nodes(nodes);
            }
            ast::Parameter::Lambda(decl) => {
                decl.push_nodes(nodes);
            }
        }
    }
}

impl Definition for ast::FunctionDefinition {
    fn placement(&self) -> Placement {
        match self {
            ast::FunctionDefinition::Expression(expression)
                if matches!(**expression, ast::Expression::Block(_)) =>
            {
                Placement::Inline
            }
            ast::FunctionDefinition::Expression(_) => Placement::Choose,
            ast::FunctionDefinition::Intrinsic(_) => Placement::Newline,
        }
    }
}

impl Ast for ast::FunctionDefinition {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::FunctionDefinition::Expression(expr) => {
                expr.push_nodes(nodes);
            }
            ast::FunctionDefinition::Intrinsic(token) => {
                nodes.token(*token);
            }
        }
    }
}

impl Ast for ast::Call {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        self.fun.push_nodes(nodes);
        self.args.push_nodes(nodes);
        if let Some(block) = &self.block {
            nodes.space();
            block.push_nodes(nodes);
        }
        if let Some(with_effects) = &self.with_effects {
            nodes.space();
            with_effects.push_nodes(nodes);
        }
    }
}

impl<T> Ast for Option<T>
where
    T: Ast,
{
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        if let Some(t) = self {
            t.push_nodes(nodes);
        }
    }
}

impl<T> Ast for Box<T>
where
    T: Ast,
{
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        (**self).push_nodes(nodes);
    }
}

impl Ast for ast::Separated<ast::LambdaParameter> {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        for (i, param) in self.iter().enumerate() {
            if i > 0 {
                nodes.comma();
                nodes.space();
            }
            nodes.token(param.var.token);
            if let Some(ty) = &param.ty {
                nodes.space();
                ty.push_nodes(nodes);
            }
        }
    }
}

impl Ast for ast::Expression {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::Expression::Constant(constant) => constant.push_nodes(nodes),
            ast::Expression::Uninit(token) => nodes.token(*token),
            ast::Expression::Path(path) => path.push_nodes(nodes),
            ast::Expression::Block(group) => {
                nodes.token(group.open);
                if let Some((ref lambda, tk_arrow)) = group.inner.params {
                    nodes.space();
                    lambda.push_nodes(nodes);
                    nodes.space();
                    nodes.token(tk_arrow);
                }
                match group.inner.stmts.elements.as_slice() {
                    [] if !nodes.contains_comments(group.span()) => {}
                    // [(single, _)] if !matches!(**single, ast::Expression::Use { .. }) => {
                    //     nodes.group(false, |nodes| {
                    //         nodes.indent_on_wrap(|nodes| {
                    //             nodes.line_or_space();
                    //             single.push_nodes(nodes);
                    //             nodes.space();
                    //             nodes.comments(group.close.span())
                    //         });
                    //     });
                    // }
                    _ => {
                        nodes.indent(|nodes| {
                            for expr in group.inner.stmts.iter() {
                                nodes.line();
                                nodes.comments(expr.span());
                                nodes.optional_empty_line(expr.span());
                                expr.push_nodes(nodes);
                            }
                            nodes.line();
                            nodes.comments(group.close.span())
                        });
                    }
                }
                nodes.token(group.close);
            }
            ast::Expression::Enclosed(grouped) => {
                grouped.push_nodes(nodes);
            }
            ast::Expression::Let {
                tk_let,
                var,
                ty,
                tk_equals,
                value,
            } => {
                nodes.token(*tk_let);
                nodes.space();
                nodes.token(var.token);
                nodes.space();
                if let Some(ty) = ty {
                    ty.push_nodes(nodes);
                    nodes.space();
                }
                nodes.token(*tk_equals);
                nodes.space();
                value.push_nodes(nodes);
            }
            ast::Expression::If {
                tk_if,
                condition,
                branch_true,
                branch_false,
            } => {
                nodes.token(*tk_if);
                nodes.space();
                condition.push_nodes(nodes);
                if let Some(tk_then) = branch_true.0 {
                    nodes.space();
                    nodes.token(tk_then);
                }
                nodes.space();
                branch_true.1.push_nodes(nodes);
                if let Some(branch_false) = branch_false {
                    nodes.space();
                    nodes.token(branch_false.0);
                    nodes.space();
                    branch_false.1.push_nodes(nodes);
                }
            }
            ast::Expression::AssignOp(_, lhs, tk_op, rhs)
            | ast::Expression::PredicateOp(_, lhs, tk_op, rhs)
            | ast::Expression::MathOp(_, lhs, tk_op, rhs) => {
                lhs.push_nodes(nodes);
                nodes.space();
                nodes.token(*tk_op);
                nodes.space();
                rhs.push_nodes(nodes);
            }
            ast::Expression::UnOp { tk_op, expr, .. } => {
                nodes.token(*tk_op);
                expr.push_nodes(nodes);
            }
            ast::Expression::Dereference { expr, tk_caret } => {
                expr.push_nodes(nodes);
                nodes.token(*tk_caret);
            }
            ast::Expression::Index { array, index } => {
                array.push_nodes(nodes);
                index.push_nodes(nodes);
            }
            ast::Expression::Array(group) => {
                group.push_nodes(nodes);
            }
            ast::Expression::Call(call) => {
                call.push_nodes(nodes);
            }
            ast::Expression::Use {
                params,
                tk_use,
                call,
                block,
                ..
            } => {
                if let Some((tk_let, params, tk_equals)) = params {
                    nodes.token(*tk_let);
                    nodes.space();
                    params.push_nodes(nodes);
                    nodes.space();
                    nodes.token(*tk_equals);
                    nodes.space();
                }
                nodes.token(*tk_use);
                nodes.space();
                call.push_nodes(nodes);
                for expr in block.iter() {
                    nodes.line();
                    nodes.comments(expr.span());
                    nodes.optional_empty_line(expr.span());
                    expr.push_nodes(nodes);
                }
            }
            ast::Expression::Handle {
                tk_handle: tk,
                expr,
                handlers,
            } => {
                nodes.token(*tk);
                nodes.space();
                expr.push_nodes(nodes);
                if let Some((tk_with, handlers)) = handlers {
                    nodes.space();
                    nodes.token(*tk_with);
                    for (handler, tk_with) in handlers.elements.iter() {
                        nodes.space();
                        handler.push_nodes(nodes);
                        if let Some(tk_with) = tk_with {
                            nodes.space();
                            nodes.token(*tk_with);
                        }
                    }
                }
            }
            ast::Expression::Discard {
                tk_discard: tk,
                expr,
            }
            | ast::Expression::Cast {
                tk_cast: tk, expr, ..
            } => {
                nodes.token(*tk);
                nodes.space();
                expr.push_nodes(nodes);
            }
            ast::Expression::Raise { tk_raise, expr } => {
                nodes.token(*tk_raise);
                if let Some(expr) = expr {
                    nodes.space();
                    expr.push_nodes(nodes);
                }
            }
            ast::Expression::Member { lhs, tk_dot, rhs } => {
                lhs.push_nodes(nodes);
                nodes.token(*tk_dot);
                nodes.token(rhs.token);
            }
        }
    }
}

impl Ast for ast::Name {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        nodes.token(self.ident.token);

        if let Some(generics) = &self.generics {
            generics.push_nodes(nodes);
        }
    }
}

impl Ast for ast::RegionKind {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::RegionKind::Mutable(token) => nodes.token(*token),
        }
    }
}

impl Ast for ast::GenericParameter {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::GenericParameter::Type(name) => name.push_nodes(nodes),
            ast::GenericParameter::Region(token, identifier) => {
                if let Some(kind) = token {
                    kind.push_nodes(nodes);
                    nodes.space();
                }
                nodes.token(identifier.token);
            }
            ast::GenericParameter::Other(name, kind) => {
                name.push_nodes(nodes);
                nodes.space();
                kind.push_nodes(nodes);
            }
        }
    }
}

impl Ast for ast::Kind {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::Kind::Type(token)
            | ast::Kind::Effect(token)
            | ast::Kind::Region(token)
            | ast::Kind::Thunk(token) => nodes.token(*token),
            ast::Kind::Constant(ty) => ty.push_nodes(nodes),
        }
    }
}

impl Ast for ast::PointerRegion {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::PointerRegion::At(at, region) => {
                nodes.token(*at);
                region.push_nodes(nodes);
            }
            ast::PointerRegion::Kind(region_kind) => region_kind.push_nodes(nodes),
        }
    }
}

impl Ast for ast::Sentinel {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        nodes.token(self.colon);
        nodes.token(self.zero);
    }
}

impl Ast for ast::ArrayProperties {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        if let Some(constant) = &self.size {
            constant.push_nodes(nodes);
        }
        if let Some(sentinel) = &self.sentinel {
            sentinel.push_nodes(nodes);
        }
    }
}

impl Ast for ast::Grouped<ast::ArrayProperties> {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        nodes.token(self.open);
        self.inner.push_nodes(nodes);
        nodes.token(self.close);
    }
}

impl Ast for ast::Type {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::Type::Path(path) => path.push_nodes(nodes),
            ast::Type::Maybe(maybe, ty) => {
                nodes.token(*maybe);
                ty.push_nodes(nodes);
            }
            ast::Type::Pointer(pointer, region, ty) => {
                nodes.token(*pointer);
                if let Some(region) = region {
                    region.push_nodes(nodes);
                    nodes.space();
                }
                ty.push_nodes(nodes);
            }
            ast::Type::Array(props, ty) => {
                props.push_nodes(nodes);
                ty.push_nodes(nodes);
            }
        }
    }
}

impl Ast for ast::TypeDefinition {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::TypeDefinition::Type(ty) => ty.push_nodes(nodes),
            ast::TypeDefinition::Struct(struc) => struc.push_nodes(nodes),
            ast::TypeDefinition::Intrinsic(token) => nodes.token(*token),
        }
    }
}

impl Definition for ast::TypeDefinition {
    fn placement(&self) -> Placement {
        match self {
            ast::TypeDefinition::Type(_) => Placement::Choose,
            ast::TypeDefinition::Struct(_) => Placement::Inline,
            ast::TypeDefinition::Intrinsic(_) => Placement::Inline,
        }
    }
}

impl Ast for ast::EffectDefinition {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::EffectDefinition::Body(body) => {
                body.push_nodes(nodes);
            }
            ast::EffectDefinition::Alias(paths) => {
                if paths.is_empty() {
                    nodes.push(Node::text(";"));
                } else {
                    nodes.no_wrap(|nodes| {
                        for (i, path) in paths.iter().enumerate() {
                            if i > 0 {
                                nodes.space();
                            }
                            path.push_nodes(nodes);
                        }
                    });
                }
            }
            ast::EffectDefinition::Intrinsic(token) => nodes.token(*token),
        }
    }
}

impl Definition for ast::EffectDefinition {
    fn placement(&self) -> Placement {
        match self {
            ast::EffectDefinition::Body(_) => Placement::Inline,
            ast::EffectDefinition::Alias(_) => Placement::Choose,
            ast::EffectDefinition::Intrinsic(_) => Placement::Newline,
        }
    }
}

impl Ast for ast::EffectBody {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        self.items.push_nodes(nodes);
    }
}

impl Ast for ast::PathOrigin {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::PathOrigin::Package(pkg, token, id) => {
                nodes.token(pkg.token);
                nodes.token(*token);
                nodes.token(id.token);
            }
            ast::PathOrigin::Local(id) => {
                nodes.token(id.token);
            }
            ast::PathOrigin::Underscore(token) => {
                nodes.token(*token);
            }
        }
    }
}

impl Ast for ast::Path {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        self.origin.push_nodes(nodes);
        if let Some(generics) = &self.generics {
            generics.push_nodes(nodes);
        }
    }
}

impl Ast for ast::GenericArgument {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::GenericArgument::Path(path, effects) => {
                path.push_nodes(nodes);
                if let Some(effects) = effects {
                    nodes.space();
                    effects.push_nodes(nodes);
                }
            }
            ast::GenericArgument::Type(ty, effects) => {
                ty.push_nodes(nodes);
                if let Some(effects) = effects {
                    nodes.space();
                    effects.push_nodes(nodes);
                }
            }
            ast::GenericArgument::Constant(constant) => constant.push_nodes(nodes),
        }
    }
}

impl Ast for ast::Constant {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::Constant::Path(path) => path.push_nodes(nodes),
            ast::Constant::Integer(integer) => nodes.token(integer.token),
            ast::Constant::String(string) => nodes.token(string.token),
            ast::Constant::Character(character) => nodes.token(character.token),
            ast::Constant::Zero(token) => nodes.token(*token),
        }
    }
}

impl Ast for ast::Struct {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        nodes.token(self.r#struct);
        nodes.token(self.members.open);
        if self.members.inner.elements.len() > 0 {
            nodes.indent(|nodes| {
                nodes.line();
                for param in self.members.inner.iter() {
                    param.push_nodes(nodes);
                    nodes.push(Node::Text(Chunk::COMMA));
                    nodes.line();
                }
                nodes.comments(self.members.close.span());
            });
        }
        nodes.token(self.members.close);
    }
}

impl Ast for ast::StructMember {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::StructMember::Data(name, ty) => {
                nodes.token(name.token);
                nodes.space();
                ty.push_nodes(nodes);
            }
        }
    }
}
