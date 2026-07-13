use std::collections::VecDeque;
use std::io::{self, Read};

use asta_pretty::{Node, Text};
use lucu::ast;
use lucu::module::Module;
use lucu::pass::lexer::Lexer;
use lucu::pass::parser::Parser;
use lucu::span::{HasSpan, Span};

fn main() -> Result<(), io::Error> {
    // get source
    let mut source = String::new();
    let stdin = io::stdin();
    let mut handle = stdin.lock();
    handle.read_to_string(&mut source)?;

    let mut comments = VecDeque::new();
    let tokens = Lexer::new(&source)
        .with_comments(&mut comments)
        .collect::<Box<_>>();
    let ast = Parser::new(&Module::MAIN, &source, &tokens).module();

    if ast.has_error() {
        print!("{}", source);
        return Ok(());
    }

    // format source
    let mut nodes = Nodes {
        source: &source,
        nodes: Vec::new(),
        comments: comments.clone(),
        last_token: 0,
    };
    let ast = ast.value().unwrap();
    ast.push_nodes(&mut nodes);
    let text = Text {
        nodes: &nodes.nodes,
        indent_size: 3,
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
        self.nodes.push(Node::LN);
    }
    fn line_or_space(&mut self) {
        self.nodes.push(Node::LN_SPACE)
    }
    fn comma(&mut self) {
        self.nodes.push(Node::LN_COMMA_SPACE);
    }
    fn trailing_comma(&mut self) {
        self.nodes.push(Node::LN_TRAILING_COMMA);
    }
    fn group(&mut self, force: bool, f: impl FnOnce(&mut Self)) {
        let idx = self.nodes.len();
        self.nodes.push(Node::OpenGroup(force));
        f(self);
        if self.nodes[idx] == Node::OpenWrap {
            self.nodes.push(Node::CloseWrap)
        } else {
            self.nodes.push(Node::CloseGroup)
        }
    }
    fn group_nowrap(&mut self, f: impl FnOnce(&mut Self)) {
        let idx = self.nodes.len();
        self.nodes.push(Node::OpenNoWrap);
        f(self);
        if self.nodes[idx] == Node::OpenWrap {
            self.nodes.push(Node::CloseWrap)
        } else {
            self.nodes.push(Node::CloseNoWrap)
        }
    }
    fn indent_on_wrap(&mut self, f: impl FnOnce(&mut Self)) {
        self.nodes.push(Node::OpenIndentOnWrap);
        f(self);
        self.nodes.push(Node::CloseIndentOnWrap);
    }
    fn no_wrap(&mut self, f: impl FnOnce(&mut Self)) {
        self.nodes.push(Node::OpenFlat);
        f(self);
        self.nodes.push(Node::CloseFlat);
    }
    fn indent(&mut self, f: impl FnOnce(&mut Self)) {
        self.nodes.push(Node::OpenIndent);
        f(self);
        self.nodes.push(Node::CloseIndent);
    }
    fn end_with_space(&mut self) {
        for node in self.nodes.iter_mut().rev() {
            match node {
                Node::Text(chunk) if !chunk.contents.is_empty() => {
                    if !chunk.contents.ends_with(' ') {
                        self.space();
                    }
                    return;
                }
                Node::Line => return,
                Node::LineOr(_, _) => {
                    if *node == Node::LN_TRAILING_COMMA {
                        *node = Node::LN_COMMA_SPACE;
                    }
                    return;
                }
                _ => {}
            }
        }
    }
    fn open_group(&mut self) {
        let mut nesting: usize = 0;
        let mut done = false;
        for node in self.nodes.iter_mut().rev() {
            match node {
                Node::OpenFlat if nesting == 0 => {
                    return;
                }
                Node::OpenGroup(force) => {
                    if (!done || *force) && nesting == 0 {
                        *node = Node::OpenWrap;
                        done = true;
                    }
                    nesting = nesting.saturating_sub(1);
                }
                Node::OpenNoWrap => {
                    if !done && nesting == 0 {
                        *node = Node::OpenWrap;
                        done = true;
                    }
                    nesting = nesting.saturating_sub(1);
                }
                Node::CloseGroup | Node::CloseNoWrap => {
                    nesting += 1;
                }
                _ => {}
            }
        }
    }
    fn check_comments(&mut self, start: u32, open_group: bool, max_lines: usize) -> bool {
        let len = self.comments.len();

        let mut first = true;
        while let Some(comment) = self
            .comments
            .pop_front_if(|s| s.start >= self.last_token && s.end <= start)
        {
            if open_group && first {
                self.open_group();
            } else {
                let count = self.source[self.last_token as usize..comment.start as usize]
                    .matches('\n')
                    .count()
                    .min(if first { max_lines } else { 2 });
                for _ in 0..count {
                    self.line();
                }
            }

            self.end_with_space();
            self.nodes.push(Node::text("-- "));
            let comment_str = &self.source[comment][2..];
            self.nodes.push(Node::text(
                comment_str.strip_prefix(' ').unwrap_or(comment_str),
            ));

            self.last_token = comment.end;
            first = false;
        }

        self.comments.len() < len
    }
    fn token(&mut self, token: ast::Token) {
        if self.check_comments(token.0.start, true, 0) {
            self.line();
        }
        self.nodes.push(Node::text(&self.source[token.0]));
        self.last_token = token.0.end;
    }
}

trait Ast {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>);
}

fn is_heavy(def: &ast::Item) -> bool {
    match def {
        ast::Item::Function(_, def) => def.is_some(),
        ast::Item::Type(_, _, _) => false,
        ast::Item::Effect(_, _, def) => def.as_ref().is_some_and(|(_, def)| match def {
            ast::EffectDefinition::Body(_) => true,
            ast::EffectDefinition::Alias(_) => false,
            ast::EffectDefinition::Intrinsic(_) => true,
        }),
        ast::Item::Region(_, _, _) => false,
        ast::Item::Constant(_, _, _, _) => false,
        ast::Item::Handle(_, _, _) => true,
    }
}

impl Ast for ast::Module {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        for (i, import) in self.imports.iter().enumerate() {
            let this_span = import.span();
            if i == 0 {
                let had_comments = nodes.check_comments(this_span.start, false, 0);
                if had_comments {
                    if nodes.source[nodes.last_token as usize..this_span.start as usize]
                        .matches('\n')
                        .count()
                        > 1
                    {
                        nodes.line();
                    }
                    nodes.line();
                }
            } else if i > 0 {
                nodes.check_comments(this_span.start, false, 2);
                if nodes.source[nodes.last_token as usize..this_span.start as usize]
                    .matches('\n')
                    .count()
                    > 1
                {
                    nodes.line();
                }
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
            let this_span = def.span();
            if i == 0 {
                let had_comments = nodes.check_comments(this_span.start, false, 0);
                if had_comments {
                    if nodes.source[nodes.last_token as usize..this_span.start as usize]
                        .matches('\n')
                        .count()
                        > 1
                    {
                        nodes.line();
                    }
                    nodes.line();
                }
            } else {
                let had_comments = if last_heavy {
                    nodes.line();
                    nodes.check_comments(this_span.start, false, 1)
                } else {
                    nodes.check_comments(this_span.start, false, 2)
                };
                if (!last_heavy || had_comments)
                    && (this_heavy
                        || nodes.source[nodes.last_token as usize..this_span.start as usize]
                            .matches('\n')
                            .count()
                            > 1)
                {
                    nodes.line();
                }
                nodes.line();
            }
            last_heavy = this_heavy;
            def.push_nodes(nodes);
        }

        nodes.check_comments(u32::MAX, false, 2);
        nodes.line();
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

impl<T: Ast + HasSpan> Ast for ast::Grouped<ast::Separated<T>> {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        if &nodes.source[self.open.0] == "{" {
            nodes.token(self.open);
            nodes.indent(|nodes| {
                for (i, param) in self.inner.iter().enumerate() {
                    if i == 0 {
                        nodes.check_comments(param.span().start, false, 1);
                    } else {
                        nodes.check_comments(param.span().start, false, 2);
                    }
                    nodes.line();
                    param.push_nodes(nodes);
                }
                nodes.check_comments(self.close.0.start, false, 2);
            });
            nodes.line();
            nodes.token(self.close);
        } else if self.inner.elements.len() < 2 {
            nodes.group_nowrap(|nodes| {
                nodes.token(self.open);
                nodes.indent_on_wrap(|nodes| {
                    nodes.line_on_wrap();
                    for (i, param) in self.inner.iter().enumerate() {
                        if i > 0 {
                            nodes.comma();
                        }
                        param.push_nodes(nodes);
                    }
                });
                nodes.trailing_comma();
                nodes.token(self.close);
            });
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
                });
                nodes.trailing_comma();
                nodes.token(self.close);
            });
        }
    }
}

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
                decl.push_nodes(nodes);

                if let Some((equals, def)) = def {
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

        if let Some(effects) = &self.effects {
            nodes.space();
            effects.push_nodes(nodes);
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

impl Ast for ast::Expression {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        match self {
            ast::Expression::Block(group) => {
                nodes.token(group.open);
                nodes.indent(|nodes| {
                    nodes.check_comments(group.close.0.start, false, 1);
                });
                nodes.line();
                nodes.token(group.close);
            }
            _ => todo!(),
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

impl Ast for ast::Grouped<()> {
    fn push_nodes<'a>(&'a self, nodes: &mut Nodes<'a>) {
        nodes.token(self.open);
        if &nodes.source[self.open.0] == "{" {
            nodes.indent(|nodes| {
                nodes.check_comments(self.close.0.start, false, 1);
            });
            nodes.line();
        }
        nodes.token(self.close);
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
        self.members.push_nodes(nodes);
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
