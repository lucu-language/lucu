use std::io::{self, Read};

use lucu::ast::{self, inner};
use lucu::module::Module;
use lucu::pass::lexer::Lexer;
use lucu::pass::parser::Parser;
use lucu_pretty::{Node, Text};

fn main() -> Result<(), io::Error> {
    // get source
    let mut source = String::new();
    let stdin = io::stdin();
    let mut handle = stdin.lock();
    handle.read_to_string(&mut source)?;

    let tokens = Lexer::new(&source).collect::<Box<_>>();
    let ast = Parser::new(&Module::MAIN, &source, &tokens).module();
    // TODO: get comments

    if ast.has_error() {
        print!("{}", source);
        return Ok(());
    }

    // format source
    let mut nodes = Vec::new();
    let ast = ast.value().unwrap();
    ast.push_nodes(&source, &mut nodes);
    let text = Text {
        nodes: &nodes,
        indent_size: 3,
        maximum_width: 100,
    };
    let formatted = format!("{}", text);

    // check if ast is the same
    let formatted_tokens = Lexer::new(&formatted).collect::<Box<_>>();
    let formatted_ast = Parser::new(&Module::MAIN, &formatted, &formatted_tokens).module();
    if formatted_ast.has_error() || formatted_ast.value().unwrap() != ast {
        eprint!("{}", formatted);
        panic!("generated different ast!");
    }

    print!("{}", formatted);
    Ok(())
}

trait Ast {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>);
}

impl Ast for ast::Module {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        for import in &self.imports {
            import.push_nodes(source, nodes);
        }
        nodes.push(Node::Line);
        for (i, def) in self.definitions.iter().enumerate() {
            if i > 0 {
                nodes.push(Node::Line);
            }
            def.push_nodes(source, nodes);
        }
    }
}

impl Ast for ast::Import {
    fn push_nodes<'a>(&'a self, _source: &'a str, nodes: &mut Vec<Node<'a>>) {
        nodes.push(Node::text("import \""));
        nodes.push(Node::text(self.path.as_str()));
        nodes.push(Node::text("\""));
        if let Some(ident) = &self.ident {
            nodes.push(Node::text(" "));
            nodes.push(Node::text(ident.as_str()));
        }
        nodes.push(Node::Line);
    }
}

impl Ast for ast::Definition {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match &self.0 {
            inner::Definition::Function(decl, def) => {
                decl.push_nodes(source, nodes);

                if let Some(def) = def {
                    def.push_nodes(source, nodes);
                }
            }
            inner::Definition::Type(name, def) => {
                nodes.push(Node::text("type "));
                name.push_nodes(source, nodes);

                if let Some(def) = def {
                    def.push_nodes(source, nodes);
                }
            }
            inner::Definition::Effect(name, def) => {
                nodes.push(Node::text("effect "));
                name.push_nodes(source, nodes);

                if let Some(def) = def {
                    def.push_nodes(source, nodes);
                }
            }
            inner::Definition::Handle(generics, def) => {
                nodes.push(Node::text("handle"));
                if let Some(generics) = generics {
                    if let [param] = generics.as_slice() {
                        nodes.push(Node::text("["));
                        param.push_nodes(source, nodes);
                        nodes.push(Node::text("]"));
                    } else {
                        nodes.push(Node::OpenGroup(true));
                        nodes.push(Node::text("["));
                        nodes.push(Node::OpenIndentOnWrap);
                        nodes.push(Node::LN);
                        for (i, param) in generics.iter().enumerate() {
                            if i > 0 {
                                nodes.push(Node::LN_COMMA_SPACE);
                            }
                            param.push_nodes(source, nodes);
                        }
                        nodes.push(Node::CloseIndentOnWrap);
                        nodes.push(Node::LN_TRAILING_COMMA);
                        nodes.push(Node::text("]"));
                        nodes.push(Node::CloseGroup);
                    }
                }
                nodes.push(Node::text(" "));
                def.push_nodes(source, nodes);
            }
        }
    }
}

impl Ast for ast::Handler {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        self.effect.push_nodes(source, nodes);
        if let Some(paths) = &self.with_effects {
            nodes.push(Node::text(" with "));

            nodes.push(Node::OpenNoWrap);
            for (i, path) in paths.iter().enumerate() {
                if i > 0 {
                    nodes.push(Node::text(" "));
                }
                path.push_nodes(source, nodes);
            }
            nodes.push(Node::CloseNoWrap);
        }

        nodes.push(Node::text(" {"));
        nodes.push(Node::OpenIndent);
        nodes.push(Node::Line);

        for (i, def) in self.definitions.iter().enumerate() {
            if i > 0 {
                nodes.push(Node::Line);
            }
            def.push_nodes(source, nodes);
        }

        nodes.push(Node::CloseIndent);
        nodes.push(Node::Line);
        nodes.push(Node::text("}"));
    }
}

impl Ast for ast::FunctionDeclaration {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        nodes.push(Node::text("fun "));
        self.name.push_nodes(source, nodes);

        if let Some(params) = &self.parameters {
            if let [param] = params.as_slice() {
                nodes.push(Node::text("("));
                param.push_nodes(source, nodes);
                nodes.push(Node::text(")"));
            } else {
                nodes.push(Node::OpenGroup(true));
                nodes.push(Node::text("("));
                nodes.push(Node::OpenIndentOnWrap);
                nodes.push(Node::LN);
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        nodes.push(Node::LN_COMMA_SPACE);
                    }
                    param.push_nodes(source, nodes);
                }
                nodes.push(Node::CloseIndentOnWrap);
                nodes.push(Node::LN_TRAILING_COMMA);
                nodes.push(Node::text(")"));
                nodes.push(Node::CloseGroup);
            }
        }

        if let Some(returns) = &self.returns {
            nodes.push(Node::text(" "));
            returns.push_nodes(source, nodes);
        }

        if let Some(paths) = &self.effects {
            nodes.push(Node::text(" with "));
            nodes.push(Node::OpenNoWrap);
            for (i, path) in paths.iter().enumerate() {
                if i > 0 {
                    nodes.push(Node::text(" "));
                }
                path.push_nodes(source, nodes);
            }
            nodes.push(Node::CloseNoWrap);
        }
    }
}

impl Ast for ast::Returns {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match &self.0 {
            inner::Returns::Never => nodes.push(Node::text("!")),
            inner::Returns::Data(ty) => ty.push_nodes(source, nodes),
        }
    }
}

impl Ast for ast::FunctionParameter {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match &self.0 {
            inner::FunctionParameter::Data(name, ty) => {
                nodes.push(Node::text(name.as_str()));
                nodes.push(Node::text(" "));
                ty.push_nodes(source, nodes);
            }
            inner::FunctionParameter::Lambda(decl) => {
                decl.push_nodes(source, nodes);
            }
        }
    }
}

impl Ast for ast::FunctionDefinition {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match &self.0 {
            inner::FunctionDefinition::Expression(expr) => {
                if matches!(expr.0, inner::Expression::Block) {
                    nodes.push(Node::text(" = "));
                    expr.push_nodes(source, nodes);
                } else {
                    nodes.push(Node::OpenGroup(false));
                    nodes.push(Node::OpenIndentOnWrap);
                    nodes.push(Node::LN_SPACE);
                    nodes.push(Node::text("= "));

                    expr.push_nodes(source, nodes);

                    nodes.push(Node::CloseIndentOnWrap);
                    nodes.push(Node::CloseGroup);
                }
            }
            inner::FunctionDefinition::Intrinsic => {
                nodes.push(Node::OpenIndent);
                nodes.push(Node::Line);
                nodes.push(Node::text("= #intrinsic"));
                nodes.push(Node::CloseIndent);
            }
        }
    }
}

impl Ast for ast::Expression {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match &self.0 {
            inner::Expression::Block => {
                nodes.push(Node::text("{"));
                nodes.push(Node::Line);
                nodes.push(Node::text("}"));
            }
        }
    }
}

impl Ast for ast::Name {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        nodes.push(Node::text(self.ident.as_str()));

        if let Some(generics) = &self.generics {
            if let [param] = generics.as_slice() {
                nodes.push(Node::text("["));
                param.push_nodes(source, nodes);
                nodes.push(Node::text("]"));
            } else {
                nodes.push(Node::OpenGroup(true));
                nodes.push(Node::text("["));
                nodes.push(Node::OpenIndentOnWrap);
                nodes.push(Node::LN);
                for (i, param) in generics.iter().enumerate() {
                    if i > 0 {
                        nodes.push(Node::LN_COMMA_SPACE);
                    }
                    param.push_nodes(source, nodes);
                }
                nodes.push(Node::CloseIndentOnWrap);
                nodes.push(Node::LN_TRAILING_COMMA);
                nodes.push(Node::text("]"));
                nodes.push(Node::CloseGroup);
            }
        }
    }
}

impl Ast for ast::GenericParameter {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        self.name.push_nodes(source, nodes);
        if let Some(kind) = &self.kind {
            nodes.push(Node::text(" "));
            kind.push_nodes(source, nodes);
        }
    }
}

impl Ast for ast::Kind {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match &self.0 {
            inner::Kind::Type => nodes.push(Node::text("type")),
            inner::Kind::Effect => nodes.push(Node::text("effect")),
            inner::Kind::Region => nodes.push(Node::text("region")),
            inner::Kind::Constant(ty) => ty.push_nodes(source, nodes),
        }
    }
}

impl Ast for ast::Type {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match &self.0 {
            inner::Type::Path(path) => path.push_nodes(source, nodes),
            inner::Type::Pointer(ty, region) => {
                nodes.push(Node::text("^"));
                if let Some(region) = region {
                    nodes.push(Node::text("@"));
                    region.push_nodes(source, nodes);
                    nodes.push(Node::text(" "));
                }
                ty.push_nodes(source, nodes);
            }
            inner::Type::PointerSlice(ty, region) => {
                nodes.push(Node::text("^"));
                if let Some(region) = region {
                    nodes.push(Node::text("@"));
                    region.push_nodes(source, nodes);
                    nodes.push(Node::text(" "));
                }
                nodes.push(Node::text("[]"));
                ty.push_nodes(source, nodes);
            }
            inner::Type::PointerSliceNullTerminated(ty, region) => {
                nodes.push(Node::text("^"));
                if let Some(region) = region {
                    nodes.push(Node::text("@"));
                    region.push_nodes(source, nodes);
                    nodes.push(Node::text(" "));
                }
                nodes.push(Node::text("[:0]"));
                ty.push_nodes(source, nodes);
            }
        }
    }
}

impl Ast for ast::TypeDefinition {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        nodes.push(Node::OpenGroup(false));
        nodes.push(Node::OpenIndentOnWrap);
        nodes.push(Node::LN_SPACE);
        nodes.push(Node::text("= "));
        match &self.0 {
            inner::TypeDefinition::Type(ty) => ty.push_nodes(source, nodes),
            inner::TypeDefinition::Struct(struc) => struc.push_nodes(source, nodes),
            inner::TypeDefinition::Intrinsic => nodes.push(Node::text("#intrinsic")),
        }
        nodes.push(Node::CloseIndentOnWrap);
        nodes.push(Node::CloseGroup);
    }
}

impl Ast for ast::EffectDefinition {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match &self.0 {
            inner::EffectDefinition::Body(body) => {
                nodes.push(Node::text(" = "));
                body.push_nodes(source, nodes);
            }
            inner::EffectDefinition::Alias(paths) => {
                nodes.push(Node::OpenGroup(false));
                nodes.push(Node::OpenIndentOnWrap);
                nodes.push(Node::LN_SPACE);
                nodes.push(Node::text("= "));

                nodes.push(Node::OpenNoWrap);
                for (i, path) in paths.iter().enumerate() {
                    if i > 0 {
                        nodes.push(Node::text(" "));
                    }
                    path.push_nodes(source, nodes);
                }
                nodes.push(Node::CloseNoWrap);

                nodes.push(Node::CloseIndentOnWrap);
                nodes.push(Node::CloseGroup);
            }
            inner::EffectDefinition::Intrinsic => {
                nodes.push(Node::OpenGroup(false));
                nodes.push(Node::OpenIndentOnWrap);
                nodes.push(Node::LN_SPACE);
                nodes.push(Node::text("= "));

                nodes.push(Node::text("#intrinsic"));

                nodes.push(Node::CloseIndentOnWrap);
                nodes.push(Node::CloseGroup);
            }
        }
    }
}

impl Ast for ast::EffectBody {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        nodes.push(Node::text("{"));
        nodes.push(Node::OpenIndent);
        nodes.push(Node::Line);

        for (i, def) in self.definitions.iter().enumerate() {
            if i > 0 {
                nodes.push(Node::Line);
            }
            def.push_nodes(source, nodes);
        }

        nodes.push(Node::CloseIndent);
        nodes.push(Node::Line);
        nodes.push(Node::text("}"));
    }
}

impl Ast for ast::Path {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        if let Some(module) = &self.package {
            nodes.push(Node::text(module.as_str()));
            nodes.push(Node::text("."));
        }
        nodes.push(Node::text(self.name.as_str()));

        if let Some(generics) = &self.generics {
            if let [param] = generics.as_slice() {
                nodes.push(Node::text("["));
                param.push_nodes(source, nodes);
                nodes.push(Node::text("]"));
            } else {
                nodes.push(Node::OpenGroup(true));
                nodes.push(Node::text("["));
                nodes.push(Node::OpenIndentOnWrap);
                nodes.push(Node::LN);
                for (i, param) in generics.iter().enumerate() {
                    if i > 0 {
                        nodes.push(Node::LN_COMMA_SPACE);
                    }
                    param.push_nodes(source, nodes);
                }
                nodes.push(Node::CloseIndentOnWrap);
                nodes.push(Node::LN_TRAILING_COMMA);
                nodes.push(Node::text("]"));
                nodes.push(Node::CloseGroup);
            }
        }
    }
}

impl Ast for ast::GenericArgument {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match &self.0 {
            inner::GenericArgument::Path(path) => path.push_nodes(source, nodes),
            inner::GenericArgument::Type(ty) => ty.push_nodes(source, nodes),
            inner::GenericArgument::Constant(constant) => constant.push_nodes(source, nodes),
        }
    }
}

impl Ast for ast::Constant {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match self.0 {}
    }
}

impl Ast for ast::Struct {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        nodes.push(Node::text("struct("));
        if !self.members.is_empty() {
            nodes.push(Node::OpenIndent);
            nodes.push(Node::Line);
            for (i, member) in self.members.iter().enumerate() {
                if i > 0 {
                    nodes.push(Node::Line);
                }
                member.push_nodes(source, nodes);
                nodes.push(Node::text(","));
            }
            nodes.push(Node::CloseIndent);
            nodes.push(Node::Line);
        }
        nodes.push(Node::text(")"));
    }
}

impl Ast for ast::StructMember {
    fn push_nodes<'a>(&'a self, source: &'a str, nodes: &mut Vec<Node<'a>>) {
        match &self.0 {
            inner::StructMember::Data(name, ty) => {
                nodes.push(Node::text(name.as_str()));
                nodes.push(Node::text(" "));
                ty.push_nodes(source, nodes);
            }
        }
    }
}
