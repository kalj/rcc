use crate::ast::AstContext;
use crate::ast::{BlockItem, Declaration, Expression, Function, FunctionParameter, Program, Statement, ToplevelItem};
use std::collections::HashMap;

pub struct ValidationError {
    pub message: String,
    pub position: usize,
    pub length: usize,
}

impl ValidationError {
    fn new(message: String, ctx: &AstContext) -> ValidationError {
        ValidationError { message, position: ctx.position, length: ctx.length }
    }
}

struct Func {
    nparam: usize,
    defined: bool,
}

struct Validator {
    errors: Vec<ValidationError>,
    function_map: HashMap<String, Func>,
    globals_map: HashMap<String, bool>,
}

impl Validator {
    fn new() -> Validator {
        Validator { errors: Vec::new(), function_map: HashMap::new(), globals_map: HashMap::new() }
    }

    fn validate_expression(&mut self, expr: &Expression) {
        match expr {
            Expression::Assign(_, _, expr, _) => self.validate_expression(expr),
            Expression::BinaryOp(_, e1, e2) => {
                self.validate_expression(e1);
                self.validate_expression(e2);
            }
            Expression::UnaryOp(_, expr) => self.validate_expression(expr),
            Expression::Conditional(e1, e2, e3) => {
                self.validate_expression(e1);
                self.validate_expression(e2);
                self.validate_expression(e3);
            }
            Expression::FunctionCall(name, args, ctx) => {
                for arg in args {
                    self.validate_expression(arg);
                }

                if !self.function_map.contains_key(name) {
                    self.errors.push(ValidationError::new(format!("Missing declaration of function '{}'", name), ctx));
                } else if self.function_map[name].nparam != args.len() {
                    self.errors.push(ValidationError::new(format!("Too many arguments to function '{}'", name), ctx));
                }
            }
            _ => {}
        }
    }

    fn validate_statement(&mut self, stmt: &Statement) {
        match stmt {
            Statement::Return(expr) => self.validate_expression(expr),
            Statement::Expr(expr) => self.validate_expression(expr),
            Statement::If(cond, ifbody, elsebody) => {
                self.validate_expression(cond);
                self.validate_statement(ifbody);
                if let Some(eb) = elsebody {
                    self.validate_statement(eb);
                }
            }
            Statement::Compound(bkitems) => self.validate_block_items(bkitems),
            Statement::For(initexpr, cond, postexpr, body) => {
                if let Some(ie) = initexpr {
                    self.validate_expression(ie);
                }
                self.validate_expression(cond);
                if let Some(pe) = postexpr {
                    self.validate_expression(pe);
                }
                self.validate_statement(body);
            }
            Statement::ForDecl(decl, cond, postexpr, body) => {
                self.validate_declaration(decl);
                self.validate_expression(cond);
                if let Some(pe) = postexpr {
                    self.validate_expression(pe);
                }
                self.validate_statement(body);
            }
            Statement::While(cond, body) => {
                self.validate_expression(cond);
                self.validate_statement(body);
            }
            Statement::DoWhile(body, cond) => {
                self.validate_statement(body);
                self.validate_expression(cond);
            }
            _ => {}
        }
    }

    fn validate_declaration(&mut self, decl: &Declaration) {
        if let Some(expr) = &decl.init {
            self.validate_expression(&expr);
        }
    }

    fn validate_block_items(&mut self, bkitems: &[BlockItem]) {
        for bkitem in bkitems {
            match bkitem {
                BlockItem::Stmt(stmt) => {
                    self.validate_statement(&stmt);
                }
                BlockItem::Decl(decl) => {
                    self.validate_declaration(&decl);
                }
            }
        }
    }

    fn validate_function_declaration(&mut self, id: &str, parameters: &[FunctionParameter], ctx: &AstContext) {
        let nparam = parameters.len();

        if self.globals_map.contains_key(id) {
            self.errors.push(ValidationError::new(format!("Global variable redeclared as function '{}'", id), ctx));
        }

        for i in 1..nparam {
            for j in 0..i {
                if parameters[i].id == parameters[j].id {
                    self.errors.push(ValidationError::new(
                        format!("Redefinition of parameter {}", parameters[i].id),
                        &parameters[i].ctx,
                    ));
                }
            }
        }

        if self.function_map.contains_key(id) {
            let f = &self.function_map[id];

            // check for different number of parameters
            if f.nparam != nparam {
                self.errors.push(ValidationError::new(
                    format!(
                        "Multiple conflicting declarations for {}, with {} and {} parameters",
                        id, f.nparam, nparam
                    ),
                    ctx,
                ));
            }
        }
    }

    fn validate_function(&mut self, func: &Function) {
        match func {
            Function::Declaration(id, parameters, ctx) => {
                self.validate_function_declaration(id, parameters, ctx);

                if !self.function_map.contains_key(id) {
                    self.function_map.insert(id.to_string(), Func { nparam: parameters.len(), defined: false });
                }
            }
            Function::Definition(id, parameters, body, ctx) => {
                self.validate_function_declaration(id, parameters, ctx);

                if self.function_map.contains_key(id) {
                    let f = &self.function_map[id];

                    // check if already defined
                    if f.defined {
                        self.errors.push(ValidationError::new(format!("Redefinition of '{}'", id), ctx));
                    } else {
                        self.function_map.get_mut(id).unwrap().defined = true;
                    }
                } else {
                    self.function_map.insert(id.to_string(), Func { nparam: parameters.len(), defined: true });
                }

                self.validate_block_items(body);
            }
        }
    }

    fn validate_global_declaration(&mut self, decl: &Declaration) {
        let Declaration { id, init, ctx } = decl;

        if self.function_map.contains_key(id) {
            self.errors.push(ValidationError::new(format!("Function redeclared as global variable '{}'", id), ctx));
        }

        if let Some(expr) = init {
            if let Expression::Constant(_) = expr {
                if self.globals_map.contains_key(id) && self.globals_map[id] {
                    self.errors.push(ValidationError::new(format!("Redefinition of global variable '{}'", id), ctx));
                } else {
                    self.globals_map.insert(id.to_string(), true);
                }
            } else {
                self.errors.push(ValidationError::new(format!("Non-constant initializer for global '{}'", id), ctx));
            }
        } else {
            if !self.globals_map.contains_key(id) {
                self.globals_map.insert(id.to_string(), false);
            }
        }
    }

    fn validate_program(&mut self, prog: &Program) {
        let Program::Prog(toplevel_items) = prog;

        for item in toplevel_items {
            match item {
                ToplevelItem::Function(func) => self.validate_function(func),
                ToplevelItem::Variable(decl) => self.validate_global_declaration(decl),
            }
        }
    }
}

pub fn validate(prog: &Program) -> Vec<ValidationError> {
    let mut val = Validator::new();

    val.validate_program(prog);

    val.errors
}
