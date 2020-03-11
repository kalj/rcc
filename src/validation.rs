use crate::ast::AstContext;
use crate::ast::{BlockItem, Declaration, Expression, Function, FunctionParameter, Program, Statement};
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
}

impl Validator {
    fn new() -> Validator {
        Validator { errors: Vec::new() }
    }

    fn validate_expression(&mut self, expr: &Expression, fmap: &HashMap<String, Func>) {
        match expr {
            Expression::Assign(_, _, expr, _) => self.validate_expression(expr, fmap),
            Expression::BinaryOp(_, e1, e2) => {
                self.validate_expression(e1, fmap);
                self.validate_expression(e2, fmap);
            }
            Expression::UnaryOp(_, expr) => self.validate_expression(expr, fmap),
            Expression::Conditional(e1, e2, e3) => {
                self.validate_expression(e1, fmap);
                self.validate_expression(e2, fmap);
                self.validate_expression(e3, fmap);
            }
            Expression::FunctionCall(name, args, ctx) => {
                for arg in args {
                    self.validate_expression(arg, fmap);
                }

                if !fmap.contains_key(name) {
                    self.errors.push(ValidationError::new(format!("Missing declaration of function '{}'", name), ctx));
                } else if fmap[name].nparam != args.len() {
                    self.errors.push(ValidationError::new(format!("Too many arguments to function '{}'", name), ctx));
                }
            }
            _ => {}
        }
    }

    fn validate_statement(&mut self, stmt: &Statement, fmap: &HashMap<String, Func>) {
        match stmt {
            Statement::Return(expr) => self.validate_expression(expr, fmap),
            Statement::Expr(expr) => self.validate_expression(expr, fmap),
            Statement::If(cond, ifbody, elsebody) => {
                self.validate_expression(cond, fmap);
                self.validate_statement(ifbody, fmap);
                if let Some(eb) = elsebody {
                    self.validate_statement(eb, fmap);
                }
            }
            Statement::Compound(bkitems) => self.validate_block_items(bkitems, fmap),
            Statement::For(initexpr, cond, postexpr, body) => {
                if let Some(ie) = initexpr {
                    self.validate_expression(ie, fmap);
                }
                self.validate_expression(cond, fmap);
                if let Some(pe) = postexpr {
                    self.validate_expression(pe, fmap);
                }
                self.validate_statement(body, fmap);
            }
            Statement::ForDecl(decl, cond, postexpr, body) => {
                self.validate_declaration(decl, fmap);
                self.validate_expression(cond, fmap);
                if let Some(pe) = postexpr {
                    self.validate_expression(pe, fmap);
                }
                self.validate_statement(body, fmap);
            }
            Statement::While(cond, body) => {
                self.validate_expression(cond, fmap);
                self.validate_statement(body, fmap);
            }
            Statement::DoWhile(body, cond) => {
                self.validate_statement(body, fmap);
                self.validate_expression(cond, fmap);
            }
            _ => {}
        }
    }

    fn validate_declaration(&mut self, decl: &Declaration, fmap: &HashMap<String, Func>) {
        if let Some(expr) = &decl.init {
            self.validate_expression(&expr, fmap);
        }
    }

    fn validate_block_items(&mut self, bkitems: &[BlockItem], fmap: &HashMap<String, Func>) {
        for bkitem in bkitems {
            match bkitem {
                BlockItem::Stmt(stmt) => {
                    self.validate_statement(&stmt, fmap);
                }
                BlockItem::Decl(decl) => {
                    self.validate_declaration(&decl, fmap);
                }
            }
        }
    }

    fn validate_function_declaration(
        &mut self,
        id: &str,
        parameters: &[FunctionParameter],
        fmap: &HashMap<String, Func>,
        ctx: &AstContext,
    ) {
        let nparam = parameters.len();

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

        if fmap.contains_key(id) {
            let f = &fmap[id];

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

    fn validate(&mut self, prog: &Program) {
        let mut function_map = HashMap::<String, Func>::new();

        let Program::Prog(funcs) = prog;

        for func in funcs {
            match func {
                Function::Declaration(id, parameters, ctx) => {
                    self.validate_function_declaration(id, parameters, &function_map, ctx);

                    if !function_map.contains_key(id) {
                        function_map.insert(id.to_string(), Func { nparam: parameters.len(), defined: false });
                    }
                }
                Function::Definition(id, parameters, body, ctx) => {
                    self.validate_function_declaration(id, parameters, &function_map, ctx);

                    if function_map.contains_key(id) {
                        let f = &function_map[id];

                        // check if already defined
                        if f.defined {
                            self.errors.push(ValidationError::new(format!("Redefinition of {}", id), ctx));
                        } else {
                            function_map.get_mut(id).unwrap().defined = true;
                        }
                    } else {
                        function_map.insert(id.to_string(), Func { nparam: parameters.len(), defined: true });
                    }

                    self.validate_block_items(body, &function_map);
                }
            }
        }
    }
}

pub fn validate(prog: &Program) -> Vec<ValidationError> {
    let mut val = Validator::new();

    val.validate(prog);

    val.errors
}
