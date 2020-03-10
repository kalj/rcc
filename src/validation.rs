use std::error;
use std::fmt;

use std::collections::HashMap;

use crate::ast::{BlockItem, Declaration, Expression, Function, Program, Statement};

#[derive(Debug, Clone)]
pub struct ValidationError {
    pub message: String,
}

impl ValidationError {
    fn new(message: String) -> ValidationError {
        ValidationError { message }
    }
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ValidationError: {}", self.message)
    }
}

impl error::Error for ValidationError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
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
            Expression::Assign(_, _, expr) => self.validate_expression(expr, fmap),
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
            Expression::FunctionCall(name, args) => {
                for arg in args {
                    self.validate_expression(arg, fmap);
                }

                if !fmap.contains_key(name) {
                    self.errors.push(ValidationError::new(format!("Missing declaration of function '{}'", name)));
                } else {
                    let f = &fmap[name];

                    if f.nparam != args.len() {
                        self.errors.push(ValidationError::new(format!("Too many arguments to function '{}'", name)));
                    }
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

    fn validate_block_items(&mut self, bkitems: &Vec<BlockItem>, fmap: &HashMap<String, Func>) {
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

    fn validate(&mut self, prog: &Program) -> Result<(), ValidationError> {
        let mut function_map = HashMap::<String, Func>::new();

        let Program::Prog(funcs) = prog;

        for func in funcs {
            match func {
                Function::Declaration(id, parameters) => {
                    let nparam = parameters.len();
                    if function_map.contains_key(id) {
                        let f = &function_map[id];

                        // check for different number of parameters
                        if f.nparam != nparam {
                            self.errors.push(ValidationError::new(format!(
                                "Multiple conflicting declarations for {}, with {} and {} parameters",
                                id, f.nparam, nparam
                            )));
                        }
                    } else {
                        function_map.insert(id.to_string(), Func { nparam, defined: false });
                    }
                }
                Function::Definition(id, parameters, body) => {
                    let nparam = parameters.len();
                    if function_map.contains_key(id) {
                        let f = &function_map[id];

                        // check for different number of parameters
                        if f.nparam != nparam {
                            self.errors.push(ValidationError::new(format!(
                                "Multiple conflicting declarations for {}, with {} and {} parameters",
                                id, f.nparam, nparam
                            )));
                        }

                        // check if already defined
                        if f.defined {
                            self.errors.push(ValidationError::new(format!("Redefinition of {}", id)));
                        } else {
                            function_map.get_mut(id).unwrap().defined = true;
                        }
                    } else {
                        function_map.insert(id.to_string(), Func { nparam, defined: true });
                    }

                    self.validate_block_items(body, &function_map);
                }
            }
        }

        if !self.errors.is_empty() {
            let messages: Vec<String> = self.errors.iter().map(|e| e.message.clone()).collect();
            Err(ValidationError::new(messages.join("\n")))
        } else {
            Ok(())
        }
    }
}

pub fn validate(prog: &Program) -> Result<(), ValidationError> {
    let mut val = Validator::new();

    val.validate(prog)
}
