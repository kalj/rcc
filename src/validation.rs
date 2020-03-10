use crate::ast::AstItem;
use crate::ast::{BlockItem, Declaration, Expression, Function, Program, Statement};
use std::collections::HashMap;

pub struct ValidationError {
    pub message: String,
    pub position: usize,
    pub length: usize,
}

impl ValidationError {
    fn new<T>(message: String, item: &AstItem<T>) -> ValidationError {
        ValidationError { message, position: item.position, length: item.length }
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

                if !fmap.contains_key(&name.item) {
                    self.errors
                        .push(ValidationError::new(format!("Missing declaration of function '{}'", name.item), name));
                } else if fmap[&name.item].nparam != args.len() {
                    self.errors
                        .push(ValidationError::new(format!("Too many arguments to function '{}'", name.item), name));
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
        id: &AstItem<String>,
        parameters: &[AstItem<String>],
        fmap: &HashMap<String, Func>,
    ) {
        let nparam = parameters.len();

        for i in 1..nparam {
            for j in 0..i {
                if parameters[i].item == parameters[j].item {
                    self.errors.push(ValidationError::new(
                        format!("Redefinition of parameter {}", parameters[i].item),
                        &parameters[i],
                    ));
                }
            }
        }

        if fmap.contains_key(&id.item) {
            let f = &fmap[&id.item];

            // check for different number of parameters
            if f.nparam != nparam {
                self.errors.push(ValidationError::new(
                    format!(
                        "Multiple conflicting declarations for {}, with {} and {} parameters",
                        id.item, f.nparam, nparam
                    ),
                    &id,
                ));
            }
        }
    }

    fn validate(&mut self, prog: &Program) {
        let mut function_map = HashMap::<String, Func>::new();

        let Program::Prog(funcs) = prog;

        for func in funcs {
            match func {
                Function::Declaration(id, parameters) => {
                    self.validate_function_declaration(id, parameters, &function_map);

                    if !function_map.contains_key(&id.item) {
                        function_map.insert(id.item.to_string(), Func { nparam: parameters.len(), defined: false });
                    }
                }
                Function::Definition(id, parameters, body) => {
                    self.validate_function_declaration(id, parameters, &function_map);

                    if function_map.contains_key(&id.item) {
                        let f = &function_map[&id.item];

                        // check if already defined
                        if f.defined {
                            self.errors.push(ValidationError::new(format!("Redefinition of {}", id.item), id));
                        } else {
                            function_map.get_mut(&id.item).unwrap().defined = true;
                        }
                    } else {
                        function_map.insert(id.item.to_string(), Func { nparam: parameters.len(), defined: true });
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
