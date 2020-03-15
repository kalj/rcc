use crate::ast::params_to_string;
use crate::ast::AstContext;
use crate::ast::{
    BlockItem, Declaration, Expression, Function, FunctionParameter, FunctionParameters, Program, Statement,
    ToplevelItem, Type,
};
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

#[derive(Clone)]
struct Func {
    params: Option<Vec<FunctionParameter>>,
    ret: Type,
    has_definition: bool,
    ctx: AstContext,
}

impl Func {
    fn new(ret: &Type, fparams: &FunctionParameters, has_def: bool, ctx: &AstContext) -> Func {
        let params = match fparams {
            FunctionParameters::Void => Some(Vec::new()),
            FunctionParameters::List(l) => Some(l.clone()),
            FunctionParameters::Unspecified => {
                if has_def {
                    Some(Vec::new())
                } else {
                    None
                }
            }
        };
        Func { ret: ret.clone(), params: params, has_definition: has_def, ctx: ctx.clone() }
    }
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

    fn new_error(&mut self, msg: String, ctx: &AstContext) {
        self.errors.push(ValidationError::new(msg, ctx));
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
                    self.new_error(format!("Missing declaration of function '{}'", name), ctx);
                } else {
                    match &self.function_map[name].params {
                        None => {}
                        Some(params) => {
                            if params.len() != args.len() {
                                self.new_error(format!("Too many arguments to function '{}'", name), ctx);
                            }
                        }
                    }
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
        if let Type::Void = decl.typ {
            self.new_error(format!("Variable '{}' declared as void", decl.id), &decl.ctx);
        }

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

    fn validate_function_declaration(&mut self, id: &str, func: &Func) {
        if self.globals_map.contains_key(id) {
            self.new_error(format!("Global variable redeclared as function '{}'", id), &func.ctx);
        }

        // Check for repeated parameter names
        if let Some(params) = &func.params {
            let nparam = params.len();
            for i1 in 1..nparam {
                if let Some(id1) = &params[i1].id {
                    for i2 in 0..i1 {
                        if let Some(id2) = &params[i2].id {
                            if id1 == id2 {
                                self.new_error(format!("Redefinition of parameter {}", id1), &func.ctx);
                            }
                        }
                    }
                }
            }
        }

        if self.function_map.contains_key(id) {
            let old_func = self.function_map[id].clone();

            // check for different return types
            if old_func.ret != func.ret {
                let msg = format!(
                    "Multiple conflicting declarations for {}, with return types {} and {}",
                    id, old_func.ret, func.ret
                );
                self.new_error(msg, &func.ctx);
            }

            // check for different number of parameters
            if let Some(old_params) = &old_func.params {
                if let Some(params) = &func.params {
                    if params.len() != old_params.len() {
                        let msg = format!(
                            "Multiple conflicting declarations for {}, with parameters ({}) and ({})",
                            id,
                            params_to_string(&old_params),
                            params_to_string(&params)
                        );
                        self.new_error(msg, &func.ctx);
                    }
                }
            }
        }
    }

    fn validate_function(&mut self, func: &Function) {
        match func {
            Function::Declaration(rettyp, id, parameters, ctx) => {
                let new_fdecl = Func::new(rettyp, parameters, false, ctx);

                self.validate_function_declaration(id, &new_fdecl);

                if self.function_map.contains_key(id) && !self.function_map[id].has_definition {
                    // update parameters if not defined
                    if let FunctionParameters::Unspecified = parameters {
                    } else {
                        self.function_map.insert(id.to_string(), new_fdecl);
                    }
                } else {
                    self.function_map.insert(id.to_string(), new_fdecl);
                }
            }
            Function::Definition(rettyp, id, parameters, body, ctx) => {
                if let FunctionParameters::List(params) = parameters {
                    for param in params {
                        if param.id.is_none() {
                            self.new_error(format!("Missing parameter name of function '{}'", id), &param.ctx);
                        }
                    }
                }

                let new_fdecl = Func::new(rettyp, parameters, true, ctx);
                self.validate_function_declaration(id, &new_fdecl);

                if self.function_map.contains_key(id) {
                    let f = &self.function_map[id];

                    // check if already defined
                    if f.has_definition {
                        self.new_error(format!("Redefinition of '{}'", id), ctx);
                    } else {
                        self.function_map.insert(id.to_string(), new_fdecl);
                    }
                } else {
                    self.function_map.insert(id.to_string(), new_fdecl);
                }

                self.validate_block_items(body);
            }
        }
    }

    fn validate_global_declaration(&mut self, decl: &Declaration) {
        let Declaration { id, init, ctx, .. } = decl;

        if self.function_map.contains_key(id) {
            self.new_error(format!("Function redeclared as global variable '{}'", id), ctx);
        }

        if let Some(expr) = init {
            if let Expression::Constant(_) = expr {
                if self.globals_map.contains_key(id) && self.globals_map[id] {
                    self.new_error(format!("Redefinition of global variable '{}'", id), ctx);
                } else {
                    self.globals_map.insert(id.to_string(), true);
                }
            } else {
                self.new_error(format!("Non-constant initializer for global '{}'", id), ctx);
            }
        } else if !self.globals_map.contains_key(id) {
            self.globals_map.insert(id.to_string(), false);
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
