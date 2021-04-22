use crate::{
  ast::{
    AstContext,
    BasicType,
    BlockItem,
    Declaration,
    Expression,
    Function,
    FunctionParameters,
    Program,
    Statement,
    ToplevelItem,
    Type,
  },
  evaluation::{
    expression_type,
    is_constant_expression,
    is_lvalue_expression,
    TypeError,
  },
  symbol_table::{
    FunctionSymbol,
    GlobalVariableSymbol,
    LocalVariableSymbol,
    SymbolTable,
  },
};
use std::cmp::Ordering;

pub struct ValidationError {
  pub message: String,
  pub position: usize,
  pub length: usize,
}

impl ValidationError {
  fn new(message: String, ctx: &AstContext) -> ValidationError {
    ValidationError {
      message,
      position: ctx.position,
      length: ctx.length,
    }
  }

  fn from_type_error(terr: &TypeError) -> ValidationError {
    ValidationError {
      message: terr.message.to_string(),
      position: terr.position,
      length: terr.length,
    }
  }
}

struct Validator {
  errors: Vec<ValidationError>,
  current_rettype: Option<Type>,
  symtab: SymbolTable,
}

impl Validator {
  fn new() -> Validator {
    Validator {
      errors: Vec::new(),
      current_rettype: None,
      symtab: SymbolTable::new(),
    }
  }

  fn new_error(&mut self, msg: String, ctx: &AstContext) {
    self.errors.push(ValidationError::new(msg, ctx));
  }

  fn validate_expression(&mut self, expr: &Expression) {
    match expr {
      Expression::Assign(_, lhs, rhs, ctx) => {
        self.validate_expression(lhs);
        if !is_lvalue_expression(lhs, &self.symtab) {
          self.new_error("Left hand side of assignment must be lvalue".to_string(), ctx);
        }

        match expression_type(rhs, &self.symtab) {
          Ok(rhs_typ) => match expression_type(lhs, &self.symtab) {
            Ok(lhs_typ) => {
              if lhs_typ != rhs_typ {
                self.new_error(
                  format!("Invalid assignment. Type of lhs ({}) and rhs ({}) are different", lhs_typ, rhs_typ),
                  ctx,
                );
              }
            },
            Err(e) => self.errors.push(ValidationError::from_type_error(&e)),
          },
          Err(e) => self.errors.push(ValidationError::from_type_error(&e)),
        }

        self.validate_expression(rhs)
      },
      Expression::BinaryOp(_, e1, e2, _) => {
        self.validate_expression(e1);
        self.validate_expression(e2);
      },
      Expression::UnaryOp(_, expr, _) => self.validate_expression(expr),
      Expression::Conditional(e1, e2, e3, _) => {
        self.validate_expression(e1);
        self.validate_expression(e2);
        self.validate_expression(e3);
      },
      Expression::FunctionCall(name, args, ctx) => {
        for arg in args {
          self.validate_expression(arg);
        }

        if let Some(func) = self.symtab.get_function(name) {
          match &func.params {
            None => {},
            Some(params) => {
              // check for mismatch in number of arguments
              match params.len().cmp(&args.len()) {
                Ordering::Less => {
                  self.new_error(format!("Too many arguments to function '{}'", name), ctx);
                },
                Ordering::Greater => {
                  self.new_error(format!("Too few arguments to function '{}'", name), ctx);
                },
                _ => {},
              }

              // check for mismatch in type of arguments
              for (arg, param) in args.iter().zip(params.iter()) {
                match expression_type(arg, &self.symtab) {
                  Ok(argtyp) => {
                    if argtyp != param.typ {
                      let paramid = if let Some(id) = &param.id { id.to_string() } else { "<unnamed>".to_string() };
                      self.new_error(
                        format!("Expected type '{}' for parameter '{}', type '{}' passed", param.typ, paramid, argtyp),
                        &param.ctx,
                      );
                    }
                  },
                  Err(e) => self.errors.push(ValidationError::from_type_error(&e)),
                }
              }
            },
          }
        } else {
          self.new_error(format!("Missing declaration of function '{}'", name), ctx);
        }
      },
      _ => {},
    }
  }

  fn validate_statement(&mut self, stmt: &Statement) {
    match stmt {
      Statement::Return(maybe_expr, ctx) => {
        match self.current_rettype.as_ref().unwrap() {
          Type::Basic(BasicType::Void) => {
            if maybe_expr.is_some() {
              self.new_error("Return with value in void function".to_string(), ctx);
            }
          },
          _ => {
            if maybe_expr.is_none() {
              self.new_error("Return without value in non-void function".to_string(), ctx);
            }
          },
        }

        if let Some(expr) = maybe_expr {
          self.validate_expression(expr)
        }
      },

      Statement::Expr(expr) => self.validate_expression(expr),
      Statement::If(cond, ifbody, elsebody) => {
        self.validate_expression(cond);
        self.validate_statement(ifbody);
        if let Some(eb) = elsebody {
          self.validate_statement(eb);
        }
      },
      Statement::Compound(bkitems) => {
        self.symtab.new_scope();
        self.validate_block_items(bkitems);
        self.symtab.end_scope();
      },
      Statement::For(initexpr, cond, postexpr, body) => {
        if let Some(ie) = initexpr {
          self.validate_expression(ie);
        }
        self.validate_expression(cond);
        if let Some(pe) = postexpr {
          self.validate_expression(pe);
        }
        self.validate_statement(body);
      },
      Statement::ForDecl(decl, cond, postexpr, body) => {
        self.symtab.new_scope();
        self.validate_declaration(decl);
        self.validate_expression(cond);
        if let Some(pe) = postexpr {
          self.validate_expression(pe);
        }
        self.validate_statement(body);
        self.symtab.end_scope();
      },
      Statement::While(cond, body) => {
        self.validate_expression(cond);
        self.validate_statement(body);
      },
      Statement::DoWhile(body, cond) => {
        self.validate_statement(body);
        self.validate_expression(cond);
      },
      _ => {},
    }
  }

  fn validate_declaration(&mut self, decl: &Declaration) {
    if match &decl.typ {
      Type::Basic(BasicType::Void) => true,
      Type::Basic(BasicType::Int) => false,
      Type::Ptr(tt) => match **tt {
        Type::Basic(BasicType::Int) => false,
        _ => true,
      },
    } {
      self.new_error(
        format!("Bad declaration for {}. Variables can only have type 'int' or 'int*'", decl.id),
        &decl.ctx,
      );
    }

    self.symtab.insert_local(&decl.id, LocalVariableSymbol::new(&decl.typ));

    if let Some(init_expr) = &decl.init {
      match expression_type(init_expr, &self.symtab) {
        Ok(init_typ) => {
          if decl.typ != init_typ {
            self.new_error(
              format!("Invalid declaration. Type of lhs ({}) and rhs ({}) are different", decl.typ, init_typ),
              &decl.ctx,
            );
          }
        },
        Err(e) => self.errors.push(ValidationError::from_type_error(&e)),
      }

      self.validate_expression(&init_expr);
    }
  }

  fn validate_block_items(&mut self, bkitems: &[BlockItem]) {
    for bkitem in bkitems {
      match bkitem {
        BlockItem::Stmt(stmt) => {
          self.validate_statement(&stmt);
        },
        BlockItem::Decl(decl) => {
          self.validate_declaration(&decl);
        },
      }
    }
  }

  fn validate_function_declaration(&mut self, id: &str, func: &FunctionSymbol) {
    if self.symtab.get_global(id).is_some() {
      self.new_error(format!("Global variable redeclared as function '{}'", id), &func.ctx);
    }

    if let Some(params) = &func.params {
      // Check for multiple void or named void parameter
      let mut voidcount = 0;
      for p in params {
        if let Type::Basic(BasicType::Void) = p.typ {
          voidcount += 1;
          if voidcount > 1 {
            self.new_error("Only a single void parameter is allowed".to_string(), &p.ctx);
          }

          if let Some(id) = &p.id {
            self.new_error(format!("Parameter {} has incomplete type 'void'", id), &p.ctx);
          }
        }
      }

      // Check for repeated parameter names
      for i1 in 1..params.len() {
        if let Some(id1) = &params[i1].id {
          for p2 in params.iter().take(i1) {
            if let Some(id2) = &p2.id {
              if id1 == id2 {
                self.new_error(format!("Redefinition of parameter {}", id1), &p2.ctx);
              }
            }
          }
        }
      }
    }

    if let Some(old_func) = self.symtab.get_function(id) {
      // check for different return types
      if old_func.ret != func.ret {
        let msg = format!(
          "Multiple conflicting declarations for {}, with return types {} and {}",
          id, old_func.ret, func.ret
        );
        self.new_error(msg, &func.ctx);
      }

      // check for different number or type of parameters
      if let Some(old_params) = &old_func.params {
        if let Some(params) = &func.params {
          if params.len() != old_params.len() {
            let msg = format!("Declaration for {} conflicts with previous declaration; different number of parameters", id);
            self.new_error(msg, &func.ctx);
          } else {
            for (pold, pnew) in old_params.iter().zip(params.iter()) {
              if pold.typ != pnew.typ {
                let msg = format!("Declaration for {} conflicts with previous declaration; mismatching parameter type", id);
                self.new_error(msg, &pnew.ctx);
              }
            }
          }
        }
      }
    }
  }

  fn validate_function(&mut self, func: &Function) {
    match func {
      Function::Declaration(rettyp, id, parameters, ctx) => {
        let new_fdecl = FunctionSymbol::new(rettyp, parameters, false, ctx);

        self.validate_function_declaration(id, &new_fdecl);

        if let Some(func) = self.symtab.get_function(id) {
          if !func.has_definition && !matches!(parameters, FunctionParameters::Unspecified) {
            // update parameters if not defined
            self.symtab.insert_function(id, new_fdecl);
          }
        } else {
          self.symtab.insert_function(id, new_fdecl);
        }
      },
      Function::Definition(rettyp, id, parameters, body, ctx) => {
        let new_fdecl = FunctionSymbol::new(rettyp, parameters, true, ctx);

        if let Some(params) = &new_fdecl.params {
          for param in params {
            if param.id.is_none() {
              self.new_error(format!("Missing parameter name of function '{}'", id), &param.ctx);
            }
          }
        }

        self.validate_function_declaration(id, &new_fdecl);

        self.symtab.new_scope();

        if let Some(params) = &new_fdecl.params {
          for param in params {
            if let Some(id) = &param.id {
              self.symtab.insert_local(id, LocalVariableSymbol::new(&param.typ));
            }
          }
        }

        if let Some(f) = self.symtab.get_function(id) {
          // check if already defined
          if f.has_definition {
            self.new_error(format!("Redefinition of '{}'", id), ctx);
          } else {
            self.symtab.insert_function(id, new_fdecl);
          }
        } else {
          self.symtab.insert_function(id, new_fdecl);
        }

        self.current_rettype = Some(rettyp.clone());

        self.validate_block_items(body);

        self.current_rettype = None;
        self.symtab.end_scope();
      },
    }
  }

  fn validate_global_declaration(&mut self, decl: &Declaration) {
    let Declaration {
      id,
      init,
      ctx,
      typ,
    } = decl;

    if self.symtab.get_function(id).is_some() {
      self.new_error(format!("Function redeclared as global variable '{}'", id), ctx);
    }

    if let Some(expr) = init {
      match expression_type(expr, &self.symtab) {
        Ok(init_typ) => {
          if typ != &init_typ {
            self.new_error(
              format!("Invalid global declaration. Type of lhs ({}) and rhs ({}) are different", typ, init_typ),
              &decl.ctx,
            );
          }
        },
        Err(e) => self.errors.push(ValidationError::from_type_error(&e)),
      }

      if !is_constant_expression(expr, &self.symtab) {
        self.new_error(format!("Non-constant initializer element for global '{}'", id), ctx);
      }

      if let Some(glob) = self.symtab.get_global(id) {
        if glob.has_definition {
          self.new_error(format!("Redefinition of global variable '{}'", id), ctx);
        }
      } else {
        self.symtab.insert_global(id, GlobalVariableSymbol::new(typ, true, &ctx));
      }
    } else if !self.symtab.contains(id) {
      self.symtab.insert_global(id, GlobalVariableSymbol::new(typ, false, &ctx));
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
