use crate::{
  ast::{
    AstContext,
    BasicType,
    BinaryOp,
    Expression,
    Type,
    UnaryOp,
  },
  symbol_table::SymbolTable,
};

#[derive(Debug)]
pub struct TypeError {
  pub message: String,
  pub position: usize,
  pub length: usize,
}

impl TypeError {
  fn new(message: String, ctx: &AstContext) -> TypeError {
    TypeError {
      message,
      position: ctx.position,
      length: ctx.length,
    }
  }
}

pub fn expression_type(expr: &Expression, symtab: &SymbolTable) -> Result<Type, TypeError> {
  match expr {
    Expression::Variable(id, ctx) => {
      if let Some(typ) = symtab.get_variable_type(id) {
        Ok(typ)
      } else {
        Err(TypeError::new("Failed getting type of variable".to_string(), &ctx))
      }
    },
    Expression::UnaryOp(uop, operand, ctx) => match uop {
      UnaryOp::Negate | UnaryOp::Not | UnaryOp::Complement => {
        let optyp = expression_type(operand, symtab)?;
        match optyp {
          Type::Basic(BasicType::Int) => Ok(optyp),
          _ => Err(TypeError::new("Arithmetic is only supported for 'int' type".to_string(), ctx)),
        }
      },
      UnaryOp::AddressOf => Ok(Type::Ptr(Box::new(expression_type(operand, symtab)?))),
      UnaryOp::Indirection => match expression_type(operand, symtab)? {
        Type::Ptr(t) => Ok(*t),
        _ => Err(TypeError::new("Dereference of non-pointer".to_string(), ctx)),
      },
    },
    Expression::Constant(_) => Ok(Type::Basic(BasicType::Int)),
    Expression::BinaryOp(_, e1, e2, ctx) => {
      let t1 = expression_type(e1, symtab)?;
      let t2 = expression_type(e2, symtab)?;
      if !matches!(t1, Type::Basic(BasicType::Int)) || !matches!(t2, Type::Basic(BasicType::Int)) {
        Err(TypeError::new("Arithmetic only supported for 'int' type".to_string(), ctx))
      } else {
        Ok(Type::Basic(BasicType::Int))
      }
    },
    Expression::PrefixOp(_, operand, _) => expression_type(operand, symtab),
    Expression::PostfixOp(_, operand, _) => expression_type(operand, symtab),
    Expression::Assign(_, _, rhs, _) => expression_type(rhs, symtab),
    Expression::Conditional(_, ifexpr, elseexpr, ctx) => {
      let tif = expression_type(ifexpr, symtab)?;
      let telse = expression_type(elseexpr, symtab)?;
      if !matches!(tif, Type::Basic(BasicType::Int)) || !matches!(telse, Type::Basic(BasicType::Int)) {
        Err(TypeError::new("Conditional operator only supported for 'int' type".to_string(), ctx))
      } else {
        Ok(Type::Basic(BasicType::Int))
      }
    },
    Expression::FunctionCall(id, _, ctx) => {
      if let Some(func) = symtab.get_function(id) {
        Ok(func.ret)
      } else {
        Err(TypeError::new("No such function".to_string(), ctx))
      }
    },
  }
}

pub fn is_lvalue_expression(expr: &Expression, symtab: &SymbolTable) -> bool {
  match expr {
    Expression::Variable(_, _) => true,
    Expression::UnaryOp(uop, operand, _) => {
      match uop {
        // UnaryOp::Indirection => match self.expression_type(operand) {
        //     Type::Ptr(_) => true,
        //     _ => false
        // }
        UnaryOp::Indirection => {
          if let Expression::Variable(id, _) = &**operand {
            let typ = symtab.get_variable_type(id).unwrap();
            matches!(typ, Type::Ptr(_))
          } else {
            false
          }
        },
        UnaryOp::Negate | UnaryOp::Not | UnaryOp::Complement | UnaryOp::AddressOf => false,
      }
    },
    Expression::Constant(_)
    | Expression::BinaryOp(_, _, _, _)
    | Expression::PrefixOp(_, _, _)
    | Expression::PostfixOp(_, _, _)
    | Expression::Assign(_, _, _, _)
    | Expression::Conditional(_, _, _, _)
    | Expression::FunctionCall(_, _, _) => false,
  }
}

pub fn is_constant_expression(expr: &Expression, symtab: &SymbolTable) -> bool {
  match expr {
    Expression::Constant(_) => true,
    Expression::Variable(_, _) => false,
    Expression::UnaryOp(uop, operand, _) => match uop {
      UnaryOp::Indirection => false,
      UnaryOp::Negate | UnaryOp::Not | UnaryOp::Complement => is_constant_expression(operand, symtab),
      UnaryOp::AddressOf => {
        if is_lvalue_expression(operand, symtab) {
          match &**operand {
            Expression::Variable(id, _) => symtab.has_static_storage(&id),
            _ => false,
          }
        } else {
          false
        }
      },
    },
    Expression::BinaryOp(BinaryOp::LogicalOr, e1, e2, _) => {
      if !is_constant_expression(e1, symtab) {
        false
      } else {
        let v1 = evaluate_const_int_expression(e1);
        if v1 != 0 { true } else { is_constant_expression(e2, symtab) }
      }
    },
    Expression::BinaryOp(BinaryOp::LogicalAnd, e1, e2, _) => {
      if !is_constant_expression(e1, symtab) {
        false
      } else {
        let v1 = evaluate_const_int_expression(e1);
        if v1 == 0 { true } else { is_constant_expression(e2, symtab) }
      }
    },
    Expression::BinaryOp(_, e1, e2, _) => is_constant_expression(e1, symtab) && is_constant_expression(e2, symtab),
    Expression::PrefixOp(_, _, _) | Expression::PostfixOp(_, _, _) => false,
    Expression::Assign(_, _, _, _) => false,
    Expression::Conditional(condexpr, ifexpr, elseexpr, _) => {
      is_constant_expression(condexpr, symtab) && is_constant_expression(ifexpr, symtab) && is_constant_expression(elseexpr, symtab)
    },
    Expression::FunctionCall(_, _, _) => false,
  }
}

pub fn evaluate_const_address_expression(expr: &Expression) -> String {
  match expr {
    Expression::Variable(_, _) => panic!("Not a const address expression"),
    Expression::UnaryOp(uop, operand, _) => match uop {
      UnaryOp::Indirection | UnaryOp::Negate | UnaryOp::Not | UnaryOp::Complement => {
        panic!("Not a const address expression")
      },
      UnaryOp::AddressOf => {
        if let Expression::Variable(id, _) = &**operand {
          id.to_string()
        } else {
          panic!("Not a const address expression")
        }
      },
    },
    _ => panic!("Not a valid address expression"),
  }
}

pub fn evaluate_const_int_expression(expr: &Expression) -> i32 {
  match expr {
    Expression::Constant(v) => *v as i32,
    Expression::UnaryOp(uop, operand, _) => match uop {
      UnaryOp::Negate => -evaluate_const_int_expression(operand),
      UnaryOp::Not => {
        if evaluate_const_int_expression(operand) > 0 {
          1
        } else {
          0
        }
      },
      UnaryOp::Complement => !evaluate_const_int_expression(operand),
      UnaryOp::Indirection => panic!("Indirection ('*') is not a constant expression"),
      UnaryOp::AddressOf => panic!("AddressOf ('&') does not yield an int-valued expression"),
    },
    Expression::BinaryOp(BinaryOp::LogicalOr, e1, e2, _) => {
      if evaluate_const_int_expression(e1) != 0 || evaluate_const_int_expression(e2) != 0 {
        1
      } else {
        0
      }
    },
    Expression::BinaryOp(BinaryOp::LogicalAnd, e1, e2, _) => {
      if evaluate_const_int_expression(e1) == 0 || evaluate_const_int_expression(e2) == 0 {
        0
      } else {
        1
      }
    },
    Expression::BinaryOp(binop, e1, e2, _) => {
      let op1 = evaluate_const_int_expression(e1);
      let op2 = evaluate_const_int_expression(e2);
      match binop {
        BinaryOp::Addition => op1 + op2,
        BinaryOp::Subtraction => op1 - op2,
        BinaryOp::Multiplication => op1 * op2,
        BinaryOp::Division => op1 / op2,
        BinaryOp::Remainder => op1 % op2,
        BinaryOp::Equal => (op1 == op2) as i32,
        BinaryOp::NotEqual => (op1 != op2) as i32,
        BinaryOp::Less => (op1 < op2) as i32,
        BinaryOp::Greater => (op1 > op2) as i32,
        BinaryOp::LessEqual => (op1 <= op2) as i32,
        BinaryOp::GreaterEqual => (op1 >= op2) as i32,
        BinaryOp::BitwiseAnd => op1 & op2,
        BinaryOp::BitwiseOr => op1 | op2,
        BinaryOp::BitwiseXor => op1 ^ op2,
        BinaryOp::LeftShift => op1 << op2,
        BinaryOp::RightShift => op1 >> op2,
        _ => panic!("LogicalAnd/LogicalOr are handled above"),
      }
    },
    Expression::Conditional(condexpr, ifexpr, elseexpr, _) => {
      let cond = evaluate_const_int_expression(condexpr);
      let ifval = evaluate_const_int_expression(ifexpr);
      let elseval = evaluate_const_int_expression(elseexpr);
      if cond != 0 { ifval } else { elseval }
    },
    Expression::Variable(_, _)
    | Expression::FunctionCall(_, _, _)
    | Expression::PrefixOp(_, _, _)
    | Expression::PostfixOp(_, _, _)
    | Expression::Assign(_, _, _, _) => panic!("Non-constant expression"),
  }
}
