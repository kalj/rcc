use std::error;
use std::fmt;

use crate::ast::AstContext;
use crate::ast::{AssignmentKind, BinaryOp, FixOp, UnaryOp};
use crate::ast::{BasicType, Type};
use crate::ast::{BlockItem, Declaration, Expression, Function, FunctionParameters, Program, Statement, ToplevelItem};
use crate::evaluation::{evaluate_const_address_expression, evaluate_const_int_expression, expression_type};
use crate::symbol_table::{GlobalVariableSymbol, LocalVariableSymbol, SymbolTable};

//===================================================================
// Code generation
//===================================================================

#[derive(Debug, Clone)]
pub struct CodegenError {
    pub position: usize,
    pub length: usize,
    pub message: String,
}

impl CodegenError {
    fn new(message: String, ctx: &AstContext) -> CodegenError {
        CodegenError { position: ctx.position, length: ctx.length, message }
    }
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "CodegenError {}: {}", self.position, self.message)
    }
}

impl error::Error for CodegenError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

enum CodeLine {
    LabelRef(String),
    Instr1(String),
    Instr2(String, String),
    Instr3(String, String, String),
}

impl CodeLine {
    fn lbl(l: &str) -> CodeLine {
        CodeLine::LabelRef(l.to_string())
    }

    fn i1(opcode: &str) -> CodeLine {
        CodeLine::Instr1(opcode.to_string())
    }

    fn i2(opcode: &str, op1: &str) -> CodeLine {
        CodeLine::Instr2(opcode.to_string(), op1.to_string())
    }

    fn i3(opcode: &str, op1: &str, op2: &str) -> CodeLine {
        CodeLine::Instr3(opcode.to_string(), op1.to_string(), op2.to_string())
    }
}

pub struct Code {
    code: Vec<CodeLine>,
}

impl Code {
    fn new() -> Code {
        Code { code: Vec::new() }
    }

    fn push(&mut self, cl: CodeLine) {
        self.code.push(cl)
    }

    pub fn get_str(self) -> String {
        let strs: Vec<String> = self
            .code
            .iter()
            .map(|cl| match cl {
                CodeLine::LabelRef(lbl) => format!("{}:", lbl),
                CodeLine::Instr1(opcode) => format!("    {}", opcode),
                CodeLine::Instr2(opcode, operand) => format!("    {} {}", opcode, operand),
                CodeLine::Instr3(opcode, operand1, operand2) => format!("    {} {}, {}", opcode, operand1, operand2),
            })
            .collect();
        strs.join("\n") + "\n"
    }
}

struct LoopContext {
    break_lbl: Option<String>,
    continue_lbl: Option<String>,
}

struct Register {
    n: String,
    n32: String,
}

impl Register {
    fn new(name: &str, name32: &str) -> Register {
        Register { n: name.to_string(), n32: name32.to_string() }
    }
}

struct Registers {
    ax: Register,
    cx: Register,
    dx: Register,
    bp: Register,
    sp: Register,
    args: Vec<Register>,
}

impl Registers {
    fn new(for32bit: bool) -> Registers {
        if for32bit {
            Registers {
                ax: Register::new("%eax", "%eax"),
                cx: Register::new("%ecx", "%ecx"),
                dx: Register::new("%edx", "%edx"),
                bp: Register::new("%ebp", "%ebp"),
                sp: Register::new("%esp", "%esp"),
                args: Vec::new(),
            }
        } else {
            Registers {
                ax: Register::new("%rax", "%eax"),
                cx: Register::new("%rcx", "%ecx"),
                dx: Register::new("%rdx", "%edx"),
                bp: Register::new("%rbp", "%ebp"),
                sp: Register::new("%rsp", "%esp"),
                args: vec![
                    Register::new("%rdi", "%edi"),
                    Register::new("%rsi", "%esi"),
                    Register::new("%rdx", "%edx"),
                    Register::new("%rcx", "%ecx"),
                    Register::new("%r8", "%r8d"),
                    Register::new("%r9", "%r9d"),
                ],
            }
        }
    }
}

pub struct Stack {
    entry_size: usize,
    index: i32,
    saved_indices: Vec<i32>,
}

impl Stack {
    fn new(_32bit: bool) -> Stack {
        let entry_size = if _32bit { 4 } else { 8 };
        Stack { entry_size, index: -(entry_size as i32), saved_indices: Vec::new() }
    }

    fn new_scope(&mut self) {
        self.saved_indices.push(self.index);
    }

    fn end_scope(&mut self) -> usize {
        let saved_index = self.saved_indices.pop().unwrap();

        let scope_size = saved_index - self.index;
        self.index = saved_index;
        scope_size as usize
    }
}

pub struct Generator {
    code: Code,
    emit_32bit: bool,
    label_counter: i32,
    reg: Registers,
    stack: Stack,
    symtab: SymbolTable,
    loop_ctx: LoopContext,
    alignment: u8,
}

impl Generator {
    fn new(emit_32bit: bool) -> Generator {
        Generator {
            code: Code::new(),
            emit_32bit,
            label_counter: 0,
            symtab: SymbolTable::new(),
            stack: Stack::new(emit_32bit),
            reg: Registers::new(emit_32bit),
            loop_ctx: LoopContext { break_lbl: None, continue_lbl: None },
            alignment: 4,
        }
    }

    fn size_of_type(&self, t: &Type) -> usize {
        match t {
            Type::Ptr(_) => {
                if self.emit_32bit {
                    4
                } else {
                    8
                }
            }
            Type::Basic(bt) => match bt {
                BasicType::Int => 4,
                BasicType::Void => 0,
            },
        }
    }

    fn emit(&mut self, cl: CodeLine) {
        self.code.push(cl)
    }

    fn new_label(&mut self) -> String {
        let lbl = format!("_label{}", self.label_counter);
        self.label_counter += 1;
        lbl
    }

    fn get_variable_address(&self, name: &str) -> Option<String> {
        if let Some(loc) = self.symtab.get_local(name) {
            if let Some(offset) = loc.stack_offset {
                Some(format!("{}({})", offset, self.reg.bp.n))
            } else {
                panic!("Internal error. No stack offset for variable {}", name);
            }
        } else if self.symtab.get_global(name).is_some() {
            Some(name.to_string())
        } else {
            None
        }
    }

    fn new_scope(&mut self) {
        self.stack.new_scope();
        self.symtab.new_scope();
    }

    fn end_scope(&mut self) {
        let scope_size = self.stack.end_scope();
        if scope_size > 0 {
            // restore stack pointer
            self.emit(CodeLine::i3("add", &format!("${}", scope_size), &self.reg.sp.n));
        }
        self.symtab.end_scope();
    }

    fn insert_local_variable(&mut self, id: &str, typ: &Type) {
        self.symtab.insert_local(&id, LocalVariableSymbol::new_with_stack_offset(typ, self.stack.index)); // save new variable
        self.stack.index -= self.stack.entry_size as i32;
    }

    fn new_loop_context(&mut self, brk_lbl: &str, cnt_lbl: &str) -> LoopContext {
        std::mem::replace(
            &mut self.loop_ctx,
            LoopContext { break_lbl: Some(brk_lbl.to_string()), continue_lbl: Some(cnt_lbl.to_string()) },
        )
    }

    fn restore_loop_context(&mut self, old_loop_context: LoopContext) {
        self.loop_ctx = old_loop_context;
    }

    fn generate_binop_code(&mut self, binop: &BinaryOp) {
        match binop {
            BinaryOp::Addition => {
                // add, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
                self.emit(CodeLine::i3("add", &self.reg.cx.n32, &self.reg.ax.n32));
            }
            BinaryOp::Subtraction => {
                // subtract %eax (arg1) - %ecx (arg2) -> %eax
                self.emit(CodeLine::i3("sub", &self.reg.cx.n32, &self.reg.ax.n32));
            }
            BinaryOp::Multiplication => {
                // multiply, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
                self.emit(CodeLine::i3("imul", &self.reg.cx.n32, &self.reg.ax.n32));
            }
            BinaryOp::Division | BinaryOp::Remainder => {
                // sign extend %eax into %edx:%eax
                self.emit(CodeLine::i1("cltd"));
                //  idiv takes numerator in %eax, denominator in arg (%ecx). quotient is put in %eax, remainder in %edx.
                self.emit(CodeLine::i2("idiv", &self.reg.cx.n32));
                if let BinaryOp::Remainder = binop {
                    // copy remainder into %eax
                    self.emit(CodeLine::i3("mov", &self.reg.dx.n32, &self.reg.ax.n32));
                }
            }
            BinaryOp::Equal
            | BinaryOp::NotEqual
            | BinaryOp::Less
            | BinaryOp::Greater
            | BinaryOp::LessEqual
            | BinaryOp::GreaterEqual => {
                // compare ECX and EAX
                self.emit(CodeLine::i3("cmp", &self.reg.cx.n32, &self.reg.ax.n32));
                // zero out EAX without changing ZF
                self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32));

                match binop {
                    BinaryOp::Equal => {
                        // set bit to 1 if ecx (op1) was equal to eax (op2)
                        self.emit(CodeLine::i2("sete", "%al"));
                    }
                    BinaryOp::NotEqual => {
                        // set bit to 1 if ecx (op1) was not equal to eax (op2)
                        self.emit(CodeLine::i2("setne", "%al"));
                    }
                    BinaryOp::Less => {
                        // set bit to 1 if ecx (op1) was less than eax (op2)
                        self.emit(CodeLine::i2("setl", "%al"));
                    }
                    BinaryOp::Greater => {
                        // set bit to 1 if ecx (op1) was greater than eax (op2)
                        self.emit(CodeLine::i2("setg", "%al"));
                    }
                    BinaryOp::LessEqual => {
                        // set bit to 1 if ecx (op1) was less than or equal to eax (op2)
                        self.emit(CodeLine::i2("setle", "%al"));
                    }
                    BinaryOp::GreaterEqual => {
                        // set bit to 1 if ecx (op1) was greater than or equal to eax (op2)
                        self.emit(CodeLine::i2("setge", "%al"));
                    }
                    _ => {}
                }
            }
            BinaryOp::BitwiseOr => {
                // bitwise or, %eax = %ecx | %eax
                self.emit(CodeLine::i3("or", &self.reg.cx.n32, &self.reg.ax.n32));
            }
            BinaryOp::BitwiseXor => {
                // bitwise xor, %eax = %ecx ^ %eax
                self.emit(CodeLine::i3("xor", &self.reg.cx.n32, &self.reg.ax.n32));
            }
            BinaryOp::BitwiseAnd => {
                // bitwise and, %eax = %ecx & %eax
                self.emit(CodeLine::i3("and", &self.reg.cx.n32, &self.reg.ax.n32));
            }
            BinaryOp::LeftShift => {
                // arithmetic left shift (== logical left shift), %eax = %eax << %cl
                self.emit(CodeLine::i3("sal", "%cl", &self.reg.ax.n32));
            }
            BinaryOp::RightShift => {
                // arithmetic right shift; %eax = %eax >> %cl
                self.emit(CodeLine::i3("sar", "%cl", &self.reg.ax.n32));
            }
            BinaryOp::LogicalAnd | BinaryOp::LogicalOr => {
                panic!("Internal Error"); // Handled above separately
            }
        }
    }

    fn get_lvalue_address(&mut self, expr: &Expression) -> Result<String, CodegenError> {
        match expr {
            Expression::Variable(id, ctx) => {
                if let Some(addr) = self.get_variable_address(&id) {
                    Ok(addr)
                } else {
                    Err(CodegenError::new(format!("Missing declaration for variable '{}'", id), &ctx))
                }
            }
            Expression::UnaryOp(uop, expr, _) => {
                match uop {
                    UnaryOp::Indirection => {
                        // this has to be a pointer
                        self.generate_expression_code(expr)?;
                        Ok(format!("({})", &self.reg.ax.n))
                    }
                    _ => {
                        panic!("Internal error. Indirection ('*') is the sole unary operator producing a valid lvalue")
                    }
                }
            }
            _ => panic!("Internal error. Expression is not a valid lvalue"),
        }
    }

    fn generate_expression_code(&mut self, expr: &Expression) -> Result<(), CodegenError> {
        match expr {
            Expression::Constant(val) => {
                let literal = format!("${}", val);
                self.emit(CodeLine::i3("mov", &literal, &self.reg.ax.n32));
            }
            Expression::Variable(id, ctx) => {
                if let Some(addr) = self.get_variable_address(id) {
                    self.emit(CodeLine::i3("mov", &addr, &self.reg.ax.n));
                } else {
                    return Err(CodegenError::new(format!("Missing declaration for variable '{}'", id), &ctx));
                }
            }
            Expression::UnaryOp(uop, expr, _) => {
                match uop {
                    UnaryOp::Negate => {
                        self.generate_expression_code(expr)?;
                        self.emit(CodeLine::i2("neg", &self.reg.ax.n32));
                    }
                    UnaryOp::Not => {
                        self.generate_expression_code(expr)?;
                        self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32));
                        self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32));
                        self.emit(CodeLine::i2("sete", "%al"));
                    }
                    UnaryOp::Complement => {
                        self.generate_expression_code(expr)?;
                        self.emit(CodeLine::i2("not", &self.reg.ax.n32));
                    }
                    UnaryOp::Indirection => {
                        // this has to be a pointer
                        self.generate_expression_code(expr)?;
                        self.emit(CodeLine::i3("mov", &format!("({})", &self.reg.ax.n), &self.reg.ax.n32))
                    }
                    UnaryOp::AddressOf => {
                        let addr = self.get_lvalue_address(expr)?;
                        self.emit(CodeLine::i3("lea", &addr, &self.reg.ax.n));
                    }
                }
            }
            Expression::BinaryOp(BinaryOp::LogicalOr, e1, e2, _) => {
                // setup labels
                let cond2 = self.new_label();
                let end = self.new_label();

                self.generate_expression_code(e1)?;
                // if true then just jump over second part and set true
                // else evaluate second part and set to return status of that
                self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           set ZF if EAX == 0
                self.emit(CodeLine::i2("je", &cond2)); //                            if ZF is set, go to cond2
                self.emit(CodeLine::i3("mov", "$1", &self.reg.ax.n32)); //           else we are done, so set result to 1,
                self.emit(CodeLine::i2("jmp", &end)); //                             and jump to end.
                self.emit(CodeLine::lbl(&cond2));
                self.generate_expression_code(e2)?;
                self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           set ZF if EAX == 0
                self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32)); //           zero out EAX without changing ZF
                self.emit(CodeLine::i2("setnz", "%al")); //                          set bit to 1 if eax was not zero
                self.emit(CodeLine::lbl(&end));
            }
            Expression::BinaryOp(BinaryOp::LogicalAnd, e1, e2, _) => {
                // setup labels
                let cond2 = self.new_label();
                let end = self.new_label();

                self.generate_expression_code(e1)?;
                // if false then just jump over second part and set false
                // else evaluate second part and set to return status of that
                self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           set ZF if EAX == 0
                self.emit(CodeLine::i2("jne", &cond2)); //                           if ZF is not set, go to cond2
                self.emit(CodeLine::i2("jmp", &end)); //                             else we are done (and eax is 0), so jump to end.
                self.emit(CodeLine::lbl(&cond2));
                self.generate_expression_code(e2)?;
                self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           set ZF if EAX == 0
                self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32)); //           zero out EAX without changing ZF
                self.emit(CodeLine::i2("setnz", "%al")); //                          set bit to 1 if eax was not zero
                self.emit(CodeLine::lbl(&end));
            }
            Expression::BinaryOp(bop, e1, e2, _) => {
                self.generate_expression_code(e1)?;

                self.emit(CodeLine::i2("push", &self.reg.ax.n));
                self.generate_expression_code(e2)?;

                self.emit(CodeLine::i3("mov", &self.reg.ax.n32, &self.reg.cx.n32)); // copy arg2 into %ecx
                self.emit(CodeLine::i2("pop", &self.reg.ax.n)); //                     get arg1 from stack into %eax
                self.generate_binop_code(bop);
            }
            Expression::PrefixOp(fixop, operand, _) => {
                let addr = self.get_lvalue_address(operand)?;

                if let FixOp::Inc = fixop {
                    self.emit(CodeLine::i2("incl", &addr));
                } else {
                    self.emit(CodeLine::i2("decl", &addr));
                }
                self.emit(CodeLine::i3("mov", &addr, &self.reg.ax.n));
            }
            Expression::PostfixOp(fixop, operand, _) => {
                let addr = self.get_lvalue_address(operand)?;

                self.emit(CodeLine::i3("lea", &addr, &self.reg.cx.n));

                self.emit(CodeLine::i3("mov", &format!("({})", &self.reg.cx.n), &self.reg.ax.n));
                if let FixOp::Inc = fixop {
                    self.emit(CodeLine::i2("incl", &format!("({})", &self.reg.cx.n)));
                } else {
                    self.emit(CodeLine::i2("decl", &format!("({})", &self.reg.cx.n)));
                }
            }
            Expression::Assign(kind, lhs, expr, _) => {
                let lhs_type = expression_type(lhs, &self.symtab).unwrap();

                let addr = self.get_lvalue_address(lhs)?;
                self.emit(CodeLine::i3("lea", &addr, &self.reg.ax.n));
                self.emit(CodeLine::i2("push", &self.reg.ax.n));

                self.generate_expression_code(expr)?;

                let binop = match kind {
                    AssignmentKind::Write => None,
                    AssignmentKind::Add => Some(BinaryOp::Addition),
                    AssignmentKind::Subtract => Some(BinaryOp::Subtraction),
                    AssignmentKind::Multiply => Some(BinaryOp::Multiplication),
                    AssignmentKind::Divide => Some(BinaryOp::Division),
                    AssignmentKind::Remainder => Some(BinaryOp::Remainder),
                    AssignmentKind::BitwiseOr => Some(BinaryOp::BitwiseOr),
                    AssignmentKind::BitwiseXor => Some(BinaryOp::BitwiseXor),
                    AssignmentKind::BitwiseAnd => Some(BinaryOp::BitwiseAnd),
                    AssignmentKind::LeftShift => Some(BinaryOp::LeftShift),
                    AssignmentKind::RightShift => Some(BinaryOp::RightShift),
                };

                if let Some(bop) = binop {
                    self.emit(CodeLine::i3("mov", &self.reg.ax.n32, &self.reg.cx.n32));
                    // load address of lhs
                    let addr_expr = format!("({})", &self.reg.sp.n);
                    self.emit(CodeLine::i3("mov", &addr_expr, &self.reg.ax.n));
                    // load value of lhs
                    self.emit(CodeLine::i3("mov", &format!("({})", &self.reg.ax.n), &self.reg.ax.n32));
                    self.generate_binop_code(&bop);
                }

                // get the address
                self.emit(CodeLine::i2("pop", &self.reg.cx.n));
                match lhs_type {
                    Type::Basic(_) => {
                        self.emit(CodeLine::i3("mov", &self.reg.ax.n32, &format!("({})", self.reg.cx.n)));
                    }
                    Type::Ptr(_) => {
                        self.emit(CodeLine::i3("mov", &self.reg.ax.n, &format!("({})", self.reg.cx.n)));
                    }
                }
            }
            Expression::Conditional(condexpr, ifexpr, elseexpr, _) => {
                // setup labels
                let else_case = self.new_label();
                let end = self.new_label();

                self.generate_expression_code(condexpr)?;

                self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           set ZF if EAX == 0
                self.emit(CodeLine::i2("je", &else_case)); //                        if ZF is set, go to else_case

                self.generate_expression_code(ifexpr)?; //                           else execute ifexpr
                self.emit(CodeLine::i2("jmp", &end)); //                             then jump to end

                self.emit(CodeLine::lbl(&else_case));
                self.generate_expression_code(elseexpr)?;
                self.emit(CodeLine::lbl(&end));
            }
            Expression::FunctionCall(id, args, _) => {
                let narg_regs = self.reg.args.len();

                // evaluate arguments and push on stack (or put in registers) in reverse order
                for (iarg, arg) in args.iter().enumerate().rev() {
                    self.generate_expression_code(arg)?;

                    if iarg >= narg_regs {
                        self.emit(CodeLine::i2("push", &self.reg.ax.n));
                    } else {
                        let argtyp = expression_type(arg, &self.symtab).unwrap();

                        match argtyp {
                            Type::Basic(_) => {
                                self.emit(CodeLine::i3("mov", &self.reg.ax.n32, &self.reg.args[iarg].n32));
                            }
                            Type::Ptr(_) => {
                                self.emit(CodeLine::i3("mov", &self.reg.ax.n, &self.reg.args[iarg].n));
                            }
                        }
                    }
                }

                self.emit(CodeLine::i2("call", &id));
                if args.len() > narg_regs {
                    let n_stack_args = args.len() - narg_regs;
                    let offset_literal = format!("${}", self.stack.entry_size * n_stack_args);
                    self.emit(CodeLine::i3("add", &offset_literal, &self.reg.sp.n));
                }
            }
        }
        Ok(())
    }

    fn generate_declaration_code(&mut self, decl: &Declaration) -> Result<(), CodegenError> {
        let Declaration { id, init, ctx, typ } = decl;
        if self.symtab.declared_in_scope(&id) {
            return Err(CodegenError::new(format!("Variable {} already declared in block", id), &ctx));
        }
        if let Some(expr) = init {
            self.generate_expression_code(&expr)?; //                   possibly compute initial value, saved in %rax
        } else {
            self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n)); //    otherwise initialize %rax with 0
        }
        self.emit(CodeLine::i2("push", &self.reg.ax.n)); //             push value on stack at known index
        self.insert_local_variable(&id, typ);
        Ok(())
    }

    fn generate_return_statement_code(&mut self, maybe_expr: &Option<Expression>) -> Result<(), CodegenError> {
        if let Some(expr) = maybe_expr {
            self.generate_expression_code(&expr)?;
        }
        self.emit(CodeLine::i3("mov", &self.reg.bp.n, &self.reg.sp.n));
        self.emit(CodeLine::i2("pop", &self.reg.bp.n));
        self.emit(CodeLine::i1("ret"));
        Ok(())
    }

    fn generate_statement_code(&mut self, stmnt: &Statement) -> Result<(), CodegenError> {
        match stmnt {
            Statement::Return(maybe_expr, _) => {
                self.generate_return_statement_code(&maybe_expr)?;
            }
            Statement::Break(ctx) => {
                if let Some(blbl) = &self.loop_ctx.break_lbl {
                    let l = blbl.to_string();
                    self.emit(CodeLine::i2("jmp", &l));
                } else {
                    return Err(CodegenError::new(
                        "Invalid break not inside a loop or switch statement".to_string(),
                        ctx,
                    ));
                }
            }
            Statement::Continue(ctx) => {
                if let Some(clbl) = &self.loop_ctx.continue_lbl {
                    let l = clbl.to_string();
                    self.emit(CodeLine::i2("jmp", &l));
                } else {
                    return Err(CodegenError::new("Invalid continue not inside a loop".to_string(), ctx));
                }
            }
            Statement::Expr(expr) => self.generate_expression_code(&expr)?,
            Statement::Null => {}
            Statement::If(condexpr, ifstmt, maybe_elsestmt) => {
                if let Some(elsestmt) = maybe_elsestmt {
                    // setup labels
                    let else_case = self.new_label();
                    let end = self.new_label();

                    self.generate_expression_code(&condexpr)?;

                    self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           set ZF if EAX == 0
                    self.emit(CodeLine::i2("je", &else_case)); //                        if ZF is set, go to else_case

                    self.generate_statement_code(ifstmt)?; //                            else execute ifstmt
                    self.emit(CodeLine::i2("jmp", &end)); //                             then jump to end

                    self.emit(CodeLine::lbl(&else_case));
                    self.generate_statement_code(elsestmt)?;
                    self.emit(CodeLine::lbl(&end));
                } else {
                    // setup label
                    let end = self.new_label();

                    self.generate_expression_code(&condexpr)?;

                    self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           set ZF if EAX == 0
                    self.emit(CodeLine::i2("je", &end)); //                              if ZF is set, go to end

                    self.generate_statement_code(ifstmt)?; //                            else execute ifexpr

                    self.emit(CodeLine::lbl(&end));
                }
            }
            Statement::While(cond, body) => {
                // setup labels
                let start = self.new_label();
                let end = self.new_label();
                let old_loop_ctx = self.new_loop_context(&end, &start);

                self.emit(CodeLine::lbl(&start));
                self.generate_expression_code(&cond)?;

                self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           set ZF if EAX == 0
                self.emit(CodeLine::i2("je", &end)); //                              if ZF is set, go to end

                self.generate_statement_code(body)?; //                              else execute body
                self.emit(CodeLine::i2("jmp", &start)); //                           and go to next iteration

                self.emit(CodeLine::lbl(&end));
                self.restore_loop_context(old_loop_ctx);
            }
            Statement::DoWhile(body, cond) => {
                // setup labels
                let start = self.new_label();
                let end = self.new_label();
                let old_loop_ctx = self.new_loop_context(&end, &start);

                self.emit(CodeLine::lbl(&start));

                // execute body
                self.generate_statement_code(body)?;

                self.generate_expression_code(&cond)?;

                self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           check if false (set ZF if EAX == 0)
                self.emit(CodeLine::i2("jne", &start)); //                           if true (ZF is not set), go start

                // else simply fall through to end
                self.emit(CodeLine::lbl(&end));

                self.restore_loop_context(old_loop_ctx);
            }
            Statement::For(maybe_initexpr, cond, maybe_postexpr, body) => {
                // setup labels
                let start = self.new_label();
                let end = self.new_label();
                let cnt = self.new_label();
                let old_loop_ctx = self.new_loop_context(&end, &cnt);

                if let Some(initexpr) = maybe_initexpr {
                    self.generate_expression_code(&initexpr)?;
                }

                self.emit(CodeLine::lbl(&start));
                self.generate_expression_code(&cond)?;

                self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           set ZF if EAX == 0
                self.emit(CodeLine::i2("je", &end)); //                              if ZF is set, go to end

                self.generate_statement_code(body)?; //                              else execute body

                self.emit(CodeLine::lbl(&cnt)); //                                   jump here from continue in body
                if let Some(postexpr) = maybe_postexpr {
                    self.generate_expression_code(&postexpr)?;
                }

                self.emit(CodeLine::i2("jmp", &start)); //                           and go to next iteration

                self.emit(CodeLine::lbl(&end));
                self.restore_loop_context(old_loop_ctx);
            }
            Statement::ForDecl(initdecl, cond, maybe_postexpr, body) => {
                // setup labels
                let start = self.new_label();
                let end = self.new_label();
                let cnt = self.new_label();
                let old_loop_ctx = self.new_loop_context(&end, &cnt);

                self.new_scope();

                self.generate_declaration_code(&initdecl)?;

                self.emit(CodeLine::lbl(&start));
                self.generate_expression_code(&cond)?;

                self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32)); //           set ZF if EAX == 0
                self.emit(CodeLine::i2("je", &end)); //                              if ZF is set, go to end

                self.generate_statement_code(body)?; //                              else execute body

                self.emit(CodeLine::lbl(&cnt)); //                                   jump here from continue in body
                if let Some(postexpr) = maybe_postexpr {
                    self.generate_expression_code(&postexpr)?;
                }

                self.emit(CodeLine::i2("jmp", &start)); //                           and go to next iteration

                self.emit(CodeLine::lbl(&end));

                // restore old scope
                self.end_scope();

                self.restore_loop_context(old_loop_ctx);
            }
            Statement::Compound(bkitems) => {
                self.new_scope();

                self.generate_block_items(bkitems)?;

                // restore old scope
                self.end_scope();
            }
        }
        Ok(())
    }

    fn generate_block_item_code(&mut self, bkitem: &BlockItem) -> Result<(), CodegenError> {
        match bkitem {
            BlockItem::Decl(decl) => self.generate_declaration_code(decl)?,
            BlockItem::Stmt(stmt) => self.generate_statement_code(&stmt)?,
        }
        Ok(())
    }

    fn generate_block_items(&mut self, block_items: &[BlockItem]) -> Result<(), CodegenError> {
        for bkitem in block_items {
            self.generate_block_item_code(bkitem)?;
        }
        Ok(())
    }

    fn generate_function_code(&mut self, func: &Function) -> Result<(), CodegenError> {
        match func {
            Function::Declaration(_, _, _, _) => {}
            Function::Definition(rettyp, name, parameters, body, _) => {
                self.emit(CodeLine::i2(".globl", name));
                self.emit(CodeLine::lbl(name));
                self.emit(CodeLine::i2("push", &self.reg.bp.n));
                self.emit(CodeLine::i3("mov", &self.reg.sp.n, &self.reg.bp.n));

                self.new_scope();

                //add parameters to variable map
                let narg_regs = self.reg.args.len();

                // evaluate arguments and push on stack in reverse order
                if let FunctionParameters::List(params) = parameters {
                    for (i, p) in params.iter().enumerate() {
                        let id = p.id.as_ref().unwrap();
                        if i < narg_regs {
                            // push value on stack at known index
                            self.emit(CodeLine::i2("push", &self.reg.args[i].n));
                            self.insert_local_variable(&id, &p.typ);
                        } else {
                            // `regsize` extra for the stack pointer which will be pushed
                            let stack_offset = self.stack.entry_size * (1 + 1 + i - narg_regs);
                            self.symtab.insert_local(
                                &id,
                                LocalVariableSymbol::new_with_stack_offset(&p.typ, stack_offset as i32),
                            );
                        }
                    }
                }

                self.generate_block_items(&body)?;

                // restore old scope
                self.end_scope();

                if !self.code.code.iter().any(|cl| if let CodeLine::Instr1(op) = cl { op == "ret" } else { false }) {
                    match rettyp {
                        Type::Basic(BasicType::Void) => self.generate_return_statement_code(&None)?,
                        _ => self.generate_return_statement_code(&Some(Expression::Constant(0)))?,
                    };
                }
            }
        }
        Ok(())
    }

    fn generate_global_declaration_code(&mut self, decl: &Declaration) -> Result<(), CodegenError> {
        let Declaration { id, init, typ, ctx } = decl;

        let mut has_def = false;

        if let Some(expr) = init {
            has_def = true;

            self.emit(CodeLine::i2(".globl", &id));
            self.emit(CodeLine::i1(".data"));
            self.emit(CodeLine::i2(".align", &format!("{}", self.alignment)));
            self.emit(CodeLine::lbl(&id));

            let type_size = self.size_of_type(typ);
            let cmd_str = match type_size {
                8 => ".quad",
                4 => ".long",
                _ => panic!("No data command for size {}", type_size),
            };

            let val_str = match typ {
                Type::Basic(_) => format!("{}", evaluate_const_int_expression(expr)),
                Type::Ptr(_) => evaluate_const_address_expression(expr),
            };

            self.emit(CodeLine::i2(cmd_str, &val_str));
        }

        // switch back to emitting code
        self.emit(CodeLine::i1(".text"));

        self.symtab.insert_global(&id, GlobalVariableSymbol::new(&typ, has_def, &ctx));
        Ok(())
    }

    fn generate_program_code(&mut self, prog: &Program) -> Result<(), CodegenError> {
        let Program::Prog(toplevel_items) = prog;
        for item in toplevel_items {
            match item {
                ToplevelItem::Function(func) => self.generate_function_code(func)?,
                ToplevelItem::Variable(decl) => self.generate_global_declaration_code(decl)?,
            }
        }

        // generate code for uninitialized variables
        for (gid, gv) in self.symtab.get_globals() {
            if !gv.has_definition {
                self.emit(CodeLine::i2(".globl", &gid));
                self.emit(CodeLine::i1(".bss"));
                self.emit(CodeLine::i2(".align", &format!("{}", self.alignment)));
                self.emit(CodeLine::lbl(&gid));
                let size = self.size_of_type(&gv.typ);
                self.emit(CodeLine::i2(".zero", &format!("{}", size)));
            }
        }

        Ok(())
    }
}

pub fn generate_code(prog: &Program, emit_32_bit: bool) -> Result<Code, CodegenError> {
    let mut generator = Generator::new(emit_32_bit);
    generator.generate_program_code(prog)?;

    Ok(generator.code)
}
