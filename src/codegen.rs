use std::collections::{HashMap, HashSet};
use std::error;
use std::fmt;

use crate::ast::AstContext;
use crate::ast::{AssignmentKind, BinaryOp, FixOp, UnaryOp};
use crate::ast::{BlockItem, Declaration, Expression, Function, Program, Statement, ToplevelItem};

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

#[derive(Debug, Clone)]
struct VarMap {
    addr_map: HashMap<String, i32>,
    globals: HashMap<String, bool>,
    regsize: u8,
    stack_index: i32,
    block_decl_set: HashSet<String>,
    bp: String
}

impl VarMap {
    fn new(regsize: u8, bp: &str) -> VarMap {
        VarMap { addr_map: HashMap::new(),
                 globals:  HashMap::new(),
                 regsize,
                 stack_index: -(regsize as i32),
                 block_decl_set: HashSet::new(),
                 bp: bp.to_string()}
    }

    fn block_decl(&self, name: &str) -> bool {
        self.block_decl_set.contains(name)
    }

    fn insert_local(&mut self, name: &str) {
        self.addr_map.insert(name.to_string(), self.stack_index);
        self.stack_index -= self.regsize as i32;
        self.block_decl_set.insert(name.to_string());
    }

    fn insert_arg(&mut self, name: &str, idx: i32) {
        self.addr_map.insert(name.to_string(), idx);
        self.block_decl_set.insert(name.to_string());
    }

    fn insert_global(&mut self, name: &str) {
        if !self.globals.contains_key(name) {
            self.globals.insert(name.to_string(), false);
        }
    }

    fn set_global_defined(&mut self, name: &str) {
        if self.globals.contains_key(name) {
            *self.globals.get_mut(name).unwrap() = true;
        }
    }

    fn has(&self, name: &str) -> bool {
        self.addr_map.contains_key(name) ||
            self.globals.contains_key(name)
    }

    fn get_address(&self, name: &str) -> String {

        if self.addr_map.contains_key(name) {
            format!("{}({})", self.addr_map[name], self.bp)
        } else if self.globals.contains_key(name) {
            name.to_string()
        } else {
            panic!("Internal error. No such variable");
        }
    }

    fn get_undefined_globals(&self) -> Vec<String> {
        let mut v = Vec::new();
        for (id,def) in &self.globals {
            if ! def {
                v.push(id.to_string());
            }
        }
        return v;
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
                args: vec![
                    Register::new("%edi", "%edi"),
                    Register::new("%esi", "%esi"),
                    Register::new("%edx", "%edx"),
                    Register::new("%ecx", "%ecx"),
                    Register::new("%r8d", "%r8d"),
                    Register::new("%r9d", "%r9d"),
                ],
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

pub struct Generator {
    code: Code,
    emit_32bit: bool,
    label_counter: i32,
    reg: Registers,
    var_map: VarMap,
    loop_ctx: LoopContext,
    alignment: u8,
}

impl Generator {
    fn new(emit_32bit: bool) -> Generator {
        let bytes_per_reg = if emit_32bit { 4 } else { 8 };
        let reg = Registers::new(emit_32bit);
        Generator {
            code: Code::new(),
            emit_32bit,
            label_counter: 0,
            var_map: VarMap::new(bytes_per_reg, &reg.bp.n),
            reg: reg,
            loop_ctx: LoopContext { break_lbl: None, continue_lbl: None },
            alignment: 4
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

    fn new_scope(&mut self) -> VarMap {
        let old_var_map = self.var_map.clone();
        self.var_map.block_decl_set = HashSet::new();
        old_var_map
    }

    fn restore_scope(&mut self, old_var_map: VarMap) {
        // restore var_map, and stack pointer
        let diff_stack_index = old_var_map.stack_index - self.var_map.stack_index;
        self.var_map = old_var_map;
        if diff_stack_index > 0 {
            self.emit(CodeLine::i3("add", &format!("${}", diff_stack_index), &self.reg.sp.n));
        }
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
                self.emit(CodeLine::i3("add", &self.reg.cx.n32, &self.reg.ax.n32)); //   add, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::Subtraction => {
                self.emit(CodeLine::i3("sub", &self.reg.cx.n32, &self.reg.ax.n32)); //   subtract %eax (arg1) - %ecx (arg2) -> %eax
            }
            BinaryOp::Multiplication => {
                self.emit(CodeLine::i3("imul", &self.reg.cx.n32, &self.reg.ax.n32)); //  multiply, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::Division | BinaryOp::Remainder => {
                self.emit(CodeLine::i1("cltd")); //                sign extend %eax into %edx:%eax
                self.emit(CodeLine::i2("idiv", &self.reg.cx.n32)); //  idiv takes numerator in %eax, denominator in arg (%ecx). quotient is put in %eax, remainder in %edx.
                if let BinaryOp::Remainder = binop {
                    self.emit(CodeLine::i3("mov", &self.reg.dx.n32, &self.reg.ax.n32)); //   copy remainder into %eax
                }
            }
            BinaryOp::Equal => {
                self.emit(CodeLine::i3("cmp", &self.reg.cx.n32, &self.reg.ax.n32)); // set ZF if EAX == ECX
                self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32)); //             zero out EAX without changing ZF
                self.emit(CodeLine::i2("sete", "%al")); //                        set bit to 1 if ecx (op1) was equal to eax (op2)
            }
            BinaryOp::NotEqual => {
                self.emit(CodeLine::i3("cmp", &self.reg.cx.n32, &self.reg.ax.n32)); // set ZF if EAX == ECX
                self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32)); //             zero out EAX without changing ZF
                self.emit(CodeLine::i2("setne", "%al")); //                       set bit to 1 if ecx (op1) was not equal to eax (op2)
            }
            BinaryOp::Less => {
                self.emit(CodeLine::i3("cmp", &self.reg.cx.n32, &self.reg.ax.n32)); // compare ECX and EAX
                self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32)); //             zero out EAX without changing ZF
                self.emit(CodeLine::i2("setl", "%al")); //                        set bit to 1 if ecx (op1) was less than eax (op2)
            }
            BinaryOp::Greater => {
                self.emit(CodeLine::i3("cmp", &self.reg.cx.n32, &self.reg.ax.n32)); // compare ECX and EAX
                self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32)); //             zero out EAX without changing ZF
                self.emit(CodeLine::i2("setg", "%al")); //                        set bit to 1 if ecx (op1) was greater than eax (op2)
            }
            BinaryOp::LessEqual => {
                self.emit(CodeLine::i3("cmp", &self.reg.cx.n32, &self.reg.ax.n32)); // compare ECX and EAX
                self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32)); //             zero out EAX without changing ZF
                self.emit(CodeLine::i2("setle", "%al")); //                       set bit to 1 if ecx (op1) was less than or equal to eax (op2)
            }
            BinaryOp::GreaterEqual => {
                self.emit(CodeLine::i3("cmp", &self.reg.cx.n32, &self.reg.ax.n32)); // compare ECX and EAX
                self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32)); //             zero out EAX without changing ZF
                self.emit(CodeLine::i2("setge", "%al")); //                       set bit to 1 if ecx (op1) was greater than or equal to eax (op2)
            }
            BinaryOp::BitwiseOr => {
                self.emit(CodeLine::i3("or", &self.reg.cx.n32, &self.reg.ax.n32)); // or, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::BitwiseXor => {
                self.emit(CodeLine::i3("xor", &self.reg.cx.n32, &self.reg.ax.n32)); //   xor, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::BitwiseAnd => {
                self.emit(CodeLine::i3("and", &self.reg.cx.n32, &self.reg.ax.n32)); // bitwise and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::LeftShift => {
                self.emit(CodeLine::i3("sal", "%cl", &self.reg.ax.n32)); //          do arithmetic left shift (== logical left shift), %eax = %eax << %cl
            }
            BinaryOp::RightShift => {
                self.emit(CodeLine::i3("sar", "%cl", &self.reg.ax.n32)); //          do arithmetic right shift, %eax = %eax >> %cl
            }
            BinaryOp::LogicalAnd | BinaryOp::LogicalOr => {
                panic!("Internal Error"); // Handled above separately
            }
        }
    }

    fn generate_expression_code(&mut self, expr: &Expression) -> Result<(), CodegenError> {
        match expr {
            Expression::Constant(val) => {
                let literal = format!("${}", val);
                self.emit(CodeLine::i3("mov", &literal, &self.reg.ax.n32));
            }
            Expression::Variable(id, ctx) => {
                if !self.var_map.has(id) {
                    return Err(CodegenError::new(format!("Missing declaration for variable '{}'", id), &ctx));
                }
                let addr = self.var_map.get_address(&id);
                self.emit(CodeLine::i3("mov", &addr, &self.reg.ax.n));
            }
            Expression::UnaryOp(uop, expr) => {
                self.generate_expression_code(expr)?;
                match uop {
                    UnaryOp::Negate => {
                        self.emit(CodeLine::i2("neg", &self.reg.ax.n32));
                    }
                    UnaryOp::Not => {
                        self.emit(CodeLine::i3("cmp", "$0", &self.reg.ax.n32));
                        self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n32));
                        self.emit(CodeLine::i2("sete", "%al"));
                    }
                    UnaryOp::Complement => {
                        self.emit(CodeLine::i2("not", &self.reg.ax.n32));
                    }
                }
            }
            Expression::BinaryOp(BinaryOp::LogicalOr, e1, e2) => {
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
            Expression::BinaryOp(BinaryOp::LogicalAnd, e1, e2) => {
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
            Expression::BinaryOp(bop, e1, e2) => {
                self.generate_expression_code(e1)?;

                self.emit(CodeLine::i2("push", &self.reg.ax.n));
                self.generate_expression_code(e2)?;

                self.emit(CodeLine::i3("mov", &self.reg.ax.n32, &self.reg.cx.n32)); // copy arg2 into %ecx
                self.emit(CodeLine::i2("pop", &self.reg.ax.n)); //                     get arg1 from stack into %eax
                self.generate_binop_code(bop);
            }
            Expression::PrefixOp(fixop, id, ctx) => {
                if !self.var_map.has(&id) {
                    return Err(CodegenError::new(format!("Tried referencing undeclared variable {}.", id), &ctx));
                }

                let addr = self.var_map.get_address(&id);
                if let FixOp::Inc = fixop {
                    self.emit(CodeLine::i2("incl", &addr));
                } else {
                    self.emit(CodeLine::i2("decl", &addr));
                }
                self.emit(CodeLine::i3("mov", &addr, &self.reg.ax.n));
            }
            Expression::PostfixOp(fixop, id, ctx) => {
                if !self.var_map.has(&id) {
                    return Err(CodegenError::new(format!("Tried referencing undeclared variable {}.", id), &ctx));
                }

                let addr = self.var_map.get_address(&id);
                self.emit(CodeLine::i3("mov", &addr, &self.reg.ax.n));
                if let FixOp::Inc = fixop {
                    self.emit(CodeLine::i2("incl", &addr));
                } else {
                    self.emit(CodeLine::i2("decl", &addr));
                }
            }
            Expression::Assign(kind, id, expr, ctx) => {
                if !self.var_map.has(id) {
                    return Err(CodegenError::new(format!("Tried referencing undeclared variable {}.", id), &ctx));
                }

                self.generate_expression_code(expr)?;

                let addr = self.var_map.get_address(id);

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
                    self.emit(CodeLine::i3("mov", &addr, &self.reg.ax.n32));
                    self.generate_binop_code(&bop);
                }

                self.emit(CodeLine::i3("mov", &self.reg.ax.n32, &addr));
            }
            Expression::Conditional(condexpr, ifexpr, elseexpr) => {
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
                if self.emit_32bit {
                    // evaluate arguments and push on stack in reverse order
                    for arg in args.iter().rev() {
                        self.generate_expression_code(arg)?;
                        self.emit(CodeLine::i2("push", &self.reg.ax.n));
                    }

                    self.emit(CodeLine::i2("call", id));
                    if !args.is_empty() {
                        let offset_literal = format!("${}", 4 * args.len());
                        self.emit(CodeLine::i3("add", &offset_literal, &self.reg.sp.n));
                    }
                } else {
                    let nargs = args.len();

                    for i in 0..nargs {
                        let iarg = nargs - 1 - i;
                        self.generate_expression_code(&args[iarg])?;
                        if iarg >= self.reg.args.len() {
                            self.emit(CodeLine::i2("push", &self.reg.ax.n));
                        } else {
                            self.emit(CodeLine::i3("mov", &self.reg.ax.n32, &self.reg.args[iarg].n32));
                        }
                    }

                    self.emit(CodeLine::i2("call", &id));
                    if args.len() > 6 {
                        let offset_literal = format!("${}", 8 * (args.len() - 6));
                        self.emit(CodeLine::i3("add", &offset_literal, &self.reg.sp.n));
                    }
                }
            }
        }
        Ok(())
    }

    fn generate_declaration_code(&mut self, decl: &Declaration) -> Result<(), CodegenError> {
        let Declaration { id, init, ctx } = decl;
        if self.var_map.block_decl(&id) {
            return Err(CodegenError::new(format!("Variable {} already declared in block", id), &ctx));
        }
        if let Some(expr) = init {
            self.generate_expression_code(&expr)?; //                  possibly compute initial value, saved in %rax
        } else {
            self.emit(CodeLine::i3("mov", "$0", &self.reg.ax.n)); //   otherwise initialize %rax with 0
        }
        self.emit(CodeLine::i2("push", &self.reg.ax.n)); //            push value on stack at known index
        self.var_map.insert_local(&id); //                        save new variable
        Ok(())
    }

    fn generate_statement_code(&mut self, stmnt: &Statement) -> Result<(), CodegenError> {
        match stmnt {
            Statement::Return(expr) => {
                self.generate_expression_code(&expr)?;
                self.emit(CodeLine::i3("mov", &self.reg.bp.n, &self.reg.sp.n));
                self.emit(CodeLine::i2("pop", &self.reg.bp.n));
                self.emit(CodeLine::i1("ret"));
            }
            Statement::Break(ctx) => {
                if let Some(blbl) = &self.loop_ctx.break_lbl {
                    self.emit(CodeLine::i2("jmp", blbl));
                } else {
                    return Err(CodegenError::new(
                        "Invalid break not inside a loop or switch statement".to_string(),
                        ctx,
                    ));
                }
            }
            Statement::Continue(ctx) => {
                if let Some(clbl) = &self.loop_ctx.continue_lbl {
                    self.emit(CodeLine::i2("jmp", clbl));
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

                let old_scope = self.new_scope();

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
                self.restore_scope(old_scope);

                self.restore_loop_context(old_loop_ctx);
            }
            Statement::Compound(bkitems) => {
                let old_scope = self.new_scope();

                self.generate_block_items(bkitems)?;

                // restore old scope
                self.restore_scope(old_scope);
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
            Function::Declaration(_, _, _) => {}
            Function::Definition(name, parameters, body, _) => {
                self.emit(CodeLine::i2(".globl", name));
                self.emit(CodeLine::lbl(name));
                self.emit(CodeLine::i2("push", &self.reg.bp.n));
                self.emit(CodeLine::i3("mov", &self.reg.sp.n, &self.reg.bp.n));

                let old_scope = self.new_scope();

                //add parameters to variable map

                if self.emit_32bit {
                    // evaluate arguments and push on stack in reverse order
                    for (i, p) in parameters.iter().enumerate() {
                        // 4 extra for the stack pointer which will be pushed
                        let stack_offset = 4 + 4 * (1 + i as i32);
                        self.var_map.insert_arg(&p.id, stack_offset);
                    }
                } else {
                    let narg_regs = self.reg.args.len();

                    for (i, p) in parameters.iter().enumerate() {
                        if i < narg_regs {
                            //  push value on stack at known index
                            self.emit(CodeLine::i2("push", &self.reg.args[i].n));
                            self.var_map.insert_local(&p.id); //      save new variable
                        } else {
                            // 8 extra for the stack pointer which will be pushed
                            let stack_offset = 8 + 8 * (1 + i - narg_regs);
                            self.var_map.insert_arg(&p.id, stack_offset as i32);
                        }
                    }
                }

                self.generate_block_items(&body)?;

                // restore old scope
                self.restore_scope(old_scope);

                if !self.code.code.iter().any(|cl| if let CodeLine::Instr1(op) = cl { op == "ret" } else { false }) {
                    self.generate_statement_code(&Statement::Return(Expression::Constant(0)))?;
                }
            }
        }
        Ok(())
    }

    fn generate_global_declaration_code(&mut self, decl: &Declaration) -> Result<(), CodegenError> {
        let Declaration { id, init, ctx: _ } = decl;

        self.var_map.insert_global(&id);

        if let Some(expr) = init {
            // unpack constant. we have verified that it is a constant during validation.
            if let Expression::Constant(v) = expr {

                self.emit(CodeLine::i2(".globl", &id));
                self.emit(CodeLine::i1(".data"));
                self.emit(CodeLine::i2(".align", &format!("{}",self.alignment)));
                self.emit(CodeLine::lbl(&id));
                self.emit(CodeLine::i2(".long", &format!("{}",v)));

                // switch back to emitting code
                self.emit(CodeLine::i1(".text"));

                self.var_map.set_global_defined(id);
            } else {
                panic!("Internal error, non-constant initializer for global variable should have been caught during validation.");
            }

        }
        Ok(())
    }

    fn generate_program_code(&mut self, prog: &Program) -> Result<(), CodegenError> {
        let Program::Prog(toplevel_items) = prog;
        for item in toplevel_items {
            match item {
                ToplevelItem::Function(func) => self.generate_function_code(func)?,
                ToplevelItem::Variable(decl) => self.generate_global_declaration_code(decl)?
            }
        }

        // generate code for uninitialized variables
        for gid in self.var_map.get_undefined_globals() {
            self.emit(CodeLine::i2(".globl", &gid));
            self.emit(CodeLine::i1(".bss"));
            self.emit(CodeLine::i2(".align", &format!("{}",self.alignment)));
            self.emit(CodeLine::lbl(&gid));
            self.emit(CodeLine::i2(".zero", "4")); // size of int
        }

        Ok(())
    }
}

pub fn generate_code(prog: &Program, emit_32_bit: bool) -> Result<Code, CodegenError> {
    let mut generator = Generator::new(emit_32_bit);
    generator.generate_program_code(prog)?;

    Ok(generator.code)
}
