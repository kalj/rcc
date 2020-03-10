use std::collections::{HashMap, HashSet};

use crate::ast::{AssignmentKind, BinaryOp, FixOp, UnaryOp};
use crate::ast::{BlockItem, CompoundStatement, Declaration, Expression, Function, Program, Statement};

//===================================================================
// Code generation
//===================================================================

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
    regsize: u8,
    stack_index: i32,
    block_decl_set: HashSet<String>,
}

impl VarMap {
    fn new(regsize: u8) -> VarMap {
        VarMap { addr_map: HashMap::new(), regsize, stack_index: -(regsize as i32), block_decl_set: HashSet::new() }
    }

    fn block_decl(&self, name: &str) -> bool {
        self.block_decl_set.contains(name)
    }

    fn insert(&mut self, name: &str) {
        self.addr_map.insert(name.to_string(), self.stack_index);
        self.stack_index -= self.regsize as i32;
        self.block_decl_set.insert(name.to_string());
    }

    fn get(&self, name: &str) -> i32 {
        self.addr_map[name]
    }
}

struct LoopContext {
    break_lbl: Option<String>,
    continue_lbl: Option<String>,
}

pub struct Generator {
    pub code: Code,
    emit_32bit: bool,
    label_counter: i32,
    rega: String,
    regc: String,
    regbp: String,
    regsp: String,
    rega32: String,
    regc32: String,
    regd32: String,
    var_map: VarMap,
    loop_ctx: LoopContext,
}

impl Generator {
    pub fn new(emit_32bit: bool) -> Generator {
        let bytes_per_reg = if emit_32bit { 4 } else { 8 };
        Generator {
            code: Code::new(),
            emit_32bit,
            label_counter: 0,
            rega: (if emit_32bit { "%eax" } else { "%rax" }).to_string(),
            regc: (if emit_32bit { "%ecx" } else { "%rcx" }).to_string(),
            regbp: (if emit_32bit { "%ebp" } else { "%rbp" }).to_string(),
            regsp: (if emit_32bit { "%esp" } else { "%rsp" }).to_string(),
            rega32: "%eax".to_string(),
            regc32: "%ecx".to_string(),
            regd32: "%edx".to_string(),
            var_map: VarMap::new(bytes_per_reg),
            loop_ctx: LoopContext { break_lbl: None, continue_lbl: None },
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
        self.emit(CodeLine::i3("add", &format!("${}", diff_stack_index), &self.regsp));
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
                self.emit(CodeLine::i3("add", &self.regc32, &self.rega32)); //   add, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::Subtraction => {
                self.emit(CodeLine::i3("sub", &self.regc32, &self.rega32)); //   subtract %eax (arg1) - %ecx (arg2) -> %eax
            }
            BinaryOp::Multiplication => {
                self.emit(CodeLine::i3("imul", &self.regc32, &self.rega32)); //  multiply, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::Division | BinaryOp::Remainder => {
                self.emit(CodeLine::i1("cltd")); //                sign extend %eax into %edx:%eax
                self.emit(CodeLine::i2("idiv", &self.regc32)); //  idiv takes numerator in %eax, denominator in arg (%ecx). quotient is put in %eax, remainder in %edx.
                if let BinaryOp::Remainder = binop {
                    self.emit(CodeLine::i3("mov", &self.regd32, &self.rega32)); //   copy remainder into %eax
                }
            }
            BinaryOp::Equal => {
                self.emit(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    set ZF if EAX == ECX
                self.emit(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                self.emit(CodeLine::i2("sete", "%al")); //                        set bit to 1 if ecx (op1) was equal to eax (op2)
            }
            BinaryOp::NotEqual => {
                self.emit(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    set ZF if EAX == ECX
                self.emit(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                self.emit(CodeLine::i2("setne", "%al")); //                       set bit to 1 if ecx (op1) was not equal to eax (op2)
            }
            BinaryOp::Less => {
                self.emit(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                self.emit(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                self.emit(CodeLine::i2("setl", "%al")); //                        set bit to 1 if ecx (op1) was less than eax (op2)
            }
            BinaryOp::Greater => {
                self.emit(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                self.emit(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                self.emit(CodeLine::i2("setg", "%al")); //                        set bit to 1 if ecx (op1) was greater than eax (op2)
            }
            BinaryOp::LessEqual => {
                self.emit(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                self.emit(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                self.emit(CodeLine::i2("setle", "%al")); //                       set bit to 1 if ecx (op1) was less than or equal to eax (op2)
            }
            BinaryOp::GreaterEqual => {
                self.emit(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                self.emit(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                self.emit(CodeLine::i2("setge", "%al")); //                       set bit to 1 if ecx (op1) was greater than or equal to eax (op2)
            }
            BinaryOp::BitwiseOr => {
                self.emit(CodeLine::i3("or", &self.regc32, &self.rega32)); //    and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::BitwiseXor => {
                self.emit(CodeLine::i3("xor", &self.regc32, &self.rega32)); //   and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::BitwiseAnd => {
                self.emit(CodeLine::i3("and", &self.regc32, &self.rega32)); //   and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::LeftShift => {
                self.emit(CodeLine::i3("sal", "%cl", &self.rega32)); //          do arithmetic left shift (== logical left shift), %eax = %eax << %cl
            }
            BinaryOp::RightShift => {
                self.emit(CodeLine::i3("sar", "%cl", &self.rega32)); //          do arithmetic right shift, %eax = %eax >> %cl
            }
            BinaryOp::LogicalAnd | BinaryOp::LogicalOr => {
                panic!("Internal Error"); // Handled above separately
            }
        }
    }

    fn generate_expression_code(&mut self, expr: &Expression) {
        match expr {
            Expression::Constant(val) => {
                let literal = format!("${}", val);
                self.emit(CodeLine::i3("mov", &literal, &self.rega32));
            }
            Expression::Variable(id) => {
                let var_offset = self.var_map.get(id);
                self.emit(CodeLine::i3("mov", &format!("{}({})", var_offset, self.regbp), &self.rega));
            }
            Expression::UnaryOp(uop, expr) => {
                self.generate_expression_code(expr);
                match uop {
                    UnaryOp::Negate => {
                        self.emit(CodeLine::i2("neg", &self.rega32));
                    }
                    UnaryOp::Not => {
                        self.emit(CodeLine::i3("cmp", "$0", &self.rega32));
                        self.emit(CodeLine::i3("mov", "$0", &self.rega32));
                        self.emit(CodeLine::i2("sete", "%al"));
                    }
                    UnaryOp::Complement => {
                        self.emit(CodeLine::i2("not", &self.rega32));
                    }
                }
            }
            Expression::BinaryOp(BinaryOp::LogicalOr, e1, e2) => {
                // setup labels
                let cond2 = self.new_label();
                let end = self.new_label();

                self.generate_expression_code(e1);
                // if true then just jump over second part and set true
                // else evaluate second part and set to return status of that
                self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                self.emit(CodeLine::i2("je", &cond2)); //                            if ZF is set, go to cond2
                self.emit(CodeLine::i3("mov", "$1", &self.rega32)); //               else we are done, so set result to 1,
                self.emit(CodeLine::i2("jmp", &end)); //                             and jump to end.
                self.emit(CodeLine::lbl(&cond2));
                self.generate_expression_code(e2);
                self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                self.emit(CodeLine::i3("mov", "$0", &self.rega32)); //               zero out EAX without changing ZF
                self.emit(CodeLine::i2("setnz", "%al")); //                          set bit to 1 if eax was not zero
                self.emit(CodeLine::lbl(&end));
            }
            Expression::BinaryOp(BinaryOp::LogicalAnd, e1, e2) => {
                // setup labels
                let cond2 = self.new_label();
                let end = self.new_label();

                self.generate_expression_code(e1);
                // if false then just jump over second part and set false
                // else evaluate second part and set to return status of that
                self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                self.emit(CodeLine::i2("jne", &cond2)); //                           if ZF is not set, go to cond2
                self.emit(CodeLine::i2("jmp", &end)); //                             else we are done (and eax is 0), so jump to end.
                self.emit(CodeLine::lbl(&cond2));
                self.generate_expression_code(e2);
                self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                self.emit(CodeLine::i3("mov", "$0", &self.rega32)); //               zero out EAX without changing ZF
                self.emit(CodeLine::i2("setnz", "%al")); //                          set bit to 1 if eax was not zero
                self.emit(CodeLine::lbl(&end));
            }
            Expression::BinaryOp(bop, e1, e2) => {
                self.generate_expression_code(e1);

                self.emit(CodeLine::i2("push", &self.rega));
                self.generate_expression_code(e2);

                self.emit(CodeLine::i3("mov", &self.rega32, &self.regc32)); //   copy arg2 into %ecx
                self.emit(CodeLine::i2("pop", &self.rega)); //                   get arg1 from stack into %eax
                self.generate_binop_code(bop);
            }
            Expression::PrefixOp(fixop, id) => {
                let var_offset = self.var_map.get(id);
                if let FixOp::Inc = fixop {
                    self.emit(CodeLine::i2("incl", &format!("{}({})", var_offset, self.regbp)));
                } else {
                    self.emit(CodeLine::i2("decl", &format!("{}({})", var_offset, self.regbp)));
                }
                self.emit(CodeLine::i3("mov", &format!("{}({})", var_offset, self.regbp), &self.rega));
            }
            Expression::PostfixOp(fixop, id) => {
                let var_offset = self.var_map.get(id);
                self.emit(CodeLine::i3("mov", &format!("{}({})", var_offset, self.regbp), &self.rega));
                if let FixOp::Inc = fixop {
                    self.emit(CodeLine::i2("incl", &format!("{}({})", var_offset, self.regbp)));
                } else {
                    self.emit(CodeLine::i2("decl", &format!("{}({})", var_offset, self.regbp)));
                }
            }
            Expression::Assign(kind, id, expr) => {
                self.generate_expression_code(expr);
                let var_offset = self.var_map.get(id);

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
                    self.emit(CodeLine::i3("mov", &self.rega32, &self.regc32));
                    self.emit(CodeLine::i3("mov", &format!("{}({})", var_offset, self.regbp), &self.rega32));
                    self.generate_binop_code(&bop);
                }

                self.emit(CodeLine::i3("mov", &self.rega32, &format!("{}({})", var_offset, self.regbp)));
            }
            Expression::Conditional(condexpr, ifexpr, elseexpr) => {
                // setup labels
                let else_case = self.new_label();
                let end = self.new_label();

                self.generate_expression_code(condexpr);

                self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                self.emit(CodeLine::i2("je", &else_case)); //                        if ZF is set, go to else_case

                self.generate_expression_code(ifexpr); //                            else execute ifexpr
                self.emit(CodeLine::i2("jmp", &end)); //                             then jump to end

                self.emit(CodeLine::lbl(&else_case));
                self.generate_expression_code(elseexpr);
                self.emit(CodeLine::lbl(&end));
            }
            Expression::FunctionCall(id, args) => {}
        }
    }

    fn generate_declaration_code(&mut self, decl: &Declaration) {
        let Declaration { id, init } = decl;
        if self.var_map.block_decl(id) {
            panic!("Variable {} already declared in block", id);
        }
        if let Some(expr) = init {
            self.generate_expression_code(&expr); //                   possibly compute initial value, saved in %rax
        } else {
            self.emit(CodeLine::i3("mov", "$0", &self.rega)); //       otherwise initialize %rax with 0
        }
        self.emit(CodeLine::i2("push", &self.rega)); //                push value on stack at known index
        self.var_map.insert(id); //                                    save new variable
    }

    fn generate_statement_code(&mut self, stmnt: &Statement) {
        match stmnt {
            Statement::Return(expr) => {
                self.generate_expression_code(&expr);
                self.emit(CodeLine::i3("mov", &self.regbp, &self.regsp));
                self.emit(CodeLine::i2("pop", &self.regbp));
                self.emit(CodeLine::i1("ret"));
            }
            Statement::Break => self.emit(CodeLine::i2(
                "jmp",
                &self.loop_ctx.break_lbl.as_ref().expect("Invalid break not inside a loop or switch statement"),
            )),
            Statement::Continue => self.emit(CodeLine::i2(
                "jmp",
                &self.loop_ctx.continue_lbl.as_ref().expect("Invalid continue not inside a loop"),
            )),
            Statement::Expr(expr) => self.generate_expression_code(&expr),
            Statement::Null => {}
            Statement::If(condexpr, ifstmt, maybe_elsestmt) => {
                if let Some(elsestmt) = maybe_elsestmt {
                    // setup labels
                    let else_case = self.new_label();
                    let end = self.new_label();

                    self.generate_expression_code(&condexpr);

                    self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                    self.emit(CodeLine::i2("je", &else_case)); //                        if ZF is set, go to else_case

                    self.generate_statement_code(ifstmt); //                             else execute ifstmt
                    self.emit(CodeLine::i2("jmp", &end)); //                             then jump to end

                    self.emit(CodeLine::lbl(&else_case));
                    self.generate_statement_code(elsestmt);
                    self.emit(CodeLine::lbl(&end));
                } else {
                    // setup label
                    let end = self.new_label();

                    self.generate_expression_code(&condexpr);

                    self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                    self.emit(CodeLine::i2("je", &end)); //                              if ZF is set, go to end

                    self.generate_statement_code(ifstmt); //                             else execute ifexpr

                    self.emit(CodeLine::lbl(&end));
                }
            }
            Statement::While(cond, body) => {
                // setup labels
                let start = self.new_label();
                let end = self.new_label();
                let old_loop_ctx = self.new_loop_context(&end, &start);

                self.emit(CodeLine::lbl(&start));
                self.generate_expression_code(&cond);

                self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                self.emit(CodeLine::i2("je", &end)); //                              if ZF is set, go to end

                self.generate_statement_code(body); //                               else execute body
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

                self.generate_statement_code(body); //                               execute body

                self.generate_expression_code(&cond);

                self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               check if false (set ZF if EAX == 0)
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
                    self.generate_expression_code(&initexpr);
                }

                self.emit(CodeLine::lbl(&start));
                self.generate_expression_code(&cond);

                self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                self.emit(CodeLine::i2("je", &end)); //                              if ZF is set, go to end

                self.generate_statement_code(body); //                               else execute body

                self.emit(CodeLine::lbl(&cnt)); //                                   jump here from continue in body
                if let Some(postexpr) = maybe_postexpr {
                    self.generate_expression_code(&postexpr);
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

                self.generate_declaration_code(&initdecl);

                self.emit(CodeLine::lbl(&start));
                self.generate_expression_code(&cond);

                self.emit(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                self.emit(CodeLine::i2("je", &end)); //                              if ZF is set, go to end

                self.generate_statement_code(body); //                               else execute body

                self.emit(CodeLine::lbl(&cnt)); //                                   jump here from continue in body
                if let Some(postexpr) = maybe_postexpr {
                    self.generate_expression_code(&postexpr);
                }

                self.emit(CodeLine::i2("jmp", &start)); //                           and go to next iteration

                self.emit(CodeLine::lbl(&end));

                // restore old scope
                self.restore_scope(old_scope);

                self.restore_loop_context(old_loop_ctx);
            }
            Statement::Compound(comp) => self.generate_compound_statement(comp),
        }
    }

    fn generate_block_item_code(&mut self, bkitem: &BlockItem) {
        match bkitem {
            BlockItem::Decl(decl) => self.generate_declaration_code(decl),
            BlockItem::Stmt(stmt) => self.generate_statement_code(&stmt),
        }
    }

    fn generate_compound_statement(&mut self, comp: &CompoundStatement) {
        let old_scope = self.new_scope();

        for bkitem in &comp.block_items {
            self.generate_block_item_code(bkitem);
        }

        // restore old scope
        self.restore_scope(old_scope);
    }

    fn generate_function_code(&mut self, func: Function) {
        match func {
            Function::Declaration(name, parameters) => {}
            Function::Definition(name, parameters, body) => {
                self.emit(CodeLine::i2(".globl", &name));
                self.emit(CodeLine::lbl(&name));
                self.emit(CodeLine::i2("push", &self.regbp));
                self.emit(CodeLine::i3("mov", &self.regsp, &self.regbp));
                self.generate_compound_statement(&body);

                if !self.code.code.iter().any(|cl| if let CodeLine::Instr1(op) = cl { op == "ret" } else { false }) {
                    self.generate_statement_code(&Statement::Return(Expression::Constant(0)));
                }
            }
        }
    }

    pub fn generate_program_code(&mut self, prog: Program) {
        let Program::Prog(funcs) = prog;
        for func in funcs {
            self.generate_function_code(func);
        }
    }
}
