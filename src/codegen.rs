use std::collections::HashMap;

use crate::ast::{AssignmentKind, BinaryOp, FixOp, UnaryOp};
use crate::ast::{BlockItem, CompoundStatement, Expression, Function, Program, Statement};

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

    fn append(&mut self, mut more: Code) {
        self.code.append(&mut more.code);
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

pub struct Generator {
    emit_32bit: bool,
    label_counter: i32,
    rega: String,
    regc: String,
    regbp: String,
    regsp: String,
    rega32: String,
    regc32: String,
    regd32: String,
    bytes_per_reg: usize,
    var_map: HashMap<String, i32>,
    var_stack_index: i32,
}

impl Generator {
    pub fn new(emit_32bit: bool) -> Generator {
        let bytes_per_reg = if emit_32bit { 4 } else { 8 };
        Generator {
            emit_32bit,
            label_counter: 0,
            rega: (if emit_32bit { "%eax" } else { "%rax" }).to_string(),
            regc: (if emit_32bit { "%ecx" } else { "%rcx" }).to_string(),
            regbp: (if emit_32bit { "%ebp" } else { "%rbp" }).to_string(),
            regsp: (if emit_32bit { "%esp" } else { "%rsp" }).to_string(),
            rega32: "%eax".to_string(),
            regc32: "%ecx".to_string(),
            regd32: "%edx".to_string(),
            bytes_per_reg,
            var_map: HashMap::new(),
            var_stack_index: -(bytes_per_reg as i32),
        }
    }

    fn generate_binop_code(&self, binop: &BinaryOp) -> Code {
        let mut code = Code::new();

        match binop {
            BinaryOp::Addition => {
                code.push(CodeLine::i3("add", &self.regc32, &self.rega32)); //   add, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::Subtraction => {
                code.push(CodeLine::i3("sub", &self.regc32, &self.rega32)); //   subtract %eax (arg1) - %ecx (arg2) -> %eax
            }
            BinaryOp::Multiplication => {
                code.push(CodeLine::i3("imul", &self.regc32, &self.rega32)); //  multiply, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::Division | BinaryOp::Remainder => {
                code.push(CodeLine::i1("cltd")); //                sign extend %eax into %edx:%eax
                code.push(CodeLine::i2("idiv", &self.regc32)); //  idiv takes numerator in %eax, denominator in arg (%ecx). quotient is put in %eax, remainder in %edx.
                if let BinaryOp::Remainder = binop {
                    code.push(CodeLine::i3("mov", &self.regd32, &self.rega32)); //   copy remainder into %eax
                }
            }
            BinaryOp::Equal => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    set ZF if EAX == ECX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("sete", "%al")); //                        set bit to 1 if ecx (op1) was equal to eax (op2)
            }
            BinaryOp::NotEqual => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    set ZF if EAX == ECX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("setne", "%al")); //                       set bit to 1 if ecx (op1) was not equal to eax (op2)
            }
            BinaryOp::Less => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("setl", "%al")); //                        set bit to 1 if ecx (op1) was less than eax (op2)
            }
            BinaryOp::Greater => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("setg", "%al")); //                        set bit to 1 if ecx (op1) was greater than eax (op2)
            }
            BinaryOp::LessEqual => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("setle", "%al")); //                       set bit to 1 if ecx (op1) was less than or equal to eax (op2)
            }
            BinaryOp::GreaterEqual => {
                code.push(CodeLine::i3("cmp", &self.regc32, &self.rega32)); //    compare ECX and EAX
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //            zero out EAX without changing ZF
                code.push(CodeLine::i2("setge", "%al")); //                       set bit to 1 if ecx (op1) was greater than or equal to eax (op2)
            }
            BinaryOp::BitwiseOr => {
                code.push(CodeLine::i3("or", &self.regc32, &self.rega32)); //    and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::BitwiseXor => {
                code.push(CodeLine::i3("xor", &self.regc32, &self.rega32)); //   and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::BitwiseAnd => {
                code.push(CodeLine::i3("and", &self.regc32, &self.rega32)); //   and, arg1 is in %ecx, arg2 is in %eax, and result is in %eax
            }
            BinaryOp::LeftShift => {
                code.push(CodeLine::i3("sal", "%cl", &self.rega32)); //          do arithmetic left shift (== logical left shift), %eax = %eax << %cl
            }
            BinaryOp::RightShift => {
                code.push(CodeLine::i3("sar", "%cl", &self.rega32)); //          do arithmetic right shift, %eax = %eax >> %cl
            }
            BinaryOp::LogicalAnd | BinaryOp::LogicalOr => {
                panic!("Internal Error"); // Handled above separately
            }
        }

        code
    }

    fn generate_expression_code(&mut self, expr: &Expression) -> Code {
        let mut code = Code::new();
        match expr {
            Expression::Constant(val) => {
                let literal = format!("${}", val);
                code.push(CodeLine::i3("mov", &literal, &self.rega32));
            }
            Expression::Variable(id) => {
                let var_offset = self.var_map[id];
                code.push(CodeLine::i3("mov", &format!("{}({})", var_offset, self.regbp), &self.rega));
            }
            Expression::UnaryOp(uop, expr) => {
                code = self.generate_expression_code(expr);
                match uop {
                    UnaryOp::Negate => {
                        code.push(CodeLine::i2("neg", &self.rega32));
                    }
                    UnaryOp::Not => {
                        code.push(CodeLine::i3("cmp", "$0", &self.rega32));
                        code.push(CodeLine::i3("mov", "$0", &self.rega32));
                        code.push(CodeLine::i2("sete", "%al"));
                    }
                    UnaryOp::Complement => {
                        code.push(CodeLine::i2("not", &self.rega32));
                    }
                }
            }
            Expression::BinaryOp(BinaryOp::LogicalOr, e1, e2) => {
                // setup labels
                let cond2 = format!("_label{}", self.label_counter);
                let end = format!("_label{}", self.label_counter + 1);
                self.label_counter += 2;

                code = self.generate_expression_code(e1);
                // if true then just jump over second part and set true
                // else evaluate second part and set to return status of that
                code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                code.push(CodeLine::i2("je", &cond2)); //                            if ZF is set, go to cond2
                code.push(CodeLine::i3("mov", "$1", &self.rega32)); //               else we are done, so set result to 1,
                code.push(CodeLine::i2("jmp", &end)); //                             and jump to end.
                code.push(CodeLine::lbl(&cond2));
                code.append(self.generate_expression_code(e2));
                code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //               zero out EAX without changing ZF
                code.push(CodeLine::i2("setnz", "%al")); //                          set bit to 1 if eax was not zero
                code.push(CodeLine::lbl(&end));
            }
            Expression::BinaryOp(BinaryOp::LogicalAnd, e1, e2) => {
                // setup labels
                let cond2 = format!("_label{}", self.label_counter);
                let end = format!("_label{}", self.label_counter + 1);
                self.label_counter += 2;

                code = self.generate_expression_code(e1);
                // if false then just jump over second part and set false
                // else evaluate second part and set to return status of that
                code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                code.push(CodeLine::i2("jne", &cond2)); //                           if ZF is not set, go to cond2
                code.push(CodeLine::i2("jmp", &end)); //                             else we are done (and eax is 0), so jump to end.
                code.push(CodeLine::lbl(&cond2));
                code.append(self.generate_expression_code(e2));
                code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                code.push(CodeLine::i3("mov", "$0", &self.rega32)); //               zero out EAX without changing ZF
                code.push(CodeLine::i2("setnz", "%al")); //                          set bit to 1 if eax was not zero
                code.push(CodeLine::lbl(&end));
            }
            Expression::BinaryOp(bop, e1, e2) => {
                code = self.generate_expression_code(e1);

                code.push(CodeLine::i2("push", &self.rega));
                code.append(self.generate_expression_code(e2));

                code.push(CodeLine::i3("mov", &self.rega32, &self.regc32)); //   copy arg2 into %ecx
                code.push(CodeLine::i2("pop", &self.rega)); //                   get arg1 from stack into %eax
                code.append(self.generate_binop_code(bop))
            }
            Expression::PrefixOp(fixop, id) => {
                let var_offset = self.var_map[id];
                if let FixOp::Inc = fixop {
                    code.push(CodeLine::i2("incl", &format!("{}({})", var_offset, self.regbp)));
                } else {
                    code.push(CodeLine::i2("decl", &format!("{}({})", var_offset, self.regbp)));
                }
                code.push(CodeLine::i3("mov", &format!("{}({})", var_offset, self.regbp), &self.rega));
            }
            Expression::PostfixOp(fixop, id) => {
                let var_offset = self.var_map[id];
                code.push(CodeLine::i3("mov", &format!("{}({})", var_offset, self.regbp), &self.rega));
                if let FixOp::Inc = fixop {
                    code.push(CodeLine::i2("incl", &format!("{}({})", var_offset, self.regbp)));
                } else {
                    code.push(CodeLine::i2("decl", &format!("{}({})", var_offset, self.regbp)));
                }
            }
            Expression::Assign(kind, id, expr) => {
                code = self.generate_expression_code(expr);
                let var_offset = self.var_map[id];

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
                    code.push(CodeLine::i3("mov", &self.rega32, &self.regc32));
                    code.push(CodeLine::i3("mov", &format!("{}({})", var_offset, self.regbp), &self.rega32));
                    code.append(self.generate_binop_code(&bop));
                }

                code.push(CodeLine::i3("mov", &self.rega32, &format!("{}({})", var_offset, self.regbp)));
            }
            Expression::Conditional(condexpr, ifexpr, elseexpr) => {
                // setup labels
                let else_case = format!("_label{}", self.label_counter);
                let end = format!("_label{}", self.label_counter + 1);
                self.label_counter += 2;

                code = self.generate_expression_code(condexpr);

                code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                code.push(CodeLine::i2("je", &else_case)); //                        if ZF is not set, go to else_case

                code.append(self.generate_expression_code(ifexpr)); //               else execute ifexpr
                code.push(CodeLine::i2("jmp", &end)); //                             then jump to end

                code.push(CodeLine::lbl(&else_case));
                code.append(self.generate_expression_code(elseexpr));
                code.push(CodeLine::lbl(&end));
            }
        }
        code
    }

    fn generate_statement_code(&mut self, stmnt: &Statement) -> Code {
        match stmnt {
            Statement::Return(expr) => {
                let mut code = self.generate_expression_code(&expr);
                code.push(CodeLine::i3("mov", &self.regbp, &self.regsp));
                code.push(CodeLine::i2("pop", &self.regbp));
                code.push(CodeLine::i1("ret"));
                code
            }
            Statement::Expr(expr) => self.generate_expression_code(&expr),
            Statement::If(condexpr, ifstmt, maybe_elsestmt) => {
                let mut code;

                if let Some(elsestmt) = maybe_elsestmt {
                    // setup labels
                    let else_case = format!("_label{}", self.label_counter);
                    self.label_counter += 1;
                    let end = format!("_label{}", self.label_counter);
                    self.label_counter += 1;

                    code = self.generate_expression_code(&condexpr);

                    code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                    code.push(CodeLine::i2("je", &else_case)); //                        if ZF is not set, go to else_case

                    code.append(self.generate_statement_code(ifstmt)); //                else execute ifstmt
                    code.push(CodeLine::i2("jmp", &end)); //                             then jump to end

                    code.push(CodeLine::lbl(&else_case));
                    code.append(self.generate_statement_code(elsestmt));
                    code.push(CodeLine::lbl(&end));
                } else {
                    // setup label
                    let end = format!("_label{}", self.label_counter);
                    self.label_counter += 1;

                    code = self.generate_expression_code(&condexpr);

                    code.push(CodeLine::i3("cmp", "$0", &self.rega32)); //               set ZF if EAX == 0
                    code.push(CodeLine::i2("je", &end)); //                              if ZF is not set, go to end

                    code.append(self.generate_statement_code(ifstmt)); //                else execute ifexpr

                    code.push(CodeLine::lbl(&end));
                }

                code
            }
            Statement::Compound(comp) => self.generate_compound_statement(comp),
        }
    }

    fn generate_compound_statement(&mut self, comp: &CompoundStatement) -> Code {
        let mut code = Code::new();
        for bkitem in &comp.block_items {
            code.append(self.generate_block_item_code(bkitem));
        }

        code
    }

    fn generate_block_item_code(&mut self, bkitem: &BlockItem) -> Code {
        let mut code = Code::new();
        match bkitem {
            BlockItem::Decl(id, init) => {
                if self.var_map.contains_key(id) {
                    panic!("Variable {} already declared", id);
                }
                if let Some(expr) = init {
                    code = self.generate_expression_code(&expr); //            possibly compute initial value, saved in %rax
                } else {
                    code.push(CodeLine::i3("mov", "$0", &self.rega)); //       otherwise initialize %rax with 0
                }
                code.push(CodeLine::i2("push", &self.rega)); //                push value on stack at known index
                self.var_map.insert(id.to_string(), self.var_stack_index); //  save name and stack offset
                self.var_stack_index -= self.bytes_per_reg as i32; //          update stack index
            }
            BlockItem::Stmt(stmt) => {
                code = self.generate_statement_code(&stmt);
            }
        }

        code
    }

    fn generate_function_code(&mut self, func: Function) -> Code {
        let mut code = Code::new();

        let Function::Func(name, body) = func;
        code.push(CodeLine::i2(".globl", &name));
        code.push(CodeLine::lbl(&name));
        code.push(CodeLine::i2("push", &self.regbp));
        code.push(CodeLine::i3("mov", &self.regsp, &self.regbp));
        code.append(self.generate_compound_statement(&body));

        if !code.code.iter().any(|cl| if let CodeLine::Instr1(op) = cl { op == "ret" } else { false }) {
            code.append(self.generate_statement_code(&Statement::Return(Expression::Constant(0))));
        }
        code
    }

    pub fn generate_program_code(&mut self, prog: Program) -> Code {
        let Program::Prog(func) = prog;
        self.generate_function_code(func)
    }
}
