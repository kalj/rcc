#[derive(Debug)]
pub enum BinaryOp {
    Addition,
    Subtraction,
    Multiplication,
    Division,
    Remainder,
    LogicalAnd,
    LogicalOr,
    Equal,
    NotEqual,
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    LeftShift,
    RightShift,
}

#[derive(Debug)]
pub enum UnaryOp {
    Negate,
    Not,
    Complement,
}

#[derive(Debug)]
pub enum AssignmentKind {
    Write,
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    BitwiseXor,
    BitwiseOr,
    BitwiseAnd,
    LeftShift,
    RightShift,
}

#[derive(Debug)]
pub enum FixOp {
    Inc,
    Dec,
}

#[derive(Debug)]
pub enum Expression {
    Assign(AssignmentKind, String, Box<Expression>),
    BinaryOp(BinaryOp, Box<Expression>, Box<Expression>),
    UnaryOp(UnaryOp, Box<Expression>),
    PrefixOp(FixOp, String),
    PostfixOp(FixOp, String),
    Constant(i64),
    Variable(String),
    Conditional(Box<Expression>, Box<Expression>, Box<Expression>),
    FunctionCall(String, Vec<Expression>),
}

#[derive(Debug)]
pub struct CompoundStatement {
    pub block_items: Vec<BlockItem>,
}

#[derive(Debug)]
pub struct Declaration {
    pub id: String,
    pub init: Option<Expression>,
}

#[derive(Debug)]
pub enum Statement {
    Null,
    Return(Expression),
    Expr(Expression),
    If(Expression, Box<Statement>, Option<Box<Statement>>),
    Compound(CompoundStatement),
    For(Option<Expression>, Expression, Option<Expression>, Box<Statement>),
    ForDecl(Declaration, Expression, Option<Expression>, Box<Statement>),
    While(Expression, Box<Statement>),
    DoWhile(Box<Statement>, Expression),
    Continue,
    Break,
}

#[derive(Debug)]
pub enum BlockItem {
    Stmt(Statement),
    Decl(Declaration),
}

#[derive(Debug)]
pub enum Function {
    Declaration(String, Vec<String>),
    Definition(String, Vec<String>, CompoundStatement),
}

#[derive(Debug)]
pub enum Program {
    Prog(Vec<Function>),
}

fn print_expression(expr: &Expression, lvl: i32) {
    match expr {
        Expression::Assign(kind, var, exp) => {
            println!("{:<1$}Assign {2:?} {3:?} {{", "", (lvl * 2) as usize, var, kind);
            print_expression(exp, lvl + 1);
            println!("{:<1$}}}", "", (lvl * 2) as usize);
        }
        Expression::BinaryOp(binop, exp1, exp2) => {
            println!("{:<1$}BinaryOp {2:?} {{", "", (lvl * 2) as usize, binop);
            print_expression(exp1, lvl + 1);
            print_expression(exp2, lvl + 1);
            println!("{:<1$}}}", "", (lvl * 2) as usize);
        }
        Expression::UnaryOp(unop, exp) => {
            println!("{:<1$}UnaryOp {2:?} {{", "", (lvl * 2) as usize, unop);
            print_expression(exp, lvl + 1);
            println!("{:<1$}}}", "", (lvl * 2) as usize);
        }
        Expression::PrefixOp(fop, id) => {
            println!("{:<1$}PrefixOp {2:?} {3:?}", "", (lvl * 2) as usize, fop, id);
        }
        Expression::PostfixOp(fop, id) => {
            println!("{:<1$}PrefixOp {2:?} {3:?}", "", (lvl * 2) as usize, id, fop);
        }
        Expression::Variable(id) => {
            println!("{0:<1$}Variable {2}", "", (lvl * 2) as usize, id);
        }
        Expression::Constant(val) => {
            println!("{0:<1$}Constant {2}", "", (lvl * 2) as usize, val);
        }
        Expression::Conditional(condexpr, ifexpr, elseexpr) => {
            println!("{:<1$}Conditional {{", "", (lvl * 2) as usize);
            print_expression(condexpr, lvl + 1);
            print_expression(ifexpr, lvl + 1);
            print_expression(elseexpr, lvl + 1);
            println!("{:<1$}}}", "", (lvl * 2) as usize);
        }
        Expression::FunctionCall(id, arguments) => {
            println!("{:<1$}FunctionCall {2} {{", "", (lvl * 2) as usize, id);
            for arg in arguments {
                print_expression(arg, lvl + 1);
            }
            println!("{:<1$}}}", "", (lvl * 2) as usize);
        }
    }
}

fn print_compound_statement(comp: &CompoundStatement, lvl: i32) {
    println!("{: <1$}Compound {{", "", (lvl * 2) as usize);
    for bkitem in &comp.block_items {
        print_block_item(bkitem, lvl + 1);
    }
    println!("{: <1$}}}", "", (lvl * 2) as usize);
}

fn print_statement(stmt: &Statement, lvl: i32) {
    match stmt {
        Statement::Return(expr) => {
            println!("{: <1$}Return {{", "", (lvl * 2) as usize);
            print_expression(expr, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
        Statement::Break => println!("{: <1$}Break", "", (lvl * 2) as usize),
        Statement::Continue => println!("{: <1$}Continue", "", (lvl * 2) as usize),
        Statement::Expr(expr) => {
            println!("{: <1$}Expr {{", "", (lvl * 2) as usize);
            print_expression(expr, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
        Statement::Null => {
            println!("{: <1$}NullStatement", "", (lvl * 2) as usize);
        }
        Statement::If(cond, if_stmt, else_stmt) => {
            println!("{: <1$}If {{", "", (lvl * 2) as usize);
            print_expression(cond, lvl + 1);
            print_statement(if_stmt, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
            if let Some(stmt) = else_stmt {
                println!("{: <1$}Else {{", "", (lvl * 2) as usize);
                print_statement(stmt, lvl + 1);
                println!("{: <1$}}}", "", (lvl * 2) as usize);
            }
        }
        Statement::Compound(comp_stmt) => {
            print_compound_statement(comp_stmt, lvl);
        }
        Statement::While(cond, body) => {
            println!("{: <1$}While {{", "", (lvl * 2) as usize);
            println!("{: <1$} Condition:", "", (lvl * 2) as usize);
            print_expression(cond, lvl + 1);
            println!("{: <1$} Body:", "", (lvl * 2) as usize);
            print_statement(body, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
        Statement::DoWhile(body, cond) => {
            println!("{: <1$}DoWhile {{", "", (lvl * 2) as usize);
            println!("{: <1$} Body:", "", (lvl * 2) as usize);
            print_statement(body, lvl + 1);
            println!("{: <1$} Condition:", "", (lvl * 2) as usize);
            print_expression(cond, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
        Statement::For(maybe_initexpr, cond, maybe_postexpr, body) => {
            println!("{: <1$}For {{", "", (lvl * 2) as usize);

            println!("{: <1$} InitExpression:", "", (lvl * 2) as usize);
            if let Some(initexpr) = maybe_initexpr {
                print_expression(initexpr, lvl + 1);
            }

            println!("{: <1$} Condition:", "", (lvl * 2) as usize);
            print_expression(cond, lvl + 1);

            println!("{: <1$} PostExpression:", "", (lvl * 2) as usize);
            if let Some(postexpr) = maybe_postexpr {
                print_expression(postexpr, lvl + 1);
            }

            println!("{: <1$} Body:", "", (lvl * 2) as usize);
            print_statement(body, lvl + 1);

            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
        Statement::ForDecl(initdecl, cond, maybe_postexpr, body) => {
            println!("{: <1$}ForDecl {{", "", (lvl * 2) as usize);

            println!("{: <1$} InitDeclaration:", "", (lvl * 2) as usize);
            print_declaration(initdecl, lvl + 1);

            println!("{: <1$} Condition:", "", (lvl * 2) as usize);
            print_expression(cond, lvl + 1);

            println!("{: <1$} PostExpression:", "", (lvl * 2) as usize);
            if let Some(postexpr) = maybe_postexpr {
                print_expression(postexpr, lvl + 1);
            }

            println!("{: <1$} Body:", "", (lvl * 2) as usize);
            print_statement(body, lvl + 1);

            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
    }
}

fn print_declaration(decl: &Declaration, lvl: i32) {
    let Declaration { id, init } = decl;
    if let Some(expr) = init {
        println!("{: <1$}Decl {2:?} {{", "", (lvl * 2) as usize, id);
        print_expression(expr, lvl + 1);
        println!("{: <1$}}}", "", (lvl * 2) as usize);
    } else {
        println!("{: <1$}Decl {2:?}", "", (lvl * 2) as usize, id);
    }
}

fn print_block_item(bkitem: &BlockItem, lvl: i32) {
    match bkitem {
        BlockItem::Stmt(stmt) => {
            println!("{: <1$}Statement {{", "", (lvl * 2) as usize);
            print_statement(stmt, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
        BlockItem::Decl(decl) => {
            print_declaration(decl, lvl);
        }
    }
}

fn print_function(func: &Function, lvl: i32) {
    match func {
        Function::Declaration(id, parameters) => {
            let parameter_string = parameters.join(", ");
            println!("{: <1$}FunctionDeclaration {2} ({3})", "", (lvl * 2) as usize, id, parameter_string);
        }
        Function::Definition(id, parameters, body) => {
            let parameter_string = parameters.join(", ");
            print!("{: <1$}FunctionDefinition {2} ({3}) {{", "", (lvl * 2) as usize, id, parameter_string);
            print_compound_statement(body, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
    }
}

pub fn print_program(prog: &Program) {
    let lvl = 0;
    println!("Program {{");
    let Program::Prog(funcs) = prog;
    for f in funcs {
        print_function(f, lvl + 1);
    }
    println!("}}");
}
