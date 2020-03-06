
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
}

#[derive(Debug)]
pub enum Statement {
    Return(Expression),
    Expr(Expression),
    If(Expression, Box<Statement>, Option<Box<Statement>>),
}

#[derive(Debug)]
pub enum BlockItem {
    Stmt(Statement),
    Decl(String, Option<Expression>),
}

#[derive(Debug)]
pub enum Function {
    Func(String, Vec<BlockItem>),
}

#[derive(Debug)]
pub enum Program {
    Prog(Function),
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
    }
}

fn print_statement(stmt: &Statement, lvl: i32) {
    match stmt {
        Statement::Return(expr) => {
            println!("{: <1$}Return {{", "", (lvl * 2) as usize);
            print_expression(expr, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
        Statement::Expr(expr) => {
            println!("{: <1$}Expr {{", "", (lvl * 2) as usize);
            print_expression(expr, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
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
    }
}

fn print_block_item(bkitem: &BlockItem, lvl: i32) {
    match bkitem {
        BlockItem::Stmt(stmt) => {
            println!("{: <1$}Statement {{", "", (lvl * 2) as usize);
            print_statement(stmt, lvl + 1);
            println!("{: <1$}}}", "", (lvl * 2) as usize);
        }
        BlockItem::Decl(id, init) => {
            if let Some(expr) = init {
                println!("{: <1$}Decl {2:?} {{", "", (lvl * 2) as usize, id);
                print_expression(expr, lvl + 1);
                println!("{: <1$}}}", "", (lvl * 2) as usize);
            } else {
                println!("{: <1$}Decl {2:?}", "", (lvl * 2) as usize, id);
            }
        }
    }
}

pub fn print_program(prog: &Program) {
    let lvl = 0;
    println!("Program {{");
    let Program::Prog(Function::Func(name, bkitems)) = prog;
    println!("  Function \"{}\" {{", name);
    for bkitem in bkitems {
        print_block_item(bkitem, lvl + 2);
    }
    println!("  }}");
    println!("}}");
}
