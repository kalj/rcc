use crate::ast::{AstContext, FunctionParameter, FunctionParameters, Type};
use std::collections::HashMap;

#[derive(Clone)]
pub struct FunctionSymbol {
    pub params: Option<Vec<FunctionParameter>>,
    pub ret: Type,
    pub has_definition: bool,
    pub ctx: AstContext,
}

impl FunctionSymbol {
    pub fn new(ret: &Type, fparams: &FunctionParameters, has_def: bool, ctx: &AstContext) -> FunctionSymbol {
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
        FunctionSymbol { ret: ret.clone(), params, has_definition: has_def, ctx: ctx.clone() }
    }
}

#[derive(Clone)]
pub struct LocalVariableSymbol {
    pub typ: Type,
    pub stack_offset: Option<i32>,
}

impl LocalVariableSymbol {
    pub fn new(typ: &Type) -> LocalVariableSymbol {
        LocalVariableSymbol { typ: typ.clone(), stack_offset: None }
    }
    pub fn new_with_stack_offset(typ: &Type, stack_offset: i32) -> LocalVariableSymbol {
        LocalVariableSymbol { typ: typ.clone(), stack_offset: Some(stack_offset) }
    }
}

#[derive(Clone)]
pub struct GlobalVariableSymbol {
    pub typ: Type,
    pub has_definition: bool,
    pub ctx: AstContext,
}

impl GlobalVariableSymbol {
    pub fn new(typ: &Type, has_definition: bool, ctx: &AstContext) -> GlobalVariableSymbol {
        GlobalVariableSymbol { typ: typ.clone(), has_definition, ctx: ctx.clone() }
    }
}

pub struct SymbolTable {
    functions: HashMap<String, FunctionSymbol>,
    globals: HashMap<String, GlobalVariableSymbol>,
    locals: Vec<HashMap<String, LocalVariableSymbol>>,
}

impl SymbolTable {
    pub fn new() -> SymbolTable {
        SymbolTable { locals: Vec::new(), globals: HashMap::new(), functions: HashMap::new() }
    }

    pub fn new_scope(&mut self) {
        self.locals.push(HashMap::new());
    }

    pub fn end_scope(&mut self) {
        self.locals.pop();
    }

    pub fn insert_local(&mut self, id: &str, loc: LocalVariableSymbol) {
        let current = &mut self.locals.last_mut().unwrap();
        current.insert(id.to_string(), loc);
    }

    pub fn insert_global(&mut self, id: &str, glob: GlobalVariableSymbol) {
        self.globals.insert(id.to_string(), glob);
    }

    pub fn insert_function(&mut self, id: &str, func: FunctionSymbol) {
        self.functions.insert(id.to_string(), func);
    }

    pub fn contains(&self, id: &str) -> bool {
        for map in self.locals.iter().rev() {
            if map.contains_key(id) {
                return true;
            }
        }

        if self.globals.contains_key(id) {
            return true;
        }

        if self.functions.contains_key(id) {
            return true;
        }

        false
    }

    pub fn has_static_storage(&self, id: &str) -> bool {
        self.globals.contains_key(id)
    }

    pub fn declared_in_scope(&self, id: &str) -> bool {
        self.locals.last().unwrap().contains_key(id)
    }

    pub fn get_local(&self, id: &str) -> Option<LocalVariableSymbol> {
        for map in self.locals.iter().rev() {
            if map.contains_key(id) {
                return Some(map[id].clone());
            }
        }
        None
    }

    pub fn get_global(&self, id: &str) -> Option<GlobalVariableSymbol> {
        if self.globals.contains_key(id) {
            return Some(self.globals[id].clone());
        }
        None
    }

    pub fn get_globals(&self) -> HashMap<String, GlobalVariableSymbol> {
        self.globals.clone()
    }

    pub fn get_function(&self, id: &str) -> Option<FunctionSymbol> {
        if self.functions.contains_key(id) {
            return Some(self.functions[id].clone());
        }
        None
    }

    pub fn get_variable_type(&self, id: &str) -> Option<Type> {
        for map in self.locals.iter().rev() {
            if map.contains_key(id) {
                return Some(map[id].typ.clone());
            }
        }

        if self.globals.contains_key(id) {
            return Some(self.globals[id].typ.clone());
        }

        None
    }
}
