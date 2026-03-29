use std::collections::HashMap;

use crate::typechecker::Type;

pub(crate) type StlModuleExports = HashMap<String, Type>;
pub(crate) type StlRegistry = HashMap<String, StlModuleExports>;
