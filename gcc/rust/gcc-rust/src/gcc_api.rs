#![allow(dead_code)]

use std::{
    convert::TryInto,
    ffi::{CStr, CString},
    ops::{Deref, DerefMut},
    os::raw::c_char,
    ptr::{null_mut, NonNull},
};

use crate::gcc_api_sys::*;

pub fn get_crate_type() -> Option<String> {
    unsafe { crate_type }.map(|p| {
        unsafe { CStr::from_ptr(p.as_ptr()) }
            .to_str()
            .unwrap()
            .to_string()
    })
}

#[repr(transparent)]
pub struct Location(location_t);

pub const UNKNOWN_LOCATION: Location = Location(0);
pub const BUILTINS_LOCATION: Location = Location(1);

pub use crate::gcc_api_sys::BuiltinFunction;
pub use crate::gcc_api_sys::IntegerTypeKind;
pub use crate::gcc_api_sys::SizeTypeKind;
pub use crate::gcc_api_sys::TreeCode;
pub use crate::gcc_api_sys::TreeIndex;

fn opt_tree_wrapper_to_tree(wrapper: Option<impl Deref<Target = Tree>>) -> Tree {
    wrapper.as_deref().copied().unwrap_or(NULL_TREE)
}

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Tree(tree);

pub const NULL_TREE: Tree = Tree(null_mut());

impl From<TreeIndex> for Tree {
    fn from(index: TreeIndex) -> Self {
        assert_ne!(index, TreeIndex::Max);

        Tree(unsafe { global_trees[index as usize].0 })
    }
}

impl Tree {
    pub fn get_type(self) -> Type {
        unsafe { get_tree_type(self) }
    }

    pub fn get_code(self) -> TreeCode {
        unsafe { get_tree_code(self) }
    }

    fn new0(code: TreeCode, type_: Type) -> Self {
        unsafe { Tree(build0(code, (type_.0).0)) }
    }

    fn new1(code: TreeCode, type_: Type, arg0: Tree) -> Self {
        unsafe { Tree(build1(code, (type_.0).0, arg0.0)) }
    }

    fn new2(code: TreeCode, type_: Type, arg0: Tree, arg1: Tree) -> Self {
        unsafe { Tree(build2(code, (type_.0).0, arg0.0, arg1.0)) }
    }

    fn new3(code: TreeCode, type_: Type, arg0: Tree, arg1: Tree, arg2: Tree) -> Self {
        unsafe { Tree(build3(code, (type_.0).0, arg0.0, arg1.0, arg2.0)) }
    }

    fn new4(code: TreeCode, type_: Type, arg0: Tree, arg1: Tree, arg2: Tree, arg3: Tree) -> Self {
        unsafe { Tree(build4(code, (type_.0).0, arg0.0, arg1.0, arg2.0, arg3.0)) }
    }

    pub fn set_static(&mut self, value: bool) {
        unsafe {
            set_tree_static(*self, value);
        }
    }

    pub fn set_public(&mut self, value: bool) {
        unsafe {
            set_tree_public(*self, value);
        }
    }

    pub fn set_side_effects(&mut self, value: bool) {
        unsafe {
            set_tree_side_effects(*self, value);
        }
    }

    pub fn set_constant(&mut self, value: bool) {
        unsafe {
            set_tree_constant(*self, value);
        }
    }

    pub fn set_readonly(&mut self, value: bool) {
        unsafe {
            set_tree_readonly(*self, value);
        }
    }

    pub fn set_used(&mut self, value: bool) {
        unsafe {
            set_tree_used(*self, value);
        }
    }

    pub fn set_addressable(&mut self, value: bool) {
        unsafe {
            set_tree_addressable(*self, value);
        }
    }

    pub fn set_decl_context(&mut self, context: Expr) {
        unsafe {
            set_decl_context(*self, *context);
        }
    }

    pub fn set_decl_initial(&mut self, value: Expr) {
        unsafe {
            set_decl_initial(*self, *value);
        }
    }

    pub fn set_decl_name(&mut self, name: Tree) {
        unsafe {
            set_decl_name(*self, name);
        }
    }

    pub fn finalize_decl(&mut self) {
        unsafe {
            finalize_decl(*self);
        }
    }

    pub fn new_identifier(name: impl Into<Vec<u8>>) -> Tree {
        let name = CString::new(name).unwrap();

        Tree(unsafe { get_identifier(name.as_ptr()) })
    }
}

impl std::fmt::Debug for Tree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        if self.0.is_null() {
            write!(f, "NULL_TREE")
        } else {
            write!(
                f,
                "Tree({:?}, code={:?}, type={:?}",
                self.0,
                self.get_code(),
                // This is recursive but should end eventually with a NULL_TREE
                self.get_type()
            )?;

            if self.get_code() == TreeCode::RecordType {
                let mut field_decls = vec![];
                for i in 0.. {
                    let field_decl = Type(*self).get_record_type_field_decl(i);
                    if (field_decl.0).0.is_null() {
                        break;
                    }
                    field_decls.push(field_decl);
                }

                write!(f, ", fields={:#?}", field_decls)?;
            }

            write!(f, ")")
        }
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Expr(Tree);

impl Deref for Expr {
    type Target = Tree;

    fn deref(&self) -> &Tree {
        &self.0
    }
}

impl DerefMut for Expr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Expr {
    pub fn void() -> Self {
        Self(Tree::new1(TreeCode::NopExpr, Type::void(), NULL_TREE))
    }

    pub fn null_ptr() -> Self {
        Self(Tree::from(TreeIndex::NullPointer))
    }

    /// Perform a binary expression, keeping the old type
    fn math(self, code: TreeCode, other: Expr) -> Self {
        Self(Tree::new2(code, self.get_type(), *self, *other))
    }

    /// Perform a binary expression, setting the result type
    pub fn typed_math(self, code: TreeCode, type_: Type, other: Expr) -> Self {
        Self(Tree::new2(code, type_, *self, *other))
    }

    pub fn plus(self, other: Expr) -> Self {
        self.math(TreeCode::PlusExpr, other)
    }

    pub fn minus(self, other: Expr) -> Self {
        self.math(TreeCode::MinusExpr, other)
    }

    pub fn mult(self, other: Expr) -> Self {
        self.math(TreeCode::MultExpr, other)
    }

    pub fn pointer_plus(self, other: Expr) -> Self {
        self.math(TreeCode::PointerPlusExpr, other)
    }

    pub fn equal_value(self, other: Expr) -> Self {
        self.typed_math(TreeCode::EqExpr, Type::bool(), other)
    }

    pub fn less_than_or_equal_value(self, other: Expr) -> Self {
        self.typed_math(TreeCode::LeExpr, Type::bool(), other)
    }

    /// Cast to type_ with a NopExpr
    pub fn nop_cast(self, type_: Type) -> Self {
        Self(Tree::new1(TreeCode::NopExpr, type_, self.0))
    }

    /// Cast to type_ with a ConvertExpr
    pub fn convert_cast(self, type_: Type) -> Self {
        Self(Tree::new1(TreeCode::ConvertExpr, type_, self.0))
    }

    /// Cast to type_ with a ViewConvertExpr
    pub fn view_convert_cast(self, type_: Type) -> Self {
        Self(Tree::new1(TreeCode::ViewConvertExpr, type_, self.0))
    }

    /// Apply a NegateExpr to this tree
    pub fn negate(self, type_: Type) -> Self {
        Self(Tree::new1(TreeCode::NegateExpr, type_, self.0))
    }

    /// Apply a BitNotExpr to this tree
    pub fn bit_not(self, type_: Type) -> Self {
        Self(Tree::new1(TreeCode::BitNotExpr, type_, self.0))
    }

    pub fn new_translation_unit_decl(name: Tree) -> Self {
        unsafe { Self(Tree(build_translation_unit_decl(name.0))) }
    }

    pub fn new_assignment(var: Expr, value: Expr) -> Self {
        Self(Tree::new2(
            TreeCode::ModifyExpr,
            value.get_type(),
            *var,
            *value,
        ))
    }

    pub fn new_int_constant<T: Into<Type>>(int_type: T, value: i64) -> Self {
        unsafe { Self(Tree(build_int_constant(int_type.into(), value))) }
    }

    /// value is `u64`, not usize, because our usize may be u32 while the target's usize may be u64
    pub fn new_usize(value: u64) -> Self {
        Self::new_int_constant(SizeTypeKind::UnsignedBytes, value.try_into().unwrap())
    }

    pub fn new_string_array(buf: &[u8]) -> Expr {
        unsafe { build_string_array(buf.len(), buf.as_ptr() as *const c_char) }
    }

    pub fn new_return_expr(value: Option<Expr>) -> Self {
        let value = opt_tree_wrapper_to_tree(value);

        Self(Tree::new1(TreeCode::ReturnExpr, Type::void(), value))
    }

    pub fn new_block(
        vars: Option<Expr>,
        subblocks: Option<Expr>,
        supercontext: Expr,
        chain: Option<Expr>,
    ) -> Self {
        let vars = opt_tree_wrapper_to_tree(vars);
        let subblocks = opt_tree_wrapper_to_tree(subblocks);
        let supercontext = (supercontext.0).0;
        let chain = opt_tree_wrapper_to_tree(chain);

        unsafe {
            Self(Tree(build_block(
                vars.0,
                subblocks.0,
                supercontext,
                chain.0,
            )))
        }
    }

    pub fn new_bind_expr(vars: Option<Expr>, body: Expr, block: Expr) -> Self {
        let vars = opt_tree_wrapper_to_tree(vars);

        Self(Tree::new3(
            TreeCode::BindExpr,
            Type::void(),
            vars,
            *body,
            *block,
        ))
    }

    pub fn new_result_decl(loc: Location, type_: Type) -> Self {
        unsafe {
            Self(Tree(build_decl(
                loc.0,
                TreeCode::ResultDecl,
                NULL_TREE.0,
                (type_.0).0,
            )))
        }
    }

    pub fn new_var_decl(loc: Location, name: Tree, type_: Type) -> Self {
        let mut t = unsafe {
            Self(Tree(build_decl(
                loc.0,
                TreeCode::VarDecl,
                name.0,
                (type_.0).0,
            )))
        };
        t.set_used(true);
        t
    }

    pub fn new_label_decl(loc: Location, context: Expr) -> Self {
        unsafe { Self(build_label_decl(loc, *context)) }
    }

    pub fn new_goto(label: Expr) -> Self {
        Self(Tree::new1(TreeCode::GotoExpr, Type::void(), *label))
    }

    pub fn new_label_expr(decl: Expr) -> Self {
        Self(Tree::new1(TreeCode::LabelExpr, Type::void(), *decl))
    }

    pub fn new_cond_expr(cond: Expr, true_expr: Expr, false_expr: Expr) -> Self {
        Self(Tree::new3(
            TreeCode::CondExpr,
            true_expr.get_type(),
            *cond,
            *true_expr,
            *false_expr,
        ))
    }

    pub fn new_case_label_expr(value: Option<Expr>, label_decl: Expr) -> Self {
        Self(Tree::new4(
            TreeCode::CaseLabelExpr,
            Type::void(),
            opt_tree_wrapper_to_tree(value),
            NULL_TREE,
            *label_decl,
            NULL_TREE,
        ))
    }

    pub fn new_switch_expr(switch_ty: Type, discr: Expr, body: Expr) -> Self {
        Self(Tree::new2(TreeCode::SwitchExpr, switch_ty, *discr, *body))
    }

    pub fn new_record_constructor(
        record_type: Type,
        field_decls: &[Expr],
        field_values: &[Expr],
    ) -> Self {
        assert_eq!(field_decls.len(), field_values.len());
        unsafe {
            build_constructor_from_field_array(
                record_type,
                field_decls.len(),
                field_decls.as_ptr(),
                field_values.as_ptr(),
            )
        }
    }

    pub fn new_array_constructor(array_type: Type, elements: &[Expr]) -> Self {
        unsafe {
            build_constructor_from_element_array(array_type, elements.len(), elements.as_ptr())
        }
    }

    pub fn new_compound_literal_expr(type_: Type, value: Expr, context: Expr) -> Self {
        unsafe { build_compound_literal_expr(type_, *value, *context) }
    }

    pub fn get_field(self, field_decl: Expr) -> Self {
        Self(Tree::new3(
            TreeCode::ComponentRef,
            field_decl.get_type(),
            *self,
            *field_decl,
            NULL_TREE,
        ))
    }

    pub fn get_record_field(self, field_index: usize) -> Self {
        let field_decl = self.get_type().get_record_type_field_decl(field_index);
        self.get_field(field_decl)
    }

    pub fn mk_pointer(mut self) -> Self {
        match self.get_code() {
            TreeCode::VarDecl
            | TreeCode::ParmDecl
            | TreeCode::ResultDecl
            | TreeCode::Constructor => {
                self.set_addressable(true);
            }

            _ => {}
        }

        let mut t = Self(Tree::new1(
            TreeCode::AddrExpr,
            self.get_type().mk_pointer_type(),
            *self,
        ));
        t.set_constant(true);
        t
    }

    pub fn deref_value(self) -> Self {
        let pointer_ty = self.get_type();
        let deref_ty = pointer_ty.get_pointer_type_deref_type();
        Self(Tree::new1(TreeCode::IndirectRef, deref_ty, *self))
    }

    pub fn new_call_expr(loc: Location, return_type: Type, fn_ptr: Expr, args: &[Expr]) -> Self {
        unsafe {
            Self(Tree(build_call_array_loc(
                loc.0,
                (return_type.0).0,
                (fn_ptr.0).0,
                args.len() as i32,
                args.as_ptr() as *const tree,
            )))
        }
    }

    pub fn index_array(self, index_expr: Expr) -> Self {
        let array_type = self.get_type();
        assert_eq!(array_type.get_code(), TreeCode::ArrayType);
        let element_type = array_type.get_type();

        Self(Tree::new4(
            TreeCode::ArrayRef,
            element_type,
            *self,
            *index_expr,
            NULL_TREE,
            NULL_TREE,
        ))
    }

    pub fn place_field_manually(&mut self, byte_offset: u64) {
        unsafe {
            place_field_manually(**self, byte_offset);
        }
    }
}

impl From<BuiltinFunction> for Expr {
    fn from(bf: BuiltinFunction) -> Self {
        unsafe { _builtin_decl_implicit(bf) }
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Type(Tree);

impl Deref for Type {
    type Target = Tree;

    fn deref(&self) -> &Tree {
        &self.0
    }
}

impl Type {
    pub fn void() -> Self {
        Self(TreeIndex::VoidType.into())
    }

    pub fn u16() -> Self {
        Self(TreeIndex::Uint16Type.into())
    }

    pub fn u32() -> Self {
        Self(TreeIndex::Uint32Type.into())
    }

    pub fn u64() -> Self {
        Self(TreeIndex::Uint64Type.into())
    }

    pub fn bool() -> Self {
        Self(TreeIndex::BooleanType.into())
    }

    pub fn new_function_type(return_type: Type, arg_types: &[Type]) -> Self {
        unsafe {
            Self(Tree(build_function_type_array(
                (return_type.0).0,
                arg_types.len() as i32,
                arg_types.as_ptr() as *mut tree,
            )))
        }
    }

    pub fn new_record_type(code: TreeCode) -> Self {
        Self(Tree::new0(code, Type(NULL_TREE)))
    }

    pub fn finish_record_type(
        &mut self,
        mut fields: DeclList,
        byte_size: u64,
        byte_alignment: u64,
    ) {
        unsafe {
            finish_record_type(
                *self,
                opt_tree_wrapper_to_tree(fields.head()),
                byte_size,
                byte_alignment,
            );
        }
        fields.set_context(self.0);
    }

    pub fn get_record_type_field_decl(&self, index: usize) -> Expr {
        unsafe { get_record_type_field_decl(*self, index) }
    }

    pub fn new_signed_int_type(bits: usize) -> Self {
        Self(Tree(unsafe { make_signed_type(bits as i32) }))
    }

    pub fn new_unsigned_int_type(bits: usize) -> Self {
        Self(Tree(unsafe { make_unsigned_type(bits as i32) }))
    }

    pub fn mk_pointer_type(self) -> Self {
        Self(Tree(unsafe { build_pointer_type((self.0).0) }))
    }

    pub fn new_vector_type(element_type: Type, num_elements: u64) -> Self {
        Self(Tree(unsafe {
            build_vector_type((element_type.0).0, num_elements.try_into().unwrap())
        }))
    }

    pub fn new_array_type(element_type: Type, num_elements: u64) -> Self {
        Self(Tree(unsafe {
            build_array_type_nelts((element_type.0).0, num_elements)
        }))
    }

    pub fn set_name(&mut self, identifier: Tree) {
        unsafe { set_type_name(*self, identifier) }
    }

    pub fn get_size_bytes(self) -> Expr {
        unsafe { get_type_size_bytes(self) }
    }

    pub fn is_compatible(self, other: Type) -> bool {
        unsafe { useless_type_conversion_p((self.0).0, (other.0).0) }
    }

    // Get the type pointed to by a pointer type tree
    pub fn get_pointer_type_deref_type(&self) -> Type {
        assert_eq!(self.get_code(), TreeCode::PointerType);
        // Type of dereffed item is stored in POINTER_TYPE's TREE_TYPE
        self.get_type()
    }
}

impl From<IntegerTypeKind> for Type {
    fn from(itk: IntegerTypeKind) -> Self {
        assert_ne!(itk, IntegerTypeKind::None);

        Self(Tree(unsafe { integer_types[itk as usize].0 }))
    }
}

impl From<SizeTypeKind> for Type {
    fn from(stk: SizeTypeKind) -> Self {
        Self(Tree(unsafe { sizetype_tab[stk as usize].0 }))
    }
}

extern "C" {
    static global_trees: [Tree; TreeIndex::Max as usize];
    static integer_types: [Tree; IntegerTypeKind::None as usize];
    static sizetype_tab: [Tree; SizeTypeKind::Last as usize];

    static crate_type: Option<NonNull<c_char>>;

    fn build_int_constant(int_type: Type, value: i64) -> tree;

    fn _builtin_decl_implicit(fncode: BuiltinFunction) -> Expr;

    fn build_constructor_from_field_array(
        type_: Type,
        num_fields: usize,
        field_decls: *const Expr,
        field_values: *const Expr,
    ) -> Expr;

    fn build_constructor_from_element_array(
        type_: Type,
        num_elements: usize,
        elements: *const Expr,
    ) -> Expr;

    fn get_tree_type(tree: Tree) -> Type;
    fn get_tree_code(tree: Tree) -> TreeCode;
    fn get_type_size_bytes(tree: Type) -> Expr;
    fn set_type_name(tt: Type, identifier: Tree);
    fn build_label_decl(loc: Location, context: Tree) -> Tree;
    fn build_string_array(len: usize, str: *const c_char) -> Expr;
    fn set_tree_static(tree: Tree, value: bool);
    fn set_tree_public(tree: Tree, value: bool);
    fn set_tree_side_effects(tree: Tree, value: bool);
    fn set_tree_constant(tree: Tree, value: bool);
    fn set_tree_readonly(tree: Tree, value: bool);
    fn set_tree_used(tree: Tree, value: bool);
    fn set_tree_addressable(tree: Tree, value: bool);
    fn make_decl_chain(code: TreeCode, num_decls: usize, types: *const Type, decls: *mut Expr);
    fn set_decl_context(decl: Tree, context: Tree);
    fn set_decl_initial(decl: Tree, value: Tree);
    fn set_decl_chain_context(chain_head: Tree, context: Tree);
    fn set_decl_name(decl: Tree, identifier: Tree);
    fn place_field_manually(field_decl: Tree, byte_offset: u64);
    fn finish_record_type(
        record_type: Type,
        fields_chain_head: Tree,
        byte_size: u64,
        byte_alignment: u64,
    ) -> Tree;
    fn get_record_type_field_decl(record_type: Type, index: usize) -> Expr;
    fn build_compound_literal_expr(type_: Type, value: Tree, context: Tree) -> Expr;
    fn set_fn_result(fn_decl: Function, result: Tree);
    fn set_fn_initial(fn_decl: Function, tree: Tree);
    fn set_fn_saved_tree(fn_decl: Function, tree: Tree);
    fn set_fn_external(fn_decl: Function, value: bool);
    fn set_fn_preserve_p(fn_decl: Function, value: bool);
    fn attach_fn_parm_decls(fn_decl: Function, decl_chain: Tree);
    fn finalize_decl(tree: Tree);
    fn finalize_function(tree: Function, no_collect: bool);
}

#[derive(Debug)]
pub struct StatementList(pub Expr);

impl StatementList {
    pub fn new() -> Self {
        unsafe { Self(Expr(Tree(alloc_stmt_list()))) }
    }

    pub fn push(&mut self, stmt: Expr) {
        unsafe {
            append_to_statement_list((stmt.0).0, &mut ((self.0).0).0);
        }
    }
}

#[derive(Debug)]
pub struct DeclList(Vec<Expr>);

impl DeclList {
    pub fn new(code: TreeCode, types: &[Type]) -> Self {
        let mut decls = vec![Expr(NULL_TREE); types.len()];

        unsafe {
            make_decl_chain(code, types.len(), types.as_ptr(), decls.as_mut_ptr());
        }

        if code == TreeCode::VarDecl {
            for decl in &mut decls {
                decl.set_used(true);
            }
        }

        DeclList(decls)
    }

    pub fn head(&self) -> Option<Expr> {
        self.0.first().copied()
    }

    pub fn set_context(&mut self, context: Tree) {
        if let Some(decl) = self.head() {
            unsafe {
                set_decl_chain_context(*decl, context);
            }
        }
    }
}

impl Deref for DeclList {
    type Target = [Expr];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for DeclList {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct Function(pub Expr);

impl Function {
    pub fn new(name: &CStr, type_: Type) -> Self {
        unsafe { Self(Expr(Tree(build_fn_decl(name.as_ptr(), (type_.0).0)))) }
    }

    pub fn set_result(&mut self, result: Expr) {
        unsafe {
            set_fn_result(*self, *result);
        }
    }

    pub fn set_initial(&mut self, tree: Expr) {
        unsafe {
            set_fn_initial(*self, *tree);
        }
    }

    pub fn set_saved_tree(&mut self, tree: Expr) {
        unsafe {
            set_fn_saved_tree(*self, *tree);
        }
    }

    pub fn set_external(&mut self, value: bool) {
        unsafe {
            set_fn_external(*self, value);
        }
    }

    pub fn set_preserve_p(&mut self, value: bool) {
        unsafe {
            set_fn_preserve_p(*self, value);
        }
    }

    pub fn attach_parm_decls(&mut self, decls: &DeclList) {
        unsafe {
            attach_fn_parm_decls(*self, opt_tree_wrapper_to_tree(decls.head()));
        }
    }

    pub fn gimplify(&mut self) {
        unsafe {
            gimplify_function_tree(((self.0).0).0);
        }
    }

    pub fn finalize(&mut self) {
        unsafe {
            finalize_function(*self, true);
        }
    }
}
