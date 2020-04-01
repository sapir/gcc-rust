#![allow(dead_code)]

use std::{
    convert::TryInto,
    ffi::{CStr, CString},
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

impl From<IntegerTypeKind> for Tree {
    fn from(itk: IntegerTypeKind) -> Self {
        assert_ne!(itk, IntegerTypeKind::None);

        Tree(unsafe { integer_types[itk as usize].0 })
    }
}

impl From<SizeTypeKind> for Tree {
    fn from(stk: SizeTypeKind) -> Self {
        Tree(unsafe { sizetype_tab[stk as usize].0 })
    }
}

impl From<BuiltinFunction> for Tree {
    fn from(bf: BuiltinFunction) -> Self {
        unsafe { _builtin_decl_implicit(bf) }
    }
}

impl Tree {
    pub fn get_type(self) -> Self {
        unsafe { get_tree_type(self) }
    }

    pub fn get_code(self) -> TreeCode {
        unsafe { get_tree_code(self) }
    }

    pub fn get_type_size_bytes(self) -> Tree {
        unsafe { get_type_size_bytes(self) }
    }

    pub fn set_type_name(&mut self, identifier: Tree) {
        unsafe { set_type_name(*self, identifier) }
    }

    pub fn is_compatible_type(self, other: Tree) -> bool {
        unsafe { useless_type_conversion_p(self.0, other.0) }
    }

    pub fn new_function_type(return_type: Tree, arg_types: &[Tree]) -> Self {
        unsafe {
            Tree(build_function_type_array(
                return_type.0,
                arg_types.len() as i32,
                arg_types.as_ptr() as *mut tree,
            ))
        }
    }

    pub fn new0(code: TreeCode, type_: Tree) -> Self {
        unsafe { Tree(build0(code, type_.0)) }
    }

    pub fn new1(code: TreeCode, type_: Tree, arg0: Tree) -> Self {
        unsafe { Tree(build1(code, type_.0, arg0.0)) }
    }

    pub fn new2(code: TreeCode, type_: Tree, arg0: Tree, arg1: Tree) -> Self {
        unsafe { Tree(build2(code, type_.0, arg0.0, arg1.0)) }
    }

    pub fn new3(code: TreeCode, type_: Tree, arg0: Tree, arg1: Tree, arg2: Tree) -> Self {
        unsafe { Tree(build3(code, type_.0, arg0.0, arg1.0, arg2.0)) }
    }

    pub fn new4(
        code: TreeCode,
        type_: Tree,
        arg0: Tree,
        arg1: Tree,
        arg2: Tree,
        arg3: Tree,
    ) -> Self {
        unsafe { Tree(build4(code, type_.0, arg0.0, arg1.0, arg2.0, arg3.0)) }
    }

    pub fn new_translation_unit_decl(name: Tree) -> Self {
        unsafe { Tree(build_translation_unit_decl(name.0)) }
    }

    pub fn new_assignment(var: Tree, value: Tree) -> Self {
        Self::new2(TreeCode::ModifyExpr, value.get_type(), var, value)
    }

    pub fn new_int_constant<T: Into<Tree>>(int_type: T, value: i64) -> Self {
        Tree(unsafe { build_int_constant(int_type.into().0, value) })
    }

    pub fn new_return_expr(value: Tree) -> Self {
        Tree::new1(TreeCode::ReturnExpr, TreeIndex::VoidType.into(), value)
    }

    pub fn new_block(vars: Tree, subblocks: Tree, supercontext: Tree, chain: Tree) -> Self {
        unsafe { Tree(build_block(vars.0, subblocks.0, supercontext.0, chain.0)) }
    }

    pub fn new_bind_expr(vars: Tree, body: Tree, block: Tree) -> Self {
        let bind_expr = Tree::new3(
            TreeCode::BindExpr,
            TreeIndex::VoidType.into(),
            vars,
            body,
            block,
        );

        if vars.0 != NULL_TREE.0 {
            unsafe {
                set_decl_chain_context(vars, block);
            }
        }

        bind_expr
    }

    pub fn new_result_decl(loc: Location, type_: Tree) -> Self {
        unsafe {
            Tree(build_decl(
                loc.0,
                TreeCode::ResultDecl,
                NULL_TREE.0,
                type_.0,
            ))
        }
    }

    pub fn new_var_decl(loc: Location, name: Tree, type_: Tree) -> Self {
        let mut t = unsafe { Tree(build_decl(loc.0, TreeCode::VarDecl, name.0, type_.0)) };
        t.set_used(true);
        t
    }

    pub fn new_label_decl(loc: Location, context: Tree) -> Self {
        unsafe { build_label_decl(loc, context) }
    }

    pub fn new_goto(label: Tree) -> Self {
        Tree::new1(TreeCode::GotoExpr, TreeIndex::VoidType.into(), label)
    }

    pub fn new_label_expr(decl: Tree) -> Self {
        Tree::new1(TreeCode::LabelExpr, TreeIndex::VoidType.into(), decl)
    }

    pub fn new_cond_expr(cond: Tree, true_expr: Tree, false_expr: Tree) -> Self {
        Tree::new3(
            TreeCode::CondExpr,
            TreeIndex::VoidType.into(),
            cond,
            true_expr,
            false_expr,
        )
    }

    pub fn new_case_label_expr(value: Option<Tree>, label_decl: Tree) -> Self {
        Tree::new4(
            TreeCode::CaseLabelExpr,
            TreeIndex::VoidType.into(),
            value.unwrap_or(NULL_TREE),
            NULL_TREE,
            label_decl,
            NULL_TREE,
        )
    }

    pub fn new_switch_expr(switch_ty: Tree, discr: Tree, body: Tree) -> Self {
        Tree::new2(TreeCode::SwitchExpr, switch_ty, discr, body)
    }

    pub fn new_record_type(code: TreeCode) -> Self {
        Tree::new0(code, NULL_TREE)
    }

    pub fn place_field_manually(&mut self, byte_offset: u64) {
        unsafe {
            place_field_manually(*self, byte_offset);
        }
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
                fields.head().unwrap_or(NULL_TREE),
                byte_size,
                byte_alignment,
            );
        }
        fields.set_context(*self);
    }

    pub fn get_record_type_field_decl(&self, index: usize) -> Self {
        unsafe { get_record_type_field_decl(*self, index) }
    }

    pub fn new_record_constructor(
        record_type: Tree,
        field_decls: &[Tree],
        field_values: &[Tree],
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

    pub fn new_array_constructor(array_type: Tree, elements: &[Tree]) -> Self {
        unsafe {
            build_constructor_from_element_array(array_type, elements.len(), elements.as_ptr())
        }
    }

    pub fn new_compound_literal_expr(type_: Tree, value: Tree, context: Tree) -> Self {
        unsafe { build_compound_literal_expr(type_, value, context) }
    }

    pub fn new_component_ref(base_expr: Tree, field_decl: Tree) -> Self {
        Self::new3(
            TreeCode::ComponentRef,
            field_decl.get_type(),
            base_expr,
            field_decl,
            NULL_TREE,
        )
    }

    pub fn new_record_field_ref(base_expr: Tree, field_index: usize) -> Self {
        let field_decl = base_expr.get_type().get_record_type_field_decl(field_index);
        Self::new_component_ref(base_expr, field_decl)
    }

    // Get the type pointed to by a pointer type tree
    pub fn get_pointer_type_deref_type(&self) -> Self {
        assert_eq!(self.get_code(), TreeCode::PointerType);
        // Type of dereffed item is stored in POINTER_TYPE's TREE_TYPE
        self.get_type()
    }

    pub fn new_indirect_ref(base_expr: Tree) -> Self {
        let pointer_ty = base_expr.get_type();
        let deref_ty = pointer_ty.get_pointer_type_deref_type();
        Self::new1(TreeCode::IndirectRef, deref_ty, base_expr)
    }

    pub fn new_call_expr(loc: Location, return_type: Tree, fn_ptr: Tree, args: &[Tree]) -> Self {
        unsafe {
            Tree(build_call_array_loc(
                loc.0,
                return_type.0,
                fn_ptr.0,
                args.len() as i32,
                args.as_ptr() as *const tree,
            ))
        }
    }

    pub fn new_signed_int_type(bits: usize) -> Self {
        Tree(unsafe { make_signed_type(bits as i32) })
    }

    pub fn new_unsigned_int_type(bits: usize) -> Self {
        Tree(unsafe { make_unsigned_type(bits as i32) })
    }

    pub fn new_pointer_type(to_type: Tree) -> Self {
        Tree(unsafe { build_pointer_type(to_type.0) })
    }

    pub fn new_addr_expr(value: Tree) -> Self {
        Tree::new1(
            TreeCode::AddrExpr,
            Tree::new_pointer_type(value.get_type()),
            value,
        )
    }

    pub fn new_vector_type(element_type: Tree, num_elements: u64) -> Self {
        Tree(unsafe { build_vector_type(element_type.0, num_elements.try_into().unwrap()) })
    }

    pub fn new_array_type(element_type: Tree, num_elements: u64) -> Self {
        Tree(unsafe { build_array_type_nelts(element_type.0, num_elements) })
    }

    pub fn new_array_index_ref(element_type: Tree, array_expr: Tree, index_expr: Tree) -> Self {
        Tree::new4(
            TreeCode::ArrayRef,
            element_type,
            array_expr,
            index_expr,
            NULL_TREE,
            NULL_TREE,
        )
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

    pub fn set_decl_context(&mut self, context: Tree) {
        unsafe {
            set_decl_context(*self, context);
        }
    }

    pub fn set_decl_initial(&mut self, value: Tree) {
        unsafe {
            set_decl_initial(*self, value);
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
                    let field_decl = self.get_record_type_field_decl(i);
                    if field_decl.0.is_null() {
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

extern "C" {
    static global_trees: [Tree; TreeIndex::Max as usize];
    static integer_types: [Tree; IntegerTypeKind::None as usize];
    static sizetype_tab: [Tree; SizeTypeKind::Last as usize];

    static crate_type: Option<NonNull<c_char>>;

    fn build_int_constant(int_type: tree, value: i64) -> tree;

    fn _builtin_decl_implicit(fncode: BuiltinFunction) -> Tree;

    fn build_constructor_from_field_array(
        type_: Tree,
        num_fields: usize,
        field_decls: *const Tree,
        field_values: *const Tree,
    ) -> Tree;

    fn build_constructor_from_element_array(
        type_: Tree,
        num_elements: usize,
        elements: *const Tree,
    ) -> Tree;

    fn get_tree_type(tree: Tree) -> Tree;
    fn get_tree_code(tree: Tree) -> TreeCode;
    fn get_type_size_bytes(tree: Tree) -> Tree;
    fn set_type_name(tt: Tree, identifier: Tree);
    fn build_label_decl(loc: Location, context: Tree) -> Tree;
    fn set_tree_static(tree: Tree, value: bool);
    fn set_tree_public(tree: Tree, value: bool);
    fn set_tree_side_effects(tree: Tree, value: bool);
    fn set_tree_constant(tree: Tree, value: bool);
    fn set_tree_used(tree: Tree, value: bool);
    fn set_tree_addressable(tree: Tree, value: bool);
    fn make_decl_chain(code: TreeCode, num_decls: usize, types: *const Tree, decls: *mut Tree);
    fn set_decl_context(decl: Tree, context: Tree);
    fn set_decl_initial(decl: Tree, value: Tree);
    fn set_decl_chain_context(chain_head: Tree, context: Tree);
    fn place_field_manually(field_decl: Tree, byte_offset: u64);
    fn finish_record_type(
        record_type: Tree,
        fields_chain_head: Tree,
        byte_size: u64,
        byte_alignment: u64,
    ) -> Tree;
    fn get_record_type_field_decl(record_type: Tree, index: usize) -> Tree;
    fn build_compound_literal_expr(type_: Tree, value: Tree, context: Tree) -> Tree;
    fn set_fn_result(fn_decl: Tree, result: Tree);
    fn set_fn_initial(fn_decl: Tree, tree: Tree);
    fn set_fn_saved_tree(fn_decl: Tree, tree: Tree);
    fn set_fn_external(fn_decl: Tree, value: bool);
    fn set_fn_preserve_p(fn_decl: Tree, value: bool);
    fn attach_fn_parm_decls(fn_decl: Tree, decl_chain: Tree);
    fn finalize_decl(tree: Tree);
    fn finalize_function(tree: Tree, no_collect: bool);
}

#[derive(Debug)]
pub struct StatementList(pub Tree);

impl StatementList {
    pub fn new() -> Self {
        Self(Tree(unsafe { alloc_stmt_list() }))
    }

    pub fn push(&mut self, stmt: Tree) {
        unsafe {
            append_to_statement_list(stmt.0, &mut (self.0).0);
        }
    }
}

#[derive(Debug)]
pub struct DeclList(Vec<Tree>);

impl DeclList {
    pub fn new(code: TreeCode, types: &[Tree]) -> Self {
        let mut decls = vec![NULL_TREE; types.len()];

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

    pub fn head(&self) -> Option<Tree> {
        self.0.first().copied()
    }

    pub fn set_context(&mut self, context: Tree) {
        if let Some(decl) = self.head() {
            unsafe {
                set_decl_chain_context(decl, context);
            }
        }
    }
}

impl std::ops::Deref for DeclList {
    type Target = [Tree];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for DeclList {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct Function(pub Tree);

impl Function {
    pub fn new(name: &CStr, type_: Tree) -> Self {
        Self(Tree(unsafe { build_fn_decl(name.as_ptr(), type_.0) }))
    }

    pub fn set_result(&mut self, result: Tree) {
        unsafe {
            set_fn_result(self.0, result);
        }
    }

    pub fn set_initial(&mut self, tree: Tree) {
        unsafe {
            set_fn_initial(self.0, tree);
        }
    }

    pub fn set_saved_tree(&mut self, tree: Tree) {
        unsafe {
            set_fn_saved_tree(self.0, tree);
        }
    }

    pub fn set_external(&mut self, value: bool) {
        unsafe {
            set_fn_external(self.0, value);
        }
    }

    pub fn set_preserve_p(&mut self, value: bool) {
        unsafe {
            set_fn_preserve_p(self.0, value);
        }
    }

    pub fn attach_parm_decls(&mut self, decls: &DeclList) {
        unsafe {
            attach_fn_parm_decls(self.0, decls.head().unwrap_or(NULL_TREE));
        }
    }

    pub fn gimplify(&mut self) {
        unsafe {
            gimplify_function_tree((self.0).0);
        }
    }

    pub fn finalize(&mut self) {
        unsafe {
            finalize_function(self.0, true);
        }
    }
}
