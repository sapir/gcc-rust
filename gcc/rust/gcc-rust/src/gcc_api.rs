#![allow(dead_code)]

use std::{
    ffi::CStr,
    os::raw::{c_char, c_uint, c_ulong},
    ptr::null_mut,
};

#[repr(transparent)]
pub struct Location(c_uint);

pub const UNKNOWN_LOCATION: Location = Location(0);
pub const BUILTINS_LOCATION: Location = Location(1);

// TODO: autogenerate this
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntegerTypeKind {
    Char,
    SignedChar,
    UnsignedChar,
    Short,
    UnsignedShort,
    Int,
    UnsignedInt,
    Long,
    UnsignedLong,
    LongLong,
    UnsignedLongLong,

    IntN0,
    UnsignedIntN0,
    IntN1,
    UnsignedIntN1,
    IntN2,
    UnsignedIntN2,
    IntN3,
    UnsignedIntN3,

    None,
}

// TODO: autogenerate this
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TreeIndex {
    ErrorMark,
    IntqiType,
    InthiType,
    IntsiType,
    IntdiType,
    InttiType,
    UintqiType,
    UinthiType,
    UintsiType,
    UintdiType,
    UinttiType,
    AtomicqiType,
    AtomichiType,
    AtomicsiType,
    AtomicdiType,
    AtomictiType,
    Uint6Type,
    Uint2Type,
    Uint4Type,
    Void,
    IntegerZero,
    IntegerOne,
    IntegerThree,
    IntegerMinusOne,
    NullPointer,
    SizeZero,
    SizeOne,
    BitsizeZero,
    BitsizeOne,
    BitsizeUnit,
    Public,
    Protected,
    Private,
    BooleanFalse,
    BooleanTrue,
    FloatType,
    DoubleType,
    LongDoubleType,
    Float6Type,
    Float2Type,
    Float4Type,
    Float28Type,
    Float2XType,
    Float4XType,
    Float28XType,
    ComplexIntegerType,
    ComplexFloatType,
    ComplexDoubleType,
    ComplexLongDoubleType,
    ComplexFloat6Type,
    ComplexFloat2Type,
    ComplexFloat4Type,
    ComplexFloat28Type,
    ComplexFloat2XType,
    ComplexFloat4XType,
    ComplexFloat28XType,
    FloatPtrType,
    DoublePtrType,
    LongDoublePtrType,
    IntegerPtrType,
    VoidType,
    PtrType,
    ConstPtrType,
    SizeType,
    PidType,
    PtrdiffType,
    VaListType,
    VaListGprCounterField,
    VaListFprCounterField,
    BooleanType,
    FileptrType,
    ConstTmPtrType,
    FenvTPtrType,
    ConstFenvTPtrType,
    FexceptTPtrType,
    ConstFexceptTPtrType,
    PointerSizedType,
    Dfloat2Type,
    Dfloat4Type,
    Dfloat28Type,
    VoidListNode,
    MainIdentifier,
    SatSfractType,
    SatFractType,
    SatLfractType,
    SatLlfractType,
    SatUsfractType,
    SatUfractType,
    SatUlfractType,
    SatUllfractType,
    SfractType,
    FractType,
    LfractType,
    LlfractType,
    UsfractType,
    UfractType,
    UlfractType,
    UllfractType,
    SatSaccumType,
    SatAccumType,
    SatLaccumType,
    SatLlaccumType,
    SatUsaccumType,
    SatUaccumType,
    SatUlaccumType,
    SatUllaccumType,
    SaccumType,
    AccumType,
    LaccumType,
    LlaccumType,
    UsaccumType,
    UaccumType,
    UlaccumType,
    UllaccumType,
    QqType,
    HqType,
    SqType,
    DqType,
    TqType,
    UqqType,
    UhqType,
    UsqType,
    UdqType,
    UtqType,
    SatQqType,
    SatHqType,
    SatSqType,
    SatDqType,
    SatTqType,
    SatUqqType,
    SatUhqType,
    SatUsqType,
    SatUdqType,
    SatUtqType,
    HaType,
    SaType,
    DaType,
    TaType,
    UhaType,
    UsaType,
    UdaType,
    UtaType,
    SatHaType,
    SatSaType,
    SatDaType,
    SatTaType,
    SatUhaType,
    SatUsaType,
    SatUdaType,
    SatUtaType,
    OptimizationDefault,
    OptimizationCurrent,
    TargetOptionDefault,
    TargetOptionCurrent,
    CurrentTargetPragma,
    CurrentOptimizePragma,
    ChrecDontKnow,
    ChrecKnown,

    Max,
}

// TODO: autogenerate this
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TreeCode {
    ErrorMark,
    IdentifierNode,
    TreeList,
    TreeVec,
    Block,
    OffsetType,
    EnumeralType,
    BooleanType,
    IntegerType,
    RealType,
    PointerType,
    ReferenceType,
    NullptrType,
    FixedPointType,
    ComplexType,
    VectorType,
    ArrayType,
    RecordType,
    UnionType,
    QualUnionType,
    VoidType,
    FunctionType,
    MethodType,
    LangType,
    VoidCst,
    IntegerCst,
    PolyIntCst,
    RealCst,
    FixedCst,
    ComplexCst,
    VectorCst,
    StringCst,
    FunctionDecl,
    LabelDecl,
    FieldDecl,
    VarDecl,
    ConstDecl,
    ParmDecl,
    TypeDecl,
    ResultDecl,
    DebugExprDecl,
    DebugBeginStmt,
    NamespaceDecl,
    ImportedDecl,
    NamelistDecl,
    TranslationUnitDecl,
    ComponentRef,
    BitFieldRef,
    ArrayRef,
    ArrayRangeRef,
    RealpartExpr,
    ImagpartExpr,
    ViewConvertExpr,
    IndirectRef,
    ObjTypeRef,
    Constructor,
    CompoundExpr,
    ModifyExpr,
    InitExpr,
    TargetExpr,
    CondExpr,
    VecDuplicateExpr,
    VecSeriesExpr,
    VecCondExpr,
    VecPermExpr,
    BindExpr,
    CallExpr,
    WithCleanupExpr,
    CleanupPointExpr,
    PlaceholderExpr,
    PlusExpr,
    MinusExpr,
    MultExpr,
    PointerPlusExpr,
    PointerDiffExpr,
    MultHighpartExpr,
    TruncDivExpr,
    CeilDivExpr,
    FloorDivExpr,
    RoundDivExpr,
    TruncModExpr,
    CeilModExpr,
    FloorModExpr,
    RoundModExpr,
    RdivExpr,
    ExactDivExpr,
    FixTruncExpr,
    FloatExpr,
    NegateExpr,
    MinExpr,
    MaxExpr,
    AbsExpr,
    AbsuExpr,
    LShiftExpr,
    RShiftExpr,
    LRotateExpr,
    RRotateExpr,
    BitIorExpr,
    BitXorExpr,
    BitAndExpr,
    BitNotExpr,
    TruthAndifExpr,
    TruthOrifExpr,
    TruthAndExpr,
    TruthOrExpr,
    TruthXorExpr,
    TruthNotExpr,
    LtExpr,
    LeExpr,
    GtExpr,
    GeExpr,
    LtgtExpr,
    EqExpr,
    NeExpr,
    UnorderedExpr,
    OrderedExpr,
    UnltExpr,
    UnleExpr,
    UngtExpr,
    UngeExpr,
    UneqExpr,
    RangeExpr,
    ParenExpr,
    ConvertExpr,
    AddrSpaceConvertExpr,
    FixedConvertExpr,
    NopExpr,
    NonLvalueExpr,
    CompoundLiteralExpr,
    SaveExpr,
    AddrExpr,
    FdescExpr,
    BitInsertExpr,
    ComplexExpr,
    ConjExpr,
    PredecrementExpr,
    PreincrementExpr,
    PostdecrementExpr,
    PostincrementExpr,
    VaArgExpr,
    TryCatchExpr,
    TryFinallyExpr,
    EhElseExpr,
    DeclExpr,
    LabelExpr,
    GotoExpr,
    ReturnExpr,
    ExitExpr,
    LoopExpr,
    SwitchExpr,
    CaseLabelExpr,
    AsmExpr,
    SsaName,
    CatchExpr,
    EhFilterExpr,
    ScevKnown,
    ScevNotKnown,
    PolynomialChrec,
    StatementList,
    AssertExpr,
    TreeBinfo,
    WithSizeExpr,
    RealignLoadExpr,
    TargetMemRef,
    MemRef,
    OaccParallel,
    OaccKernels,
    OaccSerial,
    OaccData,
    OaccHostData,
    OmpParallel,
    OmpTask,
    OmpFor,
    OmpSimd,
    OmpDistribute,
    OmpTaskloop,
    OmpLoop,
    OaccLoop,
    OmpTeams,
    OmpTargetData,
    OmpTarget,
    OmpSections,
    OmpOrdered,
    OmpCritical,
    OmpSingle,
    OmpTaskgroup,
    OmpScan,
    OmpSection,
    OmpMaster,
    OaccCache,
    OaccDeclare,
    OaccEnterData,
    OaccExitData,
    OaccUpdate,
    OmpTargetUpdate,
    OmpTargetEnterData,
    OmpTargetExitData,
    OmpAtomic,
    OmpAtomicRead,
    OmpAtomicCaptureOld,
    OmpAtomicCaptureNew,
    OmpClause,
    TransactionExpr,
    DotProdExpr,
    WidenSumExpr,
    SadExpr,
    WidenMultExpr,
    WidenMultPlusExpr,
    WidenMultMinusExpr,
    WidenLShiftExpr,
    VecWidenMultHiExpr,
    VecWidenMultLoExpr,
    VecWidenMultEvenExpr,
    VecWidenMultOddExpr,
    VecUnpackHiExpr,
    VecUnpackLoExpr,
    VecUnpackFloatHiExpr,
    VecUnpackFloatLoExpr,
    VecUnpackFixTruncHiExpr,
    VecUnpackFixTruncLoExpr,
    VecPackTruncExpr,
    VecPackSatExpr,
    VecPackFixTruncExpr,
    VecPackFloatExpr,
    VecWidenLShiftHiExpr,
    VecWidenLShiftLoExpr,
    PredictExpr,
    OptimizationNode,
    TargetOptionNode,
    AnnotateExpr,
}

#[repr(C)]
pub struct TreeNode {
    _private: [u8; 0],
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Tree(*mut TreeNode);

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

impl Tree {
    pub fn new_function_type(return_type: Tree, arg_types: &[Tree]) -> Self {
        unsafe { _build_function_type_array(return_type, arg_types.len(), arg_types.as_ptr()) }
    }

    pub fn new2(code: TreeCode, type_: Tree, arg0: Tree, arg1: Tree) -> Self {
        unsafe { _build2(code, type_, arg0, arg1) }
    }

    pub fn new_init_expr(var: Tree, value: Tree) -> Self {
        Self::new2(TreeCode::InitExpr, TreeIndex::VoidType.into(), var, value)
    }

    pub fn new_int_constant<T: Into<Tree>>(int_type: T, value: i64) -> Self {
        unsafe { build_int_constant(int_type.into(), value) }
    }

    pub fn new_return_expr(value: Tree) -> Self {
        unsafe { _build1(TreeCode::ReturnExpr, TreeIndex::VoidType.into(), value) }
    }

    pub fn new_block(vars: Tree, subblocks: Tree, supercontext: Tree, chain: Tree) -> Self {
        unsafe { _build_block(vars, subblocks, supercontext, chain) }
    }

    pub fn new_bind_expr(vars: Tree, body: Tree, block: Tree) -> Self {
        let bind_expr = unsafe {
            _build3(
                TreeCode::BindExpr,
                TreeIndex::VoidType.into(),
                vars,
                body,
                block,
            )
        };

        if vars.0 != NULL_TREE.0 {
            unsafe {
                set_decl_chain_context(vars, block);
            }
        }

        bind_expr
    }

    pub fn new_result_decl(loc: Location, type_: Tree) -> Self {
        unsafe { _build_decl(loc, TreeCode::ResultDecl, NULL_TREE, type_) }
    }

    pub fn new_label_decl(loc: Location, context: Tree) -> Self {
        unsafe { build_label_decl(loc, context) }
    }

    pub fn new_goto(label: Tree) -> Self {
        unsafe { _build1(TreeCode::GotoExpr, TreeIndex::VoidType.into(), label) }
    }

    pub fn new_label_expr(decl: Tree) -> Self {
        unsafe { _build1(TreeCode::LabelExpr, TreeIndex::VoidType.into(), decl) }
    }

    pub fn new_cond_expr(cond: Tree, true_expr: Tree, false_expr: Tree) -> Self {
        unsafe {
            _build3(
                TreeCode::CondExpr,
                TreeIndex::VoidType.into(),
                cond,
                true_expr,
                false_expr,
            )
        }
    }
}

extern "C" {
    static global_trees: [Tree; TreeIndex::Max as usize];
    static integer_types: [Tree; IntegerTypeKind::None as usize];

    fn _alloc_stmt_list() -> Tree;
    fn _append_to_statement_list(stmt: Tree, list: *mut Tree);
    fn _build0(code: TreeCode, tt: Tree) -> Tree;
    fn _build1(code: TreeCode, tt: Tree, arg0: Tree) -> Tree;
    fn _build2(code: TreeCode, tt: Tree, arg0: Tree, arg1: Tree) -> Tree;
    fn _build3(code: TreeCode, tt: Tree, arg0: Tree, arg1: Tree, arg2: Tree) -> Tree;
    fn _build4(code: TreeCode, tt: Tree, arg0: Tree, arg1: Tree, arg2: Tree, arg3: Tree) -> Tree;
    fn _build5(
        code: TreeCode,
        tt: Tree,
        arg0: Tree,
        arg1: Tree,
        arg2: Tree,
        arg3: Tree,
        arg4: Tree,
    ) -> Tree;
    fn _build_decl(loc: Location, code: TreeCode, name: Tree, tt: Tree) -> Tree;
    fn _build_string_literal(
        len: usize,
        string: *const c_char,
        eltype: Tree,
        size: c_ulong,
    ) -> Tree;
    fn _build_block(vars: Tree, subblocks: Tree, supercontext: Tree, chain: Tree) -> Tree;
    fn _build_call_array_loc(
        loc: Location,
        returntype: Tree,
        fn_ptr: Tree,
        num_args: usize,
        args: *const Tree,
    ) -> Tree;
    fn _build_pointer_type(totype: Tree) -> Tree;
    fn _build_function_type_array(
        returntype: Tree,
        num_args: usize,
        arg_types: *const Tree,
    ) -> Tree;
    fn _build_fn_decl(name: *const c_char, decltype: Tree) -> Tree;
    fn _gimplify_function_tree(tree: Tree);

    fn build_int_constant(inttype: Tree, value: i64) -> Tree;
    fn build_label_decl(loc: Location, context: Tree) -> Tree;
    fn make_decl_chain(code: TreeCode, num_decls: usize, types: *const Tree, decls: *mut Tree);
    fn set_decl_chain_context(chain_head: Tree, context: Tree);
    fn set_fn_result(fn_decl: Tree, result: Tree);
    fn set_fn_initial(fn_decl: Tree, tree: Tree);
    fn set_fn_saved_tree(fn_decl: Tree, tree: Tree);
    fn set_fn_external(fn_decl: Tree, value: bool);
    fn set_fn_preserve_p(fn_decl: Tree, value: bool);
    fn attach_fn_parm_decls(fn_decl: Tree, decl_chain: Tree);
    fn finalize_decl(tree: Tree);
    fn finalize_function(tree: Tree, no_collect: bool);
}

pub struct StatementList(pub Tree);

impl StatementList {
    pub fn new() -> Self {
        Self(unsafe { _alloc_stmt_list() })
    }

    pub fn push(&mut self, stmt: Tree) {
        unsafe {
            _append_to_statement_list(stmt, &mut self.0);
        }
    }
}

pub struct DeclList(Vec<Tree>);

impl DeclList {
    pub fn new(code: TreeCode, types: &[Tree]) -> Self {
        let mut decls = vec![NULL_TREE; types.len()];

        unsafe {
            make_decl_chain(code, types.len(), types.as_ptr(), decls.as_mut_ptr());
        }

        DeclList(decls)
    }

    pub fn head(&self) -> Option<Tree> {
        self.0.get(0).copied()
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

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Function(pub Tree);

impl Function {
    pub fn new(name: &CStr, type_: Tree) -> Self {
        Self(unsafe { _build_fn_decl(name.as_ptr(), type_) })
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
            _gimplify_function_tree(self.0);
        }
    }

    pub fn finalize(&mut self) {
        unsafe {
            finalize_function(self.0, true);
        }
    }
}
