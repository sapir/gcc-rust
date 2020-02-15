use crate::gcc_api::*;
use rustc::{
    bug,
    mir::{
        interpret::{ConstValue, Scalar},
        mono::MonoItem,
        tcx::PlaceTy,
        AggregateKind, BasicBlock, BasicBlockData, BinOp, Body, CastKind, HasLocalDecls, Local,
        NullOp, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind, UnOp,
    },
    ty::{
        self,
        adjustment::PointerCast,
        layout::{Size, TyLayout},
        subst::{Subst, SubstsRef},
        AdtKind, Const, ConstKind, Instance, InstanceDef, ParamEnv, PolyExistentialTraitRef,
        PolyFnSig, Ty, TyCtxt, TyKind, TyS,
    },
};
use rustc_hir::def_id::DefId;
use rustc_interface::Queries;
use rustc_mir::monomorphize::collector::{collect_crate_mono_items, MonoItemCollectionMode};
use rustc_span::symbol::Symbol;
use rustc_target::spec::abi::Abi;
use std::{collections::HashMap, convert::TryInto, ffi::CString};

use crate::convert_type::TypeCache;

// Copied from https://github.com/bjorn3/rustc_codegen_cranelift/blob/7ff01a4d59779609992aad947264abcc64617917/src/abi/mod.rs#L15
// Copied from https://github.com/rust-lang/rust/blob/c2f4c57296f0d929618baed0b0d6eb594abf01eb/src/librustc/ty/layout.rs#L2349
fn fn_sig_for_fn_abi<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) -> PolyFnSig<'tcx> {
    let ty = instance.monomorphic_ty(tcx);
    match ty.kind {
        ty::FnDef(..) |
        // Shims currently have type FnPtr. Not sure this should remain.
        ty::FnPtr(_) => {
            let mut sig = ty.fn_sig(tcx);
            if let ty::InstanceDef::VtableShim(..) = instance.def {
                // Modify `fn(self, ...)` to `fn(self: *mut Self, ...)`.
                sig = sig.map_bound(|mut sig| {
                    let mut inputs_and_output = sig.inputs_and_output.to_vec();
                    inputs_and_output[0] = tcx.mk_mut_ptr(inputs_and_output[0]);
                    sig.inputs_and_output = tcx.intern_type_list(&inputs_and_output);
                    sig
                });
            }
            sig
        }
        ty::Closure(def_id, substs) => {
            let sig = substs.as_closure().sig(def_id, tcx);

            let env_ty = tcx.closure_env_ty(def_id, substs).unwrap();
            sig.map_bound(|sig| tcx.mk_fn_sig(
                std::iter::once(*env_ty.skip_binder()).chain(sig.inputs().iter().cloned()),
                sig.output(),
                sig.c_variadic,
                sig.unsafety,
                sig.abi
            ))
        }
        ty::Generator(def_id, substs, _) => {
            let sig = substs.as_generator().poly_sig(def_id, tcx);

            let env_region = ty::ReLateBound(ty::INNERMOST, ty::BrEnv);
            let env_ty = tcx.mk_mut_ref(tcx.mk_region(env_region), ty);

            let pin_did = tcx.lang_items().pin_type().unwrap();
            let pin_adt_ref = tcx.adt_def(pin_did);
            let pin_substs = tcx.intern_substs(&[env_ty.into()]);
            let env_ty = tcx.mk_adt(pin_adt_ref, pin_substs);

            sig.map_bound(|sig| {
                let state_did = tcx.lang_items().gen_state().unwrap();
                let state_adt_ref = tcx.adt_def(state_did);
                let state_substs = tcx.intern_substs(&[
                    sig.yield_ty.into(),
                    sig.return_ty.into(),
                ]);
                let ret_ty = tcx.mk_adt(state_adt_ref, state_substs);

                tcx.mk_fn_sig(std::iter::once(env_ty),
                    ret_ty,
                    false,
                    rustc_hir::Unsafety::Normal,
                    rustc_target::spec::abi::Abi::Rust
                )
            })
        }
        _ => bug!("unexpected type {:?} in Instance::fn_sig", ty)
    }
}

const USIZE_KIND: SizeTypeKind = SizeTypeKind::UnsignedBytes;
const ISIZE_KIND: SizeTypeKind = SizeTypeKind::SignedBytes;

struct ConversionCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    type_cache: TypeCache<'tcx>,
    vtables: HashMap<(Ty<'tcx>, Option<PolyExistentialTraitRef<'tcx>>), Tree>,
    translation_unit_decl: Tree,
}

impl<'tcx> ConversionCtx<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            type_cache: TypeCache::new(tcx),
            vtables: HashMap::new(),
            translation_unit_decl: Tree::new_translation_unit_decl(NULL_TREE),
        }
    }

    pub fn layout_of(&self, ty: Ty<'tcx>) -> TyLayout<'tcx> {
        self.tcx.layout_of(ParamEnv::reveal_all().and(ty)).unwrap()
    }

    fn resolve_fn(&mut self, def_id: DefId, substs: SubstsRef<'tcx>) -> Instance<'tcx> {
        // Normalize associated types
        // (instance.monomorphic_ty() calls tcx.subst_and_normalize_erasing_regions)
        let fn_type = Instance::new(def_id, substs).monomorphic_ty(self.tcx);
        // Resolve traits
        let (def_id, substs) = match fn_type.kind {
            TyKind::FnDef(def_id, substs) => (def_id, substs),
            TyKind::Closure(def_id, substs) => (def_id, substs),
            _ => unreachable!(),
        };
        Instance::resolve(self.tcx, ParamEnv::reveal_all(), def_id, substs).unwrap()
    }

    fn convert_instance_to_fn_ptr(&mut self, instance: Instance<'tcx>) -> Tree {
        let fn_sig = fn_sig_for_fn_abi(self.tcx, instance);
        match fn_sig.abi() {
            // Call instruction conversion removes intrinsics, so RustIntrinsic shouldn't show up
            // at this point
            Abi::RustIntrinsic => {
                unreachable!("RustIntrinsic {:?} used outside of Call, or Call didn't convert it")
            }
            Abi::PlatformIntrinsic => unimplemented!("PlatformIntrinsic {:?}", instance),
            _ => {}
        }

        let name = self.tcx.symbol_name(instance);
        let name = name.name;
        let fn_type = self.type_cache.convert_fn_sig(fn_sig).into_function_type();
        // TODO: move next line into Function::new
        let name = CString::new(&*name.as_str()).unwrap();
        let fn_decl = Function::new(&name, fn_type).0;
        Tree::new_addr_expr(fn_decl)
    }

    fn make_vtable_name(
        &self,
        _ty: Ty<'tcx>,
        _trait_ref: Option<PolyExistentialTraitRef<'tcx>>,
        vtable_index: usize,
    ) -> String {
        // TODO: include mangled type and trait ref
        format!(".vtable.{}", vtable_index)
    }

    // Based on librustc_codegen_ssa/meth.rs:get_vtable().
    // See also rustc_codegen_cranelift/vtable.rs:build_vtable()
    pub fn get_vtable(
        &mut self,
        ty: Ty<'tcx>,
        trait_ref: Option<PolyExistentialTraitRef<'tcx>>,
    ) -> Tree {
        let key = (ty, trait_ref);
        if let Some(&vtable) = self.vtables.get(&key) {
            return vtable;
        }

        let layout = self.layout_of(ty);
        let mut components: Vec<_> = vec![
            self.convert_instance_to_fn_ptr(Instance::resolve_drop_in_place(self.tcx, ty)),
            Tree::new_int_constant(USIZE_KIND, layout.size.bytes().try_into().unwrap()),
            Tree::new_int_constant(USIZE_KIND, layout.align.abi.bytes().try_into().unwrap()),
        ];

        let nullptr: Tree = TreeIndex::NullPointer.into();

        let methods_root;
        let methods = if let Some(trait_ref) = trait_ref {
            methods_root = self
                .tcx
                .vtable_methods(trait_ref.with_self_ty(self.tcx, ty));
            methods_root.iter()
        } else {
            (&[]).iter()
        };

        let methods = methods.map(|opt_mth| {
            opt_mth.map_or(nullptr, |(def_id, substs)| {
                self.convert_instance_to_fn_ptr(
                    Instance::resolve_for_vtable(self.tcx, ParamEnv::reveal_all(), def_id, substs)
                        .unwrap(),
                )
            })
        });

        components.extend(methods);

        // Cast to an array of void*s
        let void_ptr_ty = self.tcx.mk_nil_ptr();
        let array_ty = self
            .tcx
            .mk_array(void_ptr_ty, components.len().try_into().unwrap());

        let conv_void_ptr_ty = self.type_cache.convert_type(void_ptr_ty);
        let conv_array_ty = self.type_cache.convert_type(array_ty);

        let components = components
            .into_iter()
            .map(|comp| Tree::new1(TreeCode::ConvertExpr, conv_void_ptr_ty, comp))
            .collect::<Vec<_>>();
        // Why no need for a compound_literal_expr here? I don't know.
        let constructor = Tree::new_array_constructor(conv_array_ty, &components);

        let vtable_var_name = self.make_vtable_name(ty, trait_ref, self.vtables.len());
        let mut vtable_var = Tree::new_var_decl(
            UNKNOWN_LOCATION,
            Tree::new_identifier(vtable_var_name),
            conv_array_ty,
        );
        vtable_var.set_static(true);
        vtable_var.set_decl_context(self.translation_unit_decl);
        vtable_var.set_decl_initial(constructor);
        vtable_var.finalize_decl();

        let vtable_ptr = Tree::new_addr_expr(vtable_var);
        self.vtables.insert(key, vtable_ptr);
        vtable_ptr
    }
}

struct FunctionConversion<'a, 'tcx, 'body> {
    conv_ctx: &'a mut ConversionCtx<'tcx>,
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &'body Body<'tcx>,
    fn_decl: Function,
    return_type_is_void: bool,
    res_decl: Tree,
    /// If res_decl is a struct, and one of its fields is also a struct, and we try to set it
    /// directly, we crash gcc. This may be due to the struct being anonymous. Anyway, if we
    /// do it via a temporary variable, no crash. This is the temporary variable.
    tmp_var_decl_for_res: Tree,
    args: Vec<Tree>,
    vars: DeclList,
    block_labels: Vec<Tree>,
    main_gcc_block: Tree,
    stmt_list: StatementList,
}

impl<'a, 'tcx, 'body> FunctionConversion<'a, 'tcx, 'body> {
    fn new(
        conv_ctx: &'a mut ConversionCtx<'tcx>,
        name: Symbol,
        instance: Instance<'tcx>,
        body: &'body Body<'tcx>,
    ) -> Self {
        let return_type_is_void = if let TyKind::Tuple(substs) = &body.return_ty().kind {
            substs.is_empty()
        } else {
            false
        };

        let return_type = conv_ctx.type_cache.convert_fn_return_type(body.return_ty());

        // When we have a spread_arg, then one of our "arguments" is a tuple. Our function's
        // argument list should contain the tuple elements, but its MIR should see the tuple
        // instead. To support this, we add another VarDecl for the tuple, then initialize it
        // with the extra arguments.
        struct SpreadArgInfo {
            /// Index of tuple in args list (both internal and external)
            spread_arg_index: usize,
            /// Number of fields in tuple
            num_spread_args: usize,
        }

        let mut arg_types_for_caller = conv_ctx.type_cache.convert_fn_arg_types(&body);

        let spread_arg_info = if let Some(spread_arg) = body.spread_arg {
            let spread_arg_ty = body.local_decls[spread_arg].ty;

            let spread_arg_types = if let ty::Tuple(substs) = spread_arg_ty.kind {
                substs.types().into_iter().collect::<Vec<_>>()
            } else {
                unreachable!("spread_arg of type {:?}, expected Tuple", spread_arg_ty);
            };

            // Subtract 1 because Local indices include the return variable's local_decl, but arg
            // indices don't.
            let spread_arg_index = spread_arg.as_usize().checked_sub(1).unwrap();

            let num_spread_args = spread_arg_types.len();

            arg_types_for_caller.splice(
                spread_arg_index..(spread_arg_index + 1),
                spread_arg_types
                    .into_iter()
                    .map(|ty| conv_ctx.type_cache.convert_type(ty)),
            );

            Some(SpreadArgInfo {
                spread_arg_index,
                num_spread_args,
            })
        } else {
            None
        };

        let fn_type = Tree::new_function_type(return_type, &arg_types_for_caller);

        let name = CString::new(&*name.as_str()).unwrap();
        let mut fn_decl = Function::new(&name, fn_type);
        fn_decl.set_external(false);
        fn_decl.set_preserve_p(true);

        let main_gcc_block = Tree::new_block(NULL_TREE, NULL_TREE, fn_decl.0, NULL_TREE);
        fn_decl.set_initial(main_gcc_block);

        let mut stmt_list = StatementList::new();

        let res_decl = Tree::new_result_decl(UNKNOWN_LOCATION, return_type);
        fn_decl.set_result(res_decl);

        let tmp_var_decl_for_res;
        let spread_arg_var;
        let vars = {
            let mut var_types = conv_ctx
                .type_cache
                .convert_local_decl_types(&body, body.vars_and_temps_iter());

            // Add a var decl for tmp_var_decl_for_res
            tmp_var_decl_for_res = var_types.len();
            var_types.push(return_type);

            // Add a var decl for spread_arg if necessary
            spread_arg_var = if let Some(spread_arg) = body.spread_arg {
                var_types.push(
                    conv_ctx
                        .type_cache
                        .convert_type(body.local_decls[spread_arg].ty),
                );
                Some(var_types.len() - 1)
            } else {
                None
            };

            DeclList::new(TreeCode::VarDecl, &var_types)
        };

        let tmp_var_decl_for_res = vars[tmp_var_decl_for_res];

        let parm_decls_for_caller = DeclList::new(TreeCode::ParmDecl, &arg_types_for_caller);

        let mut internal_args = (*parm_decls_for_caller).to_vec();
        if let Some(SpreadArgInfo {
            spread_arg_index,
            num_spread_args,
        }) = spread_arg_info
        {
            let spread_arg_var = vars[spread_arg_var.unwrap()];

            let caller_arg_range = spread_arg_index..(spread_arg_index + num_spread_args);
            internal_args.splice(caller_arg_range.clone(), [spread_arg_var].iter().copied());

            for (i, parm_decl) in parm_decls_for_caller[caller_arg_range].iter().enumerate() {
                let field = Tree::new_record_field_ref(spread_arg_var, i);
                stmt_list.push(Tree::new_init_expr(field, *parm_decl));
            }
        }

        fn_decl.attach_parm_decls(&parm_decls_for_caller);

        let block_labels = body
            .basic_blocks()
            .iter()
            .map(|_bb| Tree::new_label_decl(UNKNOWN_LOCATION, fn_decl.0))
            .collect::<Vec<_>>();

        let tcx = conv_ctx.tcx;

        Self {
            conv_ctx,
            tcx,
            instance,
            body,
            fn_decl,
            return_type_is_void,
            res_decl,
            tmp_var_decl_for_res,
            args: internal_args,
            vars,
            block_labels,
            main_gcc_block,
            stmt_list,
        }
    }

    fn convert_type(&mut self, ty: Ty<'tcx>) -> Tree {
        let ty = self.conv_ctx.tcx.subst_and_normalize_erasing_regions(
            self.instance.substs,
            ParamEnv::reveal_all(),
            &ty,
        );

        self.conv_ctx.type_cache.convert_type(ty)
    }

    fn get_local(&self, local: Local) -> Tree {
        let n = local.as_usize();
        if n == 0 {
            self.tmp_var_decl_for_res
        } else if n <= self.args.len() {
            self.args[n - 1]
        } else {
            self.vars[n - self.args.len() - 1]
        }
    }

    /// Returns true for both &[T] and [T]
    fn is_place_ty_slice(place_ty: PlaceTy<'tcx>) -> bool {
        if place_ty.variant_index.is_some() {
            return false;
        }

        match place_ty.ty.kind {
            ty::Slice(_) | ty::Str => true,
            _ => place_ty.ty.is_slice(),
        }
    }

    /// Do C-style pointer math - multiply the element index by the element type to get the offset
    fn pointer_plus_element_index(pointer: Tree, element_index: Tree) -> Tree {
        let element_type = pointer.get_type().get_pointer_type_deref_type();
        let offset = Tree::new2(
            TreeCode::MultExpr,
            element_index.get_type(),
            element_index,
            element_type.get_type_size_bytes(),
        );
        Tree::new2(
            TreeCode::PointerPlusExpr,
            pointer.get_type(),
            pointer,
            offset,
        )
    }

    fn convert_const(&mut self, mut const_: &Const<'tcx>) -> Tree {
        use ConstKind::*;
        use TyKind::*;

        if let Unevaluated(def_id, substs, promoted) = const_.val {
            const_ = &self
                .tcx
                .const_eval_resolve(ParamEnv::reveal_all(), def_id, substs, promoted, None)
                .unwrap();
        }

        match const_.val {
            Value(ConstValue::Scalar(scalar @ Scalar::Raw { .. })) => {
                let size = match scalar {
                    Scalar::Raw { size, .. } => size,
                    _ => unreachable!(),
                };
                let size = Size::from_bytes(size.into());

                match const_.ty.kind {
                    Int(_) | Uint(_) => Tree::new_int_constant(
                        self.convert_type(const_.ty),
                        scalar.assert_bits(size).try_into().unwrap(),
                    ),

                    Bool => {
                        if scalar.to_bool().unwrap() {
                            TreeIndex::BooleanTrue.into()
                        } else {
                            TreeIndex::BooleanFalse.into()
                        }
                    }

                    Tuple(substs) if substs.is_empty() => TreeIndex::Void.into(),
                    // Can an adt be initialised with a scalar const
                    // without being represented himself as scalar ?
                    Adt(adt_def, _substs) if adt_def.adt_kind() == AdtKind::Struct => {
                        let type_ = self.convert_type(const_.ty);

                        let layout = self.conv_ctx.layout_of(const_.ty);
                        if layout.is_zst() {
                            let constructor = Tree::new_record_constructor(
                                type_,
                                // no fields, it's a ZST
                                &[],
                                &[],
                            );
                            Tree::new_compound_literal_expr(type_, constructor, self.fn_decl.0)
                        } else {
                            Tree::new_int_constant(
                                type_,
                                scalar.assert_bits(size).try_into().unwrap(),
                            )
                        }
                    }

                    FnDef(..) => self.make_zst_literal(const_.ty),

                    _ => unimplemented!(
                        "const, ty.kind={:?}, ty={:?}, val={:?}",
                        const_.ty.kind,
                        const_.ty,
                        const_.val
                    ),
                }
            }

            _ => unimplemented!("Const {:?} {:?}", const_.ty, const_.val),
        }
    }

    fn get_place(&mut self, place: &Place<'tcx>) -> Tree {
        let base = self.get_local(place.local);

        // Now apply any projections

        let mut component = base;
        let mut component_ty =
            PlaceTy::from_ty(&self.body.local_decls.local_decls()[place.local].ty);

        for elem in place.projection {
            use ProjectionElem::*;

            match elem {
                Field(field_index, field_ty) => {
                    let layout = self.conv_ctx.layout_of(field_ty);
                    if layout.details.abi.is_scalar() {
                        // don't do anything
                    } else {
                        component = Tree::new_record_field_ref(component, field_index.as_usize());
                    }
                }

                Downcast(_, variant_index) => {
                    // variants_ref = enum_structs.variants. The union is the 2nd field.
                    let variants_ref = Tree::new_record_field_ref(component, 1);

                    // component = variants_ref.variantN
                    component = Tree::new_record_field_ref(variants_ref, variant_index.as_usize());
                }

                Deref => {
                    if Self::is_place_ty_slice(component_ty) {
                        // If it's a slice, then don't do anything, we'll need the slice ref
                        // struct itself.
                    } else {
                        component = Tree::new_indirect_ref(component);
                    }
                }

                Index(index) => {
                    let index = self.get_local(*index);

                    if Self::is_place_ty_slice(component_ty) {
                        let ptr = Tree::new_record_field_ref(component, 0);
                        let ptr = Self::pointer_plus_element_index(ptr, index);
                        component = Tree::new_indirect_ref(ptr);
                    } else {
                        // an ArrayType's type field contains its element type
                        let array_type = component.get_type();
                        assert_eq!(array_type.get_code(), TreeCode::ArrayType);
                        let element_type = array_type.get_type();

                        component = Tree::new_array_index_ref(element_type, component, index);
                    }
                }

                _ => unimplemented!("projection {:?}", elem),
            }

            component_ty = component_ty.projection_ty(self.tcx, elem);
        }

        component
    }

    fn make_zst_literal(&mut self, array_type: Ty<'tcx>) -> Tree {
        // TypeCache::make_zst() converts ZSTs to zero-length arrays, so construct an empty array
        let array_type = self.convert_type(array_type);
        let constructor = Tree::new_array_constructor(array_type, &[]);
        Tree::new_compound_literal_expr(array_type, constructor, self.fn_decl.0)
    }

    fn convert_operand(&mut self, operand: &Operand<'tcx>) -> Tree {
        use Operand::*;

        match operand {
            Copy(place) => self.get_place(place),
            Move(place) => self.get_place(place),
            Constant(c) => self.convert_const(&c.literal),
        }
    }

    /// Get a component_ref for an enum's discriminant field
    fn get_discriminant_ref(&mut self, place: &Place<'tcx>) -> Tree {
        let place = self.get_place(place);

        // enum_struct.discriminant = variant_index.
        // discriminant is 1st field.
        Tree::new_record_field_ref(place, 0)
    }

    fn make_slice(&mut self, converted_slice_type: Tree, ptr_expr: Tree, length: u64) -> Tree {
        let constructor = Tree::new_record_constructor(
            converted_slice_type,
            &[
                converted_slice_type.get_record_type_field_decl(0),
                converted_slice_type.get_record_type_field_decl(1),
            ],
            &[
                ptr_expr,
                Tree::new_int_constant(USIZE_KIND, length.try_into().unwrap()),
            ],
        );
        Tree::new_compound_literal_expr(converted_slice_type, constructor, self.fn_decl.0)
    }

    fn make_trait_object(&mut self, trait_obj_ty: Tree, obj_ptr: Tree, vtable_ptr: Tree) -> Tree {
        let void_ptr_ty = Tree::new_pointer_type(TreeIndex::VoidType.into());
        let obj_ptr = Tree::new1(TreeCode::ConvertExpr, void_ptr_ty, obj_ptr);
        let constructor = Tree::new_record_constructor(
            trait_obj_ty,
            &[
                trait_obj_ty.get_record_type_field_decl(0),
                trait_obj_ty.get_record_type_field_decl(1),
            ],
            &[obj_ptr, vtable_ptr],
        );
        Tree::new_compound_literal_expr(trait_obj_ty, constructor, self.fn_decl.0)
    }

    fn convert_rvalue(&mut self, rv: &Rvalue<'tcx>) -> Tree {
        use Rvalue::*;

        match rv {
            Use(operand) => self.convert_operand(operand),

            BinaryOp(op, operand1, operand2) => {
                use TreeCode::*;

                let code = match op {
                    BinOp::Add => PlusExpr,
                    BinOp::Sub => MinusExpr,
                    BinOp::Mul => MultExpr,
                    // TODO: non-integer division
                    // TODO: verify truncating type is correct
                    BinOp::Div => TruncDivExpr,
                    // TODO: non-integer division
                    // TODO: verify truncating type is correct
                    BinOp::Rem => TruncModExpr,
                    BinOp::BitXor => BitXorExpr,
                    BinOp::BitAnd => BitAndExpr,
                    BinOp::BitOr => BitIorExpr,
                    BinOp::Shl => LShiftExpr,
                    BinOp::Shr => RShiftExpr,
                    BinOp::Eq => EqExpr,
                    BinOp::Lt => LtExpr,
                    BinOp::Le => LeExpr,
                    BinOp::Ne => NeExpr,
                    BinOp::Gt => GtExpr,
                    BinOp::Ge => GeExpr,
                    // TODO: offset
                    _ => unimplemented!("binop {:?}", op),
                };

                let type_ = self.convert_type(rv.ty(self.body, self.tcx));
                let operand1 = self.convert_operand(operand1);
                let operand2 = self.convert_operand(operand2);
                Tree::new2(code, type_, operand1, operand2)
            }

            CheckedBinaryOp(op, operand1, operand2) => {
                let type_ = self.convert_type(rv.ty(self.body, self.tcx));
                let unchecked_value =
                    self.convert_rvalue(&BinaryOp(*op, operand1.clone(), operand2.clone()));
                // TODO: perform the check
                let check_value = TreeIndex::BooleanTrue.into();
                let constructor = Tree::new_record_constructor(
                    type_,
                    &[
                        type_.get_record_type_field_decl(0),
                        type_.get_record_type_field_decl(1),
                    ],
                    &[unchecked_value, check_value],
                );
                Tree::new_compound_literal_expr(type_, constructor, self.fn_decl.0)
            }

            UnaryOp(op, operand) => {
                let operand = self.convert_operand(operand);
                let type_ = self.convert_type(rv.ty(self.body, self.tcx));
                let code = match op {
                    UnOp::Neg => TreeCode::NegateExpr,
                    UnOp::Not => TreeCode::BitNotExpr,
                };
                Tree::new1(code, type_, operand)
            }

            NullaryOp(op, ty) => match op {
                NullOp::SizeOf => self.convert_type(ty).get_type_size_bytes(),
                NullOp::Box => todo!("NullOp::Box, type {:?}", ty),
            },

            Discriminant(place) => self.get_discriminant_ref(place),

            Ref(_region, _borrow_kind, place) => Tree::new_addr_expr(self.get_place(place)),

            Cast(cast_kind, operand, new_ty) => {
                use CastKind::*;
                use PointerCast::*;

                match cast_kind {
                    Misc => Tree::new1(
                        TreeCode::ConvertExpr,
                        self.convert_type(new_ty),
                        self.convert_operand(operand),
                    ),

                    Pointer(MutToConstPointer) | Pointer(UnsafeFnPointer) => Tree::new1(
                        TreeCode::NopExpr,
                        self.convert_type(new_ty),
                        self.convert_operand(operand),
                    ),

                    Pointer(ReifyFnPointer) => {
                        let fn_def = operand.ty(&self.body.local_decls, self.tcx);
                        if let ty::FnDef(def_id, substs) = fn_def.kind {
                            let instance = self.conv_ctx.resolve_fn(def_id, substs);
                            self.conv_ctx.convert_instance_to_fn_ptr(instance)
                        } else {
                            unreachable!()
                        }
                    }

                    Pointer(Unsize) => {
                        let old_ty = operand.ty(&self.body.local_decls, self.tcx);

                        if TyS::same_type(old_ty, new_ty) {
                            return self.convert_operand(operand);
                        }

                        if let (
                            TyKind::Ref(
                                _,
                                TyS {
                                    kind:
                                        TyKind::Array(
                                            array_element_type,
                                            Const {
                                                val:
                                                    ConstKind::Value(ConstValue::Scalar(
                                                        array_length_scalar,
                                                    )),
                                                ..
                                            },
                                        ),
                                    ..
                                },
                                _,
                            ),
                            TyKind::Ref(
                                _,
                                TyS {
                                    kind: TyKind::Slice(slice_element_type),
                                    ..
                                },
                                _,
                            ),
                        ) = (&old_ty.kind, &new_ty.kind)
                        {
                            if array_element_type == slice_element_type {
                                let ptr = Tree::new_addr_expr(self.convert_operand(operand));
                                let slice_type = self.convert_type(new_ty);
                                return self.make_slice(
                                    slice_type,
                                    ptr,
                                    array_length_scalar.to_u64().unwrap(),
                                );
                            }
                        }

                        if let (
                            TyKind::Ref(_, old_ref_target_ty, _),
                            TyKind::Ref(
                                _,
                                TyS {
                                    kind: TyKind::Dynamic(dyn_preds, _region),
                                    ..
                                },
                                _,
                            ),
                        ) = (&old_ty.kind, &new_ty.kind)
                        {
                            let obj_ptr = self.convert_operand(operand);

                            let ext_trait_ref = dyn_preds.principal();
                            let vtable = self.conv_ctx.get_vtable(old_ref_target_ty, ext_trait_ref);

                            let trait_object_ty = self.convert_type(new_ty);
                            return self.make_trait_object(trait_object_ty, obj_ptr, vtable);
                        }

                        unimplemented!("Pointer(Unsize) cast of {:?} to {:?}", old_ty, new_ty);
                    }

                    _ => unimplemented!("cast kind {:?} in {:?}", cast_kind, rv),
                }
            }

            Aggregate(agg_kind, operands) => {
                use AggregateKind::*;

                match &**agg_kind {
                    Array(_element_type) => {
                        let array_type = self.convert_type(rv.ty(self.body, self.tcx));
                        let constructor = Tree::new_array_constructor(
                            array_type,
                            &operands
                                .into_iter()
                                .map(|operand| self.convert_operand(operand))
                                .collect::<Vec<_>>(),
                        );
                        Tree::new_compound_literal_expr(array_type, constructor, self.fn_decl.0)
                    }

                    _ => unimplemented!(
                        "rvalue aggregate kind {:?}, operands={:?}",
                        agg_kind,
                        operands
                    ),
                }
            }

            Len(place) => {
                let place_expr = self.get_place(place);

                let place_ty = place.ty(&self.body.local_decls, self.tcx);
                if Self::is_place_ty_slice(place_ty) {
                    Tree::new_record_field_ref(place_expr, 1)
                } else {
                    todo!("Len of non-slice {:?} of type {:?}", place, place_ty);
                }
            }

            _ => unimplemented!("rvalue {:?}", rv),
        }
    }

    fn convert_goto(&self, target: BasicBlock) -> Tree {
        let target = self.block_labels[target.as_usize()];
        Tree::new_goto(target)
    }

    fn convert_unreachable(&self) -> Tree {
        Tree::new_call_expr(
            UNKNOWN_LOCATION,
            TreeIndex::VoidType.into(),
            Tree::new_addr_expr(BuiltinFunction::Unreachable.into()),
            &[],
        )
    }

    fn convert_rust_intrinsic(
        &mut self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
        original_args: &[Operand<'tcx>],
        converted_args: &[Tree],
        call_expr_type: Tree,
    ) -> Tree {
        let name = self.tcx.item_name(def_id);

        match &*name.as_str() {
            "wrapping_add" => Tree::new2(
                TreeCode::PlusExpr,
                call_expr_type,
                converted_args[0],
                converted_args[1],
            ),

            "wrapping_sub" => Tree::new2(
                TreeCode::MinusExpr,
                call_expr_type,
                converted_args[0],
                converted_args[1],
            ),

            // Convert pointer to isize, do the math, then convert back.
            // TODO: The whole point of this intrinsic is not to do the conversion, is it really
            // necessary?
            "arith_offset" => Tree::new1(
                TreeCode::NopExpr,
                call_expr_type,
                Tree::new2(
                    TreeCode::PlusExpr,
                    ISIZE_KIND.into(),
                    Tree::new1(TreeCode::NopExpr, ISIZE_KIND.into(), converted_args[0]),
                    converted_args[1],
                ),
            ),

            "copy_nonoverlapping" => {
                let copied_type = substs.type_at(0);
                let element_size = self.convert_type(copied_type).get_type_size_bytes();
                let all_size = Tree::new2(
                    TreeCode::MultExpr,
                    USIZE_KIND.into(),
                    // TODO: nop_expr?
                    element_size,
                    converted_args[2],
                );

                Tree::new_call_expr(
                    UNKNOWN_LOCATION,
                    TreeIndex::VoidType.into(),
                    Tree::new_addr_expr(BuiltinFunction::Memcpy.into()),
                    // src and dst are swapped here
                    &[converted_args[1], converted_args[0], all_size],
                )
            }

            "offset" => {
                let ptr = converted_args[0];
                // gcc wants a usize instead of an isize
                let offset =
                    Tree::new1(TreeCode::ConvertExpr, USIZE_KIND.into(), converted_args[1]);
                Tree::new2(TreeCode::PointerPlusExpr, ptr.get_type(), ptr, offset)
            }

            "size_of" => {
                let of_type = substs.type_at(0);
                self.convert_type(of_type).get_type_size_bytes()
            }

            "unreachable" => self.convert_unreachable(),

            _ => todo!("rust intrinsic {:?}", name),
        }
    }

    fn convert_call_expr(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        call_expr_type: Tree,
    ) -> Tree {
        let mut converted_args = args
            .into_iter()
            .map(|arg| self.convert_operand(arg))
            .collect::<Vec<_>>();

        let func_ty = func.ty(&self.body.local_decls, self.tcx);

        let fn_sig;
        let func = match func_ty.kind {
            ty::FnDef(def_id, substs) => {
                fn_sig = func_ty.fn_sig(self.tcx);
                if fn_sig.abi() == Abi::RustIntrinsic {
                    return self.convert_rust_intrinsic(
                        def_id,
                        substs,
                        args,
                        &converted_args,
                        call_expr_type,
                    );
                }

                let instance = self.conv_ctx.resolve_fn(def_id, substs);

                if let InstanceDef::Virtual(_, index) = instance.def {
                    // The virtual method call's first argument in the IR is the trait object.
                    let trait_object = converted_args[0];
                    let obj_ptr = Tree::new_record_field_ref(trait_object, 0);
                    let vtable_ptr = Tree::new_record_field_ref(trait_object, 1);

                    // The first argument should actually be the object pointer.
                    converted_args[0] = obj_ptr;

                    // Now find the function pointer in the vtable.

                    let fn_ptr_ptr_ty = self.tcx.mk_imm_ptr(self.tcx.mk_fn_ptr(fn_sig));
                    let fn_ptr_ptr_ty = self.convert_type(fn_ptr_ptr_ty);
                    let vtable_ptr = Tree::new1(TreeCode::ConvertExpr, fn_ptr_ptr_ty, vtable_ptr);

                    // Increase index by 3 to skip drop-in-place and 2 size fields.
                    // This assumes that the size fields are the same size as function pointers,
                    // so we can treat them as elements in a function pointer array.
                    let index = Tree::new_int_constant(USIZE_KIND, (index + 3).try_into().unwrap());
                    let fn_ptr_ptr = Self::pointer_plus_element_index(vtable_ptr, index);
                    Tree::new_indirect_ref(fn_ptr_ptr)
                } else {
                    self.conv_ctx.convert_instance_to_fn_ptr(instance)
                }
            }

            ty::FnPtr(sig) => {
                fn_sig = sig;
                self.convert_operand(func)
            }

            _ => todo!("function is of type {:?}", func_ty.kind),
        };

        // For RustCall, the last argument is a tuple, and each of its fields should be passed as
        // a separate argument.
        if fn_sig.abi() == rustc_target::spec::abi::Abi::RustCall {
            let num_tupled_args = args
                .last()
                .unwrap()
                .ty(&self.body.local_decls, self.tcx)
                .tuple_fields()
                .count();

            let spread_arg = converted_args.pop().unwrap();
            converted_args.extend(
                (0..num_tupled_args)
                    .into_iter()
                    .map(|i| Tree::new_record_field_ref(spread_arg, i)),
            );
        }

        Tree::new_call_expr(UNKNOWN_LOCATION, call_expr_type, func, &converted_args)
    }

    // TODO: The original terminator struct has cleanup and from_hir_call fields which should
    // maybe be used here.
    fn handle_call_terminator(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        destination: &Option<(Place<'tcx>, BasicBlock)>,
    ) {
        let (call_expr_type, returns_void) = if let Some((place, _)) = destination {
            let place_ty = place.ty(&self.body.local_decls, self.tcx);
            if place_ty.variant_index.is_some() {
                unreachable!("call's return type is an enum variant");
            }

            let call_expr_type = self.conv_ctx.type_cache.convert_fn_return_type(place_ty.ty);
            let returns_void = place_ty.ty.is_unit();
            (call_expr_type, returns_void)
        } else {
            (TreeIndex::VoidType.into(), true)
        };

        let call_expr = self.convert_call_expr(func, args, call_expr_type);

        if let Some((place, destination)) = destination {
            if returns_void {
                self.stmt_list.push(call_expr);
            } else {
                let init_expr = Tree::new_init_expr(self.get_place(place), call_expr);
                self.stmt_list.push(init_expr);
            }

            self.stmt_list.push(self.convert_goto(*destination));
        } else {
            self.stmt_list.push(call_expr);
            self.stmt_list.push(self.convert_unreachable());
        }
    }

    fn convert_basic_block(&mut self, block_index: BasicBlock, block: &BasicBlockData<'tcx>) {
        println!("{:?}", block);

        self.stmt_list.push(Tree::new_label_expr(
            self.block_labels[block_index.as_usize()],
        ));

        use StatementKind::*;
        use TerminatorKind::*;

        for stmt in &block.statements {
            match &stmt.kind {
                Nop => {}

                // These may be useful in the future, but are currently ignored.
                StorageLive(_) | StorageDead(_) => {}

                // I think these can be ignored safely, although I'm not sure about FakeRead.
                AscribeUserType(_, _) | Retag(_, _) | FakeRead(_, _) => {}

                Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    eprintln!("{:?} = {:?}", place, rvalue);

                    let place = self.get_place(place);
                    let rvalue = self.convert_rvalue(rvalue);

                    // Avoid reads from void and writes to void. But still evaluate both the place
                    // and the rvalue, in case either of them somehow has side effects (is that
                    // possible?). The assignment would actually work, too, except that ADT members
                    // of type unit are converted to zero-length arrays instead of void, so
                    // attempts to set them to a void value (or set a void place to their value)
                    // trigger a type mismatch error.
                    let place_is_void = place.get_type().get_code() == TreeCode::VoidType;
                    let rvalue_is_void = rvalue.get_type().get_code() == TreeCode::VoidType;
                    if !place_is_void && !rvalue_is_void {
                        self.stmt_list.push(Tree::new_init_expr(place, rvalue));
                    } else {
                        self.stmt_list.push(place);
                        self.stmt_list.push(rvalue);
                    }
                }

                SetDiscriminant {
                    place,
                    variant_index,
                } => {
                    let discr_ref = self.get_discriminant_ref(place);

                    let variant_index =
                        Tree::new_int_constant(ISIZE_KIND, variant_index.as_u32().into());

                    self.stmt_list
                        .push(Tree::new_init_expr(discr_ref, variant_index));
                }

                _ => unimplemented!("{:?}", stmt),
            }
        }

        let terminator = block.terminator();
        match &terminator.kind {
            Drop { .. } | Resume | Abort => {
                eprintln!("TODO: ignoring {:?}", terminator.kind);
            }

            Goto { target } => {
                self.stmt_list.push(self.convert_goto(*target));
            }

            Assert { msg, target, .. } => {
                // TODO
                eprintln!("WARNING: ignoring assert with message: {:?}", msg);
                self.stmt_list.push(self.convert_goto(*target));
            }

            SwitchInt {
                discr,
                switch_ty,
                values,
                targets,
            } => {
                assert!(values.len() >= 1);
                assert_eq!(targets.len(), values.len() + 1);

                let switch_ty_tree = self.convert_type(switch_ty);

                if values.len() == 1 {
                    let value = values[0];

                    let cond = Tree::new2(
                        TreeCode::EqExpr,
                        TreeIndex::BooleanType.into(),
                        self.convert_operand(discr),
                        Tree::new_int_constant(switch_ty_tree, value.try_into().unwrap()),
                    );

                    let if_eq_expr = self.convert_goto(targets[0]);
                    let else_expr = self.convert_goto(targets[1]);
                    self.stmt_list
                        .push(Tree::new_cond_expr(cond, if_eq_expr, else_expr));
                } else {
                    let mut cases_list = StatementList::new();

                    for (value, target) in values.into_iter().zip(targets) {
                        let case_expr = Tree::new_case_label_expr(
                            Some(Tree::new_int_constant(
                                switch_ty_tree,
                                (*value).try_into().unwrap(),
                            )),
                            Tree::new_label_decl(UNKNOWN_LOCATION, self.fn_decl.0),
                        );

                        cases_list.push(case_expr);
                        cases_list.push(self.convert_goto(*target));
                    }

                    // default case
                    cases_list.push(Tree::new_case_label_expr(
                        None,
                        Tree::new_label_decl(UNKNOWN_LOCATION, self.fn_decl.0),
                    ));
                    cases_list.push(self.convert_goto(*targets.last().unwrap()));

                    let discr = self.convert_operand(discr);
                    self.stmt_list
                        .push(Tree::new_switch_expr(switch_ty_tree, discr, cases_list.0));
                }
            }

            Return => {
                let return_value = if self.return_type_is_void {
                    NULL_TREE
                } else {
                    Tree::new_init_expr(self.res_decl, self.tmp_var_decl_for_res)
                };

                self.stmt_list.push(Tree::new_return_expr(return_value));
            }

            Unreachable => {
                self.stmt_list.push(self.convert_unreachable());
            }

            Call {
                func,
                args,
                destination,
                cleanup: _,
                from_hir_call: _,
            } => {
                self.handle_call_terminator(func, args, destination);
            }

            DropAndReplace { .. }
            | FalseEdges { .. }
            | FalseUnwind { .. }
            | GeneratorDrop
            | Yield { .. } => {
                // See:
                // * https://github.com/sapir/gcc-rust/issues/4#issuecomment-568808850
                // * https://github.com/sapir/gcc-rust/issues/6#issuecomment-568808572
                // * https://github.com/rust-lang/rust/blob/a9c1c04e986dbf610be8cbe6a8107f90b4db61ce/src/librustc_codegen_ssa/mir/block.rs#L888
                unreachable!(
                    "{:?} should have been removed before codegen",
                    terminator.kind
                )
            }
        }
    }

    fn finalize(mut self) {
        let vars_chain_head = self.vars.head().unwrap_or(NULL_TREE);
        let bind_expr = Tree::new_bind_expr(vars_chain_head, self.stmt_list.0, self.main_gcc_block);
        self.fn_decl.set_saved_tree(bind_expr);

        self.fn_decl.gimplify();
        self.fn_decl.finalize();
    }
}

fn func_mir_to_gcc<'tcx>(
    conv_ctx: &mut ConversionCtx<'tcx>,
    name: Symbol,
    instance: Instance<'tcx>,
    body: &'tcx Body,
) {
    let body = body.subst(conv_ctx.tcx, instance.substs);
    let mut fn_conv = FunctionConversion::new(conv_ctx, name, instance, &body);

    for (bb_idx, bb) in body.basic_blocks().iter_enumerated() {
        fn_conv.convert_basic_block(bb_idx, bb);
    }

    fn_conv.finalize();
}

pub fn mir2gimple<'tcx>(queries: &'tcx Queries<'tcx>) {
    queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
        let mut conv_ctx = ConversionCtx::new(tcx);

        let (mono_items, _inlining_map) =
            collect_crate_mono_items(tcx, MonoItemCollectionMode::Eager);

        for item in mono_items {
            match item {
                MonoItem::Fn(instance) => {
                    let name = tcx.symbol_name(instance).name;
                    println!("name: {}", name);

                    let mir = tcx.instance_mir(instance.def);
                    func_mir_to_gcc(&mut conv_ctx, name, instance, &mir);

                    println!();
                }

                _ => unimplemented!("monoitem {:?}", item),
            }
        }
    });
}
