use crate::gcc_api::*;
use rustc_hir::def_id::DefId;
use rustc_index::vec::Idx;
use rustc_interface::Queries;
use rustc_middle::{
    bug,
    mir::{
        interpret::{ConstValue, Scalar},
        mono::MonoItem,
        tcx::PlaceTy,
        AggregateKind, BasicBlock, BasicBlockData, BinOp, Body, CastKind, Field, HasLocalDecls,
        Local, NullOp, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind, UnOp,
    },
    ty::{
        self,
        adjustment::PointerCast,
        layout::{LayoutCx, TyAndLayout},
        subst::{Subst, SubstsRef},
        Const, ConstKind, Instance, InstanceDef, ParamEnv, PolyExistentialTraitRef, PolyFnSig, Ty,
        TyCtxt, TyKind, TyS,
    },
};
use rustc_mir::monomorphize::collector::{collect_crate_mono_items, MonoItemCollectionMode};
use rustc_span::symbol::Symbol;
use rustc_target::{
    abi::{Size, TagEncoding},
    spec::abi::Abi,
};
use std::{collections::HashMap, convert::TryInto, ffi::CString};

// Copied from https://github.com/bjorn3/rustc_codegen_cranelift/blob/8dfb1daea7a79ad983058098a091a2f4a7525cc9/src/abi/mod.rs#L16
// Copied from https://github.com/rust-lang/rust/blob/b2c1a606feb1fbdb0ac0acba76f881ef172ed474/src/librustc_middle/ty/layout.rs#L2287
pub(crate) fn fn_sig_for_fn_abi<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> ty::PolyFnSig<'tcx> {
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
            let sig = substs.as_closure().sig();

            let env_ty = tcx.closure_env_ty(def_id, substs).unwrap();
            sig.map_bound(|sig| tcx.mk_fn_sig(
                std::iter::once(env_ty.skip_binder()).chain(sig.inputs().iter().cloned()),
                sig.output(),
                sig.c_variadic,
                sig.unsafety,
                sig.abi
            ))
        }
        ty::Generator(_, substs, _) => {
            let sig = substs.as_generator().poly_sig();

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

                tcx.mk_fn_sig(
                    [env_ty, sig.resume_ty].iter(),
                    &ret_ty,
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

struct ConvertedFnSig {
    pub return_type: Type,
    pub arg_types: Vec<Type>,
}

impl ConvertedFnSig {
    fn into_function_type(self) -> Type {
        Type::new_function_type(self.return_type, &self.arg_types)
    }
}

/// Cache the types so if we convert the same anonymous type twice, we get the exact same
/// Tree object. Otherwise, we get errors about anonymous structs not being the same, even
/// though they have the same fields.
struct TypeCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// "Regular" type cache
    tys: HashMap<Ty<'tcx>, Type>,
    /// Special cache for enum variants (and structs) because enum variants aren't full types
    variants: HashMap<(Ty<'tcx>, rustc_target::abi::VariantIdx), Type>,
}

impl<'tcx> TypeCache<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            tys: HashMap::new(),
            variants: HashMap::new(),
        }
    }

    fn make_zst() -> Type {
        // Use an empty struct.
        let mut ty = Type::new_record_type(TreeCode::RecordType);
        ty.finish_record_type(DeclList::new(TreeCode::FieldDecl, &[]), 0, 1);
        ty
    }

    fn make_layout_cx(&self) -> LayoutCx<'tcx, TyCtxt<'tcx>> {
        LayoutCx {
            tcx: self.tcx,
            param_env: ParamEnv::reveal_all(),
        }
    }

    fn convert_integer(&mut self, integer: rustc_target::abi::Integer, signed: bool) -> Type {
        use rustc_target::abi::Integer::*;

        match (integer, signed) {
            (I8, true) => Type::new_signed_int_type(8),
            (I16, true) => Type::new_signed_int_type(16),
            (I32, true) => Type::new_signed_int_type(32),
            (I64, true) => Type::new_signed_int_type(64),
            (I8, false) => Type::new_unsigned_int_type(8),
            (I16, false) => Type::u16(),
            (I32, false) => Type::u32(),
            (I64, false) => Type::u64(),
            (I128, _) => todo!("128-bit int"),
        }
    }

    /// Convert a Scalar Abi, a field of a ScalarPair Abi or an enum discriminant.
    fn convert_scalar_at_offset(
        &mut self,
        scalar_layout: &rustc_target::abi::Scalar,
        base_ty_and_layout: TyAndLayout<'tcx>,
        offset: Size,
    ) -> Type {
        use rustc_target::abi::Primitive::*;

        match scalar_layout.value {
            Int(int_type, signed) => self.convert_integer(int_type, signed),

            Pointer => base_ty_and_layout
                .pointee_info_at(&self.make_layout_cx(), offset)
                .map_or(Type::void(), |pointee| {
                    self.convert_integer(
                        rustc_target::abi::Integer::approximate_align(&self.tcx, pointee.align),
                        false,
                    )
                })
                .mk_pointer_type(),
            _ => todo!("scalar layout value type {:?}", scalar_layout.value),
        }
    }

    fn convert_scalar(
        &mut self,
        ty_and_layout: TyAndLayout<'tcx>,
        scalar: &rustc_target::abi::Scalar,
    ) -> Type {
        self.convert_scalar_at_offset(scalar, ty_and_layout, Size::ZERO)
    }

    fn convert_scalar_pair(
        &mut self,
        ty_and_layout: TyAndLayout<'tcx>,
        scalar1_layout: &rustc_target::abi::Scalar,
        scalar2_layout: &rustc_target::abi::Scalar,
    ) -> Type {
        let scalar1_ofs = Size::ZERO;
        let scalar2_ofs = scalar1_layout
            .value
            .size(&self.tcx)
            .align_to(scalar2_layout.value.align(&self.tcx).abi);

        let mut fields = DeclList::new(
            TreeCode::FieldDecl,
            &[
                self.convert_scalar_at_offset(scalar1_layout, ty_and_layout, scalar1_ofs),
                self.convert_scalar_at_offset(scalar2_layout, ty_and_layout, scalar2_ofs),
            ],
        );
        fields[0].set_decl_name(Tree::new_identifier("field0"));
        fields[0].place_field_manually(scalar1_ofs.bytes());
        fields[1].set_decl_name(Tree::new_identifier("field1"));
        fields[1].place_field_manually(scalar2_ofs.bytes());

        let mut ty = Type::new_record_type(TreeCode::RecordType);
        ty.finish_record_type(
            fields,
            ty_and_layout.layout.size.bytes(),
            ty_and_layout.layout.align.abi.bytes(),
        );
        ty
    }

    /// Returns a RecordType with the fields in ty_and_layout.fields. Ignores the variant cache.
    fn convert_adt_fields(&mut self, ty_and_layout: TyAndLayout<'tcx>) -> Type {
        let layout_cx = self.make_layout_cx();

        let field_types = (0..ty_and_layout.fields.count())
            .into_iter()
            .map(|i| {
                let field_layout = ty_and_layout.field(&layout_cx, i).unwrap();
                self.convert_type(field_layout.ty)
            })
            .collect::<Vec<_>>();

        let mut fields = DeclList::new(TreeCode::FieldDecl, &field_types);
        for (i, field) in fields.iter_mut().enumerate() {
            field.set_decl_name(Tree::new_identifier(format!("field{}", i)));
            field.place_field_manually(ty_and_layout.fields.offset(i).bytes());
        }

        let mut ty = Type::new_record_type(TreeCode::RecordType);
        ty.finish_record_type(
            fields,
            ty_and_layout.size.bytes(),
            ty_and_layout.align.abi.bytes(),
        );
        ty
    }

    fn convert_single_variant_layout(&mut self, ty_and_layout: TyAndLayout<'tcx>) -> Type {
        let variant_index =
            if let rustc_target::abi::Variants::Single { index } = &ty_and_layout.variants {
                *index
            } else {
                unreachable!("expected Single variant, got {:?}", ty_and_layout);
            };

        if let Some(tree) = self.variants.get(&(ty_and_layout.ty, variant_index)) {
            return *tree;
        }

        let tree = self.convert_adt_fields(ty_and_layout);
        self.variants
            .insert((ty_and_layout.ty, variant_index), tree);
        tree
    }

    fn convert_aggregate(&mut self, ty_and_layout: TyAndLayout<'tcx>) -> Type {
        use rustc_target::abi::FieldsShape;

        match &ty_and_layout.fields {
            FieldsShape::Primitive => unreachable!("aggregate type with FieldsShape::Primitive"),

            FieldsShape::Array { stride, count: _ } => {
                // Enum variants can contain arrays but won't be arrays themselves. So an array
                // can't be an enum variant. And ty_and_layout.ty is the type itself for everything
                // except enum variants, so it must be the array itself.
                if let TyKind::Array(element_type, num_elements) = ty_and_layout.ty.kind {
                    if let ConstKind::Value(ConstValue::Scalar(num_elements)) = num_elements.val {
                        let num_elements =
                            num_elements.to_u64().expect("expected bits, got a ptr?");
                        // TODO: use stride for alignment
                        Type::new_array_type(self.convert_type(element_type), num_elements)
                    } else {
                        unreachable!("array with non-const number of elements");
                    }
                } else {
                    unreachable!(
                        "Array field placement for non-Array type {:#?}",
                        ty_and_layout
                    )
                }
            }

            FieldsShape::Union(..) | FieldsShape::Arbitrary { .. } => {
                match &ty_and_layout.variants {
                    rustc_target::abi::Variants::Single { .. } => {
                        self.convert_single_variant_layout(ty_and_layout)
                    }

                    rustc_target::abi::Variants::Multiple { variants, .. } => {
                        // An enum. Lay it out like this:
                        // struct {
                        //     union {
                        //         own_fields;
                        //         variant_1;
                        //         variant_2;
                        //         ...
                        //         variant_n;
                        //     };
                        // }
                        //
                        // if there's a tag discriminant field, it'll be in own_fields.

                        let mut union_field_types = Vec::with_capacity(variants.len() + 1);
                        union_field_types.push(self.convert_adt_fields(ty_and_layout));
                        union_field_types.extend((0..variants.len()).into_iter().map(|i| {
                            let variant_layout =
                                ty_and_layout.for_variant(&self.make_layout_cx(), i.into());

                            if let rustc_target::abi::Variants::Single { index } =
                                &variant_layout.variants
                            {
                                assert_eq!(index.as_usize(), i);
                            } else {
                                unreachable!();
                            }

                            self.convert_single_variant_layout(variant_layout)
                        }));

                        let mut union_fields =
                            DeclList::new(TreeCode::FieldDecl, &union_field_types);
                        for (i, field) in union_fields.iter_mut().enumerate() {
                            field.set_decl_name(Tree::new_identifier(if i == 0 {
                                "own_fields".to_string()
                            } else {
                                format!("variant{}", i)
                            }));

                            field.place_field_manually(0);
                        }

                        let mut union_ty = Type::new_record_type(TreeCode::UnionType);
                        union_ty.finish_record_type(
                            union_fields,
                            ty_and_layout.size.bytes(),
                            ty_and_layout.align.abi.bytes(),
                        );
                        union_ty
                    }
                }
            }
        }
    }

    fn get_type_layout(&self, ty: Ty<'tcx>) -> TyAndLayout<'tcx> {
        self.tcx.layout_of(ParamEnv::reveal_all().and(ty)).unwrap()
    }

    /// Converts the ABI described in `ty_and_layout.layout.abi`. Doesn't save in the type cache
    /// (use `convert_type` for that.)
    ///
    /// Note that `ty_and_layout.ty` might not be the type itself if `ty_and_layout` is an enum
    /// variant.
    fn convert_layout(&mut self, ty_and_layout: TyAndLayout<'tcx>) -> Type {
        use rustc_target::abi::Abi::*;

        match &ty_and_layout.layout.abi {
            Scalar(scalar) => self.convert_scalar(ty_and_layout, &scalar),

            ScalarPair(scalar1_layout, scalar2_layout) => {
                self.convert_scalar_pair(ty_and_layout, &scalar1_layout, &scalar2_layout)
            }

            // It never gets instantiated, so I think it shouldn't matter which type we use here.
            // Also, it's nice if a pointer to this can be a void*.
            Uninhabited => Type::void(),

            Vector { element, count } => {
                Type::new_vector_type(self.convert_scalar(ty_and_layout, element), *count)
            }

            Aggregate { .. } => {
                assert!(!ty_and_layout.layout.abi.is_unsized());
                self.convert_aggregate(ty_and_layout)
            }
        }
    }

    fn convert_type(&mut self, ty: Ty<'tcx>) -> Type {
        if let Some(tree) = self.tys.get(ty) {
            return *tree;
        }

        let ty_and_layout = self.get_type_layout(ty);

        // This includes the unit type. For function return types, convert_fn_return_type()
        // converts it to void, but in other contexts, we treat it like other ZSTs, so that it can
        // be instantiated.
        if ty_and_layout.is_zst() {
            return Self::make_zst();
        }

        // convert_layout can recursively call convert_type
        let mut tree = self.convert_layout(ty_and_layout);
        tree.set_name(Tree::new_identifier(format!("{}", ty)));
        *self.tys.entry(ty).or_insert(tree)
    }

    fn convert_fn_return_type(&mut self, ty: Ty<'tcx>) -> Type {
        if ty.is_unit() {
            Type::void()
        } else {
            self.convert_type(ty)
        }
    }

    fn convert_fn_sig(&mut self, fn_sig: PolyFnSig<'tcx>) -> ConvertedFnSig {
        // TODO: fn_sig.c_variadic, fn_sig.abi
        let inputs_and_output = fn_sig.inputs_and_output();
        let inputs_and_output = self
            .tcx
            .normalize_erasing_late_bound_regions(ParamEnv::reveal_all(), &inputs_and_output);
        let (return_type, arg_types) = inputs_and_output.split_last().expect("missing return type");

        let return_type = self.convert_fn_return_type(return_type);
        let arg_types = arg_types
            .into_iter()
            .map(|arg| self.convert_type(arg))
            .collect();

        ConvertedFnSig {
            return_type,
            arg_types,
        }
    }

    fn convert_local_decl_types<I>(&mut self, body: &Body<'tcx>, iter: I) -> Vec<Type>
    where
        I: Iterator<Item = Local>,
    {
        iter.map(|local| self.convert_type(body.local_decls[local].ty))
            .collect()
    }

    fn convert_fn_arg_types(&mut self, body: &Body<'tcx>) -> Vec<Type> {
        self.convert_local_decl_types(body, body.args_iter())
    }
}

struct ConversionCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    type_cache: TypeCache<'tcx>,
    vtables: HashMap<(Ty<'tcx>, Option<PolyExistentialTraitRef<'tcx>>), Expr>,
    translation_unit_decl: Expr,
}

impl<'tcx> ConversionCtx<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            type_cache: TypeCache::new(tcx),
            vtables: HashMap::new(),
            translation_unit_decl: Expr::new_translation_unit_decl(NULL_TREE),
        }
    }

    pub fn layout_of(&self, ty: Ty<'tcx>) -> TyAndLayout<'tcx> {
        self.tcx.layout_of(ParamEnv::reveal_all().and(ty)).unwrap()
    }

    pub fn layout_of_place_ty(&self, place_ty: PlaceTy<'tcx>) -> TyAndLayout<'tcx> {
        let ty_and_layout = self.layout_of(place_ty.ty);
        if let Some(variant_index) = place_ty.variant_index {
            let cx = self.type_cache.make_layout_cx();
            ty_and_layout.for_variant(&cx, variant_index)
        } else {
            ty_and_layout
        }
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
        Instance::resolve(self.tcx, ParamEnv::reveal_all(), def_id, substs)
            .unwrap()
            .unwrap()
    }

    fn convert_instance_to_fn_ptr(&mut self, instance: Instance<'tcx>) -> Expr {
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
        fn_decl.mk_pointer()
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
    ) -> Expr {
        let key = (ty, trait_ref);
        if let Some(&vtable) = self.vtables.get(&key) {
            return vtable;
        }

        let ty_and_layout = self.layout_of(ty);
        let mut components: Vec<_> = vec![
            self.convert_instance_to_fn_ptr(Instance::resolve_drop_in_place(self.tcx, ty)),
            Expr::new_int_constant(USIZE_KIND, ty_and_layout.size.bytes().try_into().unwrap()),
            Expr::new_int_constant(
                USIZE_KIND,
                ty_and_layout.align.abi.bytes().try_into().unwrap(),
            ),
        ];

        let nullptr = Expr::null_ptr();

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
            .map(|comp| comp.convert_cast(conv_void_ptr_ty))
            .collect::<Vec<_>>();
        // Why no need for a compound_literal_expr here? I don't know.
        let constructor = Expr::new_array_constructor(conv_array_ty, &components);

        let vtable_var_name = self.make_vtable_name(ty, trait_ref, self.vtables.len());
        let mut vtable_var = Expr::new_var_decl(
            UNKNOWN_LOCATION,
            Tree::new_identifier(vtable_var_name),
            conv_array_ty,
        );
        vtable_var.set_static(true);
        vtable_var.set_decl_context(self.translation_unit_decl);
        vtable_var.set_decl_initial(constructor);
        vtable_var.finalize_decl();

        let vtable_ptr = vtable_var.mk_pointer();
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
    res_decl: Expr,
    /// If res_decl is a struct, and one of its fields is also a struct, and we try to set it
    /// directly, we crash gcc. This may be due to the struct being anonymous. Anyway, if we
    /// do it via a temporary variable, no crash. This is the temporary variable.
    tmp_var_decl_for_res: Expr,
    args: Vec<Expr>,
    vars: DeclList,
    block_labels: Vec<Expr>,
    main_gcc_block: Expr,
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
        struct SpreadArgInfo<'tcx> {
            /// Index of tuple in args list (both internal and external)
            spread_arg_index: usize,
            /// Number of fields in tuple
            num_spread_args: usize,
            /// Tuple type
            spread_arg_ty: Ty<'tcx>,
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
                spread_arg_ty,
            })
        } else {
            None
        };

        let fn_type = Type::new_function_type(return_type, &arg_types_for_caller);

        let name = CString::new(&*name.as_str()).unwrap();
        let mut fn_decl = Function::new(&name, fn_type);
        fn_decl.set_external(false);
        fn_decl.set_preserve_p(true);

        let main_gcc_block = Expr::new_block(None, None, fn_decl.0, None);
        fn_decl.set_initial(main_gcc_block);

        let mut stmt_list = StatementList::new();

        let res_decl = Expr::new_result_decl(UNKNOWN_LOCATION, return_type);
        fn_decl.set_result(res_decl);

        for (i, decl) in body.local_decls.iter_enumerated() {
            eprintln!("Local {:?}, type {:?}", i, decl.ty);
        }

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
            spread_arg_ty,
        }) = spread_arg_info
        {
            let spread_arg_var = vars[spread_arg_var.unwrap()];

            let caller_arg_range = spread_arg_index..(spread_arg_index + num_spread_args);
            internal_args.splice(caller_arg_range.clone(), [spread_arg_var].iter().copied());

            let ty_and_layout = conv_ctx.layout_of(spread_arg_ty);
            for (i, (parm_decl, field_ty)) in parm_decls_for_caller[caller_arg_range]
                .iter()
                .zip(spread_arg_ty.tuple_fields())
                .enumerate()
            {
                let field_ty = conv_ctx.type_cache.convert_type(field_ty);
                let field = Self::get_field(spread_arg_var, ty_and_layout, i, field_ty);
                stmt_list.push(Expr::new_assignment(field, *parm_decl));
            }
        }

        fn_decl.attach_parm_decls(&parm_decls_for_caller);

        let block_labels = body
            .basic_blocks()
            .iter()
            .map(|_bb| Expr::new_label_decl(UNKNOWN_LOCATION, fn_decl.0))
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

    fn convert_type(&mut self, ty: Ty<'tcx>) -> Type {
        let ty = self.conv_ctx.tcx.subst_and_normalize_erasing_regions(
            self.instance.substs,
            ParamEnv::reveal_all(),
            &ty,
        );

        self.conv_ctx.type_cache.convert_type(ty)
    }

    fn get_local(&self, local: Local) -> Expr {
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
    fn pointer_plus_element_index(pointer: Expr, element_index: Expr) -> Expr {
        let element_type = pointer.get_type().get_pointer_type_deref_type();
        let offset = element_index.mult(element_type.get_size_bytes());
        pointer.pointer_plus(offset)
    }

    fn convert_const(&mut self, mut const_: &Const<'tcx>) -> Expr {
        use TyKind::*;

        const_ = const_.eval(self.tcx, ParamEnv::reveal_all());

        if let ConstKind::Unevaluated(..) = const_.val {
            todo!("failed to evaluate const {:?}", const_);
        }

        match const_.val {
            ConstKind::Value(ConstValue::Scalar(scalar @ Scalar::Raw { .. })) => {
                let size = match scalar {
                    Scalar::Raw { size, .. } => size,
                    _ => unreachable!(),
                };
                let size = Size::from_bytes(size);

                if size == Size::ZERO {
                    return self.make_zst_literal(const_.ty);
                }

                match const_.ty.kind {
                    Bool | Int(_) | Uint(_) | Char => Expr::new_int_constant(
                        self.convert_type(const_.ty),
                        scalar.assert_bits(size).try_into().unwrap(),
                    ),

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

    fn get_place_ty(&mut self, place: &Place<'tcx>) -> PlaceTy<'tcx> {
        place.ty(&self.body.local_decls, self.tcx)
    }

    fn get_field(
        container: Expr,
        container_layout: TyAndLayout<'tcx>,
        field: usize,
        field_ty: Type,
    ) -> Expr {
        let field_offset = container_layout.fields.offset(field);

        let place_ptr = container.mk_pointer();

        let field_ptr = if field_offset == Size::ZERO {
            // We'll be converting as *(field_type*)&struct
            place_ptr
        } else {
            // We'll be converting as *(field_type*)((void*)&struct + field_offset)
            let field_offset =
                Expr::new_int_constant(USIZE_KIND, field_offset.bytes().try_into().unwrap());

            place_ptr.pointer_plus(field_offset)
        };

        let new_field_ptr_type = field_ty.mk_pointer_type();
        field_ptr.nop_cast(new_field_ptr_type).deref_value()
    }

    fn get_place(&mut self, place: &Place<'tcx>) -> Expr {
        let base = self.get_local(place.local);

        // Now apply any projections

        let mut component = base;
        // Not the same as get_place_ty() - this is only the type of the base
        let mut component_ty =
            PlaceTy::from_ty(&self.body.local_decls.local_decls()[place.local].ty);

        for elem in place.projection {
            use ProjectionElem::*;

            let next_component_ty = component_ty.projection_ty(self.tcx, elem);

            match elem {
                Field(field, field_ty) => {
                    let field_ty = self.convert_type(field_ty);
                    let ty_and_layout = self.conv_ctx.layout_of_place_ty(component_ty);
                    component = Self::get_field(component, ty_and_layout, field.index(), field_ty);
                }

                Downcast(_, variant_index) => {
                    let ty_and_layout = self.conv_ctx.layout_of_place_ty(component_ty);
                    let ty_and_layout = ty_and_layout
                        .for_variant(&self.conv_ctx.type_cache.make_layout_cx(), variant_index);
                    // TODO: convert_layout() doesn't guarantee this to be cached. But it will be,
                    // because it's an enum variant.
                    let new_ptr_type = self
                        .conv_ctx
                        .type_cache
                        .convert_layout(ty_and_layout)
                        .mk_pointer_type();
                    // Cast to a pointer to the variant
                    component = component.mk_pointer().nop_cast(new_ptr_type).deref_value();
                }

                Deref => {
                    if Self::is_place_ty_slice(component_ty) {
                        // If it's a slice, then don't do anything, we'll need the slice ref
                        // struct itself.
                    } else {
                        // Pointer type conversion is messed up. Fix it before dereferencing.
                        let dereffed_layout = self.conv_ctx.layout_of_place_ty(next_component_ty);
                        let pointer_ty = self
                            .conv_ctx
                            .type_cache
                            .convert_layout(dereffed_layout)
                            .mk_pointer_type();
                        component = component.nop_cast(pointer_ty);

                        component = component.deref_value();
                    }
                }

                Index(index) => {
                    let index = self.get_local(index);

                    if Self::is_place_ty_slice(component_ty) {
                        let ptr = component.get_record_field(0);
                        let ptr = Self::pointer_plus_element_index(ptr, index);
                        component = ptr.deref_value();
                    } else {
                        // an ArrayType's type field contains its element type
                        let array_type = component.get_type();
                        assert_eq!(array_type.get_code(), TreeCode::ArrayType);
                        let element_type = array_type.get_type();

                        component = Expr::new_array_index_ref(element_type, component, index);
                    }
                }

                _ => unimplemented!("projection {:?}", elem),
            }

            component_ty = next_component_ty;
        }

        component
    }

    fn make_zst_literal(&mut self, ty: Ty<'tcx>) -> Expr {
        // TypeCache::make_zst() converts ZSTs to empty structs, so construct an empty struct
        let ty = self.convert_type(ty);
        let constructor = Expr::new_record_constructor(ty, &[], &[]);
        Expr::new_compound_literal_expr(ty, constructor, self.fn_decl.0)
    }

    fn get_operand_ty(&mut self, operand: &Operand<'tcx>) -> Ty<'tcx> {
        operand.ty(&self.body.local_decls, self.tcx)
    }

    fn convert_operand(&mut self, operand: &Operand<'tcx>) -> Expr {
        use Operand::*;

        match operand {
            Copy(place) => self.get_place(place),
            Move(place) => self.get_place(place),
            Constant(c) => self.convert_const(&c.literal),
        }
    }

    fn implicit_cast(value: Expr, required_type: Type) -> Expr {
        if value.get_type().is_compatible(required_type) {
            value
        } else {
            value.nop_cast(required_type)
        }
    }

    fn get_discriminant_field(
        &mut self,
        enum_tree: Expr,
        enum_layout: TyAndLayout<'tcx>,
        discr_index: usize,
    ) -> Expr {
        // TODO: types here are probably wrong or inaccurate
        let field = Field::new(discr_index);
        let field_layout = enum_layout
            .field(&self.conv_ctx.type_cache.make_layout_cx(), discr_index)
            .unwrap();
        // TODO: not sure .ty is correct
        let field_ty = self.convert_type(field_layout.ty);
        Self::get_field(enum_tree, enum_layout, field.index(), field_ty)
    }

    /// Get an expression for an enum's discriminant field
    // See codegen_clif discriminant.rs:codegen_get_discriminant
    fn get_discriminant(&mut self, place: &Place<'tcx>) -> Expr {
        let place_ty = self.get_place_ty(place);
        let ty_and_layout = self.conv_ctx.layout_of_place_ty(place_ty);

        let place_tree = self.get_place(place);

        // TODO: types here are probably wrong or inaccurate
        match &ty_and_layout.variants {
            rustc_target::abi::Variants::Single { index } => Expr::new_int_constant(
                ISIZE_KIND,
                ty_and_layout
                    .ty
                    .discriminant_for_variant(self.tcx, *index)
                    .unwrap()
                    .val
                    .try_into()
                    .unwrap(),
            ),

            rustc_target::abi::Variants::Multiple {
                tag,
                tag_encoding,
                tag_field,
                variants: _,
            } => {
                let mut value = self.get_discriminant_field(place_tree, ty_and_layout, *tag_field);

                match tag_encoding {
                    // TODO: check signed value like clif does
                    TagEncoding::Direct => {}

                    TagEncoding::Niche {
                        dataful_variant,
                        niche_variants,
                        niche_start,
                    } => {
                        // Who knows what type our value field is. It might be a pointer for which
                        // we can't use regular math. Anyway, we need to cast it.
                        let discr_ty = match tag.value {
                            rustc_target::abi::Primitive::Int(int_size, signed) => {
                                self.conv_ctx.type_cache.convert_integer(int_size, signed)
                            }
                            rustc_target::abi::Primitive::Pointer => ISIZE_KIND.into(),
                            _ => todo!("Don't know how to handle tag encoding {:?}", tag),
                        };
                        value = value.nop_cast(discr_ty);

                        let niche_start = *niche_start;
                        if niche_start != 0 {
                            value = value.minus(Expr::new_int_constant(
                                value.get_type(),
                                niche_start.try_into().unwrap(),
                            ));
                        }

                        let relative_max =
                            niche_variants.end().as_u32() - niche_variants.start().as_u32();
                        let is_in_range = value.less_than_or_equal_value(Expr::new_int_constant(
                            value.get_type(),
                            relative_max.into(),
                        ));

                        value = Expr::new_cond_expr(
                            is_in_range,
                            value.plus(Expr::new_int_constant(
                                value.get_type(),
                                niche_variants.start().as_u32().into(),
                            )),
                            Expr::new_int_constant(
                                value.get_type(),
                                dataful_variant.as_u32().into(),
                            ),
                        );
                    }
                }

                value
            }
        }
    }

    /// Add statements that set an enum's discriminant field to self.stmt_list
    // See codegen_clif discriminant.rs:codegen_set_discriminant
    fn add_set_discriminant(
        &mut self,
        place: &Place<'tcx>,
        variant_index: rustc_target::abi::VariantIdx,
    ) {
        let place_ty = self.get_place_ty(place);
        let ty_and_layout = self.conv_ctx.layout_of_place_ty(place_ty);
        if ty_and_layout
            .for_variant(&self.conv_ctx.type_cache.make_layout_cx(), variant_index)
            .abi
            .is_uninhabited()
        {
            return;
        }

        let place_tree = self.get_place(place);

        match &ty_and_layout.variants {
            rustc_target::abi::Variants::Single { index } => {
                // No need to actually set it.
                assert_eq!(*index, variant_index);
            }

            rustc_target::abi::Variants::Multiple {
                tag: _,
                tag_encoding,
                tag_field,
                variants: _,
            } => {
                let field = self.get_discriminant_field(place_tree, ty_and_layout, *tag_field);

                let value = match tag_encoding {
                    TagEncoding::Direct => {
                        ty_and_layout
                            .ty
                            .discriminant_for_variant(self.tcx, variant_index)
                            .unwrap()
                            .val
                    }

                    TagEncoding::Niche {
                        dataful_variant,
                        niche_variants,
                        niche_start,
                    } => {
                        if variant_index == *dataful_variant {
                            return;
                        }

                        u128::from(
                            variant_index
                                .as_u32()
                                .wrapping_sub(niche_variants.start().as_u32().into()),
                        )
                        .wrapping_add((*niche_start).into())
                    }
                };

                let value = Expr::new_int_constant(field.get_type(), value.try_into().unwrap());

                let stmt = Expr::new_assignment(field, value);
                self.stmt_list.push(stmt);
            }
        }
    }

    fn make_slice(&mut self, converted_slice_type: Type, ptr_expr: Expr, length: u64) -> Expr {
        let constructor = Expr::new_record_constructor(
            converted_slice_type,
            &[
                converted_slice_type.get_record_type_field_decl(0),
                converted_slice_type.get_record_type_field_decl(1),
            ],
            &[
                ptr_expr,
                Expr::new_int_constant(USIZE_KIND, length.try_into().unwrap()),
            ],
        );
        Expr::new_compound_literal_expr(converted_slice_type, constructor, self.fn_decl.0)
    }

    fn make_trait_object(&mut self, trait_obj_ty: Type, obj_ptr: Expr, vtable_ptr: Expr) -> Expr {
        let void_ptr_ty = Type::void().mk_pointer_type();
        let obj_ptr = obj_ptr.convert_cast(void_ptr_ty);
        let constructor = Expr::new_record_constructor(
            trait_obj_ty,
            &[
                trait_obj_ty.get_record_type_field_decl(0),
                trait_obj_ty.get_record_type_field_decl(1),
            ],
            &[obj_ptr, vtable_ptr],
        );
        Expr::new_compound_literal_expr(trait_obj_ty, constructor, self.fn_decl.0)
    }

    fn convert_rvalue(&mut self, rv: &Rvalue<'tcx>) -> Expr {
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
                let operand1 = Self::implicit_cast(self.convert_operand(operand1), type_);
                let operand2 = Self::implicit_cast(self.convert_operand(operand2), type_);
                operand1.typed_math(code, type_, operand2)
            }

            CheckedBinaryOp(op, operand1, operand2) => {
                let type_ = self.convert_type(rv.ty(self.body, self.tcx));
                let unchecked_value =
                    self.convert_rvalue(&BinaryOp(*op, operand1.clone(), operand2.clone()));
                // TODO: perform the check
                let check_value =
                    Expr::new_int_constant(self.convert_type(self.tcx.types.bool), true.into());
                let constructor = Expr::new_record_constructor(
                    type_,
                    &[
                        type_.get_record_type_field_decl(0),
                        type_.get_record_type_field_decl(1),
                    ],
                    &[unchecked_value, check_value],
                );
                Expr::new_compound_literal_expr(type_, constructor, self.fn_decl.0)
            }

            UnaryOp(op, operand) => {
                let operand = self.convert_operand(operand);
                let type_ = self.convert_type(rv.ty(self.body, self.tcx));
                match op {
                    UnOp::Neg => operand.negate(type_),
                    UnOp::Not => operand.bit_not(type_),
                }
            }

            NullaryOp(op, ty) => match op {
                NullOp::SizeOf => self.convert_type(ty).get_size_bytes(),
                NullOp::Box => todo!("NullOp::Box, type {:?}", ty),
            },

            Discriminant(place) => {
                // The discriminant field might be any int type, but it's expected to be an isize,
                // so we need to cast it.
                self.get_discriminant(place).nop_cast(ISIZE_KIND.into())
            }

            Ref(_, _, place) | AddressOf(_, place) => {
                if let Some((ProjectionElem::Deref, except_deref)) = place.projection.split_last() {
                    // Address and deref cancel out, so make a new place without the deref
                    let projection = self.tcx.intern_place_elems(except_deref);
                    let place = Place {
                        local: place.local,
                        projection,
                    };
                    self.get_place(&place)
                } else {
                    self.get_place(place).mk_pointer()
                }
            }

            Cast(cast_kind, operand, new_ty) => {
                use CastKind::*;
                use PointerCast::*;

                match cast_kind {
                    Misc => {
                        // See codegen_clif base.rs
                        let old_ty = self.get_operand_ty(operand);

                        let is_fat_ptr = |ty: Ty<'tcx>| {
                            if let Some(pointee_ty_and_mut) = ty.builtin_deref(true) {
                                use TyKind::*;

                                match pointee_ty_and_mut.ty.kind {
                                    Slice { .. } | Str | Dynamic(..) => true,
                                    _ => false,
                                }
                            } else {
                                false
                            }
                        };

                        if is_fat_ptr(old_ty) && !is_fat_ptr(new_ty) {
                            // Get the regular part of the pointer
                            self.convert_operand(operand)
                                .get_record_field(0)
                                .nop_cast(self.convert_type(new_ty))
                        } else {
                            // TODO: enum -> discriminant cast, see clif base.rs
                            self.convert_operand(operand)
                                .convert_cast(self.convert_type(new_ty))
                        }
                    }

                    Pointer(MutToConstPointer) | Pointer(UnsafeFnPointer) => self
                        .convert_operand(operand)
                        .nop_cast(self.convert_type(new_ty)),

                    Pointer(ReifyFnPointer) => {
                        let fn_def = self.get_operand_ty(operand);
                        if let ty::FnDef(def_id, substs) = fn_def.kind {
                            let instance = self.conv_ctx.resolve_fn(def_id, substs);
                            self.conv_ctx.convert_instance_to_fn_ptr(instance)
                        } else {
                            unreachable!()
                        }
                    }

                    Pointer(Unsize) => {
                        let old_ty = self.get_operand_ty(operand);

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
                                let ptr = self.convert_operand(operand).mk_pointer();
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
                        let constructor = Expr::new_array_constructor(
                            array_type,
                            &operands
                                .into_iter()
                                .map(|operand| self.convert_operand(operand))
                                .collect::<Vec<_>>(),
                        );
                        Expr::new_compound_literal_expr(array_type, constructor, self.fn_decl.0)
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

                let place_ty = self.get_place_ty(place);
                if Self::is_place_ty_slice(place_ty) {
                    place_expr.get_record_field(1)
                } else {
                    todo!("Len of non-slice {:?} of type {:?}", place, place_ty);
                }
            }

            _ => unimplemented!("rvalue {:?}", rv),
        }
    }

    fn convert_goto(&self, target: BasicBlock) -> Expr {
        let target = self.block_labels[target.as_usize()];
        Expr::new_goto(target)
    }

    fn convert_panic(&self) -> Expr {
        // TODO: should be a trap
        self.convert_unreachable()
    }

    fn convert_unreachable(&self) -> Expr {
        Expr::new_call_expr(
            UNKNOWN_LOCATION,
            Type::void(),
            Expr::from(BuiltinFunction::Unreachable).mk_pointer(),
            &[],
        )
    }

    fn convert_rust_intrinsic(
        &mut self,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
        original_args: &[Operand<'tcx>],
        converted_args: &[Expr],
        call_expr_type: Type,
    ) -> Expr {
        let name = self.tcx.item_name(def_id);

        match &*name.as_str() {
            "wrapping_add" => {
                converted_args[0].typed_math(TreeCode::PlusExpr, call_expr_type, converted_args[1])
            }

            "wrapping_sub" => {
                converted_args[0].typed_math(TreeCode::MinusExpr, call_expr_type, converted_args[1])
            }

            // Convert pointer to isize, do the math, then convert back.
            // TODO: The whole point of this intrinsic is not to do the conversion, is it really
            // necessary?
            "arith_offset" => converted_args[0]
                .nop_cast(ISIZE_KIND.into())
                .plus(converted_args[1])
                .nop_cast(call_expr_type),

            "copy_nonoverlapping" => {
                let copied_type = substs.type_at(0);
                let element_size = self.convert_type(copied_type).get_size_bytes();
                // TODO: nop_expr before multiplying?
                let all_size = element_size.typed_math(
                    TreeCode::MultExpr,
                    USIZE_KIND.into(),
                    converted_args[2],
                );

                Expr::new_call_expr(
                    UNKNOWN_LOCATION,
                    Type::void(),
                    Expr::from(BuiltinFunction::Memcpy).mk_pointer(),
                    // src and dst are swapped here
                    &[converted_args[1], converted_args[0], all_size],
                )
            }

            "offset" => {
                let ptr = converted_args[0];
                // gcc wants a usize instead of an isize
                let offset = converted_args[1].convert_cast(USIZE_KIND.into());
                ptr.pointer_plus(offset)
            }

            "size_of" => {
                let of_type = substs.type_at(0);
                self.convert_type(of_type).get_size_bytes()
            }

            "unreachable" => self.convert_unreachable(),

            "panic_if_uninhabited" => {
                let ty = substs.type_at(0);
                let ty_and_layout = self.conv_ctx.layout_of(ty);
                if ty_and_layout.abi.is_uninhabited() {
                    self.convert_panic()
                } else {
                    Expr::void()
                }
            }

            "assume" => {
                eprintln!("Warning: Ignoring 'assume' intrinsic {:?}", original_args);
                Expr::void()
            }

            "transmute" => converted_args[0].view_convert_cast(call_expr_type),

            _ => todo!("rust intrinsic {:?}", name),
        }
    }

    fn convert_call_expr(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Operand<'tcx>],
        call_expr_type: Type,
    ) -> Expr {
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
                    let obj_ptr = trait_object.get_record_field(0);
                    let vtable_ptr = trait_object.get_record_field(1);

                    // The first argument should actually be the object pointer.
                    converted_args[0] = obj_ptr;

                    // Now find the function pointer in the vtable.

                    let fn_ptr_ptr_ty = self.tcx.mk_imm_ptr(self.tcx.mk_fn_ptr(fn_sig));
                    let fn_ptr_ptr_ty = self.convert_type(fn_ptr_ptr_ty);
                    let vtable_ptr = vtable_ptr.convert_cast(fn_ptr_ptr_ty);

                    // Increase index by 3 to skip drop-in-place and 2 size fields.
                    // This assumes that the size fields are the same size as function pointers,
                    // so we can treat them as elements in a function pointer array.
                    let index = Expr::new_int_constant(USIZE_KIND, (index + 3).try_into().unwrap());
                    let fn_ptr_ptr = Self::pointer_plus_element_index(vtable_ptr, index);
                    fn_ptr_ptr.deref_value()
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
            let spread_arg = args.last().unwrap();
            let spread_arg_ty = spread_arg.ty(&self.body.local_decls, self.tcx);

            let ty_and_layout = self.conv_ctx.layout_of(spread_arg_ty);
            let converted_spread_arg = converted_args.pop().unwrap();
            converted_args.extend(
                spread_arg_ty
                    .tuple_fields()
                    .enumerate()
                    .map(|(i, field_ty)| {
                        let field_ty = self.convert_type(field_ty);
                        Self::get_field(converted_spread_arg, ty_and_layout, i, field_ty)
                    }),
            );
        }

        // Force the ABI we're using
        let func_ty_by_abi = Type::new_function_type(
            call_expr_type,
            &converted_args
                .iter()
                .map(|arg| arg.get_type())
                .collect::<Vec<_>>(),
        );
        let func_ty_by_abi = func_ty_by_abi.mk_pointer_type();
        let func = func.nop_cast(func_ty_by_abi);

        Expr::new_call_expr(UNKNOWN_LOCATION, call_expr_type, func, &converted_args)
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
            let place_ty = self.get_place_ty(place);
            if place_ty.variant_index.is_some() {
                unreachable!("call's return type is an enum variant");
            }

            let call_expr_type = self.conv_ctx.type_cache.convert_fn_return_type(place_ty.ty);
            let returns_void = place_ty.ty.is_unit();
            (call_expr_type, returns_void)
        } else {
            (Type::void(), true)
        };

        let call_expr = self.convert_call_expr(func, args, call_expr_type);

        if let Some((place, destination)) = destination {
            if returns_void {
                self.stmt_list.push(call_expr);
            } else {
                let init_expr = Expr::new_assignment(self.get_place(place), call_expr);
                self.stmt_list.push(init_expr);
            }

            self.stmt_list.push(self.convert_goto(*destination));
        } else {
            self.stmt_list.push(call_expr);
            self.stmt_list.push(self.convert_unreachable());
        }
    }

    fn convert_basic_block(&mut self, block_index: BasicBlock, block: &BasicBlockData<'tcx>) {
        eprintln!("bb{}:", block_index.as_usize());
        for stmt in &block.statements {
            eprintln!("  {:?}", stmt);
        }
        if let Some(term) = &block.terminator {
            eprintln!("  => {:?}", term.kind);
        } else {
            eprintln!("  => (No terminator)");
        }

        self.stmt_list.push(Expr::new_label_expr(
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
                        self.stmt_list.push(Expr::new_assignment(
                            place,
                            Self::implicit_cast(rvalue, place.get_type()),
                        ));
                    } else {
                        self.stmt_list.push(place);
                        self.stmt_list.push(rvalue);
                    }
                }

                SetDiscriminant {
                    place,
                    variant_index,
                } => {
                    self.add_set_discriminant(place, *variant_index);
                }

                _ => unimplemented!("{:?}", stmt),
            }
        }

        let terminator = block.terminator();
        match &terminator.kind {
            Drop { target, .. } => {
                eprintln!("TODO: ignoring {:?}", terminator.kind);
                // Ignoring the Drop for now, but do do the goto.
                self.stmt_list.push(self.convert_goto(*target));
            }

            Resume | Abort => {
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

                    let cond = self
                        .convert_operand(discr)
                        .equal_value(Expr::new_int_constant(
                            switch_ty_tree,
                            value.try_into().unwrap(),
                        ));

                    let if_eq_expr = self.convert_goto(targets[0]);
                    let else_expr = self.convert_goto(targets[1]);
                    self.stmt_list
                        .push(Expr::new_cond_expr(cond, if_eq_expr, else_expr));
                } else {
                    let mut cases_list = StatementList::new();

                    for (value, target) in values.into_iter().zip(targets) {
                        let case_expr = Expr::new_case_label_expr(
                            Some(Expr::new_int_constant(
                                switch_ty_tree,
                                (*value).try_into().unwrap(),
                            )),
                            Expr::new_label_decl(UNKNOWN_LOCATION, self.fn_decl.0),
                        );

                        cases_list.push(case_expr);
                        cases_list.push(self.convert_goto(*target));
                    }

                    // default case
                    cases_list.push(Expr::new_case_label_expr(
                        None,
                        Expr::new_label_decl(UNKNOWN_LOCATION, self.fn_decl.0),
                    ));
                    cases_list.push(self.convert_goto(*targets.last().unwrap()));

                    let discr = self.convert_operand(discr);
                    self.stmt_list
                        .push(Expr::new_switch_expr(switch_ty_tree, discr, cases_list.0));
                }
            }

            Return => {
                let return_value = if self.return_type_is_void {
                    None
                } else {
                    Some(Expr::new_assignment(
                        self.res_decl,
                        self.tmp_var_decl_for_res,
                    ))
                };

                self.stmt_list.push(Expr::new_return_expr(return_value));
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
                fn_span: _,
            } => {
                self.handle_call_terminator(func, args, destination);
            }

            DropAndReplace { .. }
            | FalseEdge { .. }
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

            InlineAsm { .. } => todo!("inline assembly not supported"),
        }
    }

    fn finalize(mut self) {
        let bind_expr =
            Expr::new_bind_expr(self.vars.head(), self.stmt_list.0, self.main_gcc_block);
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
