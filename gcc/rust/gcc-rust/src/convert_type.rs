use crate::gcc_api::*;
use rustc::{
    mir::{interpret::ConstValue, Body, Local},
    ty::{
        self, layout, subst::SubstsRef, AdtDef, AdtKind, ConstKind, ParamEnv, PolyFnSig, Ty,
        TyCtxt, TyKind, VariantDef,
    },
};
use rustc_hir::def_id::DefId;

use std::collections::HashMap;

pub struct ConvertedFnSig {
    pub return_type: Tree,
    pub arg_types: Vec<Tree>,
}

impl ConvertedFnSig {
    pub fn into_function_type(self) -> Tree {
        Tree::new_function_type(self.return_type, &self.arg_types)
    }
}

/// Cache the types so if we convert the same anonymous type twice, we get the exact same
/// Tree object. Otherwise, we get errors about anonymous structs not being the same, even
/// though they have the same fields.
pub struct TypeCache<'tcx> {
    tcx: TyCtxt<'tcx>,
    hashmap: HashMap<Ty<'tcx>, Tree>,
}

impl<'tcx> TypeCache<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            hashmap: HashMap::new(),
        }
    }

    fn make_zst() -> Tree {
        // Use a zero-length array of whatever.
        Tree::new_array_type(IntegerTypeKind::Int.into(), 0)
    }

    fn convert_variant_fields(
        &mut self,
        variant: &VariantDef,
        substs: SubstsRef<'tcx>,
    ) -> DeclList {
        // TODO: field names
        DeclList::new(
            TreeCode::FieldDecl,
            &variant
                .fields
                .iter()
                .map(|field| {
                    // TODO: should be using the struct's layout here
                    let ty = field.ty(self.tcx, substs);
                    self.convert_type(ty)
                })
                .collect::<Vec<_>>(),
        )
    }

    fn convert_closure_upvars_struct(
        &mut self,
        closure_ty: Ty<'tcx>,
        def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Tree {
        let mut record_ty = Tree::new_record_type(TreeCode::RecordType);
        self.hashmap.insert(closure_ty, record_ty);

        let upvar_tys = substs
            .as_closure()
            .upvar_tys(def_id, self.tcx)
            .map(|ty| self.convert_type(ty))
            .collect::<Vec<_>>();

        record_ty.finish_record_type(DeclList::new(TreeCode::FieldDecl, &upvar_tys));
        record_ty
    }

    fn convert_slice(element_type: Tree) -> Tree {
        // Represent a slice reference as a record containing (*T, size)
        let t_ptr_ty = Tree::new_pointer_type(element_type);
        // usize ?
        let size_ty = Tree::new_unsigned_int_type(64);

        let mut record_ty = Tree::new_record_type(TreeCode::RecordType);
        record_ty.finish_record_type(DeclList::new(TreeCode::FieldDecl, &[t_ptr_ty, size_ty]));
        record_ty
    }

    fn convert_trait_object(&mut self) -> Tree {
        // Represent a trait object as a record containing (*object, *vtable)
        // where vtable is *void
        let mut record_ty = Tree::new_record_type(TreeCode::RecordType);
        let void_ptr_ty = Tree::new_pointer_type(TreeIndex::VoidType.into());
        let void_ptr_ptr_ty = Tree::new_pointer_type(void_ptr_ty);
        record_ty.finish_record_type(DeclList::new(
            TreeCode::FieldDecl,
            &[void_ptr_ty, void_ptr_ptr_ty],
        ));
        record_ty
    }

    fn convert_integer(&mut self, int: &layout::Integer, is_signed: bool) -> Tree {
        use layout::Integer::*;
        if is_signed {
            match int {
                I8 => Tree::new_signed_int_type(8),
                I16 => Tree::new_signed_int_type(16),
                I32 => Tree::new_signed_int_type(32),
                I64 => Tree::new_signed_int_type(64),
                I128 => Tree::new_signed_int_type(128),
            }
        } else {
            match int {
                I8 => Tree::new_unsigned_int_type(8),
                I16 => TreeIndex::Uint16Type.into(),
                I32 => TreeIndex::Uint32Type.into(),
                I64 => TreeIndex::Uint64Type.into(),
                I128 => Tree::new_unsigned_int_type(128),
            }
        }
    }

    // TODO: Add offset in parameter
    fn convert_scalar(&mut self, scalar: &layout::Scalar) -> Tree {
        match scalar.value {
            layout::Int(i, is_signed) => self.convert_integer(&i, is_signed),
            layout::Pointer => {
                // todo: better pointer type
                Tree::new_pointer_type(Tree::new_unsigned_int_type(8))
            }
            _ => panic!("convert_scalar: {:?}", scalar),
        }
    }

    fn convert_adt(&mut self, ty: Ty<'tcx>, adt_def: &AdtDef, substs: SubstsRef<'tcx>) -> Tree {
        let layout = self.tcx.layout_of(ParamEnv::reveal_all().and(ty)).unwrap();

        match &layout.abi {
            layout::Abi::Scalar(s) => {
                return self.convert_scalar(&s);
            }
            _ => {}
        }

        // Cache type before creating fields to avoid infinite recursion for
        // self-referential types.
        let code = match adt_def.adt_kind() {
            AdtKind::Struct | AdtKind::Enum => TreeCode::RecordType,
            AdtKind::Union => TreeCode::UnionType,
        };

        let mut tt = Tree::new_record_type(code);
        self.hashmap.insert(ty, tt);

        // Now add the fields...
        match adt_def.adt_kind() {
            AdtKind::Struct | AdtKind::Union => {
                let variant = adt_def.non_enum_variant();
                tt.finish_record_type(self.convert_variant_fields(variant, substs));
            }

            AdtKind::Enum => {
                // Pretend it looks like
                // struct {
                //     long discriminant;
                //     union {
                //         variant1;
                //         variant2;
                //         ...
                //     }
                // }
                //
                // (It seems rustc expects the discriminant to be an isize, which is
                // currently converted into a long.)

                let discr_ty = Tree::new_signed_int_type(64);

                let variants = adt_def
                    .variants
                    .iter()
                    .map(|variant| {
                        // afaik variants cannot currently be treated as a separate type,
                        // so they can't be self-referential and we don't need to cache
                        // them.
                        let mut variant_ty = Tree::new_record_type(TreeCode::RecordType);
                        variant_ty.finish_record_type(self.convert_variant_fields(variant, substs));
                        variant_ty
                    })
                    .collect::<Vec<_>>();
                let mut variant_union_ty = Tree::new_record_type(TreeCode::UnionType);
                variant_union_ty.finish_record_type(DeclList::new(TreeCode::FieldDecl, &variants));

                tt.finish_record_type(DeclList::new(
                    TreeCode::FieldDecl,
                    &[discr_ty, variant_union_ty],
                ));
            }
        }

        tt
    }

    fn do_convert_type(&mut self, ty: Ty<'tcx>) -> Tree {
        if ty.kind == TyKind::Bool {
            return TreeIndex::BooleanType.into();
        }

        let layout = self.tcx.layout_of(ParamEnv::reveal_all().and(ty)).unwrap();

		if layout.is_zst() {
			return Self::make_zst();
		}

        // todo: use a different cache for scalar value
        // see https://github.com/rust-lang/rust/blob/bc1571cc3cfef07251f7df52b95525aa16797ca2/src/librustc_codegen_llvm/type_of.rs#L237
        match layout.abi {
            layout::Abi::Scalar(ref scalar) => {
                return match ty.kind {
                    ty::RawPtr(ty::TypeAndMut { ty, mutbl: _ }) | ty::Ref(_, ty, _) => {
                        Tree::new_pointer_type(self.convert_type(ty))
                    }

                    ty::Adt(def, _) if def.is_box() => todo!("Box"),
                    ty::FnPtr(sig) => {
                        Tree::new_pointer_type(self.convert_fn_sig(sig).into_function_type())
                    }
                    _ => self.convert_scalar(scalar),
                };
            }
            layout::Abi::ScalarPair(ref s1, ref s2) => {
                let fields = DeclList::new(
                    TreeCode::FieldDecl,
                    &[self.convert_scalar(s1), self.convert_scalar(s2)],
                );

                let mut ty = Tree::new_record_type(TreeCode::RecordType);
                ty.finish_record_type(fields);
                return ty;
            }
            layout::Abi::Vector { ref element, count } => {
                return Tree::new_array_type(self.convert_scalar(element), count);
            }
            _ => {}
        }

        match &layout.fields {
            layout::FieldPlacement::Union(field_count) => todo!(),
            layout::FieldPlacement::Array { stride, count } => todo!(),
            layout::FieldPlacement::Arbitrary {
                offsets,
                memory_index,
            } => {
				println!("offsets: {:?}, index: {:?}", offsets, memory_index);
				todo!()
			},
        }
    }

    pub fn convert_type(&mut self, ty: Ty<'tcx>) -> Tree {
        if let Some(tree) = self.hashmap.get(ty) {
            return *tree;
        }

        // TODO: return a placeholder when called recursively!
        // do_convert_type can recursively call convert_type
        let mut tree = self.do_convert_type(ty);
        tree.set_type_name(Tree::new_identifier(format!("{}", ty)));
        *self.hashmap.entry(ty).or_insert(tree)
    }

    pub fn convert_fn_return_type(&mut self, ty: Ty<'tcx>) -> Tree {
        if ty.is_unit() {
            TreeIndex::VoidType.into()
        } else {
            self.convert_type(ty)
        }
    }

    pub fn convert_fn_sig(&mut self, fn_sig: PolyFnSig<'tcx>) -> ConvertedFnSig {
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

    pub fn convert_local_decl_types<I>(&mut self, body: &Body<'tcx>, iter: I) -> Vec<Tree>
    where
        I: Iterator<Item = Local>,
    {
        iter.map(|local| self.convert_type(body.local_decls[local].ty))
            .collect()
    }

    pub fn convert_fn_arg_types(&mut self, body: &Body<'tcx>) -> Vec<Tree> {
        self.convert_local_decl_types(body, body.args_iter())
    }
}
