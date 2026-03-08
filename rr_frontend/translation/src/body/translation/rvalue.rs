// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::{info, trace};
use radium::{code, coq, lang};
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{abi, index};

use super::TX;
use crate::base::*;
use crate::body::translation::ExprWithInfo;
use crate::regions;

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Translate an aggregate expression.
    fn translate_aggregate(
        &mut self,
        kind: &mir::AggregateKind<'tcx>,
        op: &index::IndexVec<abi::FieldIdx, mir::Operand<'tcx>>,
    ) -> Result<code::Expr, TranslationError<'tcx>> {
        // translate operands
        let mut translated_ops: Vec<code::Expr> = Vec::new();
        let mut operand_types: Vec<ty::Ty<'tcx>> = Vec::new();

        for o in op {
            let (translated_o, _) = self.translate_operand(o, true)?;
            let type_of_o = self.get_type_of_operand(o);
            translated_ops.push(translated_o);
            operand_types.push(type_of_o);
        }

        match *kind {
            mir::AggregateKind::Tuple => {
                if operand_types.is_empty() {
                    // translate to unit literal
                    return Ok(code::Expr::Literal(code::Literal::ZST));
                }

                let struct_use = self.ty_translator.generate_tuple_use(operand_types.iter().copied())?;
                let sl = struct_use.generate_raw_syn_type_term();
                let initializers: Vec<_> =
                    translated_ops.into_iter().enumerate().map(|(i, o)| (i.to_string(), o)).collect();

                Ok(code::Expr::StructInitE {
                    sls: coq::term::App::new_lhs(sl.to_string()),
                    components: initializers,
                })
            },

            mir::AggregateKind::Adt(did, variant, args, ..) => {
                // get the adt def
                let adt_def: ty::AdtDef<'tcx> = self.tcx.adt_def(did);

                if adt_def.is_struct() {
                    let variant = adt_def.variant(variant);
                    let struct_use = self.ty_translator.generate_struct_use(variant.def_id, args)?;

                    let Some(struct_use) = struct_use else {
                        // if not, it's replaced by unit
                        return Ok(code::Expr::Literal(code::Literal::ZST));
                    };

                    let sl = struct_use.generate_raw_syn_type_term();
                    let initializers: Vec<_> = translated_ops
                        .into_iter()
                        .zip(variant.fields.iter())
                        .map(|(o, field)| (field.name.to_string(), o))
                        .collect();

                    return Ok(code::Expr::StructInitE {
                        sls: coq::term::App::new_lhs(sl.to_string()),
                        components: initializers,
                    });
                }

                if adt_def.is_enum() {
                    let variant_def = adt_def.variant(variant);

                    let struct_use =
                        self.ty_translator.generate_enum_variant_use(variant_def.def_id, args)?;
                    let sl = struct_use.generate_raw_syn_type_term();

                    let initializers: Vec<_> = translated_ops
                        .into_iter()
                        .zip(variant_def.fields.iter())
                        .map(|(o, field)| (field.name.to_string(), o))
                        .collect();

                    let variant_e = code::Expr::StructInitE {
                        sls: coq::term::App::new_lhs(sl.to_string()),
                        components: initializers,
                    };

                    let enum_use = self.ty_translator.generate_enum_use(adt_def, args)?;
                    let els = enum_use.generate_raw_syn_type_term();

                    info!("generating enum annotation for type {:?}", enum_use);
                    let ty: code::RustEnumDef = enum_use.clone().try_into().unwrap();
                    let variant_name = variant_def.name.to_string();

                    return Ok(code::Expr::EnumInitE {
                        els: coq::term::App::new_lhs(els.to_string()),
                        variant: variant_name,
                        ty,
                        initializer: Box::new(variant_e),
                    });
                }

                // TODO
                Err(TranslationError::UnsupportedFeature {
                    description: format!(
                        "RefinedRust does currently not support aggregate rvalue for other ADTs (got: {kind:?}, {op:?})"
                    ),
                })
            },
            mir::AggregateKind::Closure(def, _args) => {
                trace!("Translating Closure aggregate value for {:?}", def);

                // We basically translate this to a tuple
                if operand_types.is_empty() {
                    // translate to unit literal
                    return Ok(code::Expr::Literal(code::Literal::ZST));
                }

                let struct_use = self.ty_translator.generate_tuple_use(operand_types.iter().copied())?;
                let sl = struct_use.generate_raw_syn_type_term();

                let initializers: Vec<_> =
                    translated_ops.into_iter().enumerate().map(|(i, o)| (i.to_string(), o)).collect();

                Ok(code::Expr::StructInitE {
                    sls: coq::term::App::new_lhs(sl.to_string()),
                    components: initializers,
                })
            },

            _ => {
                // TODO
                Err(TranslationError::UnsupportedFeature {
                    description: format!(
                        "RefinedRust does currently not support this kind of aggregate rvalue (got: {kind:?}, {op:?})"
                    ),
                })
            },
        }
    }

    fn translate_cast(
        &mut self,
        kind: mir::CastKind,
        op: &mir::Operand<'tcx>,
        to_ty: ty::Ty<'tcx>,
    ) -> Result<code::Expr, TranslationError<'tcx>> {
        let op_ty = self.get_type_of_operand(op);
        let op_st = self.ty_translator.translate_type_to_syn_type(op_ty)?;
        let op_ot = op_st.into();

        let (translated_op, _) = self.translate_operand(op, true)?;

        let target_st = self.ty_translator.translate_type_to_syn_type(to_ty)?;
        let target_ot = target_st.into();

        match kind {
            mir::CastKind::PointerCoercion(x, _) => match x {
                ty::adjustment::PointerCoercion::MutToConstPointer => Ok(code::Expr::UnOp {
                    o: code::Unop::Cast(lang::OpType::Ptr),
                    ot: lang::OpType::Ptr,
                    e: Box::new(translated_op),
                }),

                ty::adjustment::PointerCoercion::ArrayToPointer
                | ty::adjustment::PointerCoercion::ClosureFnPointer(_)
                | ty::adjustment::PointerCoercion::ReifyFnPointer(_)
                | ty::adjustment::PointerCoercion::UnsafeFnPointer
                | ty::adjustment::PointerCoercion::Unsize => Err(TranslationError::UnsupportedFeature {
                    description: format!(
                        "RefinedRust does currently not support this kind of pointer coercion (got: {kind:?})"
                    ),
                }),
            },

            mir::CastKind::IntToInt => {
                // Cast integer to integer
                Ok(code::Expr::UnOp {
                    o: code::Unop::Cast(target_ot),
                    ot: op_ot,
                    e: Box::new(translated_op),
                })
            },

            mir::CastKind::IntToFloat => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support int-to-float cast".to_owned(),
            }),

            mir::CastKind::FloatToInt => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support float-to-int cast".to_owned(),
            }),

            mir::CastKind::FloatToFloat => Err(TranslationError::UnsupportedFeature {
                description: "RefinedRust does currently not support float-to-float cast".to_owned(),
            }),

            mir::CastKind::PtrToPtr => {
                match (op_ty.kind(), to_ty.kind()) {
                    (ty::TyKind::RawPtr(..), ty::TyKind::RawPtr(..)) => Ok(code::Expr::UnOp {
                        o: code::Unop::Cast(lang::OpType::Ptr),
                        ot: lang::OpType::Ptr,
                        e: Box::new(translated_op),
                    }),

                    _ => {
                        // TODO: any other cases we should handle?
                        Err(TranslationError::UnsupportedFeature {
                            description: format!(
                                "RefinedRust does currently not support ptr-to-ptr cast (got: {kind:?}, {op:?}, {to_ty:?})"
                            ),
                        })
                    },
                }
            },

            mir::CastKind::FnPtrToPtr => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support fnptr-to-ptr cast (got: {kind:?}, {op:?}, {to_ty:?})"
                ),
            }),

            mir::CastKind::Transmute => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support transmute cast (got: {kind:?}, {op:?}, {to_ty:?})"
                ),
            }),

            mir::CastKind::Subtype => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support subtype casts (got: {kind:?}, {op:?}, {to_ty:?})"
                ),
            }),

            mir::CastKind::PointerExposeProvenance => {
                // Cast pointer to integer
                Ok(code::Expr::UnOp {
                    o: code::Unop::Cast(target_ot),
                    ot: lang::OpType::Ptr,
                    e: Box::new(translated_op),
                })
            },

            mir::CastKind::PointerWithExposedProvenance => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of cast (got: {kind:?}, {op:?}, {to_ty:?})"
                ),
            }),
        }
    }

    /// Translate an operand.
    /// This will either generate an lvalue (in case of Move or Copy) or an rvalue (in most cases
    /// of Constant). How this is used depends on the context. (e.g., Use of an integer constant
    /// does not typecheck, and produces a stuck program).
    pub(crate) fn translate_operand(
        &mut self,
        op: &mir::Operand<'tcx>,
        to_rvalue: bool,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError<'tcx>> {
        match op {
            // In Caesium: typed_place needs deref (not use) for place accesses.
            // use is used top-level to convert an lvalue to an rvalue, which is why we use it here.
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                // check if this goes to a temporary of a checked op
                let place_kind = *place;

                let is_copy = matches!(op, mir::Operand::Copy(_));

                let translated_place = self.translate_place(&place_kind)?;
                let ty = self.get_type_of_place(place);

                let st = self.ty_translator.translate_type_to_syn_type(ty.ty)?;

                if to_rvalue && is_copy {
                    Ok((
                        code::Expr::Copy {
                            ot: st.into(),
                            order: lang::Order::Na,
                            e: Box::new(translated_place),
                        },
                        None,
                    ))
                } else if to_rvalue {
                    Ok((
                        code::Expr::Move {
                            ot: st.into(),
                            order: lang::Order::Na,
                            e: Box::new(translated_place),
                        },
                        None,
                    ))
                } else {
                    // Usually only happens when we translate call destinations
                    Ok((translated_place, None))
                }
            },
            mir::Operand::Constant(constant) => {
                // TODO: possibly need different handling of the rvalue flag
                // when this also handles string literals etc.
                self.translate_constant(&constant.const_)
            },
            mir::Operand::RuntimeChecks(_) => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of operand (got: {op:?})"
                ),
            }),
        }
    }

    /// Translates an Rvalue.
    pub(crate) fn translate_rvalue(
        &mut self,
        loc: mir::Location,
        rval: &mir::Rvalue<'tcx>,
    ) -> Result<ExprWithInfo<'tcx, 'def>, TranslationError<'tcx>> {
        match rval {
            mir::Rvalue::Use(op) => {
                // converts an lvalue to an rvalue
                self.translate_operand(op, true)
            },

            mir::Rvalue::Ref(region, bk, pl) => {
                let translated_pl = self.translate_place(pl)?;
                let translated_bk = TX::translate_borrow_kind(*bk)?;
                let ty_annot = self.get_type_annotation_for_borrow(*bk, pl)?;

                if let Some(loan) = self.info.get_optional_loan_at_location(loc) {
                    let atomic_region = self.info.atomic_region_of_loan(loan);
                    let lft = self.ty_translator.format_atomic_region(atomic_region);
                    Ok((
                        code::Expr::Borrow {
                            lft,
                            bk: translated_bk,
                            ty: ty_annot,
                            e: Box::new(translated_pl),
                        },
                        None,
                    ))
                } else {
                    info!("Didn't find loan at {:?}: {:?}; region {:?}", loc, rval, region);
                    let region = regions::region_to_region_vid(*region);
                    let lft = self.format_region(region);

                    Ok((
                        code::Expr::Borrow {
                            lft,
                            bk: translated_bk,
                            ty: ty_annot,
                            e: Box::new(translated_pl),
                        },
                        None,
                    ))
                }
            },

            mir::Rvalue::RawPtr(mt, pl) => {
                let translated_pl = self.translate_place(pl)?;
                let translated_mt = TX::translate_raw_ptr_kind(*mt);

                Ok((
                    code::Expr::AddressOf {
                        mt: translated_mt,
                        e: Box::new(translated_pl),
                    },
                    None,
                ))
            },

            mir::Rvalue::BinaryOp(op, operands) => {
                let e = self.translate_binop(*op, &operands.as_ref().0, &operands.as_ref().1)?;
                Ok((e, None))
            },

            mir::Rvalue::UnaryOp(op, operand) => {
                let (translated_e1, _) = self.translate_operand(operand, true)?;
                let e1_ty = self.get_type_of_operand(operand);
                let e1_st = self.ty_translator.translate_type_to_syn_type(e1_ty)?;
                let translated_op = TX::translate_unop(*op, e1_ty)?;

                Ok((
                    code::Expr::UnOp {
                        o: translated_op,
                        ot: e1_st.into(),
                        e: Box::new(translated_e1),
                    },
                    None,
                ))
            },

            mir::Rvalue::Discriminant(pl) => {
                let ty = self.get_type_of_place(pl);
                let translated_pl = self.translate_place(pl)?;
                info!("getting discriminant of {:?} at type {:?}", pl, ty);

                let ty::TyKind::Adt(adt_def, args) = ty.ty.kind() else {
                    return Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "RefinedRust does currently not support discriminant accesses on non-enum types ({:?}, got {:?})",
                            rval, ty.ty
                        ),
                    });
                };

                let enum_use = self.ty_translator.generate_enum_use(*adt_def, args)?;
                let els = enum_use.generate_raw_syn_type_term();

                let discriminant_acc = code::Expr::EnumDiscriminant {
                    els: els.to_string(),
                    e: Box::new(translated_pl),
                };

                Ok((discriminant_acc, None))
            },

            mir::Rvalue::Aggregate(kind, op) => {
                let e = self.translate_aggregate(kind.as_ref(), op)?;
                Ok((e, None))
            },

            mir::Rvalue::Cast(kind, op, to_ty) => {
                let e = self.translate_cast(*kind, op, *to_ty)?;
                Ok((e, None))
            },

            mir::Rvalue::CopyForDeref(_)
            | mir::Rvalue::Repeat(..)
            | mir::Rvalue::WrapUnsafeBinder(..)
            | mir::Rvalue::ThreadLocalRef(..) => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of rvalue (got: {:?})",
                    rval
                ),
            }),
        }
    }

    /// Get the type to annotate a borrow with.
    fn get_type_annotation_for_borrow(
        &self,
        _bk: mir::BorrowKind,
        pl: &mir::Place<'tcx>,
    ) -> Result<Option<code::RustType>, TranslationError<'tcx>> {
        //let mir::BorrowKind::Mut { .. } = bk else {
        //return Ok(None);
        //};

        let ty = self.get_type_of_place(pl);

        // For borrows, we can safely ignore the downcast type -- we cannot borrow a particularly variant
        let translated_ty = self.ty_translator.translate_type(ty.ty)?;
        let annot_ty = code::RustType::of_type(&translated_ty);

        Ok(Some(annot_ty))
    }

    /// Translate binary operators.
    /// We need access to the operands, too, to handle the offset operator and get the right
    /// Caesium layout annotation.
    fn translate_binop(
        &mut self,
        op: mir::BinOp,
        e1: &mir::Operand<'tcx>,
        e2: &mir::Operand<'tcx>,
    ) -> Result<code::Expr, TranslationError<'tcx>> {
        let e1_ty = self.get_type_of_operand(e1);
        let e2_ty = self.get_type_of_operand(e2);
        let e1_st = self.ty_translator.translate_type_to_syn_type(e1_ty)?;
        let e2_st = self.ty_translator.translate_type_to_syn_type(e2_ty)?;

        let (translated_e1, _) = self.translate_operand(e1, true)?;
        let (translated_e2, _) = self.translate_operand(e2, true)?;

        let mk_binop = |op| code::Expr::BinOp {
            o: op,
            ot1: e1_st.clone().into(),
            ot2: e2_st.clone().into(),
            e1: Box::new(translated_e1.clone()),
            e2: Box::new(translated_e2.clone()),
        };

        let mk_checked_binop = |op: code::Binop| {
            // result has the same syntype
            let result_st = e1_st.clone();

            // the actual value
            let op_term = code::Expr::BinOp {
                o: op.clone(),
                ot1: e1_st.clone().into(),
                ot2: e2_st.clone().into(),
                e1: Box::new(translated_e1.clone()),
                e2: Box::new(translated_e2.clone()),
            };
            let overflow_check = code::Expr::CheckBinOp {
                o: op,
                ot1: e1_st.clone().into(),
                ot2: e2_st.clone().into(),
                e1: Box::new(translated_e1.clone()),
                e2: Box::new(translated_e2.clone()),
            };

            let sls = coq::term::App::new_lhs(format!("(tuple2_sls ({result_st}) BoolSynType)"));

            code::Expr::StructInitE {
                sls,
                components: vec![("0".to_owned(), op_term), ("1".to_owned(), overflow_check)],
            }
        };

        match op {
            mir::BinOp::Add => Ok(mk_binop(code::Binop::Add)),
            mir::BinOp::Sub => Ok(mk_binop(code::Binop::Sub)),
            mir::BinOp::Mul => Ok(mk_binop(code::Binop::Mul)),
            mir::BinOp::Div => Ok(mk_binop(code::Binop::Div)),
            mir::BinOp::Rem => Ok(mk_binop(code::Binop::Mod)),

            mir::BinOp::BitXor => Ok(mk_binop(code::Binop::BitXor)),
            mir::BinOp::BitAnd => Ok(mk_binop(code::Binop::BitAnd)),
            mir::BinOp::BitOr => Ok(mk_binop(code::Binop::BitOr)),
            mir::BinOp::Shl => Ok(mk_binop(code::Binop::Shl)),
            mir::BinOp::Shr => Ok(mk_binop(code::Binop::Shr)),

            mir::BinOp::AddUnchecked => Ok(mk_binop(code::Binop::AddUnchecked)),
            mir::BinOp::SubUnchecked => Ok(mk_binop(code::Binop::SubUnchecked)),
            mir::BinOp::MulUnchecked => Ok(mk_binop(code::Binop::MulUnchecked)),
            mir::BinOp::ShlUnchecked => Ok(mk_binop(code::Binop::ShlUnchecked)),
            mir::BinOp::ShrUnchecked => Ok(mk_binop(code::Binop::ShrUnchecked)),

            mir::BinOp::AddWithOverflow => Ok(mk_checked_binop(code::Binop::Add)),
            mir::BinOp::MulWithOverflow => Ok(mk_checked_binop(code::Binop::Mul)),
            mir::BinOp::SubWithOverflow => Ok(mk_checked_binop(code::Binop::Sub)),

            mir::BinOp::Eq => Ok(mk_binop(code::Binop::Eq)),
            mir::BinOp::Lt => Ok(mk_binop(code::Binop::Lt)),
            mir::BinOp::Le => Ok(mk_binop(code::Binop::Le)),
            mir::BinOp::Ne => Ok(mk_binop(code::Binop::Ne)),
            mir::BinOp::Ge => Ok(mk_binop(code::Binop::Ge)),
            mir::BinOp::Gt => Ok(mk_binop(code::Binop::Gt)),

            mir::BinOp::Cmp => Err(TranslationError::UnsupportedFeature {
                description: "<=> binop is currently not supported".to_owned(),
            }),

            mir::BinOp::Offset => {
                // we need to get the layout of the thing we're offsetting
                // try to get the type of e1.
                let e1_ty = self.get_type_of_operand(e1);
                let off_ty = TX::get_offset_ty(e1_ty)?;
                let st = self.ty_translator.translate_type_to_syn_type(off_ty)?;
                let ly = st.into();
                Ok(mk_binop(code::Binop::PtrOffset(ly)))
            },
        }
    }

    /// Get the inner type of a type to which we can apply the offset operator.
    fn get_offset_ty(ty: ty::Ty<'tcx>) -> Result<ty::Ty<'tcx>, TranslationError<'tcx>> {
        match ty.kind() {
            ty::TyKind::Array(t, _) | ty::TyKind::Slice(t) | ty::TyKind::Ref(_, t, _) => Ok(*t),
            ty::TyKind::RawPtr(ty, _) => Ok(*ty),
            _ => Err(TranslationError::UnknownError(format!("cannot take offset of {}", ty))),
        }
    }

    /// Translate unary operators.
    fn translate_unop(op: mir::UnOp, ty: ty::Ty<'tcx>) -> Result<code::Unop, TranslationError<'tcx>> {
        match op {
            mir::UnOp::Not => match ty.kind() {
                ty::TyKind::Bool => Ok(code::Unop::NotBool),
                ty::TyKind::Int(_) | ty::TyKind::Uint(_) => Ok(code::Unop::NotInt),
                _ => Err(TranslationError::UnknownError(
                    "application of UnOp::Not to non-{Int, Bool}".to_owned(),
                )),
            },
            mir::UnOp::Neg => Ok(code::Unop::Neg),
            mir::UnOp::PtrMetadata => Err(TranslationError::UnsupportedFeature {
                description: "PtrMetadata unop not supported".to_owned(),
            }),
        }
    }

    /// Translate a `BorrowKind`.
    fn translate_borrow_kind(kind: mir::BorrowKind) -> Result<code::BorKind, TranslationError<'tcx>> {
        match kind {
            mir::BorrowKind::Shared => Ok(code::BorKind::Shared),
            mir::BorrowKind::Fake(_) => {
                // TODO: figure out what to do with this
                // arises in match lowering
                Err(TranslationError::UnsupportedFeature {
                    description: "RefinedRust does currently not support fake borrows".to_owned(),
                })
            },
            mir::BorrowKind::Mut { .. } => {
                // TODO: handle two-phase borrows?
                Ok(code::BorKind::Mutable)
            },
        }
    }

    const fn translate_raw_ptr_kind(mt: mir::RawPtrKind) -> code::Mutability {
        match mt {
            mir::RawPtrKind::Mut | mir::RawPtrKind::FakeForPtrMetadata => code::Mutability::Mut,
            mir::RawPtrKind::Const => code::Mutability::Shared,
        }
    }
}
