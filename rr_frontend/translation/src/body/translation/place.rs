// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::info;
use radium::code;
use rr_rustc_interface::abi;
use rr_rustc_interface::middle::{mir, ty};

use super::TX;
use crate::base::*;
use crate::types;

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Translate a place to a Caesium lvalue.
    pub(crate) fn translate_place(
        &self,
        pl: &mir::Place<'tcx>,
    ) -> Result<code::Expr, TranslationError<'tcx>> {
        // Get the type of the underlying local. We will use this to
        // get the necessary layout information for dereferencing
        let mut cur_ty = self.get_type_of_local(pl.local).map(mir::PlaceTy::from_ty)?;

        let local_name = self
            .variable_map
            .get(&pl.local)
            .ok_or_else(|| TranslationError::UnknownVar(format!("{:?}", pl.local)))?;

        let mut acc_expr = code::Expr::Var(local_name.to_owned());

        // iterate in evaluation order
        for it in pl.projection {
            match &it {
                mir::ProjectionElem::Deref => {
                    // handle the magic box deref
                    if let ty::TyKind::Adt(def, args) = cur_ty.ty.kind()
                        && def.is_box()
                    {
                        // extract the type parameters
                        let [ty, alloc] = args.as_slice() else {
                            return Err(TranslationError::UnsupportedFeature {
                                description: format!("wrong arguments for Box ADT {:?}", cur_ty.ty),
                            });
                        };

                        let translated_ty = self.ty_translator.translate_type_to_syn_type(ty.expect_ty())?;
                        let translated_alloc =
                            self.ty_translator.translate_type_to_syn_type(alloc.expect_ty())?;
                        acc_expr = code::Expr::MagicBoxDeref {
                            tst: translated_ty,
                            ast: translated_alloc,
                            e: Box::new(acc_expr),
                        };
                    } else {
                        // use the type of the dereferencee
                        let st = self.ty_translator.translate_type_to_syn_type(cur_ty.ty)?;
                        acc_expr = code::Expr::Deref {
                            ot: st.into(),
                            e: Box::new(acc_expr),
                        };
                    }
                },
                mir::ProjectionElem::Field(f, _) => {
                    // `t` is the type of the field we are accessing!
                    let lit = self.ty_translator.generate_structlike_use(cur_ty.ty, cur_ty.variant_index)?;
                    // TODO: does not do the right thing for accesses to fields of zero-sized objects.
                    let struct_sls = lit.generate_raw_syn_type_term();
                    let name = self.ty_translator.translator.get_field_name_of(
                        *f,
                        cur_ty.ty,
                        cur_ty.variant_index.map(abi::VariantIdx::as_usize),
                    )?;

                    acc_expr = code::Expr::FieldOf {
                        e: Box::new(acc_expr),
                        name,
                        sls: struct_sls.to_string(),
                    };
                },
                mir::ProjectionElem::Index(_v) => {
                    //TODO
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement index access".to_owned(),
                    });
                },
                mir::ProjectionElem::ConstantIndex { .. } => {
                    //TODO
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement const index access".to_owned(),
                    });
                },
                mir::ProjectionElem::Subslice { .. } => {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement subslicing".to_owned(),
                    });
                },
                mir::ProjectionElem::Downcast(_, variant_idx) => {
                    info!("Downcast of ty {:?} to {:?}", cur_ty, variant_idx);
                    if let ty::TyKind::Adt(def, args) = cur_ty.ty.kind() {
                        if def.is_enum() {
                            let enum_use = self.ty_translator.generate_enum_use(*def, args)?;
                            let els = enum_use.generate_raw_syn_type_term();

                            let variant_name = types::TX::get_variant_name_of(cur_ty.ty, *variant_idx)?;

                            acc_expr = code::Expr::EnumData {
                                els: els.to_string(),
                                variant: variant_name,
                                e: Box::new(acc_expr),
                            }
                        } else {
                            return Err(TranslationError::UnknownError(
                                "places: ADT downcasting on non-enum type".to_owned(),
                            ));
                        }
                    } else {
                        return Err(TranslationError::UnknownError(
                            "places: ADT downcasting on non-enum type".to_owned(),
                        ));
                    }
                },
                mir::ProjectionElem::OpaqueCast(_) => {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement opaque casts".to_owned(),
                    });
                },
                mir::ProjectionElem::UnwrapUnsafeBinder(_) => {
                    return Err(TranslationError::UnsupportedFeature {
                        description: "places: implement UnwrapUnsafeBinder".to_owned(),
                    });
                },
            }
            // update cur_ty
            cur_ty = cur_ty.projection_ty(self.tcx, it);
        }
        info!("translating place {:?} to {:?}", pl, acc_expr);
        Ok(acc_expr)
    }
}
