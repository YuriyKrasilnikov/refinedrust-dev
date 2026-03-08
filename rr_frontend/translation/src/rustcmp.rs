use std::cmp::Ordering;

use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::shims;

fn region_discriminant(a: ty::Region<'_>) -> u8 {
    use ty::RegionKind;
    match a.kind() {
        RegionKind::ReEarlyParam(_) => 0,
        RegionKind::ReBound(_, _) => 1,
        RegionKind::ReLateParam(_) => 2,
        RegionKind::ReStatic => 3,
        RegionKind::ReVar(_) => 4,
        RegionKind::RePlaceholder(_) => 5,
        RegionKind::ReErased => 6,
        RegionKind::ReError(_) => 7,
    }
}

fn cmp_region<'tcx>(a: ty::Region<'tcx>, b: ty::Region<'tcx>) -> Ordering {
    region_discriminant(a).cmp(&region_discriminant(b)).then_with(|| {
        use ty::RegionKind;
        match (a.kind(), b.kind()) {
            (RegionKind::ReEarlyParam(a_r), RegionKind::ReEarlyParam(b_r)) => a_r.index.cmp(&b_r.index),
            (RegionKind::ReBound(a_d, a_r), RegionKind::ReBound(b_d, b_r)) => {
                cmp_bound_var_index_kind(a_d, b_d).then(a_r.var.cmp(&b_r.var))
            },
            (RegionKind::ReLateParam(_a_r), RegionKind::ReLateParam(_b_r)) => {
                unimplemented!("compare ReLateParam");
            },
            (RegionKind::ReVar(a_r), RegionKind::ReVar(b_r)) => a_r.index().cmp(&b_r.index()),
            (RegionKind::RePlaceholder(_a_r), RegionKind::RePlaceholder(_b_r)) => {
                unimplemented!("compare RePlaceholder");
            },
            (RegionKind::ReStatic, RegionKind::ReStatic)
            | (RegionKind::ReErased, RegionKind::ReErased)
            | (RegionKind::ReError(_), RegionKind::ReError(_)) => Ordering::Equal,
            _ => {
                unreachable!();
            },
        }
    })
}

fn cmp_bound_var_index_kind(a: ty::BoundVarIndexKind, b: ty::BoundVarIndexKind) -> Ordering {
    match (a, b) {
        (ty::BoundVarIndexKind::Canonical, ty::BoundVarIndexKind::Canonical) => Ordering::Equal,
        (ty::BoundVarIndexKind::Canonical, _) => Ordering::Greater,
        (ty::BoundVarIndexKind::Bound(idx1), ty::BoundVarIndexKind::Bound(idx2)) => idx1.cmp(&idx2),
        (ty::BoundVarIndexKind::Bound(_), ty::BoundVarIndexKind::Canonical) => Ordering::Less,
    }
}

fn cmp_const<'tcx>(_tcx: ty::TyCtxt<'tcx>, _a: ty::Const<'tcx>, _b: ty::Const<'tcx>) -> Ordering {
    unimplemented!("compare Const");
}

fn ty_discriminant(ty: ty::Ty<'_>) -> usize {
    use ty::TyKind;
    match ty.kind() {
        TyKind::Bool => 0,
        TyKind::Char => 1,
        TyKind::Int(_) => 2,
        TyKind::Uint(_) => 3,
        TyKind::Float(_) => 4,
        TyKind::Adt(_, _) => 5,
        TyKind::Foreign(_) => 6,
        TyKind::Str => 7,
        TyKind::Array(_, _) => 8,
        TyKind::Slice(_) => 9,
        TyKind::RawPtr(_, _) => 10,
        TyKind::Ref(_, _, _) => 11,
        TyKind::FnDef(_, _) => 12,
        TyKind::FnPtr(..) => 13,
        TyKind::Dynamic(..) => 14,
        TyKind::Closure(_, _) => 15,
        TyKind::CoroutineClosure(_, _) => 16,
        TyKind::Coroutine(_, _) => 17,
        TyKind::CoroutineWitness(_, _) => 18,
        TyKind::Never => 19,
        TyKind::Tuple(_) => 20,
        TyKind::Pat(_, _) => 21,
        TyKind::Alias(_, _) => 22,
        TyKind::Param(_) => 23,
        TyKind::Bound(_, _) => 24,
        TyKind::Placeholder(_) => 25,
        TyKind::Infer(_) => 26,
        TyKind::Error(_) => 27,
        TyKind::UnsafeBinder(_) => 28,
    }
}

pub(crate) fn cmp_defid(tcx: ty::TyCtxt<'_>, a: DefId, b: DefId) -> Ordering {
    // NOTE: The relative order of shims to each other may not be the same as the relative order of the
    // actual objects to each other. Therefore, use the export order.
    let a_did = shims::flat::get_external_did_for_did(tcx, a).unwrap_or(a);
    let b_did = shims::flat::get_external_did_for_did(tcx, b).unwrap_or(b);

    //let a_path = tcx.def_path(a_did);
    let a_str = tcx.def_path_str(a_did);
    let b_str = tcx.def_path_str(b_did);

    a_str.cmp(&b_str)

    //let a_hash = tcx.def_path_hash(a_did);
    //let b_hash = tcx.def_path_hash(b_did);
    //a_hash.cmp(&b_hash)
}

fn cmp_ty<'tcx>(tcx: ty::TyCtxt<'tcx>, a: ty::Ty<'tcx>, b: ty::Ty<'tcx>) -> Ordering {
    ty_discriminant(a).cmp(&ty_discriminant(b)).then_with(|| {
        use ty::TyKind;
        match (a.kind(), b.kind()) {
            (TyKind::Int(a_i), TyKind::Int(b_i)) => a_i.cmp(b_i),
            (TyKind::Uint(a_u), TyKind::Uint(b_u)) => a_u.cmp(b_u),
            (TyKind::Float(a_f), TyKind::Float(b_f)) => a_f.cmp(b_f),
            (TyKind::Adt(a_d, a_s), TyKind::Adt(b_d, b_s)) => {
                cmp_defid(tcx, a_d.did(), b_d.did()).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::Foreign(a_d), TyKind::Foreign(b_d)) => cmp_defid(tcx, *a_d, *b_d),
            (TyKind::Array(a_t, a_c), TyKind::Array(b_t, b_c)) => {
                cmp_ty(tcx, *a_t, *b_t).then_with(|| cmp_const(tcx, *a_c, *b_c))
            },
            (TyKind::Pat(..), TyKind::Pat(..)) => {
                unimplemented!("compare Pat");
            },
            (TyKind::Slice(a_t), TyKind::Slice(b_t)) => cmp_ty(tcx, *a_t, *b_t),
            (TyKind::RawPtr(a_t, a_m), TyKind::RawPtr(b_t, b_m)) => {
                cmp_ty(tcx, *a_t, *b_t).then_with(|| a_m.cmp(b_m))
            },
            (TyKind::Ref(a_r, a_t, a_m), TyKind::Ref(b_r, b_t, b_m)) => {
                cmp_region(*a_r, *b_r).then_with(|| cmp_ty(tcx, *a_t, *b_t).then_with(|| a_m.cmp(b_m)))
            },
            (TyKind::FnDef(a_d, a_s), TyKind::FnDef(b_d, b_s)) => {
                cmp_defid(tcx, *a_d, *b_d).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::FnPtr(..), TyKind::FnPtr(..)) => {
                unimplemented!("compare FnPtr");
            },
            (TyKind::Dynamic(..), TyKind::Dynamic(..)) => {
                unimplemented!("compare Dynamic");
            },
            (TyKind::Closure(a_d, a_s), TyKind::Closure(b_d, b_s)) => {
                cmp_defid(tcx, *a_d, *b_d).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::CoroutineClosure(a_d, a_s), TyKind::CoroutineClosure(b_d, b_s)) => {
                cmp_defid(tcx, *a_d, *b_d).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::Coroutine(a_d, a_s), TyKind::Coroutine(b_d, b_s)) => {
                cmp_defid(tcx, *a_d, *b_d).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::CoroutineWitness(a_d, a_s), TyKind::CoroutineWitness(b_d, b_s)) => {
                cmp_defid(tcx, *a_d, *b_d).then_with(|| cmp_arg_refs(tcx, a_s, b_s))
            },
            (TyKind::Tuple(a_t), TyKind::Tuple(b_t)) => {
                a_t.iter().cmp_by(b_t.iter(), |a, b| cmp_ty(tcx, a, b))
            },
            (TyKind::Alias(a_i, a_p), TyKind::Alias(b_i, b_p)) => a_i.cmp(b_i).then_with(|| {
                cmp_defid(tcx, a_p.def_id, b_p.def_id).then_with(|| cmp_arg_refs(tcx, a_p.args, b_p.args))
            }),
            (TyKind::Param(a_p), TyKind::Param(b_p)) => a_p.cmp(b_p),
            (TyKind::Bound(..), TyKind::Bound(..)) => {
                unimplemented!("compare Bound");
            },
            (TyKind::Placeholder(_), TyKind::Placeholder(_)) => {
                unimplemented!("compare Placeholder");
            },
            (TyKind::Infer(_), TyKind::Infer(_)) => {
                unimplemented!("compare Infer");
            },
            (TyKind::Error(_), TyKind::Error(_)) => {
                unimplemented!("compare Error");
            },
            (TyKind::UnsafeBinder(_), TyKind::UnsafeBinder(_)) => {
                unimplemented!("compare UnsafeBinder");
            },
            (TyKind::Bool, TyKind::Bool)
            | (TyKind::Char, TyKind::Char)
            | (TyKind::Str, TyKind::Str)
            | (TyKind::Never, TyKind::Never) => Ordering::Equal,
            _ => {
                unreachable!();
            },
        }
    })
}

pub(crate) fn cmp_tys<'tcx>(tcx: ty::TyCtxt<'tcx>, a: &[ty::Ty<'tcx>], b: &[ty::Ty<'tcx>]) -> Ordering {
    match a.len().cmp(&b.len()) {
        Ordering::Equal => {
            // compare elements
            for (x, y) in a.iter().zip(b.iter()) {
                // the discriminants are the same as the DefId we are calling into is the same
                let xy_cmp = cmp_ty(tcx, *x, *y);
                if xy_cmp != Ordering::Equal {
                    return xy_cmp;
                }
            }
            Ordering::Equal
        },
        o => o,
    }
}

/// Compare two `GenericArg` deterministically.
/// Should only be called on equal discriminants.
fn cmp_arg_ref<'tcx>(tcx: ty::TyCtxt<'tcx>, a: ty::GenericArg<'tcx>, b: ty::GenericArg<'tcx>) -> Ordering {
    match (a.kind(), b.kind()) {
        (ty::GenericArgKind::Const(c1), ty::GenericArgKind::Const(c2)) => cmp_const(tcx, c1, c2),
        (ty::GenericArgKind::Type(ty1), ty::GenericArgKind::Type(ty2)) => {
            // we should make sure that this always orders the Self instance first.
            match (ty1.kind(), ty2.kind()) {
                (ty::TyKind::Param(p1), ty::TyKind::Param(p2)) => p1.cmp(p2),
                (ty::TyKind::Param(_), _) => Ordering::Less,
                (_, _) => cmp_ty(tcx, ty1, ty2),
            }
        },
        (ty::GenericArgKind::Lifetime(r1), ty::GenericArgKind::Lifetime(r2)) => cmp_region(r1, r2),
        (_, _) => {
            unreachable!("Comparing GenericArg with different discriminant");
        },
    }
}

/// Compare two sequences of `GenericArg`s for the same `DefId`, where the discriminants are pairwise
/// equal.
pub(crate) fn cmp_arg_refs<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    a: &[ty::GenericArg<'tcx>],
    b: &[ty::GenericArg<'tcx>],
) -> Ordering {
    match a.len().cmp(&b.len()) {
        Ordering::Equal => {
            // compare elements
            for (x, y) in a.iter().zip(b.iter()) {
                // the discriminants are the same as the DefId we are calling into is the same
                let xy_cmp = cmp_arg_ref(tcx, *x, *y);
                if xy_cmp != Ordering::Equal {
                    return xy_cmp;
                }
            }
            Ordering::Equal
        },
        o => o,
    }
}

/// Compare two `TraitRef`s deterministically, giving a
/// consistent order that is stable across compilations.
pub(crate) fn cmp_trait_ref<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    in_trait_decl: Option<DefId>,
    a: &ty::TraitRef<'tcx>,
    b: &ty::TraitRef<'tcx>,
) -> Ordering {
    // if one of them is the self trait, that should be greater (at the end, after its
    // dependencies).
    if let Some(trait_did) = in_trait_decl {
        if a.def_id == trait_did && a.args[0].expect_ty().is_param(0) {
            return Ordering::Greater;
        }
        if b.def_id == trait_did && b.args[0].expect_ty().is_param(0) {
            return Ordering::Less;
        }
    }

    //let path_a = shims::flat::get_cleaned_def_path(tcx, a.def_id);
    //let path_b = shims::flat::get_cleaned_def_path(tcx, b.def_id);
    //let path_cmp = path_a.cmp(&path_b);
    //info!("cmp_trait_ref: comparing paths {path_a:?} and {path_b:?}");

    let path_cmp = cmp_defid(tcx, a.def_id, b.def_id);

    path_cmp.then_with(|| {
        let args_a = a.args.as_slice();
        let args_b = b.args.as_slice();
        cmp_arg_refs(tcx, args_a, args_b)
    })
}

pub(crate) fn cmp_alias_ty<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    a: &ty::AliasTy<'tcx>,
    b: &ty::AliasTy<'tcx>,
) -> Ordering {
    let did_cmp = cmp_defid(tcx, a.def_id, b.def_id);

    did_cmp.then_with(|| cmp_arg_refs(tcx, a.args.as_slice(), b.args.as_slice()))
}
