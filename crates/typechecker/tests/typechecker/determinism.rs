//! Verifies FxHash-based containers iterate deterministically given a fixed
//! insertion sequence. Inter-process determinism is the real guarantee — that
//! is exercised by the snapshot suites stored on disk. This test is a weak
//! intra-process guard that documents the contract.

use krypton_typechecker::types::{TypeVarGen, TypeVarId};
use rustc_hash::FxHashSet;

fn collect(gen: &mut TypeVarGen) -> Vec<TypeVarId> {
    let ids: Vec<TypeVarId> = (0..16).map(|_| gen.fresh()).collect();
    let mut set: FxHashSet<TypeVarId> = FxHashSet::default();
    for id in &ids {
        set.insert(*id);
    }
    set.into_iter().collect()
}

#[test]
fn fx_hashset_iteration_is_stable_for_equal_insertions() {
    let mut gen_a = TypeVarGen::new();
    let mut gen_b = TypeVarGen::new();
    assert_eq!(collect(&mut gen_a), collect(&mut gen_b));
}
