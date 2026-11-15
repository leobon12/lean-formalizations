/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntEnvelopeCore

/-!
# Bounded raw prefixes have initial-segment bounds without histories

The existing filling identity bounds each actual retained raw set.
Its inclusion in the full physical walk follows from recorded-piece
membership. These facts supply the least cutoff with no new input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntEnvelope

open WalkIntFill WalkMean

/-- The recorded prefix's raw set is bounded by its already constructed
physical hull. Its raw set need not itself be closed or connected. -/
theorem prefix_raw_isBounded {s : ExplState} (R : WalkPrefix s) :
    Bornology.IsBounded R.raw := by
  apply R.model.isHull.2.1.subset
  intro z hz
  rw [R.filled]
  exact mem_fillH_of_mem_closure (R.raw_subset_H hz) (subset_closure hz)

/-- Every raw prefix point lies on the given full physical parametrization. -/
theorem prefix_raw_subset_range {s : ExplState} (R : WalkPrefix s)
    {α : ℝ≥0 → ℂ} {w : ExplSpec} (hRange : range α = physOf w s) :
    R.raw ⊆ range α := by
  rw [hRange]
  intro z hz
  exact ((Set.ext_iff.1 (WalkIntFiber.physOf_inter_H w s) z).2 (R.raw_subset hz)).1

/-- The enclosing initial-segment inclusion required by BeforeExit exists
for every actual retained prefix, independently of chronological histories. -/
theorem exists_prefix_cutoff {s : ExplState} (R : WalkPrefix s)
    {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) {w : ExplSpec}
    (hRange : range α = physOf w s) :
    ∃ a : ℝ≥0, closure R.raw ⊆ α '' Icc 0 a ∧
      (a = 0 ∨ α a ∈ closure R.raw) ∧
      ∀ b : ℝ≥0, R.raw ⊆ α '' Icc 0 b → a ≤ b :=
  exists_least_cutoff hα (prefix_raw_isBounded R) (prefix_raw_subset_range R hRange)

/-- A closed raw prefix separated from a positive proper tail has a cutoff
strictly before that tail. Compactness and the cutoff are conclusions. -/
theorem exists_prefix_cutoff_before {s : ExplState} (R : WalkPrefix s)
    {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) {w : ExplSpec}
    (hRange : range α = physOf w s) {t : ℝ≥0} (ht : 0 < t)
    (hsep : Disjoint (closure R.raw) (α '' Ici t)) :
    ∃ a : ℝ≥0, a < t ∧ closure R.raw ⊆ α '' Icc 0 a :=
  exists_cutoff_before_of_disjoint_tail hα (prefix_raw_isBounded R)
    (prefix_raw_subset_range R hRange) ht hsep

end InteractingSLE.Theorem14.WalkIntEnvelope
