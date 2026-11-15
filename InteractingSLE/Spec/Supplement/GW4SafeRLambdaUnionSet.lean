/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRUnion

/-! # GW4: the original union version is the literal physical union -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets Sec5.GlueCond

/-- Inversion of the original relatively closed walk/counterflow union is
the literal union of the physical walk version and the physical hull.
This supplies the set-version input of the reference-mean comparison. -/
theorem ae_physical_union_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E S A : Ω → Set ℂ} (hEc : ∀ ω, E ω ⊆ H ∧ IsOpen (H \ E ω))
    (hE : E =ᵐ[P] fun ω => WangWu.negInv '' S ω)
    {Y : Ω → LawUnique.HistorySpace 0 0} (t : ℝ≥0)
    (hA : A =ᵐ[P] fun ω => relClosureH (S ω ∪ cfHullQ t (Y ω))) :
    (fun ω => WangWu.negInv '' A ω) =ᵐ[P] fun ω => E ω ∪ hullAt t (Y ω) := by
  filter_upwards [hE, hA] with ω hEω hAω
  have hS : S ω = WangWu.negInv '' E ω := by
    rw [hEω, WangWu.image_negInv_image_negInv]
  have hSc := WangWu.image_negInv_relClosed (hEc ω)
  rw [← hS] at hSc
  have hKc := cfHullQ_relClosed t (Y ω)
  have hU : H \ (S ω ∪ cfHullQ t (Y ω)) =
      (H \ S ω) ∩ (H \ cfHullQ t (Y ω)) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, not_or]
    tauto
  rw [hAω, relClosureH_eq (union_subset hSc.1 hKc.1) (hU ▸ hSc.2.inter hKc.2),
    image_union, ← hEω, cfHullQ, WangWu.image_negInv_image_negInv]

end InteractingSLE.Theorem14.GW4Fix
