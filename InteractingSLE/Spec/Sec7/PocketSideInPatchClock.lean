/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInPatchGeometry

/-!
# The capacity trace at an original interior visit

PROVE-POCKET-SIDEIN. Undoing the actual capacity and erasure clocks returns
the original counterflow point. Both bounded and seed-opening traversals
therefore put the current trace tip at the initial chart of that point.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open Sec6 PocketTraversal PocketStopMarked Lemma71C

/-- The capacity trace at the capacity reached during an actual bounded
pocket visit is exactly its initial chart of the original trace point. -/
theorem capTrace_relCap_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ β : ℝ → ℂ} {τ σ t : ℝ} {ψ : ℂ → ℂ}
    (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) (ht : t ∈ visitSet η C τ σ) :
    capTrace (trav η C τ σ ψ) (relCap η C τ σ ψ t).toNNReal = ψ (η t) := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ
  have hpos := (relCap_pos_lt_of_visit hP hAC hψ ht).1
  dsimp only [capTrace]
  rw [Real.coe_toNNReal _ hpos.le]
  change trav η C τ σ ψ (capInv (trav η C τ σ ψ)
    (capClock (trav η C τ σ ψ) (relTime η C τ σ t))) = _
  rw [hγ.capInv_eq (relTime_nonneg hP hAC ⟨ht.1.1.le, ht.1.2⟩)]
  change ψ (η (pocketFibre η C τ σ
    (clockOf (pocketClock η C τ σ σ) (relTime η C τ σ t)))) = _
  rw [clockOf_relTime hP hAC ⟨ht.1.1.le, ht.1.2⟩, hP.fibre_clock_of_mem ht]

/-- The same exact trace-point identity for the seed-opening traversal. -/
theorem capTrace_relCapInf_of_visit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ}
    {α₁ α₂ : ℝ → ℂ} {τ t : ℝ} {ψ : ℂ → ℂ}
    (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) (ht : t ∈ visitSetInf η C τ) :
    capTrace (travInf η C τ ψ) (relCapInf η C τ ψ t).toNNReal = ψ (η t) := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ
  have hpos := (relCapInf_pos_lt_of_visit hP hAC hψ ht).1
  dsimp only [capTrace]
  rw [Real.coe_toNNReal _ hpos.le]
  change travInf η C τ ψ (capInv (travInf η C τ ψ)
    (capClock (travInf η C τ ψ) (relTimeInf η C τ t))) = _
  rw [hγ.capInv_eq (relTimeInf_nonneg hP hAC ht.1.le)]
  change ψ (η (pocketFibreInf η C τ
    (clockOf (clockEnd η C τ) (relTimeInf η C τ t)))) = _
  rw [clockOf_relTimeInf hP hAC ht.1.le, hP.fibre_clock_of_mem ht]

end InteractingSLE.Sec7.PocketStopSide
