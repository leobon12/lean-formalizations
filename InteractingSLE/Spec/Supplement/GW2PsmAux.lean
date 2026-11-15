/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondMean
import InteractingSLE.Spec.Sec5.Aux61WinFibre
import InteractingSLE.Spec.Sec5.RestartGenOne
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Supplement.GW2SdmWord

/-!
# GW2's open lines: the angle shift of a flow line's bounded harmonic extension

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic):

* **`sub_eq_of_bhe_angle`**: the bounded harmonic extension of the angle-`θ` flow-line force data of `b` minus that of
  `b` is `θχ` on `ℍ` (the `uθ − u' = θχ` of the launch forms).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.GW2Psm

/-- **`uθ − u' = θχ`.** -/
theorem sub_eq_of_bhe_angle {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ} {u' uθ : ℂ → ℝ} (hu' : IsBoundedHarmonicExtension b J u')
    (huθ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uθ) :
    ∀ z ∈ H, uθ z - u' z = θ * chiC κ := by
  set S : Set ℝ := (J : Set ℝ) ∪ {0} ∪ forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0) with hS
  have hSf : S.Finite :=
    ((J.finite_toSet.union (Set.finite_singleton 0)).union (GW2Sdm.finite_forceJumpSet _ _))
  have h1 : IsBoundedHarmonicExtension (fun x => b x + θ * chiC κ) S (fun z => u' z + θ * chiC κ) :=
    Sec5.Aux61Win.IsBoundedHarmonicExtension.mono_set
      (Sec5.GlueCond.isBoundedHarmonicExtension_add_const hu' (θ * chiC κ)) fun x hx => Or.inl (Or.inl hx)
  have h2 : IsBoundedHarmonicExtension (fun x => b x + θ * chiC κ) S uθ := by
    have h := Sec5.Aux61Win.IsBoundedHarmonicExtension.mono_set huθ (S' := S) fun x hx => Or.inr hx
    refine (Restart.isBoundedHarmonicExtension_congr (fun y hy => ?_) uθ).2 h
    have hyJ : y ∉ J := fun h => hy (Or.inl (Or.inl h))
    have hy0 : y ≠ 0 := fun h => hy (Or.inl (Or.inr h))
    rw [Sec5.RestartGen.forceBoundaryData_flowLine_angle hκ b J θ 0 y, Sec4.forceBoundaryData_flowLine hκ hb hy0 hyJ]
    ring
  intro z hz
  have := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension hSf h1 h2 hz
  simp only at this
  linarith

end InteractingSLE.Theorem14.GW2Psm
