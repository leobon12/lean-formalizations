/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC10Inversion
import InteractingSLE.Spec.Sec7.Aux119Heights

/-! # R98: native two-seed matching for arbitrary R.7 angles

PROVE-SIDE-COLLAR2. The constant-angle source word has only its seed
jump. Reverse it with the compatible inversion lift and apply the
existing bounded-harmonic uniqueness theorem. No angle bounds occur.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open QuantumZipper (H chiC)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC16
open Aux119Bdry Aux2728Pocket PocketCoord PocketStopSide Lemma71O

/-- A common seed contributes no nonzero exceptional coordinate in a
flow pocket: every negative/positive landing lies off the other wall. -/
theorem exSet_zero_eq {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}
    (hF : IsFlowChart R L r Ψ c) : exSet L R {0} {0} c = {0} := by
  ext ξ
  constructor
  · rintro (h | h | h)
    · exact h
    · have ht : Function.invFun L (land c ξ) = 0 := h.2
      have hland := Aux2728Pocket.IsFlowChart.land_neg_eq hF h.1
      exact False.elim (hland.2 ⟨0, by rw [ht, hF.config.left.2.2.1, hF.config.right.2.2.1]⟩)
    · have ht : Function.invFun R (land c ξ) = 0 := h.2
      have hland := Aux2728Pocket.IsFlowChart.land_pos_eq hF h.1
      exact False.elim (hland.2 ⟨0, by rw [ht, hF.config.right.2.2.1, hF.config.left.2.2.1]⟩)
  · exact fun h => Or.inl h

/-- A source extension for the actual R.7 angles reverses to the native
force word with the two seed marks at zero, for arbitrary seed weights.
In particular this includes constant-angle outer arms. -/
theorem centeredReversedMean_eq_twoSeed_of_sourceExtension
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (rL rR : ℝ)
    {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}
    (hF : IsFlowChart R L r Ψ c) {M : ℂ → ℝ}
    (hM : IsBoundedHarmonicExtension
      (chartData L R (fun _ => sleLambda κ - rs136Theta2 κ rR * chiC κ)
        (fun _ => -sleLambda κ - rs136Theta1 κ rL * chiC κ) c)
      (exSet L R {0} {0} c) M) :
    EqOn (centeredReversedMean κ M)
      (MartChar.meanExt (16 / κ) (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) 0
        (fun _ => 0) (fun _ => 0)) H := by
  apply centeredReversedMean_eq_meanExt hκ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
    (fun _ => 0) (fun _ => 0) (fun _ => rs136Theta1 κ rL)
    (fun _ => rs136Theta2 κ rR) hM.1 hM.2.1
  · intro x hx
    have hx0 : x ≠ 0 := by
      intro heq
      apply hx
      rw [heq]
      exact Set.mem_insert 0 _
    have hy0 : -x⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hx0)
    have hy : -x⁻¹ ∉ exSet L R {0} {0} c := by
      rw [exSet_zero_eq hF]
      exact hy0
    have hlim := hM.2.2 (-x⁻¹) hy
    have hdata : chartData L R (fun _ => sleLambda κ - rs136Theta2 κ rR * chiC κ)
        (fun _ => -sleLambda κ - rs136Theta1 κ rL * chiC κ) c (-x⁻¹) =
        cf92Lower κ (rs136Theta1 κ rL) (rs136Theta2 κ rR) (-x⁻¹) := by
      rcases lt_or_gt_of_ne hy0 with hneg | hpos
      · simp only [chartData, cf92Lower, hneg, ↓reduceIte]
      · simp only [chartData, cf92Lower, not_lt.mpr hpos.le, hpos, ↓reduceIte]
    rw [hdata] at hlim
    simpa only [Complex.ofReal_neg, Complex.ofReal_inv] using hlim
  · intro x _ hx
    simp only [Finset.univ_unique, Finset.filter_singleton, hx, ↓reduceIte, Finset.sum_singleton]
    exact (cf95RhoL_rs136Theta1 hκ hκ4 rL).symm
  · intro x _ hx
    simp only [Finset.univ_unique, Finset.filter_singleton, hx.le, ↓reduceIte, Finset.sum_singleton]
    exact (cf95RhoR_rs136Theta2 hκ hκ4 rR).symm

end InteractingSLE.Sec7.SideC16
