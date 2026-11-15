/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentLLCont
import InteractingSLE.WangWu.ProbabilityForce
import InteractingSLE.Spec.Sec2.Assembly2UpTo

/-!
# Common marks of two local words with the same driver

Packet PROVE-L1-LL. An adapter from the integral local-path predicates to
`WangWu.forceImage_unique`. Same-side marks started at the same real point
agree before the common horizon when the drivers agree. The words and their
numbers of marks may differ. This removes the force-ODE uniqueness step from
the remaining geometric collision-cut input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FlowStopIdentLL

open Sec2

variable {κ : ℝ} {nL nR mL mR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
  {w w' β β' : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
  {vR : Fin nR → ℝ≥0 → ℝ} {vL' : Fin mL → ℝ≥0 → ℝ}
  {vR' : Fin mR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- Right marks at the same initial position agree for two local words with
the same driver, by the existing scalar force-image uniqueness theorem. -/
theorem right_mark_eq_of_driver_eq
    (hp : IsSLEPathUpTo κ xL xR ρL ρR w vL vR β ζ)
    (hp' : IsSLEPathUpTo κ xL' xR' ρL' ρR' w' vL' vR' β' ζ)
    (hw : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → w s = w' s)
    {i : Fin nR} {j : Fin mR} (hx : xR i = xR' j)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vR i t = vR' j t := by
  have htime : ∀ s ∈ Icc (0 : ℝ) t, (s.toNNReal : ℝ≥0∞) < ζ :=
    fun s hs => toNNReal_lt_of_mem_Icc ht hs
  have hi : IntervalIntegrable
      (fun s : ℝ => (vR i s.toNNReal - w s.toNNReal)⁻¹) volume 0 t := by
    have h := (hp.integrable_gapR ht i).neg
    change IntervalIntegrable (fun s : ℝ => -(w s.toNNReal - vR i s.toNNReal)⁻¹)
      volume 0 t at h
    simpa only [← inv_neg, neg_sub] using h
  have hj : IntervalIntegrable
      (fun s : ℝ => (vR' j s.toNNReal - w s.toNNReal)⁻¹) volume 0 t := by
    have hj' : IntervalIntegrable
        (fun s : ℝ => (vR' j s.toNNReal - w' s.toNNReal)⁻¹) volume 0 t := by
      have h := (hp'.integrable_gapR ht j).neg
      change IntervalIntegrable (fun s : ℝ => -(w' s.toNNReal - vR' j s.toNNReal)⁻¹)
        volume 0 t at h
      simpa only [← inv_neg, neg_sub] using h
    refine hj'.congr (fun s hs => ?_)
    rw [uIoc_of_le t.coe_nonneg] at hs
    rw [hw _ (htime s ⟨hs.1.le, hs.2⟩)]
  have hv : ∀ u ∈ Icc (0 : ℝ) t, vR i u.toNNReal = xR i +
      ∫ s in (0 : ℝ)..u, 2 / (vR i s.toNNReal - w s.toNNReal) := by
    intro u hu
    have h := hp.vR_eq (htime u hu) i
    rwa [Real.coe_toNNReal _ hu.1] at h
  have hv' : ∀ u ∈ Icc (0 : ℝ) t, vR' j u.toNNReal = xR i +
      ∫ s in (0 : ℝ)..u, 2 / (vR' j s.toNNReal - w s.toNNReal) := by
    intro u hu
    have h := hp'.vR_eq (htime u hu) j
    rw [Real.coe_toNNReal _ hu.1, ← hx] at h
    rw [h]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hu.1] at hs
    rw [hw _ (htime s ⟨hs.1, hs.2.trans hu.2⟩)]
  have hn : volume {s : ℝ | s ∈ Icc 0 (t : ℝ) ∧ vR i s.toNNReal = w s.toNNReal} = 0 := by
    refine measure_mono_null (fun s hs => ?_) (hp.volume_collisionR i)
    exact ⟨hs.1.1, htime s hs.1, hs.2.symm⟩
  have hn' : volume {s : ℝ | s ∈ Icc 0 (t : ℝ) ∧ vR' j s.toNNReal = w s.toNNReal} = 0 := by
    refine measure_mono_null (fun s hs => ?_) (hp'.volume_collisionR j)
    exact ⟨hs.1.1, htime s hs.1,
      (hw _ (htime s hs.1)).symm.trans hs.2.symm⟩
  have h := WangWu.forceImage_unique t.coe_nonneg
    (Or.inr (fun s hs => ⟨hp.w_le_vR (htime s hs) i,
      (hw _ (htime s hs)) ▸ hp'.w_le_vR (htime s hs) j⟩)) hi hj hv hv' hn hn'
    (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  simpa only [Real.toNNReal_coe] using h

/-- The left-mark version, by reflection of the local paths. -/
theorem left_mark_eq_of_driver_eq
    (hp : IsSLEPathUpTo κ xL xR ρL ρR w vL vR β ζ)
    (hp' : IsSLEPathUpTo κ xL' xR' ρL' ρR' w' vL' vR' β' ζ)
    (hw : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → w s = w' s)
    {i : Fin nL} {j : Fin mL} (hx : xL i = xL' j)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vL i t = vL' j t := by
  have h := right_mark_eq_of_driver_eq hp.reflect hp'.reflect
    (fun s hs => congrArg Neg.neg (hw s hs)) (congrArg Neg.neg hx) ht
  exact neg_injective h

end InteractingSLE.Restart.FlowStopIdentLL
