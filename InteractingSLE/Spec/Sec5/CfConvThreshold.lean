/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvAssemble

/-!
# Infinite continuation threshold from the image word's prefix bounds

Packet PROVE-CFCHART2. Ordered geometric images can meet the driver only in an initial
segment of each side. Prefix sums bounded strictly above minus two therefore exclude every
continuation-threshold state.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfConv

open Restart Sec7.PocketTraversal

section Threshold

variable {Ω : Type*} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {cL cR : ℝ}

/-- Prefix sums above minus two exclude the threshold at every time of a continuous driver. -/
theorem not_threshold_geom_of_prefix (hWc : ∀ ω, Continuous fun t => W t ω)
    (hxL : ∀ ω, Antitone (xL ω)) (hxR : ∀ ω, Monotone (xR ω)) (hcL : -2 < cL) (hcR : -2 < cR)
    (hpL : ∀ m : ℕ, 1 ≤ m → m ≤ nL → cL ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin nL => i.val < m), ρL i)
    (hpR : ∀ m : ℕ, 1 ≤ m → m ≤ nR → cR ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin nR => i.val < m), ρR i)
    (ω : Ω) (t : ℝ≥0) :
    ¬ ForceWord.ThresholdCondition ρL ρR (W t ω)
      (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω) := by
  have hL := Prop49Exit.neg_two_lt_sum_filter_zero (x := fun i => geomLW W xL i t ω - W t ω) hcL
    (fun i j hji hi => sub_eq_zero.2 (le_antisymm (geomLW_le hWc xL ω t j)
      ((sub_eq_zero.1 hi).symm.trans_le (antitone_index_geomLW hWc (hxL ω) t hji)))) hpL
  have hR := Prop49Exit.neg_two_lt_sum_filter_zero (x := fun j => geomRW W xR j t ω - W t ω) hcR
    (fun j i hij hj => sub_eq_zero.2 (le_antisymm
      ((monotone_index_geomRW hWc (hxR ω) t hij).trans_eq (sub_eq_zero.1 hj))
      (le_geomRW hWc xR ω t i))) hpR
  simp only [sub_eq_zero] at hL hR
  exact fun h => h.elim (not_le_of_gt hL) (not_le_of_gt hR)

/-- The geometric continuation threshold is infinite under strict prefix bounds. -/
theorem thr_eq_top_of_prefix (hWc : ∀ ω, Continuous fun t => W t ω)
    (hxL : ∀ ω, Antitone (xL ω)) (hxR : ∀ ω, Monotone (xR ω)) (hcL : -2 < cL) (hcR : -2 < cR)
    (hpL : ∀ m : ℕ, 1 ≤ m → m ≤ nL → cL ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin nL => i.val < m), ρL i)
    (hpR : ∀ m : ℕ, 1 ≤ m → m ≤ nR → cR ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin nR => i.val < m), ρR i)
    (ω : Ω) : FCDet.thr ρL ρR W xL xR ω = ⊤ := by
  by_contra hne
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.1 hne
  exact not_threshold_geom_of_prefix hWc hxL hxR hcL hcR hpL hpR ω T
    (FCDet.thr_mem_thresholdSet hWc xL xR hT.symm)

end Threshold

end InteractingSLE.Sec5.CfConv
