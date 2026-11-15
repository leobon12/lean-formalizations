/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsInv

/-!
# The distance to the closed bad set of a force word is measurable in the marks

Packet PROVE-AUX61-NOJUMP (D19, the relative cap of the stops).

* `exists_rat_bad_near`: rational bad points are dense in the bad set (bad sets are unions of half-open intervals of
  positive length, since the cumulative weights are one-sided step functions);
* **`infEDist_closure_badSet_eq`**: the extended distance to the closed bad set is the infimum over rational bad
  points; **`measurable_infEDist_badSet`**: it is measurable in the marks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vs

open Vr Vq

variable {nL nR : ℕ}

theorem wR_eq_sum_ite (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (y : ℝ) :
    wR xR ρR y = ∑ j, if xR j ≤ y then ρR j else 0 := by
  unfold wR; rw [Finset.sum_filter]

theorem wL_eq_sum_ite (xL : Fin nL → ℝ) (ρL : Fin nL → ℝ) (y : ℝ) :
    wL xL ρL y = ∑ i, if y ≤ xL i then ρL i else 0 := by
  unfold wL; rw [Finset.sum_filter]

/-- **Rational bad points are dense in the bad set.** -/
theorem mem_closure_rat_bad {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {y : ℂ}
    (hy : y ∈ badSet xL xR ρL ρR) :
    y ∈ closure {z : ℂ | (∃ q : ℚ, z = ((q : ℝ) : ℂ)) ∧ z ∈ badSet xL xR ρL ρR} := by
  have hyre : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hy.1])
  rw [Metric.mem_closure_iff]
  intro δ hδ
  rcases hy.2 with ⟨h0, hw⟩ | ⟨h0, hw⟩
  · -- a right bad point: the weight is constant just right of it
    have hall : ∀ᶠ y' in 𝓝[>] y.re, ∀ j ∈ (univ : Finset (Fin nR)), y.re < xR j → y' < xR j := by
      rw [Finset.eventually_all]
      intro j _
      by_cases hj : y.re < xR j
      · filter_upwards [Ioo_mem_nhdsGT hj] with t ht _ using ht.2
      · exact Eventually.of_forall fun t h => absurd h hj
    obtain ⟨a, ha, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y.re < min a (y.re + δ) from lt_min ha (by linarith))
    have hqa : (q : ℝ) ∈ Ioo y.re a := ⟨hq1, lt_of_lt_of_le hq2 (min_le_left _ _)⟩
    have hq : (q : ℝ) < y.re + δ := lt_of_lt_of_le hq2 (min_le_right _ _)
    have hwq : wR xR ρR q = wR xR ρR y.re := by
      unfold wR
      congr 1
      apply Finset.filter_congr
      intro j _
      constructor
      · intro hj
        by_contra hjy
        rw [not_le] at hjy
        exact absurd hj (not_le.2 (hsub hqa j (Finset.mem_univ j) hjy))
      · intro hj; exact hj.trans hq1.le
    refine ⟨((q : ℝ) : ℂ), ⟨⟨q, rfl⟩, by simp, Or.inl ⟨by rw [Complex.ofReal_re]; linarith,
      by rw [Complex.ofReal_re, hwq]; exact hw⟩⟩, ?_⟩
    rw [hyre, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  · -- a left bad point: the weight is constant just left of it
    have hall : ∀ᶠ y' in 𝓝[<] y.re, ∀ i ∈ (univ : Finset (Fin nL)), xL i < y.re → xL i < y' := by
      rw [Finset.eventually_all]
      intro i _
      by_cases hi : xL i < y.re
      · filter_upwards [Ioo_mem_nhdsLT hi] with t ht _ using ht.1
      · exact Eventually.of_forall fun t h => absurd h hi
    obtain ⟨a, ha, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hall
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max a (y.re - δ) < y.re from max_lt ha (by linarith))
    have hqa : (q : ℝ) ∈ Ioo a y.re := ⟨lt_of_le_of_lt (le_max_left _ _) hq1, hq2⟩
    have hq : y.re - δ < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
    have hwq : wL xL ρL q = wL xL ρL y.re := by
      unfold wL
      congr 1
      apply Finset.filter_congr
      intro i _
      constructor
      · intro hi
        by_contra hiy
        rw [not_le] at hiy
        exact absurd hi (not_le.2 (hsub hqa i (Finset.mem_univ i) hiy))
      · intro hi; exact hq2.le.trans hi
    refine ⟨((q : ℝ) : ℂ), ⟨⟨q, rfl⟩, by simp, Or.inr ⟨by rw [Complex.ofReal_re]; linarith,
      by rw [Complex.ofReal_re, hwq]; exact hw⟩⟩, ?_⟩
    rw [hyre, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith

open Classical in
/-- **The distance to the closed bad set is the infimum over its rational points.** -/
theorem infEDist_closure_badSet_eq (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (z : ℂ) : infEDist z (closure (badSet xL xR ρL ρR)) =
      ⨅ q : ℚ, if ((q : ℝ) : ℂ) ∈ badSet xL xR ρL ρR then edist z ((q : ℝ) : ℂ) else ⊤ := by
  set S := {z : ℂ | (∃ q : ℚ, z = ((q : ℝ) : ℂ)) ∧ z ∈ badSet xL xR ρL ρR} with hS
  have hSB : S ⊆ badSet xL xR ρL ρR := fun _ h => h.2
  have hcl : closure (badSet xL xR ρL ρR) = closure S :=
    le_antisymm (closure_minimal (fun _ h => mem_closure_rat_bad h) isClosed_closure) (closure_mono hSB)
  rw [hcl, infEDist_closure]
  refine le_antisymm (le_iInf fun q => ?_) (le_infEDist.2 fun y hy => ?_)
  · split_ifs with hq
    · exact infEDist_le_edist_of_mem ⟨⟨q, rfl⟩, hq⟩
    · exact le_top
  · obtain ⟨⟨q, rfl⟩, hq⟩ := hy
    refine iInf_le_of_le q ?_
    simp only [hq, ↓reduceIte, le_refl]

theorem measurableSet_mem_badSet (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (y : ℝ) :
    MeasurableSet {x : (Fin nL → ℝ) × (Fin nR → ℝ) | ((y : ℝ) : ℂ) ∈ badSet x.1 x.2 ρL ρR} := by
  have hR : Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => wR x.2 ρR y := by
    simp_rw [wR_eq_sum_ite]
    exact Finset.measurable_sum _ fun j _ =>
      Measurable.ite (measurableSet_le ((measurable_pi_apply j).comp measurable_snd) measurable_const)
        measurable_const measurable_const
  have hL : Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => wL x.1 ρL y := by
    simp_rw [wL_eq_sum_ite]
    exact Finset.measurable_sum _ fun i _ =>
      Measurable.ite (measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_fst))
        measurable_const measurable_const
  have e : {x : (Fin nL → ℝ) × (Fin nR → ℝ) | ((y : ℝ) : ℂ) ∈ badSet x.1 x.2 ρL ρR} =
      ({x | 0 ≤ y} ∩ {x | wR x.2 ρR y ≤ -2}) ∪ ({x | y ≤ 0} ∩ {x | wL x.1 ρL y ≤ -2}) := by
    ext x
    simp [badSet, IsBadPoint]
  rw [e]
  exact ((MeasurableSet.const _).inter (measurableSet_le hR measurable_const)).union
    ((MeasurableSet.const _).inter (measurableSet_le hL measurable_const))

open Classical in
/-- **The distance to the closed bad set is measurable in the marks.** -/
theorem measurable_infEDist_badSet (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (z : ℂ) :
    Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => infEDist z (closure (badSet x.1 x.2 ρL ρR)) := by
  simp_rw [infEDist_closure_badSet_eq]
  exact Measurable.iInf fun q => Measurable.ite (measurableSet_mem_badSet ρL ρR q) measurable_const
    measurable_const

end InteractingSLE.Theorem14.SB.Vs
