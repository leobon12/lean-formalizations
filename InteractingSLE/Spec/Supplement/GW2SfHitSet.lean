/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdHitSet
import Mathlib.Order.Interval.Set.Infinite

/-!
# Finite exceptional coordinates do not affect the bad-boundary closure

Packet PROVE-GW2-SAFE. A bad right prefix persists immediately to its right;
a bad left prefix persists immediately to its left. Consequently arbitrary
finite exceptional sets can be removed when testing the closed hitting set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Finset

namespace InteractingSLE.Theorem14.GW2Sf

open GW2Rd

/-- The closed bad-boundary set can be computed off any finite set. -/
theorem hitSet_eq_closure_sdiff_finite {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {E : Set ℝ} (hE : E.Finite) :
    hitSet κ b J θ = closure ((fun y : ℝ => (y : ℂ)) '' ((hitBadR κ b J θ ∪ hitBadL κ b J θ) \ E)) := by
  apply le_antisymm
  · apply closure_minimal ?_ isClosed_closure
    rintro _ ⟨y, hy, rfl⟩
    apply Metric.mem_closure_iff.2
    intro ε hε
    have hdist {z : ℝ} (hz : |z - y| < ε) : dist (y : ℂ) (z : ℂ) < ε := by
      simpa only [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_sub_comm] using hz
    rcases hy with hyR | hyL
    · obtain ⟨δ, hδ, hδx⟩ := exists_pos_le_abs_sub (flowLineXR b J 0) y
      obtain ⟨z, hz, hzE⟩ := (Set.Ioo_infinite (show y < y + min δ ε by
        linarith [lt_min hδ hε])).exists_notMem_finite hE
      have hzdist : |z - y| < min δ ε := by rw [abs_of_pos (sub_pos.2 hz.1)]; linarith [hz.2]
      refine ⟨(z : ℂ), ⟨z, ⟨Or.inl ⟨hyR.1.trans hz.1, ?_⟩, hzE⟩, rfl⟩,
        hdist (hzdist.trans_le (min_le_right _ _))⟩
      rw [filter_le_eq_of_near hδx (hzdist.trans_le (min_le_left _ _)) (Or.inl hz.1.le)]
      exact hyR.2
    · obtain ⟨δ, hδ, hδx⟩ := exists_pos_le_abs_sub (flowLineXL b J 0) y
      obtain ⟨z, hz, hzE⟩ := (Set.Ioo_infinite (show y - min δ ε < y by
        linarith [lt_min hδ hε])).exists_notMem_finite hE
      have hzdist : |z - y| < min δ ε := by rw [abs_of_neg (sub_neg.2 hz.2)]; linarith [hz.1]
      refine ⟨(z : ℂ), ⟨z, ⟨Or.inr ⟨hz.2.trans hyL.1, ?_⟩, hzE⟩, rfl⟩,
        hdist (hzdist.trans_le (min_le_right _ _))⟩
      rw [filter_ge_eq_of_near hδx (hzdist.trans_le (min_le_left _ _)) (Or.inl hz.2.le)]
      exact hyL.2
  · exact closure_mono (image_mono sdiff_subset)

/-- A threshold already present in the initial word puts its seed in the
closed bad-boundary set. -/
theorem mem_hitSet_of_threshold_zero {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (hth : ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      0 (flowLineXL b J 0) (flowLineXR b J 0)) : (0 : ℂ) ∈ hitSet κ b J θ := by
  have hord := Theorem15.isOrderedForceWord_flowLine b J 0
  apply Metric.mem_closure_iff.2
  intro ε hε
  rcases hth with hL | hR
  · obtain ⟨δ, hδ, hδx⟩ := exists_pos_le_abs_sub (flowLineXL b J 0) 0
    let z : ℝ := -(min δ ε / 2)
    have hz : z < 0 := neg_lt_zero.2 (half_pos (lt_min hδ hε))
    have hzd : |z - 0| < min δ ε := by
      rw [sub_zero, abs_of_neg hz]
      dsimp [z]
      linarith [lt_min hδ hε]
    have hf : (univ.filter fun i => flowLineXL b J 0 i = 0) =
        univ.filter (fun i => 0 ≤ flowLineXL b J 0 i) := by
      refine Finset.filter_congr fun i _ => ?_
      exact ⟨fun h => h.ge, fun h => le_antisymm (hord.2.1 i) h⟩
    rw [hf] at hL
    refine ⟨(z : ℂ), ⟨z, Or.inr ⟨hz, ?_⟩, rfl⟩, ?_⟩
    · rw [filter_ge_eq_of_near hδx (hzd.trans_le (min_le_left _ _)) (Or.inl hz.le)]
      exact hL
    · simpa only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, sub_zero] using
        hzd.trans_le (min_le_right _ _)
  · obtain ⟨δ, hδ, hδx⟩ := exists_pos_le_abs_sub (flowLineXR b J 0) 0
    let z : ℝ := min δ ε / 2
    have hz : 0 < z := half_pos (lt_min hδ hε)
    have hzd : |z - 0| < min δ ε := by
      rw [sub_zero, abs_of_pos hz]
      dsimp [z]
      linarith [lt_min hδ hε]
    have hf : (univ.filter fun i => flowLineXR b J 0 i = 0) =
        univ.filter (fun i => flowLineXR b J 0 i ≤ 0) := by
      refine Finset.filter_congr fun i _ => ?_
      exact ⟨fun h => h.le, fun h => le_antisymm h (hord.2.2.2 i)⟩
    rw [hf] at hR
    refine ⟨(z : ℂ), ⟨z, Or.inl ⟨hz, ?_⟩, rfl⟩, ?_⟩
    · rw [filter_le_eq_of_near hδx (hzd.trans_le (min_le_left _ _)) (Or.inl hz.le)]
      exact hR
    · simpa only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, sub_zero] using
        hzd.trans_le (min_le_right _ _)

end InteractingSLE.Theorem14.GW2Sf
