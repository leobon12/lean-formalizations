/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfThreshold
import InteractingSLE.Spec.Supplement.GW2RdHitEnd
import InteractingSLE.Spec.Restart.FlowStopIdentLLTerminal

/-!
# A geometric continuation threshold lands in the bad boundary set

Packet PROVE-GW2-SAFE. This is deterministic and uses no relative SDE law.
The existing inverse-boundary collision theorem identifies any nonempty side
collision with an interval ending at the current real tip. Its common-cut form
then gives bad real points arbitrarily close to that tip, including at the seed
and at jump points. This connects geometric thresholds to `GW2Rd.hitSet`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Sf

open Restart Restart.FlowStopIdentLL MartChar.RealFlow GW2Rd

/-- A nonadmissible group of geometric force images has a real tip. -/
theorem im_eq_zero_of_threshold_images {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {w : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {T : ℝ≥0}
    (hg : IsGeneratingTrace w U γ) (hT : 0 < T) (hTU : (T : ℝ≥0∞) ≤ U)
    {D : ℝ → ℝ} (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w s)
    (hth : ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (D T)
      (fun i => -rightImg (fun s => -D s) (-flowLineXL b J 0 i) T)
      (fun j => rightImg D (flowLineXR b J 0 j) T)) : (γ T).im = 0 := by
  rcases hth with hL | hR
  · obtain ⟨i, hi, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (ne_of_lt (hL.trans_lt (by norm_num : (-2 : ℝ) < 0)))
    have hcoll := (Finset.mem_filter.1 hi).2
    obtain ⟨hB, htip⟩ := terminal_boundary_data (LP.isGeneratingTrace_reflect hg) hT hTU
      hD.neg (by change -(D 0) = 0; rw [hD0, neg_zero]) (fun s hs => congrArg Neg.neg (hDw s hs))
    have hp := real_tip_of_rightImg_eq hD.neg (by change -(D 0) = 0; rw [hD0, neg_zero]) T.2 hB htip
      (neg_eq_iff_eq_neg.1 hcoll)
    simpa only [LP.reflectC, Complex.neg_im, Complex.conj_im, neg_neg] using hp.1
  · obtain ⟨j, hj, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (ne_of_lt (hR.trans_lt (by norm_num : (-2 : ℝ) < 0)))
    obtain ⟨hB, htip⟩ := terminal_boundary_data hg hT hTU hD hD0 hDw
    exact (real_tip_of_rightImg_eq hD hD0 T.2 hB htip ((Finset.mem_filter.1 hj).2)).1

/-- Every geometric threshold of a continuously generated chain lies in the
closed bad boundary set of its word. The trace need not satisfy an SDE. -/
theorem mem_hitSet_of_threshold_images {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {w : ℝ≥0 → ℝ} {U : ℝ≥0∞} {γ : ℝ≥0 → ℂ} {T : ℝ≥0}
    (hg : IsGeneratingTrace w U γ) (hT : 0 < T) (hTU : (T : ℝ≥0∞) ≤ U)
    {D : ℝ → ℝ} (hD : Continuous D) (hD0 : D 0 = 0)
    (hDw : ∀ s : ℝ≥0, s < T → D s = w s)
    (hth : ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (D T)
      (fun i => -rightImg (fun s => -D s) (-flowLineXL b J 0 i) T)
      (fun j => rightImg D (flowLineXR b J 0 j) T)) : γ T ∈ hitSet κ b J θ := by
  have him := im_eq_zero_of_threshold_images hg hT hTU hD hD0 hDw hth
  have hreal : γ T = ((γ T).re : ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using him)
  apply Metric.mem_closure_iff.2
  intro ε hε
  have hcuts := hasCommonCollisionCuts_terminal_images (b := b) (J := J) (bR := b) (JR := J)
    (y := 0) (O := Metric.ball (γ T).re ε) Metric.isOpen_ball hg hT hTU hD hD0 hDw
    (fun _ => by simpa only [zero_add, Metric.mem_ball, dist_self] using hε)
  have hdist (a : ℝ) (ha : a ∈ Metric.ball (γ T).re ε) : dist (γ T) (a : ℂ) < ε := by
    rw [hreal, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using ha
  rcases hth with hL | hR
  · rcases hcuts.1 with ⟨hnone, -⟩ | ⟨a, haO, ha0, haJ, -, hcut, -⟩
    · have he : (univ.filter fun i => -rightImg (fun s => -D s) (-flowLineXL b J 0 i) T = D T) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun i _ => hnone i
      rw [he, Finset.sum_empty] at hL
      norm_num at hL
    · have hfilter : (univ.filter fun i => -rightImg (fun s => -D s) (-flowLineXL b J 0 i) T = D T) =
          univ.filter (fun i => a ≤ flowLineXL b J 0 i) := by
        refine Finset.filter_congr fun i _ => ?_
        have hne : a ≠ flowLineXL b J 0 i := by
          intro he
          rcases flowLineXL_eq_zero_or_mem b J i with h0 | hJ
          · exact (ne_of_lt ha0) (he.trans h0)
          · exact haJ (he ▸ hJ)
        have hcut' := hcut i
        rw [sub_zero] at hcut'
        exact hcut'.trans
          (show a < flowLineXL b J 0 i ↔ a ≤ flowLineXL b J 0 i from
            ⟨le_of_lt, fun hi => lt_of_le_of_ne hi hne⟩)
      rw [hfilter] at hL
      exact ⟨(a : ℂ), ⟨a, Or.inr ⟨ha0, hL⟩, rfl⟩, hdist a haO⟩
  · rcases hcuts.2 with ⟨hnone, -⟩ | ⟨a, haO, ha0, -, -, hcut, -⟩
    · have he : (univ.filter fun j => rightImg D (flowLineXR b J 0 j) T = D T) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun j _ => hnone j
      rw [he, Finset.sum_empty] at hR
      norm_num at hR
    · have hfilter : (univ.filter fun j => rightImg D (flowLineXR b J 0 j) T = D T) =
          univ.filter (fun j => flowLineXR b J 0 j ≤ a) :=
        Finset.filter_congr fun j _ => by simpa only [sub_zero] using hcut j
      rw [hfilter] at hR
      exact ⟨(a : ℂ), ⟨a, Or.inl ⟨ha0, hR⟩, rfl⟩, hdist a haO⟩

end InteractingSLE.Theorem14.GW2Sf
