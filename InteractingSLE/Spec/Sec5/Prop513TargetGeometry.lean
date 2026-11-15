/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetInputs

/-! # Transferring Lemma 5.7 to the measurable Q tree -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Target
open QuantumZipper Sec4 Prop513Schedule Prop513TreeExtract

/-- The Q-to-counterflow coordinate change is precisely inversion. -/
theorem capacity_chart_of_target {q : ℝ} (hq : 0 < q) {z : ℂ} (hz : z ∈ H) :
    (stripCounterflowChart q).1 ((targetChart q).2.1 z) = infinitySourceChart.1 z := by
  have hz0 := DerivLog.ne_zero_of_mem_H hz
  have hz1 : z - 1 ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at hi
    exact (ne_of_gt hz) hi
  have hc : (1 + (q : ℂ)) ≠ 0 := by
    exact_mod_cast (show 1 + q ≠ 0 by linarith)
  have hi : (targetChart q).2.1 z = -(1 + (q : ℂ)) * z / (z - 1) := by
    rw [inv_eq, middle, stripCounterflowChart_inv]
    have he : z - (2 : ℂ) + 1 = z - 1 := by ring
    rw [he]
    field_simp
    ring
  rw [hi, stripCounterflowChart_fwd]
  change -1 - (1 + (q : ℂ)) * (-(1 + (q : ℂ)) * z / (z - 1))⁻¹ = -z⁻¹
  field_simp
  ring

/-- The positive-time visits in Lemma 5.7 remove the inversion pole and give
all the visits and strict descendant ordering required by Prop. 5.13. -/
theorem geometry_of_targetLemma57 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : Schedule → ℕ → Ω → Driver} {γ : Ω → ℝ≥0 → ℂ}
    {ξ : ℕ → Ω → ℝ → ℂ}
    (h57 : TargetLemma57Statement P E γ)
    (hH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H)
    (he : ∀ᵐ ω ∂P, ∀ n, EqOn (ξ n ω) (driverTree E n ω) (Icc 0 (treeTime n)))
    (hroot : ∀ n m ω, ξ (descendantIndex n m) ω (treeTime n) =
      extremeAngleTreeNode ξ treeTime n ω) :
    ∀ᵐ ω ∂P,
      (∀ n t, 0 < t → t ≤ treeTime n → ξ n ω t ≠ 0) ∧
      (∀ n, ∃ v, γ ω v = extremeAngleTreeNode (capacityTree ξ) treeTime n ω) ∧
      ∀ n, ∀ p ∈ extremeAngleTreeDescendants (capacityTree ξ) treeTime descendantIndex n ω,
        ∃ v, γ ω v = p ∧ ∀ w ≤ v,
          γ ω w ≠ extremeAngleTreeNode (capacityTree ξ) treeTime n ω := by
  filter_upwards [h57, hH, he] with ω h57ω hHω heω
  have hcap : ∀ n t, t ∈ Icc 0 (treeTime n) →
      capacityTree ξ n ω t = capacityTree (driverTree E) n ω t :=
    fun n t ht => congrArg infinitySourceChart.1 (heω n ht)
  have hvisit : ∀ n t, 0 < t → t ≤ treeTime n →
      ∃ v : ℝ≥0, 0 < v ∧ γ ω v = capacityTree ξ n ω t := by
    intro n t ht hT
    obtain ⟨v, hv, heq, _⟩ := h57ω n (t / 2) t (by linarith) (by linarith) hT
    exact ⟨v, hv, heq.trans (hcap n t ⟨ht.le, hT⟩).symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n t ht hT hzero
    obtain ⟨v, hv, heq⟩ := hvisit n t ht hT
    have hmem := hHω v hv
    rw [heq] at hmem
    simp only [capacityTree, infinitySourceChart, hzero, inv_zero, neg_zero, H,
      mem_ofPred_eq, Complex.zero_im, lt_self_iff_false] at hmem
  · intro n
    obtain ⟨v, _, hv⟩ := hvisit n (treeTime n) (treeTime_pos n) le_rfl
    exact ⟨v, hv⟩
  · intro n p hp
    obtain ⟨m, t, ht, rfl⟩ := mem_iUnion.1 hp
    obtain ⟨v, _, hv, hav⟩ := h57ω (descendantIndex n m) (treeTime n) t
      (treeTime_pos n) ht.1 ht.2
    refine ⟨v, hv.trans (hcap _ t ⟨(treeTime_pos n).le.trans ht.1.le, ht.2⟩).symm,
      fun w hw => ?_⟩
    have hnode : capacityTree (driverTree E) (descendantIndex n m) ω (treeTime n) =
        extremeAngleTreeNode (capacityTree ξ) treeTime n ω := by
      rw [← hcap _ _ ⟨(treeTime_pos n).le, treeTime_mono n m⟩]
      exact congrArg infinitySourceChart.1 (hroot n m ω)
    simpa only [hnode] using hav w hw

end InteractingSLE.Sec5.Prop513Target
