/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.FrameQChart
import InteractingSLE.Spec.Sec5.StripRevVisitPath
import InteractingSLE.Spec.Sec5.Prop411QOrder
import InteractingSLE.Spec.Sec5.CrossRestartExit

/-!
# Returning a Q first contact to the completed E counterflow

The counterflow is interior at positive capacity times. Its Q first contact
therefore becomes the first contact with the lower boundary together with the
physical E prefix. Both endpoints of the compactified clock are checked.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.FrameQ

open QuantumZipper Sec4 Prop513Schedule Prop513Target Prop513Wire CrossRestart
open WangWu (negInv negInv_negInv)

/-- A Q first contact gives the exact E first-exit assertion used by Lemma 5.7. -/
theorem firstHitPoint_of_isFirstHitQ {q T σ : ℝ} (hq : 0 < q) (hσ : 0 < σ) (hσT : σ ≤ T)
    {η : ℝ → ℂ} (hη0 : η 0 = 0) (hηH : ∀ t, 0 < t → t ≤ T → η t ∈ H)
    {γ : ℝ≥0 → ℂ} (hγ0 : γ 0 = 0) (hγH : ∀ t : ℝ≥0, 0 < t → γ t ∈ H)
    (hfirst : Prop411Q.IsFirstHitQ η (fun t => γ t.toNNReal) σ) :
    IsFirstHitPoint (stripCounterflowPath q γ) 1
      (lowerLineH ∪ pullPrefix q T η '' Icc 0 σ) (pullPrefix q T η σ) := by
  obtain ⟨u, hu0, hu, hbefore⟩ := hfirst
  have hpull : ∀ t, 0 < t → t ≤ T →
      (stripCounterflowChart q).2.1 (negInv (η t)) = pullPrefix q T η t := by
    intro t ht htT
    change (stripCounterflowChart q).2.1 (infinitySourceChart.1 (η t)) = _
    rw [← pullPrefix_capacity hq hηH ht htT]
    exact stripCounterflowChart_inv_fwd hq
      (DerivLog.ne_zero_of_mem_H (pullPrefix_mem_H hq (hσ.trans_le hσT) hηH t ht))
  have heγ : γ u.toNNReal = negInv (η σ) := Prop411Q.negInv_eq_iff.1 hu
  refine ⟨physTime u, ⟨(physTime_pos hu0).le, (physTime_lt_one hu0.le).le⟩, ?_,
    Or.inr ⟨σ, ⟨hσ.le, le_rfl⟩, rfl⟩, ?_⟩
  · rw [stripCounterflowPath_of_lt (physTime_lt_one hu0.le), physTime_div hu0.le,
      heγ, hpull σ hσ hσT]
  · intro v hv hmem
    rcases eq_or_lt_of_le hv.1 with hv0 | hv0
    · subst v
      rw [stripCounterflowPath_zero hγ0] at hmem
      rcases hmem with hlow | ⟨t, ht, he⟩
      · exact StripRevVisit.start_notMem hq (Or.inl hlow)
      rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · rw [← ht0, pullPrefix_zero q (hσ.le.trans hσT) hη0] at he
        exact StripRevVisit.start_notMem hq (Or.inr he.symm)
      · have hH := pullPrefix_mem_H hq (hσ.trans_le hσT) hηH t ht0
        rw [he] at hH
        simp [H] at hH
    · have hv1 : v < 1 := hv.2.trans (physTime_lt_one hu0.le)
      have hH := StripRevVisit.stripCounterflowPath_mem_H hq hγH hv0 hv1
      rcases hmem with hlow | ⟨t, ht, he⟩
      · exact StripRevVisit.notMem_lowerLineH_of_mem_H hH hlow
      rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · rw [← ht0, pullPrefix_zero q (hσ.le.trans hσT) hη0] at he
        rw [← he] at hH
        exact (DerivLog.ne_zero_of_mem_H hH) rfl
      · have hw0 : 0 < v / (1 - v) := div_pos hv0 (sub_pos.2 hv1)
        have hwU : v / (1 - v) < u := by
          have hlt := (lt_div_iff₀ (show 0 < 1 + u by linarith only [hu0])).1 hv.2
          exact (div_lt_iff₀ (sub_pos.2 hv1)).2 (by nlinarith only [hlt])
        apply hbefore (v / (1 - v)) ⟨hw0, hwU⟩
        refine ⟨t, ⟨ht0, ht.2⟩, ?_⟩
        have hM := congrArg (stripCounterflowChart q).1 he
        rw [stripCounterflowPath_of_lt hv1,
          stripCounterflowChart_fwd_inv hq (by
            have hγ := hγH (v / (1 - v)).toNNReal (Real.toNNReal_pos.2 hw0)
            intro he
            rw [he] at hγ
            simp [H] at hγ)] at hM
        rw [pullPrefix_capacity hq hηH ht0 (ht.2.trans hσT)] at hM
        exact (Prop411Q.negInv_eq_iff.2 hM.symm).symm

end InteractingSLE.Sec5.FrameQ
