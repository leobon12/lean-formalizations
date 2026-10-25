import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepeatLift

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_exists_west_level (x : ℝ) :
    ∃ k : ℤ,
      x ≤ Real.pi + 2 * Real.pi * (k : ℝ) ∧
      Real.pi + 2 * Real.pi * (k : ℝ) < x + 2 * Real.pi := by
  let k : ℤ := ⌈(x - Real.pi) / (2 * Real.pi)⌉
  have hp : 0 < 2 * Real.pi := by positivity
  have hle : (x - Real.pi) / (2 * Real.pi) ≤ (k : ℝ) := Int.le_ceil _
  have hlt : (k : ℝ) < (x - Real.pi) / (2 * Real.pi) + 1 :=
    Int.ceil_lt_add_one _
  have hmul : (x - Real.pi) / (2 * Real.pi) * (2 * Real.pi) =
      x - Real.pi := by field_simp
  refine ⟨k, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right hle hp.le
    nlinarith
  · have h := mul_lt_mul_of_pos_right hlt hp
    nlinarith

 

theorem laneC_exists_bounded_level_sweep
    {f : ℝ → ℝ} {a b A B : ℝ}
    (hab : a ≤ b) (hAB : A ≤ B)
    (hf : ContinuousOn f (Icc a b))
    (ha : f a ≤ A) (hb : B ≤ f b) :
    ∃ s ∈ Icc a b, ∃ t ∈ Icc a b,
      s ≤ t ∧ f s = A ∧ f t = B ∧
      ∀ x ∈ Icc s t, A ≤ f x ∧ f x ≤ B := by
  have htopCont : ContinuousOn (fun x => B - f x) (Icc a b) :=
    continuousOn_const.sub hf
  obtain ⟨q, hq, hqB⟩ : ∃ q ∈ Icc a b, B - f q = 0 :=
    intermediate_value_Icc' hab htopCont
      ⟨by linarith, by linarith⟩
  obtain ⟨t, ht, htB, htBefore⟩ :=
    laneC_exists_first_zero_nonneg hq.1
      (htopCont.mono (Icc_subset_Icc le_rfl hq.2))
      (by linarith : 0 ≤ B - f a) hqB
  have htMem : t ∈ Icc a b := ⟨ht.1, ht.2.trans hq.2⟩
  have hlowCont : ContinuousOn (fun x => f x - A) (Icc a t) :=
    (hf.mono (Icc_subset_Icc le_rfl htMem.2)).sub continuousOn_const
  obtain ⟨q', hq', hq'A⟩ : ∃ q' ∈ Icc a t, f q' - A = 0 :=
    intermediate_value_Icc ht.1 hlowCont
      ⟨by linarith, by linarith⟩
  obtain ⟨s, hs, hsA, hsAfter⟩ :=
    laneC_exists_last_zero_nonneg hq'.2
      (hlowCont.mono (Icc_subset_Icc hq'.1 le_rfl))
      hq'A (by linarith : 0 ≤ f t - A)
  have hsMem : s ∈ Icc a b := ⟨hq'.1.trans hs.1,
    hs.2.trans htMem.2⟩
  refine ⟨s, hsMem, t, htMem, hs.2, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · intro x hx
    have hlo := hsAfter x hx
    have hhi := htBefore x ⟨hsMem.1.trans hx.1, hx.2⟩
    constructor <;> linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
