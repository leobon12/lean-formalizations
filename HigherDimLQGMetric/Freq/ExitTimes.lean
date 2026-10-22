import HigherDimLQGMetric.Freq.Lemma51

/-!
# First and last shell crossing times

A continuous scalar path starting inside an inner radius, with both endpoints
outside an outer radius, has a previous outer hit, a next outer hit, and a
last inner hit before the next outer hit. The final crossing stays in the
closed shell.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set LQGMetric.MetricGeometry

/-- A previous outer hit and the next complete inner-to-outer crossing. -/
theorem s4c_shell_times {f : ℝ → ℝ} {L a inner outer : ℝ}
    (hf : ContinuousOn f (Icc 0 L)) (ha : a ∈ Icc 0 L)
    (h0 : outer ≤ f 0) (hL : outer ≤ f L)
    (hfa : f a < inner) (hio : inner < outer) :
    ∃ b c e : ℝ, 0 ≤ b ∧ b ≤ a ∧ a ≤ c ∧ c < e ∧ e ≤ L ∧
      f b = outer ∧ f c = inner ∧ f e = outer ∧
      ∀ u ∈ Icc c e, inner ≤ f u ∧ f u ≤ outer := by
  have hfaO : f a < outer := hfa.trans hio
  have h0a : ContinuousOn f (Icc 0 a) := hf.mono (Icc_subset_Icc le_rfl ha.2)
  obtain ⟨b, hb, hfb⟩ : ∃ b ∈ Icc (0 : ℝ) a, f b = outer := by
    obtain ⟨b, hb, hfb⟩ := (intermediate_value_Icc' ha.1 h0a) (show outer ∈ Icc (f a) (f 0) by
      exact ⟨hfaO.le, h0⟩)
    exact ⟨b, hb, hfb⟩
  have hae : ContinuousOn f (Icc a L) := hf.mono (Icc_subset_Icc ha.1 le_rfl)
  obtain ⟨e₀, he₀, hfe₀⟩ : ∃ e₀ ∈ Icc a L, f e₀ = outer := by
    obtain ⟨e₀, he₀, hfe₀⟩ := (intermediate_value_Icc ha.2 hae) (show outer ∈ Icc (f a) (f L) by
      exact ⟨hfaO.le, hL⟩)
    exact ⟨e₀, he₀, hfe₀⟩
  let T : Set ℝ := Icc a L ∩ f ⁻¹' {outer}
  have hTc : IsClosed T := hae.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hTne : T.Nonempty := ⟨e₀, he₀, hfe₀⟩
  have hTb : BddBelow T := ⟨a, fun x hx => hx.1.1⟩
  let e := sInf T
  have heT : e ∈ T := hTc.csInf_mem hTne hTb
  have hae' : a < e := by
    apply lt_of_le_of_ne heT.1.1
    intro hEq
    have : f a = outer := by rw [hEq]; exact heT.2
    linarith
  have hbefore : ∀ u ∈ Ico a e, f u < outer := by
    intro u hu
    by_contra hnot
    have huO : outer ≤ f u := le_of_not_gt hnot
    by_cases heq : f u = outer
    · have huT : u ∈ T := ⟨⟨hu.1, hu.2.le.trans heT.1.2⟩, heq⟩
      exact (not_le.mpr hu.2) (csInf_le hTb huT)
    · have hfu : outer < f u := lt_of_le_of_ne huO (Ne.symm heq)
      have hauc : ContinuousOn f (Icc a u) := hf.mono
        (Icc_subset_Icc ha.1 (hu.2.le.trans heT.1.2))
      obtain ⟨v, hv, hfv⟩ := (intermediate_value_Icc hu.1 hauc)
        (show outer ∈ Icc (f a) (f u) by exact ⟨hfaO.le, hfu.le⟩)
      have hvT : v ∈ T := ⟨⟨hv.1, hv.2.trans (hu.2.le.trans heT.1.2)⟩, hfv⟩
      exact (not_le.mpr (hv.2.trans_lt hu.2)) (csInf_le hTb hvT)
  have haec : ContinuousOn f (Icc a e) := hae.mono (Icc_subset_Icc le_rfl heT.1.2)
  obtain ⟨c₀, hc₀, hfc₀⟩ : ∃ c₀ ∈ Icc a e, f c₀ = inner := by
    obtain ⟨c₀, hc₀, hfc₀⟩ := (intermediate_value_Icc hae'.le haec)
      (show inner ∈ Icc (f a) (f e) by exact ⟨hfa.le, (heT.2 ▸ hio.le)⟩)
    exact ⟨c₀, hc₀, hfc₀⟩
  let C : Set ℝ := Icc a e ∩ f ⁻¹' {inner}
  have hCc : IsClosed C := haec.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hCne : C.Nonempty := ⟨c₀, hc₀, hfc₀⟩
  have hCb : BddAbove C := ⟨e, fun x hx => hx.1.2⟩
  let c := sSup C
  have hcC : c ∈ C := hCc.csSup_mem hCne hCb
  have hce : c < e := by
    apply lt_of_le_of_ne hcC.1.2
    intro hEq
    have : f e = inner := by rw [← hEq]; exact hcC.2
    have hfe : f e = outer := heT.2
    linarith only [this, hfe, hio]
  have hafter : ∀ u ∈ Icc c e, inner ≤ f u := by
    intro u hu
    by_cases huc : u = c
    · rw [huc, hcC.2]
    by_contra hnot
    have hfu : f u < inner := lt_of_not_ge hnot
    have hue : u < e := by
      apply lt_of_le_of_ne hu.2
      intro heq
      rw [heq, heT.2] at hfu
      linarith
    have huc' : c < u := lt_of_le_of_ne hu.1 (Ne.symm huc)
    have huec : ContinuousOn f (Icc u e) := hf.mono
      (Icc_subset_Icc (ha.1.trans (hcC.1.1.trans huc'.le)) heT.1.2)
    obtain ⟨v, hv, hfv⟩ := (intermediate_value_Icc hue.le huec)
      (show inner ∈ Icc (f u) (f e) by exact ⟨hfu.le, (heT.2 ▸ hio.le)⟩)
    have hvC : v ∈ C := ⟨⟨(hcC.1.1.trans huc'.le).trans hv.1, hv.2⟩, hfv⟩
    exact (not_le.mpr (huc'.trans_le hv.1)) (le_csSup hCb hvC)
  refine ⟨b, c, e, hb.1, hb.2, hcC.1.1, hce, heT.1.2, hfb, hcC.2, heT.2, ?_⟩
  intro u hu
  refine ⟨hafter u hu, ?_⟩
  by_cases hue : u = e
  · rw [hue, heT.2]
  · exact (hbefore u ⟨hcC.1.1.trans hu.1, lt_of_le_of_ne hu.2 hue⟩).le

end HigherDimLQGMetric
