import HigherDimLQGMetric.Freq.BadCover

/-! Last and first visits to the two small endpoint balls. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The final crossing of a scalar level before a path ends above it. -/
theorem s4c_last_level {f : ℝ → ℝ} {L q : ℝ}
    (hf : ContinuousOn f (Icc 0 L)) (hL0 : 0 ≤ L)
    (h0 : f 0 < q) (hL : q < f L) :
    ∃ a ∈ Ioo (0 : ℝ) L, f a = q ∧ ∀ t ∈ Ioc a L, q < f t := by
  obtain ⟨a₀, ha₀, hfa₀⟩ := (intermediate_value_Icc hL0 hf)
    (show q ∈ Icc (f 0) (f L) from ⟨h0.le, hL.le⟩)
  let T : Set ℝ := Icc 0 L ∩ f ⁻¹' {q}
  have hTc : IsClosed T := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hTne : T.Nonempty := ⟨a₀, ha₀, hfa₀⟩
  have hTb : BddAbove T := ⟨L, fun t ht => ht.1.2⟩
  let a := sSup T
  have haT : a ∈ T := hTc.csSup_mem hTne hTb
  have ha0 : 0 < a := by
    apply lt_of_le_of_ne haT.1.1
    intro heq
    have : f 0 = q := by rw [heq]; exact haT.2
    linarith
  have haL : a < L := by
    apply lt_of_le_of_ne haT.1.2
    intro heq
    have : f L = q := by rw [← heq]; exact haT.2
    linarith
  refine ⟨a, ⟨ha0, haL⟩, haT.2, ?_⟩
  intro t ht
  by_contra hn
  have hft : f t ≤ q := le_of_not_gt hn
  by_cases heq : f t = q
  · have htT : t ∈ T := ⟨⟨haT.1.1.trans ht.1.le, ht.2⟩, heq⟩
    exact (not_le.mpr ht.1) (le_csSup hTb htT)
  · have hft' : f t < q := lt_of_le_of_ne hft heq
    have htf : ContinuousOn f (Icc t L) :=
      hf.mono (Icc_subset_Icc (haT.1.1.trans ht.1.le) le_rfl)
    obtain ⟨v, hv, hfv⟩ := (intermediate_value_Icc ht.2 htf)
      (show q ∈ Icc (f t) (f L) from ⟨hft'.le, hL.le⟩)
    have hvT : v ∈ T := ⟨⟨haT.1.1.trans (ht.1.le.trans hv.1), hv.2⟩, hfv⟩
    exact (not_le.mpr (ht.1.trans_le hv.1)) (le_csSup hTb hvT)

/-- The first crossing of a scalar level when the path starts above it and
ends below it. -/
theorem s4c_first_level {f : ℝ → ℝ} {L a q : ℝ}
    (hf : ContinuousOn f (Icc a L)) (haL : a < L)
    (ha : q < f a) (hL : f L < q) :
    ∃ b ∈ Ioc a L, f b = q ∧ ∀ t ∈ Ico a b, q < f t := by
  obtain ⟨b₀, hb₀, hfb₀⟩ := (intermediate_value_Icc' haL.le hf)
    (show q ∈ Icc (f L) (f a) from ⟨hL.le, ha.le⟩)
  let T : Set ℝ := Icc a L ∩ f ⁻¹' {q}
  have hTc : IsClosed T := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hTne : T.Nonempty := ⟨b₀, hb₀, hfb₀⟩
  have hTb : BddBelow T := ⟨a, fun t ht => ht.1.1⟩
  let b := sInf T
  have hbT : b ∈ T := hTc.csInf_mem hTne hTb
  have hab : a < b := by
    apply lt_of_le_of_ne hbT.1.1
    intro heq
    have : f a = q := by rw [heq]; exact hbT.2
    linarith
  refine ⟨b, ⟨hab, hbT.1.2⟩, hbT.2, ?_⟩
  intro t ht
  by_contra hn
  have hft : f t ≤ q := le_of_not_gt hn
  by_cases heq : f t = q
  · have htT : t ∈ T := ⟨⟨ht.1, ht.2.le.trans hbT.1.2⟩, heq⟩
    exact (not_le.mpr ht.2) (csInf_le hTb htT)
  · have hft' : f t < q := lt_of_le_of_ne hft heq
    have hatf : ContinuousOn f (Icc a t) :=
      hf.mono (Icc_subset_Icc le_rfl (ht.2.le.trans hbT.1.2))
    obtain ⟨v, hv, hfv⟩ := (intermediate_value_Icc' ht.1 hatf)
      (show q ∈ Icc (f t) (f a) from ⟨hft'.le, ha.le⟩)
    have hvT : v ∈ T := ⟨⟨hv.1, hv.2.trans (ht.2.le.trans hbT.1.2)⟩, hfv⟩
    exact (not_le.mpr (hv.2.trans_lt ht.2)) (csInf_le hTb hvT)

/-- A path between separated endpoints has a last exit from the first small
ball and a later first entrance to the second small ball. -/
theorem s4c_macro_times (P : ℝ → Rd d) (x y : Rd d)
    {L q : ℝ} (hL : 0 ≤ L) (hq : 0 < q)
    (hPc : ContinuousOn P (Icc 0 L)) (hP0 : P 0 = x) (hPL : P L = y)
    (hxy : 2 * q < ‖x - y‖) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b ≤ L ∧
      ‖P a - x‖ = q ∧ ‖P b - y‖ = q ∧
      (∀ s ∈ Ioc a L, q < ‖P s - x‖) ∧
      (∀ s ∈ Ico a b, q < ‖P s - y‖) := by
  have hXc : ContinuousOn (fun s => ‖P s - x‖) (Icc 0 L) :=
    (hPc.sub continuousOn_const).norm
  have hX0 : ‖P 0 - x‖ < q := by rw [hP0, sub_self, norm_zero]; exact hq
  have hXL : q < ‖P L - x‖ := by
    rw [hPL]
    rw [norm_sub_rev]
    linarith
  obtain ⟨a, ha, hPa, hafterX⟩ := s4c_last_level hXc hL hX0 hXL
  have hYc : ContinuousOn (fun s => ‖P s - y‖) (Icc a L) :=
    ((hPc.mono (Icc_subset_Icc ha.1.le le_rfl)).sub continuousOn_const).norm
  have hYa : q < ‖P a - y‖ := by
    have htri : ‖x - y‖ ≤ ‖x - P a‖ + ‖P a - y‖ := by
      calc
        ‖x - y‖ = ‖(x - P a) + (P a - y)‖ := by congr 1; abel
        _ ≤ ‖x - P a‖ + ‖P a - y‖ := norm_add_le _ _
    rw [show ‖x - P a‖ = ‖P a - x‖ from norm_sub_rev _ _, hPa] at htri
    linarith
  have hYL : ‖P L - y‖ < q := by rw [hPL, sub_self, norm_zero]; exact hq
  obtain ⟨b, hb, hPb, hbeforeY⟩ := s4c_first_level hYc ha.2 hYa hYL
  exact ⟨a, b, ha.1, hb.1, hb.2, hPa, hPb, hafterX, hbeforeY⟩

end HigherDimLQGMetric
