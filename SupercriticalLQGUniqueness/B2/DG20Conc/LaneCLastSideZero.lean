import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSideDetourTrace
import Mathlib.Topology.Order.IntermediateValue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_exists_last_zero_nonneg
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a = 0) (hb : 0 ≤ f b) :
    ∃ c ∈ Icc a b, f c = 0 ∧
      ∀ t ∈ Icc c b, 0 ≤ f t := by
  let Z : Set ℝ := Icc a b ∩ f ⁻¹' {0}
  have hZc : IsCompact Z :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      inter_subset_left
  have hZne : Z.Nonempty := ⟨a, ⟨⟨le_rfl, hab⟩, ha⟩⟩
  obtain ⟨c, hc, hmax⟩ := hZc.exists_isGreatest hZne
  refine ⟨c, hc.1, hc.2, ?_⟩
  intro t ht
  by_cases htc : t = c
  · rw [htc, hc.2]
  by_contra hneg
  have htc' : c < t := lt_of_le_of_ne ht.1 (Ne.symm htc)
  have hft : f t ≤ 0 := le_of_not_ge hneg
  obtain ⟨u, hu, hfu⟩ : ∃ u ∈ Icc t b, f u = 0 :=
    intermediate_value_Icc ht.2
      (hf.mono (Icc_subset_Icc (hc.1.1.trans ht.1) le_rfl))
      ⟨hft, hb⟩
  have huZ : u ∈ Z := ⟨⟨hc.1.1.trans (ht.1.trans hu.1), hu.2⟩, hfu⟩
  exact (not_le_of_gt (htc'.trans_le hu.1)) (hmax huZ)

 

theorem laneC_exists_first_zero_nonneg
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (ha : 0 ≤ f a) (hb : f b = 0) :
    ∃ c ∈ Icc a b, f c = 0 ∧
      ∀ t ∈ Icc a c, 0 ≤ f t := by
  let Z : Set ℝ := Icc a b ∩ f ⁻¹' {0}
  have hZc : IsCompact Z :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      inter_subset_left
  have hZne : Z.Nonempty := ⟨b, ⟨⟨hab, le_rfl⟩, hb⟩⟩
  obtain ⟨c, hc, hmin⟩ := hZc.exists_isLeast hZne
  refine ⟨c, hc.1, hc.2, ?_⟩
  intro t ht
  by_cases htc : t = c
  · rw [htc, hc.2]
  by_contra hneg
  have htc' : t < c := lt_of_le_of_ne ht.2 htc
  have hft : f t ≤ 0 := le_of_not_ge hneg
  obtain ⟨u, hu, hfu⟩ : ∃ u ∈ Icc a t, f u = 0 :=
    intermediate_value_Icc' ht.1
      (hf.mono (Icc_subset_Icc le_rfl (ht.2.trans hc.1.2)))
      ⟨hft, ha⟩
  have huZ : u ∈ Z := ⟨⟨hu.1, (hu.2.trans ht.2).trans hc.1.2⟩, hfu⟩
  exact (not_le_of_gt (hu.2.trans_lt htc')) (hmin huZ)

end SupercriticalLQGUniqueness.B2.DG20Conc
