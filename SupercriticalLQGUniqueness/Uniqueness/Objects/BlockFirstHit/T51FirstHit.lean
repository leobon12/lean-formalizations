import LQGMetric.Topo.RectCross




 





set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockFirstHit

theorem first_inner_hit_prefix
    {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b))
    {c : ℂ} {r₁ r₂ : ℝ} (hr : r₁ < r₂)
    (ha : dist (P a) c = r₂) (hb : dist (P b) c ≤ r₁)
    (hball : MapsTo P (Icc a b) (closedBall c r₂)) :
    ∃ t : ℝ, a ≤ t ∧ t ≤ b ∧ P t ∈ sphere c r₁ ∧
      MapsTo P (Icc a t) (closedBall c r₂ \ ball c r₁) := by
  let f : ℝ → ℝ := fun u => dist (P u) c
  have hf : ContinuousOn f (Icc a b) :=
    (continuous_id.dist continuous_const).comp_continuousOn hP
  let S : Set ℝ := Icc a b ∩ f ⁻¹' {r₁}
  have hSc : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hab hf
      ⟨hb, by dsimp [f]; rw [ha]; exact hr.le⟩
    exact ⟨t, ht, hft⟩
  have hSb : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  let t := sInf S
  have htS : t ∈ S := hSc.csInf_mem hSne hSb
  refine ⟨t, htS.1.1, htS.1.2, mem_sphere.mpr htS.2, ?_⟩
  intro u hu
  have huab : u ∈ Icc a b := ⟨hu.1, hu.2.trans htS.1.2⟩
  have hle : r₁ ≤ f u := by
    by_contra hnot
    have hlt : f u < r₁ := lt_of_not_ge hnot
    obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc' hu.1
      (hf.mono (Icc_subset_Icc le_rfl huab.2))
      ⟨hlt.le, by dsimp [f]; rw [ha]; exact hr.le⟩
    have hvS : v ∈ S := ⟨⟨hv.1, hv.2.trans huab.2⟩, hfv⟩
    have htv : t ≤ v := csInf_le hSb hvS
    have hvu : v ≤ u := hv.2
    have hutu : u ≤ t := hu.2
    have : u = t := le_antisymm hutu (htv.trans hvu)
    subst u
    exact (lt_irrefl r₁) (htS.2 ▸ hlt)
  exact ⟨hball huab, fun hbad => (not_lt_of_ge hle) (mem_ball.mp hbad)⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockFirstHit
