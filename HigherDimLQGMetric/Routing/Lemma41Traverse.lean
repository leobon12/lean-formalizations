import HigherDimLQGMetric.Routing.Lemma41Order

/-! A simple curve containing a marked arc traverses it in one of the two orders. -/

set_option autoImplicit false

noncomputable section

open Set Topology

namespace HigherDimLQGMetric

def TraversesArcOn {X : Type*} (Q : ℝ → X) (ℓ : ℝ) (σ : ℝ → X) : Prop :=
  ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ ℓ ∧ Q s = σ 0 ∧ Q t = σ 1 ∧
    ∀ r ∈ Icc (0 : ℝ) 1, ∃ q ∈ Icc s t, Q q = σ r

theorem lemma41_arc_range_forces_traversal {X : Type*}
    [TopologicalSpace X] [T2Space X] {ℓ : ℝ}
    (Q : ℝ → X) (hQc : ContinuousOn Q (Icc 0 ℓ))
    (hQi : InjOn Q (Icc 0 ℓ)) (σ : ℝ → X)
    (hσc : ContinuousOn σ (Icc 0 1)) (hσi : InjOn σ (Icc 0 1))
    (hσrange : σ '' Icc (0 : ℝ) 1 ⊆ Q '' Icc 0 ℓ) :
    TraversesArcOn Q ℓ σ ∨ TraversesArcOn Q ℓ (fun r => σ (1 - r)) := by
  obtain ⟨f, _, hmono, hQf⟩ :=
    lemma41_arc_order_on_interval Q hQc hQi σ hσc hσi hσrange
  let z : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let o : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  rcases hmono with hm | ha
  · left
    refine ⟨f z, f o, (f z).property.1, hm.monotone (show z ≤ o from by change (0 : ℝ) ≤ 1; norm_num),
      (f o).property.2, ?_, ?_, ?_⟩
    · simpa only [z] using hQf z
    · simpa only [o] using hQf o
    · intro r hr
      let a : Icc (0 : ℝ) 1 := ⟨r, hr⟩
      refine ⟨f a, ⟨hm.monotone ?_, hm.monotone ?_⟩, ?_⟩
      · exact (show z ≤ a from Subtype.coe_le_coe.mp hr.1)
      · exact (show a ≤ o from Subtype.coe_le_coe.mp hr.2)
      · exact hQf a
  · right
    refine ⟨f o, f z, (f o).property.1, ha.antitone (show z ≤ o from by change (0 : ℝ) ≤ 1; norm_num),
      (f z).property.2, ?_, ?_, ?_⟩
    · simpa only [o, sub_zero] using hQf o
    · simpa only [z, sub_self] using hQf z
    · intro r hr
      let a : Icc (0 : ℝ) 1 := ⟨1 - r, by constructor <;> linarith [hr.1, hr.2]⟩
      refine ⟨f a, ⟨ha.antitone ?_, ha.antitone ?_⟩, ?_⟩
      · exact (show a ≤ o from Subtype.coe_le_coe.mp a.property.2)
      · exact (show z ≤ a from Subtype.coe_le_coe.mp a.property.1)
      · simpa only [a, sub_sub_cancel_left] using hQf a

end HigherDimLQGMetric
