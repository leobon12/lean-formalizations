/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinCompP38
import InteractingSLE.Spec.Supplement.SBLemmaS2

/-!
# SB2(1)'s cusp points: left-side approaches are one-sided

Packet PROVE-T14-SB2FIN, ruling R84. The second half of the route to the field `cusp` of `IsRelConfigJC`: near a
post-entrance point `p = β'(t')` of the S1 witness (`t_L < t' < t`), an approach that eventually lies on the open left
side of `β'` and off the physical filling `K = fill β'([0, t])` lies eventually in `freeNear (fill A) K p ρ` for some
`ρ > 0`. The component of the approach point in `(ℍ ∖ K) ∩ B(p, ρ)` misses `range β'` (`β'([0, t])` is in `K` or real,
and `β'([t, ∞))` stays at positive distance from `p`), so it stays on the left side; there the left side of `β'` near a
later point is in `D_A` (`SB.later_leftSide_free`, Lemma S2's "no second swallowed portion").

* **`eventually_freeNear_of_leftSide`**.

The remaining half (not formalized): every point of the relative hull image left of the tip coordinate is reached from
the lift's left side, and the left sides correspond under the chart inverse (handoff).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B (IsProperCurve leftSide rightSide closedRightSide)

namespace InteractingSLE.Theorem14.SB.FinRel

/-- **A left-side approach to a later witness point is one-sided.** -/
theorem eventually_freeNear_of_leftSide {p₀ : ℝ → ℂ} (hp : ContinuousOn p₀ (Icc 0 1)) (hp0 : p₀ 0 = 0)
    {β' : ℝ≥0 → ℂ} (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p₀ '' Icc 0 1 ⊆ closedRightSide β')
    {tL t' t : ℝ≥0} (htL : β' tL = realMin (p₀ '' Icc 0 1)) (ht' : tL < t') (ht't : t' < t)
    {α : Type*} {l : Filter α} {f : α → ℂ} (hf : Tendsto f l (𝓝 (β' t')))
    (hfL : ∀ᶠ ζ in l, f ζ ∈ leftSide β' ∧ f ζ ∈ H \ fillH (β' '' Icc 0 t)) :
    ∃ ρ > 0, ∀ᶠ ζ in l, f ζ ∈ freeNear (fillH (p₀ '' Icc 0 1)) (fillH (β' '' Icc 0 t)) (β' t') ρ := by
  set p := β' t' with hpdef
  obtain ⟨ε, hε, hfree⟩ := SB.later_leftSide_free hp hp0 hβ' hβ'0 hA htL ht'
  -- the future of the witness stays away from `p`
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hβ'.2.2.2.eventually (eventually_gt_atTop (‖p‖ + 1)))
  have hcpt : IsCompact (β' '' Icc t (max t T)) := isCompact_Icc.image hβ'.1
  have hpn : p ∉ β' '' Icc t (max t T) := by
    rintro ⟨r, hr, hre⟩
    have := hβ'.2.1 hre
    rw [this] at hr
    exact absurd hr.1 (not_le.2 ht't)
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1 hcpt.isClosed.isOpen_compl p hpn
  set ρ := min ε (min δ 1) with hρdef
  have hρ : 0 < ρ := lt_min hε (lt_min hδ one_pos)
  have hfar : ∀ r : ℝ≥0, t ≤ r → β' r ∉ ball p ρ := by
    intro r hr hb
    rcases le_total r (max t T) with hrT | hrT
    · exact hδb (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hb) ⟨r, ⟨hr, hrT⟩, rfl⟩
    · have h1 := hT r (le_trans (le_max_right _ _) hrT)
      have h2 : dist (β' r) p < 1 := lt_of_lt_of_le (mem_ball.1 hb) ((min_le_right _ _).trans (min_le_right _ _))
      have h3 := norm_le_norm_add_norm_sub' (β' r) p
      rw [dist_eq_norm] at h2
      linarith
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hfL, hf (ball_mem_nhds p hρ)] with ζ ⟨hζL, hζK⟩ hζb
  refine ⟨⟨hζK, hζb⟩, Set.disjoint_left.2 fun z hzC hzA => ?_⟩
  set U := (H \ fillH (β' '' Icc 0 t)) ∩ ball p ρ with hUdef
  -- the component misses the witness
  have hUγ : U ⊆ H \ range β' := by
    rintro z ⟨hzK, hzb⟩
    refine ⟨hzK.1, ?_⟩
    rintro ⟨r, rfl⟩
    rcases le_or_gt r t with hr | hr
    · exact hzK.2 ⟨hzK.1, Or.inl (subset_closure ⟨r, ⟨zero_le, hr⟩, rfl⟩)⟩
    · exact hfar r hr.le hzb
  have hsplit : U ⊆ leftSide β' ∪ rightSide β' := fun z hz =>
    SB.mem_leftSide_or_mem_rightSide_of_mem_H hβ' hβ'0 (hUγ hz).1 (hUγ hz).2
  have hCL : connectedComponentIn U (f ζ) ⊆ leftSide β' :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union (SB.isOpen_leftSide' hβ')
      (SB.isOpen_rightSide' hβ') (Supp9B.disjoint_leftSide_rightSide hβ' (by rw [hβ'0]; rfl))
      ((connectedComponentIn_subset _ _).trans hsplit)
      ⟨f ζ, mem_connectedComponentIn ⟨hζK, hζb⟩, hζL⟩
  have hzU := connectedComponentIn_subset _ _ hzC
  have hzD := hfree z (ball_subset_ball (min_le_left _ _) hzU.2) (hCL hzC) hzU.1.1
  exact hzD.2 hzA

end InteractingSLE.Theorem14.SB.FinRel
