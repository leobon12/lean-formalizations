/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntOrientArc
import InteractingSLE.Spec.Exist.StagedLaw2Drv

/-!
# A rational cutoff with the same traversal direction

Local unsigned agreement of two arcs and their contact order give a short
right prefix whose later points occur strictly later on the left arc.
The left cutoff endpoint is excluded by a physical open neighborhood.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntOrient

/-- The strict own-time direction field, with a rational right cutoff,
follows from contact order and unsigned local trace containment. -/
theorem exists_rational_same_direction_cut {γ δ : ℝ → ℂ} {TR τL tR tL r : ℝ}
    (htR : 0 ≤ tR) (htRT : tR < TR) (htL : tL ∈ Icc 0 τL) (htLτ : tL < τL)
    (hγ : ContinuousAt γ tR) (hδ : InjOn δ (Icc 0 τL)) (hp : γ tR = δ tL)
    (hr : 0 < r)
    (hlocal : ∀ s ∈ Icc 0 TR, γ s ∈ ball (γ tR) r →
      ∃ s' ∈ Icc 0 τL, γ s = δ s')
    (horder : ∀ s ∈ Icc 0 TR, ∀ s' ∈ Icc 0 τL,
      γ s = δ s' → (tR < s ↔ tL < s')) :
    ∃ τR : ℚ≥0, tR < (τR : ℝ) ∧ (τR : ℝ) < TR ∧
      ∀ s ∈ Ioc tR (τR : ℝ), ∃ s' ∈ Ioo tL τL, γ s = δ s' := by
  have hne : γ tR ≠ δ τL := by
    intro heq
    exact (ne_of_lt htLτ) (hδ htL (right_mem_Icc.2 (htL.1.trans htL.2)) (hp.symm.trans heq))
  have hU : ball (γ tR) r \ {δ τL} ∈ 𝓝 (γ tR) :=
    (isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨mem_ball_self hr, hne⟩
  obtain ⟨ε, hε, hnear⟩ := Metric.mem_nhds_iff.1 (hγ.preimage_mem_nhds hU)
  obtain ⟨τR, htτ, hτ⟩ := Exist.StagedLaw.exists_rat_btwn_nnrat htR
    (lt_min htRT (lt_add_of_pos_right tR hε))
  refine ⟨τR, htτ, hτ.trans_le (min_le_left _ _), fun s hs => ?_⟩
  have hsT : s ∈ Icc 0 TR := ⟨htR.trans hs.1.le,
    hs.2.trans (hτ.le.trans (min_le_left _ _))⟩
  have hsd : dist s tR < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1.le)]
    exact sub_lt_iff_lt_add'.2 (hs.2.trans_lt (hτ.trans_le (min_le_right _ _)))
  obtain ⟨hsball, hsne⟩ := hnear hsd
  obtain ⟨s', hs', heq⟩ := hlocal s hsT hsball
  refine ⟨s', ⟨(horder s hsT s' hs' heq).1 hs.1, lt_of_le_of_ne hs'.2 ?_⟩, heq⟩
  intro hse
  exact hsne (heq.trans (congrArg δ hse))

end InteractingSLE.Theorem14.WalkIntOrient
