/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntOrientCut

/-!
# WalkWords' traversal-direction field from walk chronology

The physical arcs use continuous boundary extensions at their starts.
Only their fresh points are identified with the launch charts' inverses.
No monotonicity of an own-time correspondence is an input to this theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntOrient

open GW1WalkChain WalkBdry

/-- Chronological physical arcs, full-walk contact order and unsigned
local agreement prove the exact same-direction field used in
`WalkWords.WalkPairArcDataStatement`, after choosing a shorter rational
right prefix. The histories are explicit; their construction for actual
runs remains separate from this deterministic orientation theorem. -/
theorem exists_walkPair_direction_of_histories {α β : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {AR AL : Set ℂ} {qR qL : ℂ}
    (hHistR : ArcHistory (α 0) AR qR) (hHistL : ArcHistory (β 0) AL qL)
    (hAR : AR ⊆ range α) (hAL : AL ⊆ range β)
    {γ δ : ℝ → ℂ} {TR tR tL r : ℝ} {τL : ℚ≥0}
    (htR : 0 < tR) (htRT : tR < TR)
    (htL : tL ∈ Icc 0 (τL : ℝ)) (htLτ : tL < (τL : ℝ))
    (hγ : ContinuousOn γ (Icc 0 TR)) (hinjR : InjOn γ (Icc 0 TR))
    (hδ : ContinuousOn δ (Icc 0 (τL : ℝ))) (hinjL : InjOn δ (Icc 0 (τL : ℝ)))
    (hR : γ '' Icc 0 TR ⊆ range α) (hL : δ '' Icc 0 (τL : ℝ) ⊆ range β)
    (hstartR : γ 0 = qR) (hstartL : δ 0 = qL)
    (hmeetR : ∀ t ∈ Icc 0 TR, γ t ∈ AR → t = 0)
    (hmeetL : ∀ t ∈ Icc 0 (τL : ℝ), δ t ∈ AL → t = 0)
    {pcR pcL : Piece} {ηR ηL : ℝ → ℂ}
    (heqR : ∀ s ∈ Icc tR TR, γ s = pcR.1.2.1 (ηR s))
    (heqL : ∀ s ∈ Icc tL (τL : ℝ), δ s = pcL.1.2.1 (ηL s))
    (hp : pcR.1.2.1 (ηR tR) = pcL.1.2.1 (ηL tL)) (hr : 0 < r)
    (hlocal : ∀ s ∈ Icc 0 TR, γ s ∈ ball (γ tR) r →
      ∃ s' ∈ Icc 0 (τL : ℝ), γ s = δ s') :
    ∃ τR : ℚ≥0, tR < ((τR : ℝ≥0) : ℝ) ∧ ((τR : ℝ≥0) : ℝ) < TR ∧
      ∀ s ∈ Ioc tR ((τR : ℝ≥0) : ℝ), ∃ s' ∈ Ioo tL ((τL : ℝ≥0) : ℝ),
        pcR.1.2.1 (ηR s) = pcL.1.2.1 (ηL s') := by
  have hmR := strictMonoOn_curveTime_of_history hα hHistR hAR
    (htR.le.trans htRT.le) hγ hinjR hR hstartR hmeetR
  have hmL := strictMonoOn_curveTime_of_history hβ hHistL hAL
    (htL.1.trans htL.2) hδ hinjL hL hstartL hmeetL
  have hp' : γ tR = δ tL :=
    (heqR tR ⟨le_rfl, htRT.le⟩).trans (hp.trans (heqL tL ⟨le_rfl, htLτ.le⟩).symm)
  obtain ⟨τR, htτ, hτT, hdir⟩ := exists_rational_same_direction_cut htR.le htRT htL htLτ
    (hγ.continuousAt (Icc_mem_nhds htR htRT)) hinjL hp' hr hlocal
    (fun s hs s' hs' hcontact => contact_order_on_arcs horder hR hL hmR hmL
      ⟨htR.le, htRT.le⟩ hs htL hs' hp' hcontact)
  refine ⟨τR, htτ, hτT, fun s hs => ?_⟩
  obtain ⟨s', hs', hcontact⟩ := hdir s hs
  exact ⟨s', hs', (heqR s ⟨hs.1.le, hs.2.trans hτT.le⟩).symm.trans
    (hcontact.trans (heqL s' ⟨hs'.1.le, hs'.2.le⟩))⟩

end InteractingSLE.Theorem14.WalkIntOrient
