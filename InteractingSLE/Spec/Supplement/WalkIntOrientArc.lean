/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntOrientHistory

/-!
# Chronological ordinary arcs inherit the full walks' contact order

The start and no-return conditions of an appended arc determine its
orientation. Contact order of the two full walks therefore holds in the
own-time parameters of the two ordinary pieces.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntOrient

open GW1WalkChain

/-- Chronology determines the orientation of an appended own-time arc. -/
theorem strictMonoOn_curveTime_of_history {α : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) {A : Set ℂ} {q : ℂ}
    (hHist : ArcHistory (α 0) A q) (hA : A ⊆ range α)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b))
    (hrange : γ '' Icc a b ⊆ range α) (hstart : γ a = q)
    (hmeet : ∀ t ∈ Icc a b, γ t ∈ A → t = a) :
    StrictMonoOn (fun t => curveTime α (γ t)) (Icc a b) := by
  obtain ⟨c, hcarrier, hq⟩ := arcHistory_endpoint_initial_segment hα hHist hA
  exact strictMonoOn_curveTime_of_initial_segment hα hab hγ hinj hrange
    (hstart.trans hq) (fun t ht hz => hmeet t ht (hcarrier ▸ hz))

/-- Ordered contacts of the full walks give ordered own-time contacts
on any two arcs whose inverse parameters are increasing. -/
theorem contact_order_on_arcs {α β : ℝ≥0 → ℂ}
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {γ δ : ℝ → ℂ} {a b c d : ℝ}
    (hR : γ '' Icc a b ⊆ range α) (hL : δ '' Icc c d ⊆ range β)
    (hmR : StrictMonoOn (fun s => curveTime α (γ s)) (Icc a b))
    (hmL : StrictMonoOn (fun s => curveTime β (δ s)) (Icc c d))
    {s s' t t' : ℝ} (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b)
    (ht : t ∈ Icc c d) (ht' : t' ∈ Icc c d)
    (hp : γ s = δ t) (hp' : γ s' = δ t') : (s < s' ↔ t < t') := by
  have hcontact := horder (curveTime α (γ s)) (curveTime α (γ s'))
    (curveTime β (δ t)) (curveTime β (δ t'))
    ((apply_curveTime (hR ⟨s, hs, rfl⟩)).trans
      (hp.trans (apply_curveTime (hL ⟨t, ht, rfl⟩)).symm))
    ((apply_curveTime (hR ⟨s', hs', rfl⟩)).trans
      (hp'.trans (apply_curveTime (hL ⟨t', ht', rfl⟩)).symm))
  exact (hmR.lt_iff_lt hs hs').symm.trans (hcontact.trans (hmL.lt_iff_lt ht ht'))

end InteractingSLE.Theorem14.WalkIntOrient
