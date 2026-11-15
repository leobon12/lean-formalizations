/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronBounded

/-!
# The local chart leaf from the remaining cutoff and finite-word choices

Actual run chronology is proved in the preceding modules. This distinct
conditional helper keeps the remaining geometric cutoff choice hSelect
and finite-word witnesses hMatch fully explicit. No source leaf is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntRunChron

open WalkBdry WalkNorm WalkMean WalkIntFill WalkIntClosed WalkIntFiber WalkIntActive

/-- Cutoff placement and the existing finite physical word imply the
original local normalization conclusion with one common integer. -/
theorem exists_isNormChartLoc_of_initial_selection
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {r : ExplState × ExplState}
    {C : Set ℂ} {t : Chart × (ℝ → ℝ) × Finset ℝ} {α β : ℝ≥0 → ℂ}
    (hCo : IsOpen C) (hCH : C ⊆ H)
    (hchart : IsComponentChart
      (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2) C t.1)
    (hb : IsPiecewiseConstantBoundaryData t.2.1 t.2.2)
    (hword : IsComponentBoundaryData κ b (ordOf r.1) (ordOf r.2) t.1.2.1 t.2.1 t.2.2)
    (hPR : PrefixBoundaryFacts r.1) (hPL : PrefixBoundaryFacts r.2)
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    (hR : range α = physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
    (hL : range β = physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2)
    (hC : (t.1.dom : Set ℂ) ∈ betweenComponents
      (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2))
    (hSelect : ∀ x : ℝ, ∃ (J : ClosedPair r.1 r.2) (a b' : ℝ≥0),
      J.right.raw = (α '' Icc 0 a) ∩ H ∧ J.left.raw = (β '' Icc 0 b') ∩ H ∧
      (∀ u, α u = GW4Traverse.invExt t.1 (x : ℂ) → u < a) ∧
      (∀ v, β v = GW4Traverse.invExt t.1 (x : ℂ) → v < b') ∧
      (Bornology.IsBounded (t.1.dom : Set ℂ) → ∃ s q : ℝ≥0,
        a < s ∧ b' < q ∧ α s = β q ∧ α s ∈ closure (t.1.dom : Set ℂ)))
    {E : Set ℝ} (hE : E.Finite)
    (hMatch : ∀ x : ℝ, x ∉ E →
      (0 < x → ∃ J : RetainedPair r.1 r.2,
        (((Bornology.IsBounded (t.1.dom : Set ℂ) →
            Nonempty (BeforeExit J (t.1.dom : Set ℂ) α β)) ∧
          IsPiecePhysicalMatch r.1 r.2 true t.1 J.model x ∧
          t.2.1 x = -bigLambda κ) ∨
          WalkIntGerm.IsRealIncidentMatch r.1 r.2 b jumps t.1 J.model x (t.2.1 x))) ∧
      (x < 0 → ∃ J : RetainedPair r.1 r.2,
        (((Bornology.IsBounded (t.1.dom : Set ℂ) →
            Nonempty (BeforeExit J (t.1.dom : Set ℂ) α β)) ∧
          IsPiecePhysicalMatch r.2 r.1 false t.1 J.model x ∧
          t.2.1 x = bigLambda κ) ∨
          WalkIntGerm.IsRealIncidentMatch r.1 r.2 b jumps t.1 J.model x (t.2.1 x)))) :
    ∃ n : ℤ, IsNormChartLoc κ b jumps r C t n := by
  have hClosedPoint := closed_pointwise_of_initial_selection hα hβ hR hL hSelect
  exact WalkIntOrient.exists_isNormChartLoc_of_closed_pointwise hCo hCH hchart hb hword
    hPR hPL hα hβ horder hR hL hC hClosedPoint hE hMatch

end InteractingSLE.Theorem14.WalkIntRunChron
