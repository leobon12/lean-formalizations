/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntOrientSelection
import InteractingSLE.Spec.Supplement.WalkIntOrientWord
import InteractingSLE.Spec.Supplement.WalkIntOrientDirection
import InteractingSLE.Spec.Supplement.WalkIntClosedCoverage

/-!
# Completed-prefix selection reaches the original local chart leaf

Completed finite endpoints need no conversion back to live prefixes.
Existing live finite-word witnesses embed with identical physical models.
Admissible cofinality, active containment and canonical incident intervals
feed the unchanged one-integer physical-word theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntOrient

open WalkBdry WalkNorm WalkMean WalkIntFill WalkIntClosed WalkIntFiber WalkIntActive
open WalkIntNeighborhood WalkIntWall

/-- The original local normalization conclusion from completed pointwise
physical selection and the existing live finite-word witnesses. Both
remaining mathematical inputs are explicit; no source leaf is asserted
without them. -/
theorem exists_isNormChartLoc_of_closed_pointwise
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
    (hClosedPoint : ∀ x : ℝ, ∃ J : ClosedPair r.1 r.2, ∃ ρ : ℝ, 0 < ρ ∧
      (wsetOf r.1 ∪ wsetOf r.2) ∩ ball (GW4Traverse.invExt t.1 (x : ℂ)) ρ ⊆ J.raw ∧
      (Bornology.IsBounded (t.1.dom : Set ℂ) → ∃ s q : ℝ≥0,
        0 < s ∧ 0 < q ∧ α s = β q ∧
          Disjoint (closure J.right.raw) (α '' Ici s) ∧
          Disjoint (closure J.left.raw) (β '' Ici q) ∧ α s ∈ closure (t.1.dom : Set ℂ)))
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
  obtain ⟨pair, hmono, hTail, hLocal, hdom⟩ := exists_admissible_closed_family horder hClosedPoint
  have hc := GW3Law.isConformal_of_isComponentChart hchart hCo hCH
  obtain ⟨k, ρ, hρ, hroot⟩ := hLocal 0
  let Q : ℕ → ClosedPair r.1 r.2 := fun i => pair (i + k)
  have hmonoQ : Monotone (fun i => (Q i).raw) := fun i j hij =>
    hmono (Nat.add_le_add_right hij k)
  have hrootQ : (wsetOf r.1 ∪ wsetOf r.2) ∩
      ball (GW4Traverse.invExt t.1 (0 : ℂ)) ρ ⊆ (Q 0).raw := by
    simpa only [Q, Nat.zero_add, Complex.ofReal_zero] using hroot
  have hEntry := anchor_mem_interior_of_frontier_collar hchart hCo hc hρ
    (frontier_collar_of_ordinary_cover hα hβ hR hL hC hrootQ)
  have hActive (i : ℕ) : (t.1.dom : Set ℂ) ⊆ H \ fillH (Q i).raw := by
    by_cases hb : Bornology.IsBounded (t.1.dom : Set ℂ)
    · have hC' : (t.1.dom : Set ℂ) ∈ betweenComponents (range α) (range β) := by
        rw [hR, hL]
        exact hC
      exact active_closedPair_of_tail_separation (Q i) hα hβ horder hR hL hC'
        (hTail hb (i + k))
    · exact active_closedPair_of_unbounded (Q i) hC t.1.dom.isOpen hb
  have hInterior : ∀ y : ℝ, ∃ i, y ∈ interior (landingCoordinates t.1 (Q i).raw) := by
    intro y
    obtain ⟨i, ρ, hρ, hloc⟩ := hLocal y
    have hlocQ := hloc.trans (hmono (Nat.le_add_right i k))
    exact ⟨i, anchor_mem_interior_of_frontier_collar hchart hCo hc hρ
      (frontier_collar_of_ordinary_cover hα hβ hR hL hC hlocQ)⟩
  have hcover : ∀ (x : ℝ) (j : ℕ), ∃ i, j ≤ i ∧ x ∈ incidentInterval t.1 (Q i).raw 0 := by
    intro x j
    obtain ⟨i, hji, hi⟩ := exists_incidentInterval_cover_uIcc_ge t.1
      (fun i => (Q i).raw) hmonoQ 0 x j (fun y _ => hInterior y)
    exact ⟨i, hji, hi right_mem_uIcc⟩
  have hdomQ (J : RetainedPair r.1 r.2)
      (hgood : Bornology.IsBounded (t.1.dom : Set ℂ) →
        Nonempty (BeforeExit J (t.1.dom : Set ℂ) α β)) :
      ∃ i, J.model.hull ⊆ (Q i).model.hull := by
    obtain ⟨i, hi⟩ := hdom (ClosedPair.ofRetainedPair J) (fun hb =>
      (WalkIntEnvelope.beforeExit_iff_tail_separation J hα hβ hR hL).1 (hgood hb))
    have hsub : (ClosedPair.ofRetainedPair J).raw ⊆ (Q i).raw :=
      hi.trans (hmono (Nat.le_add_right i k))
    exact ⟨i, closed_hull_subset hsub⟩
  apply exists_isNormChartLoc_of_physical hCo hCH hPR hPL
  apply isNormChartPhysical_of_closed_family Q 0 hchart hCo hmonoQ hActive hEntry hcover hb hword hE
  intro x hx
  constructor
  · intro hp
    obtain ⟨J, hJ⟩ := (hMatch x hx).1 hp
    rcases hJ with ⟨hgood, hpiece, hvalue⟩ | hreal
    · obtain ⟨i, hi⟩ := hdomQ J hgood
      exact ⟨i, Or.inl ⟨WalkIntPromote.isPiecePhysicalMatch_of_hull_subset hi hpiece, hvalue⟩⟩
    · exact ⟨0, Or.inr (isRealIncidentMatch_closed (Q 0) hreal)⟩
  · intro hn
    obtain ⟨J, hJ⟩ := (hMatch x hx).2 hn
    rcases hJ with ⟨hgood, hpiece, hvalue⟩ | hreal
    · obtain ⟨i, hi⟩ := hdomQ J hgood
      exact ⟨i, Or.inl ⟨WalkIntPromote.isPiecePhysicalMatch_of_hull_subset hi hpiece, hvalue⟩⟩
    · exact ⟨0, Or.inr (isRealIncidentMatch_closed (Q 0) hreal)⟩

end InteractingSLE.Theorem14.WalkIntOrient
