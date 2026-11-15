/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntClosedLanding
import InteractingSLE.Spec.Supplement.WalkIntPromoteWord

/-!
# Finite-word witnesses in completed-prefix landing families

The physical match promotion theorem is already independent of the old
live-prefix type. This adapter supplies the completed hull inclusions and
real collars, then feeds the unchanged physical-word consumer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntOrient

open WalkBdry WalkNorm WalkMean WalkIntClosed WalkIntFiber WalkIntNeighborhood WalkIntCanon

/-- Raw inclusion implies hull inclusion for completed references too. -/
theorem closed_hull_subset {sR sL : ExplState} {J K : ClosedPair sR sL}
    (h : J.raw ⊆ K.raw) : J.model.hull ⊆ K.model.hull := by
  rw [J.filled, K.filled]
  exact fillH_mono h

/-- A surviving real collar may use any completed physical reference. -/
theorem isRealIncidentMatch_closed {sR sL : ExplState} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {c d : Chart} {B : HullModel d} {x bx : ℝ}
    (K : ClosedPair sR sL)
    (h : WalkIntGerm.IsRealIncidentMatch sR sL b jumps c B x bx) :
    WalkIntGerm.IsRealIncidentMatch sR sL b jumps c K.model x bx := by
  obtain ⟨a, r, _, ha, hr, hland, hgap, _, _, hbx⟩ := h
  exact ⟨a, r, K.raw, ha, hr, hland, hgap, K.raw_subset, K.filled, hbx⟩

/-- Cofinal canonical intervals transfer finite-word witnesses to the
existing physical-word predicate with completed-prefix references. -/
theorem isNormChartPhysical_of_closed_family
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {r : ExplState × ExplState}
    {C : Set ℂ} {t : Chart × (ℝ → ℝ) × Finset ℝ}
    (pair : ℕ → ClosedPair r.1 r.2) (anchor : ℝ)
    (hchart : IsComponentChart
      (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2) C t.1)
    (hCo : IsOpen C) (hmono : Monotone (fun i => (pair i).raw))
    (hActive : ∀ i, (t.1.dom : Set ℂ) ⊆ H \ fillH (pair i).raw)
    (hEntry : anchor ∈ interior (landingCoordinates t.1 (pair 0).raw))
    (hcover : ∀ (x : ℝ) (j : ℕ), ∃ i, j ≤ i ∧ x ∈ incidentInterval t.1 (pair i).raw anchor)
    (hb : IsPiecewiseConstantBoundaryData t.2.1 t.2.2)
    (hword : IsComponentBoundaryData κ b (ordOf r.1) (ordOf r.2) t.1.2.1 t.2.1 t.2.2)
    {E : Set ℝ} (hE : E.Finite)
    (hMatch : ∀ x : ℝ, x ∉ E →
      (0 < x → ∃ j, ((IsPiecePhysicalMatch r.1 r.2 true t.1 (pair j).model x ∧
        t.2.1 x = -bigLambda κ) ∨
        WalkIntGerm.IsRealIncidentMatch r.1 r.2 b jumps t.1 (pair j).model x (t.2.1 x))) ∧
      (x < 0 → ∃ j, ((IsPiecePhysicalMatch r.2 r.1 false t.1 (pair j).model x ∧
        t.2.1 x = bigLambda κ) ∨
        WalkIntGerm.IsRealIncidentMatch r.1 r.2 b jumps t.1 (pair j).model x (t.2.1 x)))) :
    IsNormChartPhysical κ b jumps r C t
      (closedLandingFamily pair anchor hchart hCo (fun i => hmono (Nat.zero_le i)) hActive hEntry) := by
  refine ⟨hchart, hb, hword, E, hE, fun x hx => ⟨fun hp => ?_, fun hn => ?_⟩⟩
  · obtain ⟨j, hj⟩ := (hMatch x hx).1 hp
    obtain ⟨i, hji, hi⟩ := hcover x j
    refine ⟨i, hi, ?_⟩
    rcases hj with ⟨hpiece, hvalue⟩ | hreal
    · exact Or.inl ⟨WalkIntPromote.isPiecePhysicalMatch_of_hull_subset
        (closed_hull_subset (hmono hji)) hpiece, hvalue⟩
    · exact Or.inr (isRealIncidentMatch_closed (pair i) hreal)
  · obtain ⟨j, hj⟩ := (hMatch x hx).2 hn
    obtain ⟨i, hji, hi⟩ := hcover x j
    refine ⟨i, hi, ?_⟩
    rcases hj with ⟨hpiece, hvalue⟩ | hreal
    · exact Or.inl ⟨WalkIntPromote.isPiecePhysicalMatch_of_hull_subset
        (closed_hull_subset (hmono hji)) hpiece, hvalue⟩
    · exact Or.inr (isRealIncidentMatch_closed (pair i) hreal)

end InteractingSLE.Theorem14.WalkIntOrient
