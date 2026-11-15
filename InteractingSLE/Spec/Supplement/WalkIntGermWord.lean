/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntGermMatch

/-!
# The component word from incident geometry

The remaining finite-word and boundary-correspondence data have no lift
comparison or common-integer field. Both kinds of inherited zero limits
and the common normalization integer are supplied by the proved adapters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntGerm

open WalkBdry WalkNorm WalkMean GW3Between

/-- The exact finite component word, and its incident ordinary/real
correspondences. Constructing these data remains the GW3 geometry input. -/
def IsNormChartIncident (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (r : ExplState × ExplState) (C : Set ℂ) (t : Chart × (ℝ → ℝ) × Finset ℝ)
    (F : IncidentHullFamily t.1) : Prop :=
  IsComponentChart (physOf (boundaryWalkSpec b jumps (-(π / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (π / 2) false) r.2) C t.1 ∧
    IsPiecewiseConstantBoundaryData t.2.1 t.2.2 ∧
    IsComponentBoundaryData κ b (ordOf r.1) (ordOf r.2) t.1.2.1 t.2.1 t.2.2 ∧
    ∃ Eℝ : Set ℝ, Eℝ.Finite ∧ ∀ x : ℝ, x ∉ Eℝ →
      (0 < x → ∃ i, x ∈ F.interval i ∧
        ((IsPieceIncidentMatch r.1 r.2 true t.1 (F.model i) x ∧
          t.2.1 x = -bigLambda κ) ∨
          IsRealIncidentMatch r.1 r.2 b jumps t.1 (F.model i) x (t.2.1 x))) ∧
      (x < 0 → ∃ i, x ∈ F.interval i ∧
        ((IsPieceIncidentMatch r.2 r.1 false t.1 (F.model i) x ∧
          t.2.1 x = bigLambda κ) ∨
          IsRealIncidentMatch r.1 r.2 b jumps t.1 (F.model i) x (t.2.1 x)))

/-- Supply all the inherited lift comparisons of the landed reference
predicate from incident intervals and raw real collars. -/
theorem isNormChartRef_of_incident {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {r : ExplState × ExplState} {C : Set ℂ} {t : Chart × (ℝ → ℝ) × Finset ℝ}
    {F : IncidentHullFamily t.1} (hc : t.1.IsConformal)
    (h : IsNormChartIncident κ b jumps r C t F) :
    WalkIntBridge.IsNormChartRef κ b jumps r C t (F.referenceFamily hc) := by
  obtain ⟨hchart, hb, hword, E, hE, hm⟩ := h
  refine ⟨hchart, hb, hword, E, hE, fun x hx => ⟨fun hp => ?_, fun hn => ?_⟩⟩
  · obtain ⟨i, hi, hm⟩ := (hm x hx).1 hp
    rcases hm with ⟨hpiece, hval⟩ | hreal
    · exact ⟨i, hi, Or.inl ⟨isPieceMatchRef_of_incident hc
        (F.normalized i) (F.dom_subset i) hpiece, hval⟩⟩
    · exact ⟨i, hi, Or.inr (isRealMatchRef_of_incident hc
        (F.normalized i) (F.dom_subset i) hreal)⟩
  · obtain ⟨i, hi, hm⟩ := (hm x hx).2 hn
    rcases hm with ⟨hpiece, hval⟩ | hreal
    · exact ⟨i, hi, Or.inl ⟨isPieceMatchRef_of_incident hc
        (F.normalized i) (F.dom_subset i) hpiece, hval⟩⟩
    · exact ⟨i, hi, Or.inr (isRealMatchRef_of_incident hc
        (F.normalized i) (F.dom_subset i) hreal)⟩

/-- One integer normalizes every ordinary and real boundary match of the
component. All transition-hull gaps and inherited zero limits are proved. -/
theorem exists_isNormChartLoc_of_incident {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {r : ExplState × ExplState} {C : Set ℂ} {t : Chart × (ℝ → ℝ) × Finset ℝ}
    {F : IncidentHullFamily t.1} (hCo : IsOpen C) (hCH : C ⊆ H)
    (h : IsNormChartIncident κ b jumps r C t F) :
    ∃ n : ℤ, IsNormChartLoc κ b jumps r C t n := by
  obtain ⟨hc, -⟩ := WalkIntBridge.hasDerivLift_of_isComponentChart h.1 hCo hCH
  exact WalkIntBridge.exists_isNormChartLoc_of_ref hCo hCH
    (isNormChartRef_of_incident hc h)

end InteractingSLE.Theorem14.WalkIntGerm
