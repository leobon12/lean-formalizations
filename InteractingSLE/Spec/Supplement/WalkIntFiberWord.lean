/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFiberMatch

/-!
# The finite component word from physical collars

The remaining word data use physical retained-boundary landings and only
the central coordinate of each selected ordinary incident side. All real
transition intervals and boundary lift comparisons follow from the proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntFiber

open WalkBdry WalkNorm WalkMean GW3Between

/-- The remaining finite word and physical incident-side correspondences.
This is a distinct conditional predicate, not a replacement source theorem. -/
def IsNormChartPhysical (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (r : ExplState × ExplState) (C : Set ℂ) (t : Chart × (ℝ → ℝ) × Finset ℝ)
    (F : LandingHullFamily t.1) : Prop :=
  IsComponentChart (physOf (boundaryWalkSpec b jumps (-(π / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (π / 2) false) r.2) C t.1 ∧
    IsPiecewiseConstantBoundaryData t.2.1 t.2.2 ∧
    IsComponentBoundaryData κ b (ordOf r.1) (ordOf r.2) t.1.2.1 t.2.1 t.2.2 ∧
    ∃ Eℝ : Set ℝ, Eℝ.Finite ∧ ∀ x : ℝ, x ∉ Eℝ →
      (0 < x → ∃ i, x ∈ F.interval i ∧
        ((IsPiecePhysicalMatch r.1 r.2 true t.1 (F.model i) x ∧
          t.2.1 x = -bigLambda κ) ∨
          WalkIntGerm.IsRealIncidentMatch r.1 r.2 b jumps t.1 (F.model i) x (t.2.1 x))) ∧
      (x < 0 → ∃ i, x ∈ F.interval i ∧
        ((IsPiecePhysicalMatch r.2 r.1 false t.1 (F.model i) x ∧
          t.2.1 x = bigLambda κ) ∨
          WalkIntGerm.IsRealIncidentMatch r.1 r.2 b jumps t.1 (F.model i) x (t.2.1 x)))

/-- The physical collar hypotheses supply every transition interval of
the previous incident-word predicate. Prefix facts are already deterministic. -/
theorem isNormChartIncident_of_physical {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {r : ExplState × ExplState} {C : Set ℂ} {t : Chart × (ℝ → ℝ) × Finset ℝ}
    {F : LandingHullFamily t.1} (hCo : IsOpen C) (hCH : C ⊆ H)
    (hPR : PrefixBoundaryFacts r.1) (hPL : PrefixBoundaryFacts r.2)
    (h : IsNormChartPhysical κ b jumps r C t F) :
    ∃ hc : t.1.IsConformal,
      WalkIntGerm.IsNormChartIncident κ b jumps r C t (F.incidentFamily hc) := by
  obtain ⟨hchart, hb, hword, E, hE, hm⟩ := h
  have hc := GW3Law.isConformal_of_isComponentChart hchart hCo hCH
  have hwall : ((physOf (boundaryWalkSpec b jumps (-(π / 2)) true) r.1 ∪
      physOf (boundaryWalkSpec b jumps (π / 2) false) r.2) ∩ H) =
        wsetOf r.1 ∪ wsetOf r.2 := by
    rw [union_inter_distrib_right, physOf_inter_H, physOf_inter_H]
  refine ⟨hc, hchart, hb, hword, E, hE, fun x hx => ⟨fun hp => ?_, fun hn => ?_⟩⟩
  · obtain ⟨i, hi, hmatch⟩ := (hm x hx).1 hp
    rcases hmatch with ⟨hpiece, hval⟩ | hreal
    · exact ⟨i, hi, Or.inl ⟨isPieceIncidentMatch_of_physical hchart hCo hCH
        hwall hPR (ne_of_gt hp) hpiece, hval⟩⟩
    · exact ⟨i, hi, Or.inr hreal⟩
  · obtain ⟨i, hi, hmatch⟩ := (hm x hx).2 hn
    rcases hmatch with ⟨hpiece, hval⟩ | hreal
    · exact ⟨i, hi, Or.inl ⟨isPieceIncidentMatch_of_physical hchart hCo hCH
        (hwall.trans (union_comm _ _)) hPL (ne_of_lt hn) hpiece, hval⟩⟩
    · exact ⟨i, hi, Or.inr hreal⟩

/-- A single integer normalizes all matches, with no real transition
interval or lift-comparison hypothesis in the physical word input. -/
theorem exists_isNormChartLoc_of_physical {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {r : ExplState × ExplState} {C : Set ℂ} {t : Chart × (ℝ → ℝ) × Finset ℝ}
    {F : LandingHullFamily t.1} (hCo : IsOpen C) (hCH : C ⊆ H)
    (hPR : PrefixBoundaryFacts r.1) (hPL : PrefixBoundaryFacts r.2)
    (h : IsNormChartPhysical κ b jumps r C t F) :
    ∃ n : ℤ, IsNormChartLoc κ b jumps r C t n := by
  obtain ⟨hc, hinc⟩ := isNormChartIncident_of_physical hCo hCH hPR hPL h
  exact WalkIntGerm.exists_isNormChartLoc_of_incident hCo hCH hinc

end InteractingSLE.Theorem14.WalkIntFiber
