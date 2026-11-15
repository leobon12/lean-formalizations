/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntPromoteMatch

/-!
# Cofinal intervals cover previously selected physical matches

The finite word and its designated physical side witnesses remain explicit
inputs. Interval membership follows by moving to a larger retained hull.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntPromote

open WalkBdry WalkNorm WalkMean WalkIntFill WalkIntFiber

/-- Physical witnesses need only refer to some retained index. Cofinal
coordinate coverage supplies an admissible interval at a later index. -/
theorem isNormChartPhysical_of_cofinal {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {r : ExplState × ExplState} {C : Set ℂ} {t : Chart × (ℝ → ℝ) × Finset ℝ}
    (G : RetainedBoundaryGeometry t.1 r.1 r.2)
    (hmono : Monotone (fun i => (G.pair i).raw))
    (hcover : ∀ (x : ℝ) (j : ℕ), ∃ i, j ≤ i ∧ x ∈ G.interval i)
    (hchart : IsComponentChart
      (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) r.2) C t.1)
    (hb : IsPiecewiseConstantBoundaryData t.2.1 t.2.2)
    (hword : IsComponentBoundaryData κ b (ordOf r.1) (ordOf r.2) t.1.2.1 t.2.1 t.2.2)
    {E : Set ℝ} (hE : E.Finite)
    (hMatch : ∀ x : ℝ, x ∉ E →
      (0 < x → ∃ j,
        ((IsPiecePhysicalMatch r.1 r.2 true t.1 (G.pair j).model x ∧
          t.2.1 x = -bigLambda κ) ∨
          WalkIntGerm.IsRealIncidentMatch r.1 r.2 b jumps t.1
            (G.pair j).model x (t.2.1 x))) ∧
      (x < 0 → ∃ j,
        ((IsPiecePhysicalMatch r.2 r.1 false t.1 (G.pair j).model x ∧
          t.2.1 x = bigLambda κ) ∨
          WalkIntGerm.IsRealIncidentMatch r.1 r.2 b jumps t.1
            (G.pair j).model x (t.2.1 x)))) :
    IsNormChartPhysical κ b jumps r C t G.landingFamily := by
  refine ⟨hchart, hb, hword, E, hE, fun x hx => ⟨fun hp => ?_, fun hn => ?_⟩⟩
  · obtain ⟨j, hj⟩ := (hMatch x hx).1 hp
    obtain ⟨i, hji, hi⟩ := hcover x j
    refine ⟨i, hi, ?_⟩
    rcases hj with ⟨hpiece, hvalue⟩ | hreal
    · exact Or.inl ⟨isPiecePhysicalMatch_of_hull_subset
        (retained_hull_subset (hmono hji)) hpiece, hvalue⟩
    · exact Or.inr (isRealIncidentMatch_retained (G.pair i) hreal)
  · obtain ⟨j, hj⟩ := (hMatch x hx).2 hn
    obtain ⟨i, hji, hi⟩ := hcover x j
    refine ⟨i, hi, ?_⟩
    rcases hj with ⟨hpiece, hvalue⟩ | hreal
    · exact Or.inl ⟨isPiecePhysicalMatch_of_hull_subset
        (retained_hull_subset (hmono hji)) hpiece, hvalue⟩
    · exact Or.inr (isRealIncidentMatch_retained (G.pair i) hreal)

end InteractingSLE.Theorem14.WalkIntPromote
