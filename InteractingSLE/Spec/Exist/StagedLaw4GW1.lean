/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# GW1's properness for the walks from `StagedPiecesRegular`

Packet PROVE-STAGEDLAW4 (ruling R51). `SB.GW1PieceProperStatement` (PROVE-T14-SB) and `SB.GW1ProperStatement` quantify
over every family satisfying the frozen `IsStagedHistory`, which does not force the later pieces to be continuous
curves (PROVE-T14-GW1P §5). With R51's hypothesis `StagedPiecesRegular` on the families they hold outright, without
Theorem 1.3: the deterministic run lemma `GW1P.closure_tipSet_inter_H_subset_run` (PROVE-T14-GW1P) applies to every
sample of the regularity event.

Main results (namespace `InteractingSLE.Theorem14.GW1P`):

* **`ae_closure_tipSet_inter_H_subset_of_stagedPiecesRegular`** — for any program, almost surely every recorded piece is
  relatively closed in `ℍ`;
* **`gw1PieceProperRegStatement`**, **`gw1ProperRegStatement`** — `SB.GW1PieceProperStatement` and
  `SB.GW1ProperStatement` with R51's added hypothesis (`GW1PieceProperRegStatement`, `GW1ProperRegStatement`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1P

/-- **Every recorded piece of a `StagedPiecesRegular` family is a.s. relatively closed in `ℍ`** (any program). -/
theorem ae_closure_tipSet_inter_H_subset_of_stagedPiecesRegular {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) :
    ∀ᵐ ω ∂P, ∀ p ∈ (ExplState.run κ b jumps spec (fun k => E k ω) spec.2.2.length).1,
      closure (p.1.tipSet p.2.1 p.2.2) ∩ H ⊆ p.1.tipSet p.2.1 p.2.2 := by
  filter_upwards [hR.ae_pieceRegular] with ω hω
  exact closure_tipSet_inter_H_subset_run spec (fun j => E j ω) hω

/-- **GW1's piece properness under R51's hypothesis**: `SB.GW1PieceProperStatement` for families that are also
`StagedPiecesRegular` (the hypothesis R51 adds to the Theorem 1.4 anchors). -/
def GW1PieceProperRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P,
        (∀ p ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length).1,
          closure (p.1.tipSet p.2.1 p.2.2) ∩ H ⊆ p.1.tipSet p.2.1 p.2.2) ∧
        ∀ p ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
            (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2.length).1,
          closure (p.1.tipSet p.2.1 p.2.2) ∩ H ⊆ p.1.tipSet p.2.1 p.2.2

/-- **GW1's properness under R51's hypothesis**: `SB.GW1ProperStatement` for families that are also
`StagedPiecesRegular`. -/
def GW1ProperRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω ∂P,
        closure (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) ∩ H ⊆
          ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ∧
        closure (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) ∩ H ⊆
          ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)

/-- The two walk angles `∓π/2` lie in `[−π/2, π/2]`. -/
theorem mem_Icc_walkAngle {θ : ℝ} (hθ : θ = -(Real.pi / 2) ∨ θ = Real.pi / 2) :
    θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  rcases hθ with rfl | rfl <;> constructor <;> linarith [Real.pi_pos]

/-- **`GW1PieceProperRegStatement` holds** (no further input). -/
theorem gw1PieceProperRegStatement : GW1PieceProperRegStatement.{u} := by
  intro κ _ _ b jumps _ Ω _ _ P _ h _ W' ζ' _ _ E _ hR
  have hR1 := ae_closure_tipSet_inter_H_subset_of_stagedPiecesRegular
    (hR _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (mem_Icc_walkAngle (Or.inl rfl)) true))
  have hR2 := ae_closure_tipSet_inter_H_subset_of_stagedPiecesRegular
    (hR _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (mem_Icc_walkAngle (Or.inr rfl)) false))
  filter_upwards [hR1, hR2] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **`GW1ProperRegStatement` holds** (no further input). -/
theorem gw1ProperRegStatement : GW1ProperRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR
  filter_upwards [gw1PieceProperRegStatement κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR] with ω hω
  exact ⟨SB.closure_physSet_inter_H_subset hω.1, SB.closure_physSet_inter_H_subset hω.2⟩

end GW1P

end Theorem14

end InteractingSLE
