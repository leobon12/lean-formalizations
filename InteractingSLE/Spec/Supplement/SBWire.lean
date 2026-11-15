/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm14Inputs3
import InteractingSLE.Spec.Supplement.SBFrontier

/-!
# Theorem 1.4's frontiers with the sewn-barrier input reduced (SB4, SB5, GW1's properness, GW2)

Packet PROVE-T14-SB. `Wire.boundaryWalks_frontiers_of_open3` (PROVE-WIRE3) needs `GW2aContainmentStatement` and
`SBFrontierStatement`; the second is now `SB.sbFrontierStatement_of_sb` from GW2 (`GW2LightConeStatement`, also an
input of the light-cone anchor), Theorem SB4 and Corollary SB5 (`SB.SB4Statement`, `SB.SB5Statement`) and GW1's
properness (`SB.GW1ProperStatement`). Conditional helper, provider shape; not the provider.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

/-- **Theorem 1.4, frontiers** (`IsCenteredCounterflowDriver.boundaryWalks_frontiers`), provider shape, from Lemma
GW2a, Lemma GW2, Theorem SB4, Corollary SB5 and GW1's properness (conditional helper; not the provider). -/
theorem boundaryWalks_frontiers_of_sb (hGW2a : GW2aContainmentStatement.{u})
    (hGW2 : GW2LightConeStatement.{u}) (h4 : SB4Statement.{u}) (h5 : SB5Statement.{u})
    (hprop : GW1ProperStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption) :
    ∀ᵐ ω ∂P,
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅) ∧
      (interior (((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω)) = ∅ →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
          (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤) :=
  Wire.boundaryWalks_frontiers_of_open3 hGW2a (sbFrontierStatement_of_sb hGW2 h4 h5 hprop) hκ hκ4 hb hh hcf hζ' hE

end SB

end Theorem14

end InteractingSLE
