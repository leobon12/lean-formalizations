/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm14Inputs2
import InteractingSLE.Spec.Wire.Thm12Inputs3
import InteractingSLE.Spec.Wire.Thm13Inputs3
import InteractingSLE.Spec.Supplement.GW1
import InteractingSLE.Spec.Exist.Param12Conv
import InteractingSLE.Spec.Exist.StagedLawMain

/-!
# Theorem 1.4 with the results landed since PROVE-WIRE2 plugged in

Packet PROVE-WIRE3 (no new mathematics). PROVE-WIRE2 left the four Theorem 1.4 anchors with seven named inputs. Since
then:

* GW1's first-threshold input is a theorem (`Theorem14.GW1.gw1FirstThresholdStatement`, PROVE-T14-GW), so the frontiers
  anchor needs only GW2a and SB (`boundaryWalks_frontiers_of_open3`);
* the staged-history construction (`hCon`) follows from the frozen-type Theorems 1.2 and 1.3, the coupling-law kernel
  in the word and the staged conditional field law
  (`Exist.Param12.stagedHistoryConstructionStatement_of_couplingLawKernel`, PROVE-PARAM12 with PROVE-STAGED), and the
  staged conditional field law from the single-stage stop law and two deterministic measurability statements
  (`Exist.StagedLaw.stagedCondLawStatement_of_inputs`, PROVE-STAGEDLAW);
  Theorems 1.2 and 1.3 come from their open inputs (`theorem12Statement_of_open3`, `theorem13Statement_of_open3`)
  (`exists_isStagedHistory_of_open3`).

The light-cone anchor (GW2, GW2a) and the component-kernel anchor (GW3, GW4) are unchanged: use
`completedRange_eq_closure_lightCone_of_remaining2` and `componentKernels_of_remaining2` (`Thm14Inputs2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

open Theorem14

/-- **Theorem 1.4, frontiers** (`IsCenteredCounterflowDriver.boundaryWalks_frontiers`), provider shape, from Lemma
GW2a and SB1–SB5 alone: GW1's first-threshold input is proved (`Theorem14.GW1.gw1FirstThresholdStatement`,
PROVE-T14-GW), so Corollary GW6 follows from GW2a (conditional helper; not the provider). -/
theorem boundaryWalks_frontiers_of_open3 (hGW2a : GW2aContainmentStatement.{u})
    (hSB : SBFrontierStatement.{u})
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
  boundaryWalks_frontiers_of_remaining2 hGW2a hSB GW1.gw1FirstThresholdStatement hκ hκ4 hb hh hcf hζ' hE

/-- **The companion of Theorem 1.4** (`exists_isStagedHistory`), provider shape, from the open inputs of Theorems
1.2 and 1.3 (seventeen distinct names, as in `exists_isFlowLine_of_open3`), Theorem 1.1's coupling law as a Borel kernel
in the word (`hK`), and the three inputs of the staged conditional field law: the single-stage stop law (`hA`), the
Borel run (`hB`) and the Borel flow-line word (`hC`) (conditional helper; not the provider). -/
theorem exists_isStagedHistory_of_open3
    -- shared by Theorems 1.2 and 1.3
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    -- Theorem 1.2 only
    (hJ : Sec7.Lemma72.Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR)
    (hcon : WangWu.ReverseTipContactStatement.{0})
    (hneg : ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (h50R : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      Aux50.HasTraceStopKernel.{0, u} κ rL rR)
    (h725d : LP.Lemma725DeterminationStatement.{u})
    (hPre : ∀ κ : ℝ, 0 < κ → LocalExt.ExtPreStopStatement.{u} κ)
    (hLoc : ∀ κ : ℝ, 0 < κ → LocalExt.ExtLocalityStatement.{u} κ)
    (hdl : ∀ κ : ℝ, 0 < κ → LocalExt.RestartDrivingLocalityInput.{u} κ)
    -- Theorem 1.3 only
    (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hmid : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.TrialsHi3.LowCritStatement.{u} κ (-2))
    (hlow : ∀ κ : ℝ, 4 ≤ κ → Sec7.TrialsHi3.LowCritStatement.{u} κ (κ / 2 - 4))
    (h8 : ∀ κ : ℝ, 4 < κ → Sec7.TrialsHi3.LP8CritStatement.{u} κ)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    -- the staged histories
    (hK : Exist.Param12.CouplingLawKernelStatement.{u}) (hA : Exist.StagedLaw.StopLawStatement.{u})
    (hB : Exist.StagedLaw.RunMeasStatement.{u}) (hC : Exist.StagedLaw.WordMeasStatement)
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec,
      IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec) :=
  exists_isStagedHistory_of_remaining2
    (Exist.Param12.stagedHistoryConstructionStatement_of_couplingLawKernel
      (theorem12Statement_of_open3 hJ h50 hcon hneg hhit hR7 h50R h725d hPW hPre hLoc hdl)
      (theorem13Statement_of_open3 hPC hmid hlow h8 hhit hR7 hPW hcol) hK
      (Exist.StagedLaw.stagedCondLawStatement_of_inputs hA hB hC)) hκ hκ4 hb hh

end Wire

end InteractingSLE
