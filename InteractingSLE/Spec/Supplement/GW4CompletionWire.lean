/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4Completion
import InteractingSLE.Spec.Supplement.GB10Proof
import InteractingSLE.Spec.Wire.Thm14InputsR51

/-!
# Theorem GW4 after PROVE-T14-GW4S: the relative chain and the component kernels from the remaining inputs

Packet PROVE-T14-GW4S. Lemma GB10 is proved (`GB10.gb10Statement`) and the completion of each traversal follows from
the component law input, the filled pocket and the no-return input (`gw4CompletionStatement_of_law`). The wrappers
of PROVE-T14-GW4R are restated with these inputs:

* `gw4RelativeChainStatement_of_law` : `GW4Traverse.GW4RelativeChainStatement` from GB11, the barrier input, the
  component law input, the deterministic filled pocket, the no-return input and Theorem 1.3;
* `gw4RelativeHullStatement_of_law` : `GW4Traverse.GW4RelativeHullStatement` (adds Theorem 1.2);
* **`componentKernels_of_lawR51`** : the version-2 (ruling R51) component-kernel anchor's type, provider shape
  (conditional helper, not the provider), through `Wire.componentKernels_of_relHullsR51`.

All theorems are conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Ident

open GW4Traverse

/-- **Theorem GW4's pathwise relative chain** with Lemma GB10 discharged and the completion replaced by its inputs
(conditional helper). -/
theorem gw4RelativeChainStatement_of_law (h13 : Exist.Theorem13Statement.{u}) (hGB11 : GB11.GB11Statement)
    (hB : GW4BarrierStatement.{u}) (hL : GW4RelativeLawStatement.{u}) (hD : GW4FillDetStatement)
    (hNR : CounterflowNoReturnStatement.{u}) : GW4RelativeChainStatement.{u} :=
  gw4RelativeChainStatement_of_gb11 h13 GB10.gb10Statement hGB11 hB
    (gw4CompletionStatement_of_law h13 hL (gw4FillStatement_of_barrier h13 hB hD) hNR)

/-- **Theorem GW4's relative hulls** from the remaining inputs (conditional helper). -/
theorem gw4RelativeHullStatement_of_law (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hGB11 : GB11.GB11Statement) (hB : GW4BarrierStatement.{u}) (hL : GW4RelativeLawStatement.{u})
    (hD : GW4FillDetStatement) (hNR : CounterflowNoReturnStatement.{u}) : GW4RelativeHullStatement.{u} :=
  gw4RelativeHullStatement_of_chain_law h12 h13 (gw4RelativeChainStatement_of_law h13 hGB11 hB hL hD hNR) hL

/-- **Theorem 1.4, component kernels, version 2** (R51), provider shape, from the finest inputs after this packet:
Lemma GW3's geometry and one-chart field law, no common continuum, GW0's forward implication, the connector side,
Lemma GB11, the barrier input, the component law input, the deterministic filled pocket, the no-return input and
Theorems 1.2–1.3 (conditional helper; not the provider). -/
theorem componentKernels_of_lawR51 (hG : GW3.GW3GeometryStatement.{u})
    (hF1 : GW3Law.GW3FieldLawOneChartStatement.{u}) (hN : GW3Law.WalkNoCommonContinuumStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hS : GW3Word.WalkConnectorSideStatement.{u})
    (hGB11 : GB11.GB11Statement) (hB : GW4BarrierStatement.{u}) (hL : GW4RelativeLawStatement.{u})
    (hD : GW4FillDetStatement) (hNR : CounterflowNoReturnStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec) := by assumption)
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec) := by assumption) :
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  Wire.componentKernels_of_relHullsR51 hG hF1 hN hGW0 hS
    (gw4RelativeHullStatement_of_law h12 h13 hGB11 hB hL hD hNR) h12 h13 hκ hκ4 hb hh hcf hζ' hE hreg

end GW4Ident

end Theorem14

end InteractingSLE
