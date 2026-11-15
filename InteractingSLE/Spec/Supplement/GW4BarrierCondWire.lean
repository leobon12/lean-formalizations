/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4BarrierCond
import InteractingSLE.Spec.Supplement.GB11RelParam
import InteractingSLE.Spec.Supplement.GW4LawProofWire

/-!
# Theorem GW4's chain with the barrier input for each sample and the local growth of the relative hulls

Packet PROVE-T14-GW4T3. PROVE-T14-GW4T2's wires (`GW4LawProofWire.lean`) take Lemma GB11's relative parametrization
(`GB11RelParamStatement`) and the barrier input under the conditional law (`GW4BarrierPocketRegStatement`) as inputs.
This file replaces them by the finer inputs of this packet: the analytic core `GB11RelConnGrowthStatement`
((GB11.2) and the local growth of the relative hulls; `gb11RelParamStatement_of_connGrowth`) and the barrier input
for the walks and traces of the same sample, `GW4BarrierSelfRegStatement` (`gw4BarrierPocketRegStatement_of_self`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Reg

open GW4Traverse GW4Ident

/-- **Theorem GW4's relative hulls, R51 form**, from (GB11.2) and the local growth of the relative hulls, the
barrier input for each sample, the R51 component law, no return and Theorems 1.2–1.3 (conditional helper). -/
theorem gw4RelativeHullRegStatement_of_connGrowthSelf (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hG : GB11RelConnGrowthStatement) (hB : GW4BarrierSelfRegStatement.{u})
    (hL : GW4RelativeLawRegStatement.{u}) (hNR : CounterflowNoReturnStatement.{u}) :
    GW4RelativeHullRegStatement.{u} :=
  gw4RelativeHullRegStatement_of_relParam h12 h13 (gb11RelParamStatement_of_connGrowth hG)
    (gw4BarrierPocketRegStatement_of_self hB) hL hNR

/-- **Theorem GW4's traversal core, R51 form**, from the same inputs and GW8's openness and word-bound inputs
(conditional helper). -/
theorem gw4TraversalCoreRegStatement_of_connGrowthSelf (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hO : GW3Joint.BetweenComponentsOpenRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hG : GB11RelConnGrowthStatement)
    (hB : GW4BarrierSelfRegStatement.{u}) (hL : GW4RelativeLawRegStatement.{u})
    (hNR : CounterflowNoReturnStatement.{u}) : GW4R51.GW4TraversalCoreRegStatement.{u} :=
  gw4TraversalCoreRegStatement_of_relParam h12 h13 hO hWB (gb11RelParamStatement_of_connGrowth hG)
    (gw4BarrierPocketRegStatement_of_self hB) hL hNR

/-- **Theorem 1.4, component kernels, version 2** (R51), provider shape, as `componentKernels_of_lawReg` with Lemma
GB11's relative parametrization replaced by (GB11.2) and the local growth of the relative hulls, and the barrier
input under the conditional law replaced by the barrier input for each sample (conditional helper; not the
provider). -/
theorem componentKernels_of_connGrowthSelf (hGS : GW3Sided.GW3GeometrySidedRegStatement.{u})
    (hU : GW3Joint.GW3UnionLawRegStatement.{u}) (hP : WalkCont.RightWalkProperRegStatement.{u})
    (hS : WalkCont.WalkConnectorSideRegStatement.{u}) (hNP : WalkCont.WalkPieceContinuumRegStatement.{u})
    (hG : GB11RelConnGrowthStatement) (hB : GW4BarrierSelfRegStatement.{u}) (hL : GW4RelativeLawRegStatement.{u})
    (hNR : CounterflowNoReturnStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0})
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
  componentKernels_of_lawReg hGS hU hP hS hNP (gb11RelParamStatement_of_connGrowth hG)
    (gw4BarrierPocketRegStatement_of_self hB) hL hNR h12 h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hreg

end GW4Reg

end Theorem14

end InteractingSLE
