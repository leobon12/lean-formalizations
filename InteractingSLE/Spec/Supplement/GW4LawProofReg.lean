/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CompletionWire

/-!
# Theorem GW4's relative chain in the R51 form

Packet PROVE-T14-GW4T2. Ruling R51 adds to the frozen component-kernel anchor (version 2) the hypothesis that every
staged family is `StagedPiecesRegular`. Without it the walks need not be simple curves on a set of positive outer
measure (`planning/handoffs/PROVE-T14-GW1P.md`), so the named inputs of Theorem GW4's chain stated by PROVE-T14-GW4R and
PROVE-T14-GW4S without it (`GW4Ident.GW4BarrierStatement`, `GW4Ident.GW4FillStatement`,
`GW4Ident.GW4RelativeLawStatement`, `GW4Ident.GW4CompletionStatement`, and the chain, identification and hull
statements of `GW4Traverse`) are probably not provable as stated. This file restates each of them with the added
hypothesis `hreg` right after `hE` (verbatim otherwise) and re-proves the chain:

* `GW4BarrierRegStatement`, `GW4FillRegStatement`, `GW4RelativeLawRegStatement`, `GW4CompletionRegStatement`,
  `GW4RelativeChainRegStatement`, `GW4RelativeIdentRegStatement`, `GW4RelativeHullRegStatement`, each implied by its
  unregularized form (`*_of_unreg`);
* `gw4FillRegStatement_of_barrier` (the barrier and the deterministic `GW4Ident.GW4FillDetStatement`);
* `gw4CompletionRegStatement_of_law` (`GW4Ident.eq_top_of_law_fill`, no return, Theorem 1.3);
* `gw4RelativeChainRegStatement_of_gb11` (GB10 discharged by `GB10.gb10Statement`, GB11, barrier, completion);
* `gw4RelativeIdentRegStatement_of_law`, `gw4RelativeHullRegStatement_of_chain_ident`;
* **`gw4RelativeHullRegStatement_of_law`**: the R51 relative hulls from GB11, the R51 barrier and law inputs, the
  deterministic filled pocket, no return and Theorems 1.2–1.3.

The proofs are those of PROVE-T14-GW4R/GW4S with `hreg` threaded through. Every theorem is a conditional helper with a
distinct name; none is a provider.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Reg

open GW4Traverse GW4Ident

/-! ### The statements in the R51 form -/

/-- **Named input: the barrier input of GB11 for the actual sewn walks, R51 form**: `GW4Ident.GW4BarrierStatement` for
staged families that are also `StagedPiecesRegular`. -/
def GW4BarrierRegStatement : Prop :=
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
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∃ αR αL : ℝ≥0 → ℂ, range αR = R ∧ range αL = L ∧
          ∀ᵐ ω ∂ν, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ → GB11.IsGB11Barrier αR αL γ

/-- **The filled pocket in the setting of Theorem GW4, R51 form**: `GW4Ident.GW4FillStatement` for staged families
that are also `StagedPiecesRegular`. -/
def GW4FillRegStatement : Prop :=
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
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ c : Chart, IsComponentChart R L C c →
          ∀ᵐ ω ∂ν, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ →
            ∀ xC : ℂ, Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) → GB11.firstVisit γ xC < ⊤ →
              relDom C ⊆ fwdHull (fun r : ℝ => W' r.toNNReal ω) (GB11.firstVisit γ xC).toNNReal

/-- **Named input: the component (Det) of Theorem GW4, R51 form**: `GW4Ident.GW4RelativeLawStatement` for staged
families that are also `StagedPiecesRegular`. -/
def GW4RelativeLawRegStatement : Prop :=
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
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∃ (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ ν hC WC ζC ∧
            (∀ᵐ ω ∂ν, ζC ω = ⊤) ∧
            ∀ᵐ ω ∂ν, ∃ T : ℝ≥0 → ℝ≥0, ∀ s : ℝ≥0,
              QuantumZipper.fwdHull (fun r : ℝ => WC r.toNNReal ω) s =
                relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) (T s) ∩ relDom C)

/-- **The completion of each traversal, R51 form**: `GW4Ident.GW4CompletionStatement` for staged families that are
also `StagedPiecesRegular`. -/
def GW4CompletionRegStatement : Prop :=
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
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∀ᵐ ω ∂ν, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ →
            ∀ xC : ℂ, Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) →
            ∀ (S : ℝ≥0∞) (Wrel : ℝ≥0 → ℝ) (T : ℝ≥0 → ℝ≥0),
              GB11.IsGB11RelParam (fun t => W' t ω) γ c C xC S Wrel T →
              S = ⊤ ∧ ∀ s : ℝ≥0, 0 < s →
                (∀ p : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) (T s)) (𝓝[H] 0)
                  (𝓝 p) → p ≠ 0) ∧
                ∀ q : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => Wrel r.toNNReal) s) (𝓝[H] 0) (𝓝 q) →
                  q ≠ 0

/-- **Theorem GW4's pathwise relative chain, R51 form**: `GW4Traverse.GW4RelativeChainStatement` for staged
families that are also `StagedPiecesRegular`. -/
def GW4RelativeChainRegStatement : Prop :=
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
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∀ᵐ ω ∂ν, ∃ (Wrel : ℝ≥0 → ℝ) (T : ℝ≥0 → ℝ≥0), Continuous Wrel ∧ Wrel 0 = 0 ∧ StrictMono T ∧
            Continuous T ∧
            (∀ t : ℝ≥0, t < T 0 → ∀ p : ℂ,
              Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) t) (𝓝[H] 0) (𝓝 p) →
              p ≠ 0 → -p⁻¹ ∉ closure C) ∧
            (∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => Wrel r.toNNReal) s =
              relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) (T s) ∩ relDom C)) ∧
            ∀ s : ℝ≥0, 0 < s →
              (∀ p : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) (T s)) (𝓝[H] 0)
                (𝓝 p) → p ≠ 0) ∧
              ∀ q : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => Wrel r.toNNReal) s) (𝓝[H] 0) (𝓝 q) →
                q ≠ 0

/-- **Theorem GW4's identification of the relative driver, R51 form**: `GW4Traverse.GW4RelativeIdentStatement`
for staged families that are also `StagedPiecesRegular`. -/
def GW4RelativeIdentRegStatement : Prop :=
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
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∀ (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ ν hC WC ζC →
            (∀ᵐ ω ∂ν, ζC ω = ⊤) →
            ∀ᵐ ω ∂ν, ∀ (Wrel : ℝ≥0 → ℝ) (T : ℝ≥0 → ℝ≥0), Continuous Wrel → StrictMono T → Continuous T →
              (∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => Wrel r.toNNReal) s =
                relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) (T s) ∩ relDom C)) →
              (fun t => WC t ω) = Wrel

/-- **Theorem GW4's relative hulls, R51 form**: `GW4Traverse.GW4RelativeHullStatement` for staged families that
are also `StagedPiecesRegular`. -/
def GW4RelativeHullRegStatement : Prop :=
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
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∀ (WC : ℝ≥0 → Ω → ℝ) (ζC : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ ν hC WC ζC →
            (∀ᵐ ω ∂ν, ζC ω = ⊤) →
            ∀ᵐ ω ∂ν, ∃ T : ℝ≥0 → ℝ≥0, StrictMono T ∧ Continuous T ∧
              (∀ t : ℝ≥0, t < T 0 → ∀ p : ℂ,
                Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) t) (𝓝[H] 0) (𝓝 p) →
                p ≠ 0 → -p⁻¹ ∉ closure C) ∧
              (∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => WC r.toNNReal ω) s =
                relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) (T s) ∩ relDom C)) ∧
              ∀ s : ℝ≥0, 0 < s →
                (∀ p : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal ω) (T s)) (𝓝[H] 0)
                  (𝓝 p) → p ≠ 0) ∧
                ∀ q : ℂ, Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => WC r.toNNReal ω) s) (𝓝[H] 0) (𝓝 q) →
                  q ≠ 0

/-! ### The unregularized forms imply the R51 forms -/

theorem gw4BarrierRegStatement_of_unreg (hB : GW4BarrierStatement.{u}) : GW4BarrierRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

theorem gw4FillRegStatement_of_unreg (hF : GW4FillStatement.{u}) : GW4FillRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

theorem gw4RelativeLawRegStatement_of_unreg (hL : GW4RelativeLawStatement.{u}) :
    GW4RelativeLawRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

theorem gw4CompletionRegStatement_of_unreg (hC : GW4CompletionStatement.{u}) :
    GW4CompletionRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

theorem gw4RelativeChainRegStatement_of_unreg (hP : GW4RelativeChainStatement.{u}) :
    GW4RelativeChainRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hP κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

theorem gw4RelativeIdentRegStatement_of_unreg (hI : GW4RelativeIdentStatement.{u}) :
    GW4RelativeIdentRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hI κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

theorem gw4RelativeHullRegStatement_of_unreg (hH : GW4RelativeHullStatement.{u}) :
    GW4RelativeHullRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _
  exact hH κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE

/-! ### The chain -/

/-- **The filled pocket in GW4's setting from the barrier input, R51 form** (`GW4Ident.gw4FillStatement_of_barrier`
with `hreg` threaded through). -/
theorem gw4FillRegStatement_of_barrier (h13 : Exist.Theorem13Statement.{u}) (hB : GW4BarrierRegStatement.{u})
    (hD : GW4FillDetStatement) : GW4FillRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    (ae_trace_of_isCenteredCounterflowDriver h13 hκ hcf hζ')
  filter_upwards [hamb, hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hambω hBω
  intro R L ν C hCm c hch
  obtain ⟨αR, αL, hαR, hαL, hbar⟩ := hBω
  filter_upwards [hambω, hbar] with ω hambω' hbarω
  intro γ hγ xC hxC hσ
  obtain ⟨hW'c, hW'0, -⟩ := hambω'
  have hCm' : C ∈ betweenComponents (range αR) (range αL) := by rw [hαR, hαL]; exact hCm
  have hch' : IsComponentChart (range αR) (range αL) C c := by rw [hαR, hαL]; exact hch
  exact hD (fun t => W' t ω) γ hW'c hW'0 hγ αR αL (hbarω γ hγ) C hCm' c hch' xC hxC hσ

/-- **The completion of each traversal, R51 form** (`GW4Ident.gw4CompletionStatement_of_law` with `hreg` threaded
through): from the R51 law input, the R51 filled pocket, no return and Theorem 1.3. -/
theorem gw4CompletionRegStatement_of_law (h13 : Exist.Theorem13Statement.{u})
    (hL : GW4RelativeLawRegStatement.{u}) (hF : GW4FillRegStatement.{u}) (hN : CounterflowNoReturnStatement.{u}) :
    GW4CompletionRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    ((ae_trace_of_isCenteredCounterflowDriver h13 hκ hcf hζ').and
      (hN κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'))
  filter_upwards [hamb, hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hambω hLω hFω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨WC, ζC, hcdC, hζC, hlawC⟩ := hLω C hCm c hC bC jumpsC hch htr hpc hbd hgff
  filter_upwards [hambω, hlawC, ae_trace_of_isCenteredCounterflowDriver h13 hκ hcdC hζC,
    hN κ hκ hκ4 bC jumpsC hpc ν hC hgff WC ζC hcdC hζC, hFω C hCm c hch] with ω hambω' hlawω htrC hnoC hfillω
  intro γ hγ xC hxC S Wrel T hpar
  obtain ⟨⟨hW'c, hW'0, -⟩, hno⟩ := hambω'
  obtain ⟨TL, hTL⟩ := hlawω
  obtain ⟨hWCc, hWC0, γC, hγC, -⟩ := htrC
  have hS : S = ⊤ := eq_top_of_law_fill hpar hWCc hWC0 hTL (hfillω γ hγ xC hxC)
  subst hS
  obtain ⟨hWrelc, hWrel0, hTm, -, hKrel⟩ := hpar.global
  have hne : (𝓝[H] (0 : ℂ)).NeBot := neBot_nhdsWithin_H_zero
  refine ⟨rfl, fun s hs => ⟨fun p hp => ?_, fun q hq => ?_⟩⟩
  · have htip := hγ.tendsto_fwdMapInv_tip hW'c.continuousOn hW'0 (t := T s) ENNReal.coe_lt_top
    rw [tendsto_nhds_unique hp htip]
    exact hno γ hγ (T s) (lt_of_le_of_lt zero_le (hTm hs))
  · have heqW : Wrel = fun t => WC t ω :=
      eq_of_fwdHull_eq_comp (monotone_relHull c C _) hWrelc hWCc hWrel0 hKrel hTL
    subst heqW
    have htipC := hγC.tendsto_fwdMapInv_tip hWCc.continuousOn hWC0 (t := s) ENNReal.coe_lt_top
    rw [tendsto_nhds_unique hq htipC]
    exact hnoC γC hγC s hs

/-- **Theorem GW4's pathwise relative chain, R51 form** (`GW4Ident.gw4RelativeChainStatement_of_gb11` with GB10
discharged by `GB10.gb10Statement` and `hreg` threaded through): from GB11, the R51 barrier input, the R51 completion
and Theorem 1.3. -/
theorem gw4RelativeChainRegStatement_of_gb11 (h13 : Exist.Theorem13Statement.{u}) (hGB11 : GB11.GB11Statement)
    (hB : GW4BarrierRegStatement.{u}) (hComp : GW4CompletionRegStatement.{u}) :
    GW4RelativeChainRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    (ae_trace_noSimpleArcInterval GB10.gb10Statement h13 hκ hκ4 hcf hζ')
  filter_upwards [hamb, hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hComp κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hambω hBω hCω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  obtain ⟨αR, αL, hαR, hαL, hbar⟩ := hBω
  filter_upwards [hambω, hbar, hCω C hCm c hC bC jumpsC hch htr hpc hbd hgff] with ω hambω' hbarω hcompω
  obtain ⟨hW'c, hW'0, γ, hγ, hno⟩ := hambω'
  have hCm' : C ∈ betweenComponents (range αR) (range αL) := by rw [hαR, hαL]; exact hCm
  have hch' : IsComponentChart (range αR) (range αL) C c := by rw [hαR, hαL]; exact hch
  obtain ⟨xC, hxC, -, -⟩ := hch.2.2.2.2.1 0
  have hxC' : Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) := by simpa only [Complex.ofReal_zero] using hxC
  obtain ⟨S, Wrel, T, hpar, hent, -, -⟩ := hGB11 (fun t => W' t ω) γ hW'c hW'0 hγ hno αR αL (hbarω γ hγ) C hCm'
    c hch' xC hxC'
  obtain ⟨hS, htips⟩ := hcompω γ hγ xC hxC' S Wrel T hpar
  subst hS
  obtain ⟨hWc, hW0, hTm, hTc, hK⟩ := hpar.global
  have := neBot_nhdsWithin_H_zero
  refine ⟨Wrel, T, hWc, hW0, hTm, hTc, fun t ht p hp hp0 => ?_, hK, htips⟩
  have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hW'c.continuousOn hW'0
    (ENNReal.coe_lt_top (r := t))
  have e : p = γ t := tendsto_nhds_unique hp htip
  subst e
  exact hent t ht hp0

/-- **Theorem GW4's identification of the relative driver, R51 form** (`GW4Ident.gw4RelativeIdentStatement_of_law`
with `hreg` threaded through). -/
theorem gw4RelativeIdentRegStatement_of_law (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hL : GW4RelativeLawRegStatement.{u}) :
    GW4RelativeIdentRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  filter_upwards [hL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hLω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff WC ζC hcd hζC
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨W₀, ζ₀, hcd₀, hζ₀, hK₀⟩ := hLω C hCm c hC bC jumpsC hch htr hpc hbd hgff
  have he := ae_eq_of_isCenteredCounterflowDriver h12p h13 hκ hpc hgff hcd₀ hζ₀ hcd hζC
  have hreg₀ := ae_trace_of_isCenteredCounterflowDriver h13 hκ hcd₀ hζ₀
  filter_upwards [he, hK₀, hreg₀] with ω heω hKω hregω
  intro Wrel T hWc _ _ hK
  obtain ⟨T₀, hT₀⟩ := hKω
  rw [← heω]
  exact eq_of_fwdHull_eq_comp (monotone_relHull c C _) hregω.1 hWc hregω.2.1 hT₀ hK

/-- **The relative-hull statement from its two halves, R51 form** (`GW4Traverse.gw4RelativeHullStatement_of_chain_ident`
with `hreg` threaded through). -/
theorem gw4RelativeHullRegStatement_of_chain_ident (hP : GW4RelativeChainRegStatement.{u})
    (hI : GW4RelativeIdentRegStatement.{u}) : GW4RelativeHullRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hP κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hI κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hPω hIω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff WC ζC hcd hζC
  filter_upwards [hPω C hCm c hC bC jumpsC hch htr hpc hbd hgff,
    hIω C hCm c hC bC jumpsC hch htr hpc hbd hgff WC ζC hcd hζC] with ω hPω' hIω'
  obtain ⟨Wrel, T, hWc, -, hT, hTc, hent, hK, hne⟩ := hPω'
  have e := hIω' Wrel T hWc hT hTc hK
  subst e
  exact ⟨T, hT, hTc, hent, hK, hne⟩

/-- **Theorem GW4's relative hulls, R51 form, from the finest inputs** (conditional helper): Lemma GB11, the R51
barrier input, the R51 component law input, the deterministic filled pocket, no return and Theorems 1.2–1.3 (GB10 is
proved). -/
theorem gw4RelativeHullRegStatement_of_law (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hGB11 : GB11.GB11Statement) (hB : GW4BarrierRegStatement.{u})
    (hL : GW4RelativeLawRegStatement.{u}) (hD : GW4FillDetStatement) (hNR : CounterflowNoReturnStatement.{u}) :
    GW4RelativeHullRegStatement.{u} :=
  gw4RelativeHullRegStatement_of_chain_ident
    (gw4RelativeChainRegStatement_of_gb11 h13 hGB11 hB
      (gw4CompletionRegStatement_of_law h13 hL (gw4FillRegStatement_of_barrier h13 hB hD) hNR))
    (gw4RelativeIdentRegStatement_of_law h12 h13 hL)

end GW4Reg

end Theorem14

end InteractingSLE
