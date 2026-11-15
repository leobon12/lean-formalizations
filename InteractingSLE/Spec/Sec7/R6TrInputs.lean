/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrGeometry
import InteractingSLE.Spec.Sec7.R6TnFinal

/-!
# Same-original-time geometric inputs for the three two-outer shapes

PROVE-R6-TWO, Astra §§2 and 4 (R98). These named inputs are unproved.
They replace the retired non-corner/force-landing-patch route. Their
consumer proves the later real-time face and then the original Q face.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R6Tr

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField
open HOuter PocketWordAssembly PocketSeedOpen R6Safe R6Two R6Tn
open R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketStopWallsFin PocketStopSide

universe u

/-- **Named, unproved:** the common-time incident-face geometry for `Two`.
Seed corners and non-singleton exposed-landing fibres are permitted. -/
def R6SameTimeTwoRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEvent R L r η ψ MR ML R ML s q →
        HasSameTimeLeftGeometry (cfPocket (R ω) (ML ω) (StripSys.rt s))
          (closure (cfPocket (R ω) (ML ω) (StripSys.rt s)) \ {cfPt (openPt (R ω) (ML ω) (StripSys.rt s))})
          (fun q' => currentChart A' R ML (StripSys.rt s) η ψ' n' q'.toNNReal ω)
          (fun q' => leftSeed (travAll R ML (StripSys.rt s) η ψ') q'.toNNReal ω)
          (currentChart A R L r η ψ n (StripSys.rt q) ω)
          (innerRelCap R ML (StripSys.rt s) η ψ' (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ω)
          (η ω (outerFibreEnd R L r η ψ (StripSys.rt q) ω))
          (leftSeed (travAll R L r η ψ) (StripSys.rt q) ω)

/-- **Named, unproved:** the common-time incident-face geometry for `TwoInf`.
Seed corners and non-singleton exposed-landing fibres are permitted. -/
def R6SameTimeTwoInfRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML R ML s q →
        HasSameTimeLeftGeometry (cfPocket (R ω) (ML ω) (StripSys.rt s))
          (closure (cfPocket (R ω) (ML ω) (StripSys.rt s)) \ {cfPt (openPt (R ω) (ML ω) (StripSys.rt s))})
          (fun q' => currentChart A' R ML (StripSys.rt s) η ψ' n' q'.toNNReal ω)
          (fun q' => leftSeed (travAll R ML (StripSys.rt s) η ψ') q'.toNNReal ω)
          (currentChartInf A R L r η ψ n (StripSys.rt q) ω)
          (innerRelCap R ML (StripSys.rt s) η ψ' (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω)
          (η ω (outerFibreEndInf R L r η ψ (StripSys.rt q) ω))
          (leftSeed (travAllInf R L r η ψ) (StripSys.rt q) ω)

/-- **Named, unproved:** the common-time incident-face geometry for `TwoInfInf`.
Seed corners and non-singleton exposed-landing fibres are permitted. -/
def R6SameTimeTwoInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfgInf (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML R ML s q →
        HasSameTimeLeftGeometry (cfPocket (R ω) (ML ω) (StripSys.rt s))
          (closure (cfPocket (R ω) (ML ω) (StripSys.rt s)))
          (fun q' => currentChartInf A' R ML (StripSys.rt s) η ψ' n' q'.toNNReal ω)
          (fun q' => leftSeed (travAllInf R ML (StripSys.rt s) η ψ') q'.toNNReal ω)
          (currentChartInf A R L r η ψ n (StripSys.rt q) ω)
          (innerRelCapInf R ML (StripSys.rt s) η ψ' (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω)
          (η ω (outerFibreEndInf R L r η ψ (StripSys.rt q) ω))
          (leftSeed (travAllInf R L r η ψ) (StripSys.rt q) ω)

end InteractingSLE.Sec7.R6Tr
