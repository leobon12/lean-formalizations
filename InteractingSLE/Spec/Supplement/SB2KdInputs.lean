/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KdIdentify
import InteractingSLE.Spec.Supplement.SB2KSplit

/-!
# Exact remaining erased-driver input for SB2(1)

The problem record contains exactly the premises of `SB2DriverLinkAmbStatement`.
The chart record contains proved K2 launch inputs. The final named proposition
asks for the actual geometric driver and its canonical code, with an independent
generating trace and the original clock. It is an explicit unproved input of
the conditional assembly theorem, not a proof of the source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4 Exist.Staged Restart WalkInf Supp8.Q3Stop

/-- The unchanged source premises for one SB2(1) launch problem. -/
structure SB2LaunchProblem (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) : Prop where
  kappa_pos : 0 < κ
  kappa_lt_four : κ < 4
  boundary : IsPiecewiseConstantBoundaryData b jumps
  field : IsGFFWithBoundaryData P h b jumps
  admissible : Ly.LowerLeftAdmissible κ b jumps
  staged : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
    IsStagedHistory κ b jumps P h spec (E spec)
  pieces_regular : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
    StagedPiecesRegular κ b jumps P spec (E spec)
  drivers_regular : ∀ spec j ω, IsRegularDriver (E spec j ω)
  seed_nonpos : u ≤ 0
  angle : -(Real.pi / 2) < ψ
  left_groups : ∀ x ∈ Ioo u 0, x ∉ jumps →
    -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)
  hybrid : ∀ x ∈ Ioo u 0, x ∉ jumps →
    -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)
  flow : IsFlowLine κ b jumps u ψ P h η ζ
  one_sided : ∀ᵐ ω ∂P, Lx.LowerLaunch κ b jumps E (k + 1) ω →
    ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
      IsOneSided (lowerPrefix κ b jumps E (k + 1) u ω) (η ω) a

/-- The already proved, mutually compatible word, chart, and field inputs. -/
structure K2LaunchInputs (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) where
  entry : Ω → ℝ
  word : Ω → BoundaryWord
  types : Set WordType
  entry_measurable : Measurable[pastSigma κ b jumps
    (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] entry
  word_measurable : Measurable[pastSigma κ b jumps
    (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] word
  chart_measurable : IsMeasChart (pastSigma κ b jumps
    (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1))
    (fun ω => (verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω).recenter (entry ω))
  chart_eq : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
    (verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω).recenter (entry ω) =
    (launchChart κ b jumps E (k + 1) ω).recenter
      (launchEntry κ b jumps E (k + 1) u ω)
  field : ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
    IsPiecewiseConstantBoundaryData (word ω₀).fn (word ω₀).jumps ∧
    ∃ h' : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport
        ((verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω₀).recenter
          (entry ω₀)) 1 0 (chiC κ) (h ω) (h' ω)) ∧
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
        (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) ω₀)
        h' (word ω₀).fn (word ω₀).jumps
  frozen : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
    (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) ω₀),
    (verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω).recenter (entry ω) =
    (verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω₀).recenter (entry ω₀)
  types_countable : types.Countable
  cover : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → angleWordType κ ψ (word ω) ∈ types

/-- Named missing mathematics: construct the actual erased driver measurably,
identify its code using the marked union kernels, and retain its physical clock.
There is no assumed conditional flow-line law or chosen-trace link here. -/
def SB2ErasedDriverInputsStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ),
    ∃ (D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
      Measurable D ∧ (∀ ω, IsRegularDriver (D ω)) ∧
      (∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
        IsDriverCodeMatch (driverCode h12p H.kappa_pos ψ
          (I.word ω, Chart.chartTransport (I.chart_measurable.1 ω)
            1 0 (chiC κ) (h ω))) (D ω).1 (D ω).2) ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
        IsGeneratingTrace (D ω).1 (D ω).2 (γ ω) ∧
        IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => γ ω t + launchEntry κ b jumps E (k + 1) u ω) (D ω).2

end InteractingSLE.Theorem14.SB.Lv
