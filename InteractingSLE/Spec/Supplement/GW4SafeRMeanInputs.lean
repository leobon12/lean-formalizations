/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMeanCoords

/-!
# GW4: exact remaining phase-word analytic inputs

These are named hypotheses, not established source theorems. `ComponentPhaseCaps`
records the protected phase-word martingales used by Aux. 122, including the
seed upper bounds. The seed lower bounds come from the existing GW3 word bound.
`ComponentPhaseRepresentation` is the finite-word boundary
identification of the actual local-set mean, before removing its phase. In
particular it does not assume that phase is zero or assume the desired SLE law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull swallowTime)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart Supp8.Q3Stop Sec7.PhaseSel MartChar

/-- The remaining martingale and seed-bound inputs for the actual component
phase. All geometric-coordinate hypotheses of Aux. 122 are proved separately. -/
structure ComponentPhaseCaps {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (k : ℝ) (c₀ : BoundaryWord) (ν : Measure Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) where
  probability : IsProbabilityMeasure ν
  filtration : Filtration ℝ≥0 mΩ
  rightContinuous : filtration.IsRightContinuous
  adapted : StronglyAdapted filtration R
  seedL_upper : typedRhoL (wordType k c₀) (componentSeedL k c₀) ≤ k / 2 - 4
  seedR_upper : typedRhoR (wordType k c₀) (componentSeedR k c₀) ≤ k / 2 - 4
  phase : ℝ≥0 → Ω → ℝ
  caps : ℕ → Ω → ℝ≥0
  stopping : ∀ n, IsStoppingTime filtration fun ω => (caps n ω : WithTop ℝ≥0)
  cover : ∀ᵐ ω ∂ν, ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω → ∃ n, q ≤ caps n ω
  quantized : ∀ n (q : ℝ≥0) ω, 0 < q → q ≤ caps n ω →
    ∃ j : ℤ, phase q ω = j * phaseStep k
  martingales : ∀ n (U : Ω → ℝ≥0 → ℂ → ℝ), (∀ ω q, IsBoundedHarmonicExtension
      (phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
        (fun i => componentVL k c₀ X R V i q ω - R q ω)
        (fun j => componentVR k c₀ X R V j q ω - R q ω) (phase q ω))
      (forceJumpSet (fun i => componentVL k c₀ X R V i q ω - R q ω)
        (fun j => componentVR k c₀ X R V j q ω - R q ω)) (U ω q)) →
    ∀ z ∈ H, IsLocalMartingaleBefore filtration ν
      (fun ω => min (swallowTime (wpath R ω) z : WithTop ℝ≥0) (caps n ω))
      (fun q ω => couplingMean k (wpath R ω) q (U ω q) z)
  continuity : ∀ n (U : Ω → ℝ≥0 → ℂ → ℝ), (∀ ω q, IsBoundedHarmonicExtension
      (phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
        (fun i => componentVL k c₀ X R V i q ω - R q ω)
        (fun j => componentVR k c₀ X R V j q ω - R q ω) (phase q ω))
      (forceJumpSet (fun i => componentVL k c₀ X R V i q ω - R q ω)
        (fun j => componentVR k c₀ X R V j q ω - R q ω)) (U ω q)) →
    ∀ ω (z : ℂ) (T : ℝ), 0 ≤ T → (T.toNNReal : WithTop ℝ≥0) ≤ caps n ω →
      z ∈ H \ fwdHull (wpath R ω) T →
      ContinuousOn (fun q : ℝ => couplingMean k (wpath R ω) q (U ω q.toNNReal) z)
        (Icc 0 T)

/-- The boundary-collar and harmonic-uniqueness step still needed for the
actual component mean. The exception set must retain every incident prime-end
fiber over each excluded physical point. This predicate does not assert that
those fibers form a finite set of prime ends. -/
def ComponentPhaseRepresentation {Ω : Type*} [MeasurableSpace Ω]
    (k : ℝ) (c₀ : BoundaryWord) (F : Frame) (ν : Measure Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ)
    (B : ℝ≥0 → Ω → Set ℂ) (d : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t (g : Ω → DistOn upperHalfPlaneOpens), IsLocalSetMean (B t) (centredField X u₀) ν g →
    ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
      ∃ w G : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd w (H \ B t ω) ∧
        (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ B t ω →
          g ω ψ = ∫ z, w z * ψ z) ∧
        IsBoundedHarmonicExtension
          (phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
            (fun i => componentVL k c₀ X R V i
              (lineClock F Wd GT V t ω).toNNReal ω -
                R (lineClock F Wd GT V t ω).toNNReal ω)
            (fun j => componentVR k c₀ X R V j
              (lineClock F Wd GT V t ω).toNNReal ω -
                R (lineClock F Wd GT V t ω).toNNReal ω)
            (d (lineClock F Wd GT V t ω).toNNReal ω))
          (forceJumpSet
            (fun i => componentVL k c₀ X R V i
              (lineClock F Wd GT V t ω).toNNReal ω -
                R (lineClock F Wd GT V t ω).toNNReal ω)
            (fun j => componentVR k c₀ X R V j
              (lineClock F Wd GT V t ω).toNNReal ω -
                R (lineClock F Wd GT V t ω).toNNReal ω)) G ∧
        EqOn (fun z => w z + u₀ z)
          (couplingMean k (wpath R ω) (lineClock F Wd GT V t ω).toNNReal G)
          (H \ B t ω)

end InteractingSLE.Theorem14.GW4Fix
