/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12CtxObjects

/-! # The physical word context simultaneously for every both-low index

All physical binders of `T12AsmTop` are existential conclusions here. The
side-reference and collar assertions are separate from this construction.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Ctx

open Current Sec7 Sec7.StripWall Sec7.PocketWordIn Sec7.StripMarks

/-- The space, field, counterflow, boundary, angles, means and path versions in
exactly the indexed physical binder form used by `T12AsmTop`. -/
theorem exists_physical_context :
    ∃ (Ωw : BothLow → Type) (mWord : ∀ i, MeasurableSpace (Ωw i))
      (_ : ∀ i, StandardBorelSpace (Ωw i)) (baseWord : ∀ i, @Now.StripObjects (Ωw i) (mWord i))
      (_ : ∀ i, IsProbabilityMeasure (baseWord i).measure)
      (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps),
      let word := Relay.words cond44 baseWord hWordb
      (∀ i, (baseWord i).boundary = boundary i) ∧
      (∀ i, (baseWord i).jumps = jumps) ∧
      (∀ i, IsGFFWithBoundaryData (baseWord i).measure (baseWord i).field (baseWord i).boundary (baseWord i).jumps) ∧
      (∀ i, IsCenteredCounterflowDriver (16 / i.kappa) (baseWord i).measure
        (baseWord i).field (baseWord i).driver (baseWord i).lifetime) ∧
      (∀ i, (∀ᵐ ω ∂(baseWord i).measure, (baseWord i).lifetime ω = ⊤)) ∧
      (∀ i, (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ z : ℝ, z < 0 → z ∉ (word i).jumps →
        (word i).boundary z + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))) ∧
      (∀ i, (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ z : ℝ, 0 < z → z ∉ (word i).jumps →
        sleLambda (16 / i.kappa) ≤ (word i).boundary z + a * chiC (16 / i.kappa))) ∧
      (∀ i, (word i).thetaR ∈ Ioo (-(π / 2)) (π / 2)) ∧
      (∀ i, (word i).thetaL ∈ Ioc (-(π / 2)) (π / 2)) ∧
      (∀ i, IsBoundedHarmonicExtension (word i).boundary (word i).jumps (word i).originalMean) ∧
      (∀ i, IsWallVersion (word i).measure
        ((word i).experiment (StripSys.alphaSpec (word i).thetaR)) 1 (word i).rightWall) ∧
      (∀ i, (∀ q, IsWallVersion (word i).measure
        ((word i).experiment (StripSys.betaSpec (StripSys.rt (positiveSeed q)) (word i).thetaL))
        (StripSys.rt (positiveSeed q)) ((word i).leftWall q))) ∧
      (∀ i, (∀ ω, Continuous ((word i).outerWall ω))) ∧
      (∀ i, (∀ ω, (word i).outerWall ω 0 = 0)) ∧
      (∀ i, (∀ t, Measurable fun ω => (word i).outerWall ω t)) ∧
      (∀ i, (∀ᵐ ω ∂(word i).measure,
        IsGeneratingTrace ((word i).experiment StripSys.leftExtremalSpec 0 ω).1 ⊤ ((word i).outerWall ω))) ∧
      (∀ i, (∀ ω, ContinuousOn ((word i).curve ω) (Ici 0))) ∧
      (∀ i, (∀ ω t, 0 ≤ t → (word i).curve ω t ∈ Hbar)) ∧
      (∀ i, (∀ ω, (word i).curve ω 0 = 0)) ∧
      (∀ i, (∀ t, 0 ≤ t → Measurable fun ω => (word i).curve ω t)) ∧
      (∀ i, (∀ᵐ ω ∂(word i).measure,
        IsGeneratingTrace (fun t => (word i).driver t ω) ⊤ (fun t : ℝ≥0 => (word i).curve ω t))) ∧
      (∀ i, InnerProductSpace.HarmonicOnNhd (word i).harmonic H) ∧
      (∀ i, (∃ M : ℝ, ∀ z ∈ H, |(word i).harmonic z| ≤ M)) ∧
      (∀ i, (∀ φ : TestOn upperHalfPlaneOpens, (word i).mean φ = ∫ z, (word i).harmonic z * φ z)) ∧
      (∀ i, (∀ z ∉ StripSysField.counterflowJumps (word i).jumps ∪ Sec5.Prop513Field.jumps
          (Real.exp (π * (aux130RefFrame i).x₀))
          (Sec4.stripHJumps {0} {(aux130RefFrame i).x₀}),
        StripSysField.counterflowData (16 / i.kappa) (word i).boundary z =
          Sec4.stripCounterflowData (16 / i.kappa) 0 (Real.exp (π * (aux130RefFrame i).x₀))
            (Sec5.fig51Lower (aux130RefFrame i).a (aux130RefFrame i).b)
            (Sec5.fig51Upper (aux130RefFrame i).x₀ (aux130RefFrame i).a' (aux130RefFrame i).b') z)) ∧
      (∀ i, (word i).thetaR = rs136Theta1 (16 / i.kappa) i.leftWeight) ∧
      (∀ i, (word i).thetaL = rs136Theta2 (16 / i.kappa) i.rightWeight) ∧
      (∀ i, ∀ hc : IsCenteredCounterflowDriver (16 / i.kappa) (word i).measure
          (word i).field (word i).driver (word i).lifetime,
        (word i).harmonic = (counterflowObjects hc).mean) := by
  classical
  choose Ω mΩ hSB x hP hb hs using exists_objects
  refine ⟨Ω, mΩ, hSB, x, hP, hb, ?_⟩
  simpa only [forall_and] using hs

end InteractingSLE.Wire.T12Ctx
