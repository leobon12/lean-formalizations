/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12CtxVersions

/-! # Existence of the physical strip objects in the assembly's binder form

Every boundary, field, driver and path here is an actual witness of the
corresponding construction. The harmonic representative is the mean of the
chosen counterflow decomposition. Side-reference data are treated separately.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Ctx

open Current Sec7 Sec7.StripWall Sec7.PocketWordIn Sec7.StripMarks

/-- All physical word binders for one both-low index, on the same probability space. -/
theorem exists_objects (i : BothLow) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω)
      (x : Now.StripObjects Ω) (_ : IsProbabilityMeasure x.measure)
      (hb : IsPiecewiseConstantBoundaryData x.boundary x.jumps),
      let y := Sec5.TwoAngle.withTwoAngle cond44 i x hb
      x.boundary = boundary i ∧ x.jumps = jumps ∧
      IsGFFWithBoundaryData x.measure x.field x.boundary x.jumps ∧
      IsCenteredCounterflowDriver (16 / i.kappa) x.measure x.field x.driver x.lifetime ∧
      (∀ᵐ ω ∂x.measure, x.lifetime ω = ⊤) ∧
      (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ z : ℝ, z < 0 → z ∉ y.jumps →
        y.boundary z + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa)) ∧
      (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ z : ℝ, 0 < z → z ∉ y.jumps →
        sleLambda (16 / i.kappa) ≤ y.boundary z + a * chiC (16 / i.kappa)) ∧
      y.thetaR ∈ Ioo (-(π / 2)) (π / 2) ∧
      y.thetaL ∈ Ioc (-(π / 2)) (π / 2) ∧
      IsBoundedHarmonicExtension y.boundary y.jumps y.originalMean ∧
      IsWallVersion y.measure (y.experiment (StripSys.alphaSpec y.thetaR)) 1 y.rightWall ∧
      (∀ q, IsWallVersion y.measure
        (y.experiment (StripSys.betaSpec (StripSys.rt (positiveSeed q)) y.thetaL))
        (StripSys.rt (positiveSeed q)) (y.leftWall q)) ∧
      (∀ ω, Continuous (y.outerWall ω)) ∧
      (∀ ω, y.outerWall ω 0 = 0) ∧
      (∀ t, Measurable fun ω => y.outerWall ω t) ∧
      (∀ᵐ ω ∂y.measure,
        IsGeneratingTrace (y.experiment StripSys.leftExtremalSpec 0 ω).1 ⊤ (y.outerWall ω)) ∧
      (∀ ω, ContinuousOn (y.curve ω) (Ici 0)) ∧
      (∀ ω t, 0 ≤ t → y.curve ω t ∈ Hbar) ∧
      (∀ ω, y.curve ω 0 = 0) ∧
      (∀ t, 0 ≤ t → Measurable fun ω => y.curve ω t) ∧
      (∀ᵐ ω ∂y.measure,
        IsGeneratingTrace (fun t => y.driver t ω) ⊤ (fun t : ℝ≥0 => y.curve ω t)) ∧
      InnerProductSpace.HarmonicOnNhd y.harmonic H ∧
      (∃ M : ℝ, ∀ z ∈ H, |y.harmonic z| ≤ M) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, y.mean φ = ∫ z, y.harmonic z * φ z) ∧
      (∀ z ∉ StripSysField.counterflowJumps y.jumps ∪ Sec5.Prop513Field.jumps
          (Real.exp (π * (aux130RefFrame i).x₀))
          (Sec4.stripHJumps {0} {(aux130RefFrame i).x₀}),
        StripSysField.counterflowData (16 / i.kappa) y.boundary z =
          Sec4.stripCounterflowData (16 / i.kappa) 0 (Real.exp (π * (aux130RefFrame i).x₀))
            (Sec5.fig51Lower (aux130RefFrame i).a (aux130RefFrame i).b)
            (Sec5.fig51Upper (aux130RefFrame i).x₀ (aux130RefFrame i).a' (aux130RefFrame i).b') z) ∧
      y.thetaR = rs136Theta1 (16 / i.kappa) i.leftWeight ∧
      y.thetaL = rs136Theta2 (16 / i.kappa) i.rightWeight ∧
      (∀ hc : IsCenteredCounterflowDriver (16 / i.kappa) y.measure y.field y.driver y.lifetime,
        y.harmonic = (counterflowObjects hc).mean) := by
  obtain ⟨Ω, mΩ, hSB, P, hP, h, W, ζ, hh, hcf, hζ⟩ := exists_counterflow i
  obtain ⟨u₀, hu₀⟩ := exists_originalMean i
  obtain ⟨hleft, hright⟩ := boundary_heights i
  obtain ⟨hθR, hθL⟩ := angles i
  obtain ⟨hS, hreg⟩ := experiments_system i hh hcf hζ
  obtain ⟨R, hR⟩ := exists_rightWall hS hleft hright (Ioo_subset_Icc_self hθR) (fun k ω => hreg _ k ω)
  obtain ⟨L, hL⟩ := exists_leftWalls hS hleft hright (Ioc_subset_Icc_self hθL)
    (fun r k ω => hreg _ k ω)
  obtain ⟨β, hβc, hβ0, hβm, hβtr⟩ := exists_outerWall hS hleft hright
  obtain ⟨η, hηc, hηH, hη0, hηm, hηtr⟩ := exists_curve hS hleft hright
  let c := counterflowObjects hcf
  have hu := (counterflowObjects_spec hcf).2.2.2
  let x : Now.StripObjects Ω := {
    measure := P
    boundary := boundary i
    jumps := jumps
    field := h
    driver := W
    lifetime := ζ
    experiment := experiments i h
    thetaR := rs136Theta1 (16 / i.kappa) i.leftWeight
    thetaL := rs136Theta2 (16 / i.kappa) i.rightWeight
    originalMean := u₀
    rightWall := R
    outerWall := β
    leftWall := L
    curve := η
    harmonic := c.mean
    mean := smoothDist upperHalfPlaneOpens c.mean }
  refine ⟨Ω, mΩ, hSB, x, hP, boundary_piecewise i, rfl, rfl,
    hh, hcf, hζ, hleft, hright, hθR, hθL, hu₀, hR, hL,
    hβc, hβ0, hβm, hβtr, hηc, hηH, hη0, hηm, hηtr, hu.1, hu.2.1, ?_, reference_word i,
    rfl, rfl, fun _ => rfl⟩
  intro φ
  simpa only [mul_comm] using smoothDist_apply hu.1.continuousOn φ

end InteractingSLE.Wire.T12Ctx
