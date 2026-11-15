/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC17MeanExists
import InteractingSLE.Spec.Sec7.SideC17Source

/-! # The original source input exists on all unrefined physical tests

PROVE-SIDE-COLLAR2. Both mean existence and the measurable branch are
conclusions. The native source mean and its zero additive constant are
the ones in `ColCovSourceInput`; the principal-chart branch is retained.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Asm3
open Current LocalSets WholeField Sec7 Sec7.SideC13 Sec7.SideC12 Sec7.StripWall Sec7.PocketWordIn

variable {Ωw : BothLow → Type} [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    {baseWord : ∀ i, Now.StripObjects (Ωw i)} [∀ i, IsProbabilityMeasure (baseWord i).measure]
    {hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps}

/-- Every physical word context supplies the exact original source mean
with a walls-measurable, possibly sample-dependent branch. -/
theorem PhysCtx.exists_initial_source (hC : PhysCtx Ωw baseWord hWordb) (i : BothLow) :
    let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i
    let d := wordSafeObjects i x (hC.wordT i)
    ∃ (G₀ : SideTest (Ωw i) → Ωw i → DistOn upperHalfPlaneOpens)
      (n : SideTest (Ωw i) → Ωw i → ℤ),
      (∀ j, j.Ready d → Measurable[(j.target i d).walls] (n j)) ∧
      InitialPocketConjugateFlowMean i d G₀ (fun j => j.canonicalInitialFlowMean i d) n (fun _ => 0) := by
  classical
  let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i
  let hS := hC.wordT i
  let d := wordSafeObjects i x hS
  let : IsProbabilityMeasure d.measure := inferInstanceAs (IsProbabilityMeasure x.measure)
  have hEach : ∀ j : SideTest (Ωw i), ∃ (g₀ : Ωw i → DistOn upperHalfPlaneOpens) (n : Ωw i → ℤ),
      j.Ready d → Measurable[(j.target i d).walls] n ∧
        IsLocalSetMean (fun ω => WangWu.negInv '' j.capacityReference i d 0 ω)
          (centredField d.field d.originalMean) d.measure g₀ ∧
        ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
          Aux119Heights.harmRep (g₀ ω) (H \ WangWu.negInv '' j.capacityReference i d 0 ω)
              (WangWu.negInv z) + d.originalMean (WangWu.negInv z) =
            j.canonicalInitialFlowMean i d ω (conjugateFlowMap ((j.target i d).baseChart ω)
              (WangWu.negInv z)) - chiC (16 / i.kappa) *
                (conjugateFlowLift ((j.target i d).baseChart ω) (WangWu.negInv z) + 2 * π * (n ω)) := by
    intro j
    by_cases hj : j.Ready d
    · obtain ⟨g₀, hg₀⟩ := hC.exists_initial_original_mean i j hj
      have hvR := hC.hWordvα i
      have hvLp := hC.hWordvL i j.seed
      obtain ⟨n, hn, hbranch⟩ := j.exists_measurable_branch_of_ready i hj
        hvR.continuous hvLp.continuous hvLp.zero
      have hvR' := hvR
      change IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1 x.rightWall at hvR'
      have hθR : x.thetaR = rs136Theta1 (16 / i.kappa) i.leftWeight := hC.thetaR_eq i
      rw [hθR] at hvR'
      have hvL' := hvLp
      change IsWallVersion x.measure
        (x.experiment (StripSys.betaSpec (StripSys.rt (positiveSeed j.seed)) x.thetaL))
        (StripSys.rt (positiveSeed j.seed)) (x.leftWall j.seed) at hvL'
      have hθL : x.thetaL = rs136Theta2 (16 / i.kappa) i.rightWeight := hC.thetaL_eq i
      rw [hθL, positiveSeed_of_pos hj.1] at hvL'
      have hleft := T12Ctx.ae_changePocket_left_of_physical_context i x hS
        (hC.hWordleft i) (hC.hWordright i) (hC.hWordθ₂ i) (hC.hWordvL i)
        (hC.hWordβc i) (hC.hWordβ0 i) (hC.hWordβtr i) (hC.hWordηc i) (hC.hWordηtr i) j hj
      refine ⟨g₀, n, fun _ => ⟨hn, hg₀, ?_⟩⟩
      exact j.ae_initialConjugateMean_sample_of_ready T12Asm2.cond44Holds hS
        (hC.hWordleft i) (hC.hWordright i) (hC.hWordu₀ i) hvR' hvL' hj hleft hg₀ n hbranch
    · exact ⟨0, 0, fun h => (hj h).elim⟩
  choose G₀ n hEach using hEach
  refine ⟨G₀, n, fun j hj => (hEach j hj).1, ?_⟩
  intro j hj
  exact ⟨(hEach j hj).2.1, by simpa only [add_zero] using (hEach j hj).2.2⟩

end InteractingSLE.Wire.T12Asm3
