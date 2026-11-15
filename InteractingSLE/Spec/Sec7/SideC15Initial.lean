/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Exterior

/-!
# The actual original initial mean in a constant-branch test

PROVE-SIDE-COLLAR2. The native source formula applies to every version
of the actual original exterior mean. A constant source branch is the
R90a refined-test condition, with no assumed flow identity.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.Current.SideTest

open LocalSets WholeField WangWu Sec7 Sec7.SideC14 Sec7.SideC13 Sec7.SideC12 Sec7.Aux119Heights
  Sec7.PocketCoord Sec7.PocketWordPerQ Sec7.StripWall Sec7.StripSideHeightProb

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The original mean formula in the precise type consumed by the physical
frame, for the original reference and the actual native word. -/
theorem ae_initialConjugateMean_native_of_ready
    (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} [IsProbabilityMeasure d.measure]
    {b : ℝ → ℝ} {jumps : Finset ℝ} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) b jumps d.measure d.field W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps →
      sleLambda (16 / i.kappa) ≤ b y + a * chiC (16 / i.kappa))
    (hu₀ : IsBoundedHarmonicExtension b jumps d.originalMean)
    (hvR : IsWallVersion d.measure (E (StripSys.alphaSpec
      (rs136Theta1 (16 / i.kappa) i.leftWeight))) 1 d.rightWall)
    (hvL : IsWallVersion d.measure (E (StripSys.betaSpec (StripSys.rt j.seed)
      (rs136Theta2 (16 / i.kappa) i.rightWeight))) (StripSys.rt j.seed) (d.leftWall j.seed))
    (hj : j.Ready d)
    (hleft : ∀ᵐ ω ∂d.measure, ω ∈ j.event →
      changePocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) ⊆ leftSideOf (range (d.rightWall ω)))
    {g₀ : Ω → DistOn upperHalfPlaneOpens}
    (hg₀ : IsLocalSetMean (fun ω => negInv '' j.capacityReference i d 0 ω)
      (centredField d.field d.originalMean) d.measure g₀)
    (k : ℤ)
    (hbranch : ∀ ω ∈ j.event, Lemma71N.IsPocketBranch (d.leftWall j.seed ω) (d.rightWall ω)
      (conjugateFlowChart ((j.target i d).baseChart ω)) k) :
    ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
      harmRep (g₀ ω) (H \ negInv '' j.capacityReference i d 0 ω) (negInv z) +
        d.originalMean (negInv z) =
      j.canonicalInitialFlowMean i d ω (conjugateFlowMap ((j.target i d).baseChart ω) (negInv z)) -
        chiC (16 / i.kappa) * (conjugateFlowLift ((j.target i d).baseChart ω) (negInv z) + 2 * π * k) := by
  have hgC := hg₀
  rw [j.original_initial_exterior_eq_selected i d] at hgC
  have hSource := j.ae_initialFlowMean_native_of_ready h44 hS hcumL hcumR hu₀ hvR hvL hj hleft hgC
  filter_upwards [hSource, hg₀.2.1] with ω hSourceω hH hω z hz
  have hω' : ω ∈ j.event := by rwa [target_event] at hω
  have hF := j.isFlowChart_conjugate_of_ready hj hvR.continuous hvL.continuous hω
  have hComp : H \ negInv '' j.capacityReference i d 0 ω =
      changePocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) := by
    rw [congrFun (j.original_initial_exterior_eq_selected i d) ω,
      selectedChangePocket, ite_eq_left hω']
    exact sdiff_sdiff_cancel_left hF.config.changePocket_subset_H
  obtain ⟨hv, hrep⟩ := harmRep_spec hH
  rw [hComp] at hv hrep
  have hzC : negInv z ∈ changePocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) := by
    rw [target_domain] at hz
    obtain ⟨y, hy, he⟩ := hz
    rw [← he, negInv_negInv]
    exact hy
  rw [hComp]
  exact hSourceω hω' _ hv hrep k (hbranch ω hω') _ hzC

end InteractingSLE.Wire.Current.SideTest
