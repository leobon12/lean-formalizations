/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Initial

/-!
# The normalized physical initial mean of a branch-refined test

PROVE-SIDE-COLLAR2. The native source formula applies to every version
of the actual original exterior mean. Transport the proved source formula through the actual physical field
relations and use the exact native-word normalization.
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

/-- The actual original mean produces the normalized physical initial
mean formula. All native-word and source-flow identities are proved. -/
theorem initialMeanFormula_native_of_ready
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
      (conjugateFlowChart ((j.target i d).baseChart ω)) k)
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω))
    (hu₁ : InnerProductSpace.HarmonicOnNhd d.coupledMean H)
    (hHarm : EqOn d.harmonic d.coupledMean H) :
    let G := fun ω => physicalMean (-(π * chiC (16 / i.kappa))) (chiC i.kappa) 0
      d.originalMean d.coupledMean (g₀ ω)
    IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure G ∧
      ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
        harmRep (G ω) (H \ j.capacityReference i d 0 ω) z + (j.target i d).harmonic z +
          chiC (j.target i d).kappa * ((j.target i d).baseChart ω).2.2 z =
        j.initialWordExtension i d ω (((j.target i d).baseChart ω).1 z) -
          sourceFrameOffset (16 / i.kappa) 0 k := by
  let G := fun ω => physicalMean (-(π * chiC (16 / i.kappa))) (chiC i.kappa) 0
    d.originalMean d.coupledMean (g₀ ω)
  have hA := fun ω => WangWu.image_negInv_relClosed (j.original_filling_regular (i := i) hj 0 ω)
  have hMean := localSetMean_physicalMean hA hT hTr hu₀.1 hu₁ hg₀
  have hRep := ae_physicalMean_formula (a := -(π * chiC (16 / i.kappa)))
    (k := chiC i.kappa) (c := 0) hA hu₀.1 hu₁ hg₀
  simp only [WangWu.image_negInv_image_negInv] at hMean hRep
  have hFlow := j.ae_initialConjugateMean_native_of_ready h44 hS hcumL hcumR
    hu₀ hvR hvL hj hleft hg₀ k hbranch
  refine ⟨?_, ?_⟩
  · rw [target_zeroField]
    exact hMean
  · filter_upwards [hRep, hFlow] with ω hRepω hFlowω hω z hz
    have hBase := j.isDomainChart_baseChart hj hvR.continuous hvL.continuous hω
    have hComp : z ∈ H \ j.capacityReference i d 0 ω := by
      have hωj : ω ∈ j.event := by rwa [target_event] at hω
      rw [capacityReference, original_filling_zero, Sec7.PocketStopSide.eventFilled, ite_eq_left hωj]
      exact ⟨hBase.subset_H hz, fun h => (h.2.resolve_right (by simp)) hz⟩
    have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
    have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
    have hEq := frame_identity_of_conjugate_flow (κ := 16 / i.kappa) (div_pos (by norm_num) hκ)
      ((j.target i d).baseChart ω) (j.canonicalInitialFlowMean i d ω)
      (fun y => harmRep (g₀ ω) (H \ negInv '' j.capacityReference i d 0 ω) y + d.originalMean y)
      k 0 z (by simpa only [add_zero] using hFlowω hω z hz)
    rw [hd] at hEq
    rw [target_harmonic_eq, hHarm (hBase.subset_H hz), target_kappa_eq,
      ← j.canonicalInitialFlowMean_normalization hj hω (hBase.fwd_mem hz)]
    change harmRep (G ω) _ z + d.coupledMean z + _ = _
    have hRepz := hRepω z hComp
    change harmRep (G ω) (H \ j.capacityReference i d 0 ω) z + d.coupledMean z = _ at hRepz
    rw [hRepz]
    exact hEq

end InteractingSLE.Wire.Current.SideTest
