/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfNextZero
import InteractingSLE.Spec.Supplement.GW2ConeData

/-!
# Reading an original counterflow coupling back through the infinity-source chart

Packet PROVE-CFCHART2. The deterministic return-test identity supplies the reverse
chart clause directly from the given optional coupling.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfNext

open CfGiven LawUnique Coupling Restart Restart.DomainMarkov Sec7.StripSysField

/-- The infinity-source chart clause follows from an actual optional coupling of
the transported field. All tests and height shifts are deterministic. -/
theorem isChartCanon_source_of_optional_top {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {α a k : ℝ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h g : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling α xL xR ρL ρR P 𝓕 W VL VR B ζ g)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (ht : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (g ω)) :
    IsChartCanon α ρL ρR P (drivingFiltration P hX) W VL VR (fun _ => ⊤)
      (fun _ => infinitySourceChart) a k (fun ω => -h ω) := by
  obtain ⟨_, hcf⟩ := hC.exists_isCouplingCharFun
  have hg := Aux50Hit.ae_isGoodPath hC.1 hζ
  intro t φ
  let ψ := Chart.pushTest isConformal_infinityReturnChart φ
  let δ : ℝ := a * (∫ z, φ z) + k * ∫ z, infinitySourceChart.2.2 z * φ z
  let e : ℂ := Complex.exp (Complex.I * ((-δ : ℝ) : ℂ))
  have hfun : (fun ω => Complex.exp (Complex.I * ((-h ω) φ : ℂ))) =
      e • (fun ω => Complex.exp (Complex.I * (g ω ψ : ℂ))) := by
    funext ω
    have hret := Theorem14.GW2Cone.eq_returnField_of_isChartTransport (ht ω)
    change Complex.exp (Complex.I * ((-(h ω φ) : ℝ) : ℂ)) = _
    rw [hret, returnField_apply, Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
    congr 1
    dsimp only [e, δ, ψ]
    push_cast
    ring
  have hce := condExp_smul (μ := P) e (fun ω => Complex.exp (Complex.I * (g ω ψ : ℂ)))
    (drivingFiltration P hX t)
  have hlt : ∀ᵐ ω ∂P, ((t : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hζ.mono fun ω hω => hω ▸ ENNReal.coe_lt_top
  have h1 := hcf (fun _ => (t : WithTop ℝ≥0)) (isStoppingTime_const _ t) hlt
    (canonU α ρL ρR W VL VR t) (fun ω => isBoundedHarmonicExtension_bheProc ω t) ψ
  rw [IsStoppingTime.measurableSpace_const] at h1
  simp only [WithTop.untopD_coe] at h1
  filter_upwards [h1, hce, hg] with ω hcω hceω hgω hE
  let V := H \ fwdHull (fun r : ℝ => W r.toNNReal ω) t
  have hψV : tsupport ψ ⊆ V := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Supp8.HullDetGen.tsupport_pushTest_subset_image
      isConformal_infinityReturnChart (Subset.refl (tsupport φ)) hz
    obtain ⟨v, hv, he⟩ := hE.2 hw
    change WangWu.negInv w ∈ V
    change WangWu.negInv v = w at he
    rw [← he, WangWu.negInv_negInv]
    exact hv
  have hdis : Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => W r.toNNReal ω) t) :=
    disjoint_left.2 fun z hz hK => (hψV hz).2 hK
  have hw := hgω.continuous_rpath
  have hVo : IsOpen V := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw t.coe_nonneg
  have hcov := Mean.zeroGFFTestCov_pushTest_of_subset Chart.isConformal_infinitySourceChart
    hVo sdiff_subset hψV
  rw [Theorem14.GW2Cone.pushTest_source_return φ] at hcov
  have henergy := WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov
    (w := fun r => W r ω) hgω.2.2.1 hgω.2.1 (by rw [hgω.1]; exact ENNReal.coe_lt_top) ψ hdis
  have hcm := (Coupling.continuousOn_couplingMean (t := t) α hw.continuousOn
    (isBoundedHarmonicExtension_bheProc (κ := α) (ρL := ρL) (ρR := ρR)
      (W := W) (VL := VL) (VR := VR) ω t).1)
  have hmap : MapsTo infinitySourceChart.1 (infinitySourceChart.2.1 '' V)
      (hullDom (fun r => W r ω) t) := by
    rintro z ⟨w, hwV, rfl⟩
    rw [Chart.isConformal_infinitySourceChart.2.2 w hwV.1]
    exact mem_hullDom hw.continuousOn hwV.1 hwV.2
  have hsub : infinitySourceChart.2.1 '' V ⊆ infinitySourceChart.dom := by
    rintro z ⟨w, hwV, rfl⟩
    exact Chart.isConformal_infinitySourceChart.inv_mem_dom hwV.1
  have hMI : Integrable fun z =>
      couplingMean α (fun r : ℝ => W r.toNNReal ω) t (canonU α ρL ρR W VL VR t ω)
        (infinitySourceChart.1 z) * φ z :=
    MartMeans2.integrable_mul_test_of_continuousOn
      (hcm.comp (Chart.isConformal_infinitySourceChart.differentiableOn_fwd.continuousOn.mono hsub) hmap)
      φ hE.2
  have hφI : Integrable fun z => φ z := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hLI := MartMeans2.integrable_mul_test_of_continuousOn continuousOn_infinitySourceChart_lift'
    φ (Coupling.tsupport_subset_H φ)
  have hmean : (∫ z, (couplingMean α (fun r : ℝ => W r.toNNReal ω) t
        (canonU α ρL ρR W VL VR t ω) (infinitySourceChart.1 z) - a - k * infinitySourceChart.2.2 z) * φ z) =
      (∫ z, couplingMean α (fun r : ℝ => W r.toNNReal ω) t
        (canonU α ρL ρR W VL VR t ω) z * ψ z) - δ := by
    rw [show ψ = Chart.pushTest isConformal_infinityReturnChart φ from rfl,
      Chart.integral_mul_pushTest isConformal_infinityReturnChart φ]
    rw [show infinityReturnChart.2.1 = infinitySourceChart.1 from rfl]
    have hpt : (fun z => (couplingMean α (fun r : ℝ => W r.toNNReal ω) t
          (canonU α ρL ρR W VL VR t ω) (infinitySourceChart.1 z) - a - k * infinitySourceChart.2.2 z) * φ z) =
        fun z => (couplingMean α (fun r : ℝ => W r.toNNReal ω) t
          (canonU α ρL ρR W VL VR t ω) (infinitySourceChart.1 z) * φ z - a * φ z) -
            k * (infinitySourceChart.2.2 z * φ z) := by funext z; ring
    have hs₁ := integral_sub (hMI.sub (hφI.const_mul a)) (hLI.const_mul k)
    have hs₂ := integral_sub hMI (hφI.const_mul a)
    simp only [Pi.sub_apply] at hs₁ hs₂
    rw [hpt, hs₁, hs₂, integral_const_mul, integral_const_mul]
    dsimp only [δ]
    ring
  rw [hfun, hceω, Pi.smul_apply, smul_eq_mul, hcω hdis]
  unfold chartRhs
  rw [henergy, ← hcov, hmean, ← Complex.exp_add]
  congr 1
  dsimp only [e]
  push_cast
  ring

end InteractingSLE.Sec5.CfNext
