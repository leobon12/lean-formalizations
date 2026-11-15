/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Meas
import InteractingSLE.Spec.Supplement.GB6MeasChart
import InteractingSLE.Spec.Jordan.Transport

/-!
# The kernel at the stop read in the record chart

Packet PROVE-STAGEDLAW3. Deterministic transport of the kernel at the stop (`ae_condExp_cexp_stop`, in the original
domain) to the half-plane of the record chart `c = recChart r = (f_T, f_T⁻¹, arg f_T′)` (rule (1.4)):

* `recField_apply_eq`: the field read in the record chart is `h'(pushTest φ) + chartShift`, where `h' = g + θχ` is the
  flow-line field and `chartShift = χ ∫ (arg f_T′ ∘ f_T⁻¹) φ − θχ ∫ φ`;
* **`cexp_chartShift_mul_eq_gaussCF`**: the conditional characteristic value at the pushed test function, times the
  shift, is the Gaussian characteristic value `gaussCF` of the force word: the mean transforms by the change of
  variables (`fwd ∘ inv = id`, the lift cancels `− χ arg f′`), the variance by conformal invariance;
* `ae_condExp_eq_of_setIntegral_eq`: a conditional expectation identified on an event from set integrals.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged Restart LQGMetric

/-! ### The field in the record chart -/

/-- The deterministic shift of the field read in the record chart. -/
def chartShift (κ θ : ℝ) (r : RecData) (φ : TestOn upperHalfPlaneOpens) : ℝ :=
  chiC κ * (∫ w, (recChart r).2.2 ((recChart r).2.1 w) * φ w) - θ * chiC κ * ∫ w, φ w

/-- **The field read in the record chart is the flow-line field at the pushed test function plus the shift.** -/
theorem recField_apply_eq {κ θ : ℝ} {g h' : DistOn upperHalfPlaneOpens}
    (htr : IsTranslateAddConst 0 (θ * chiC κ) g h') (r : RecData) (φ : TestOn upperHalfPlaneOpens) :
    recField κ r g φ = h' (Chart.pushTest (isConformal_recChart r) φ) + chartShift κ θ r φ := by
  have h1 := IsChartTransport.apply_eq (isConformal_recChart r) (isChartTransport_recField κ r g) φ
  have h2 := htr (Chart.pushTest (isConformal_recChart r) φ) (Chart.pushTest (isConformal_recChart r) φ)
    (fun z => by rw [Complex.ofReal_zero, add_zero])
  rw [Chart.integral_pushTest] at h2
  rw [h1, h2, chartShift]
  ring

theorem coe_upperHalfPlaneOpens : ((upperHalfPlaneOpens : TopologicalSpace.Opens ℂ) : Set ℂ) = H := rfl

/-- The domain of the record chart is the complement of the hull at the stop. -/
theorem coe_dom_recChart (r : RecData) : ((recChart r).dom : Set ℂ) = H \ stopHull r := by
  rw [recChart_eq]
  exact Supp8.GB6.loewner_dom_eq (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)

theorem isOpen_compl_stopHull (r : RecData) : IsOpen (H \ stopHull r) := by
  rw [← coe_dom_recChart]
  exact (recChart r).dom.isOpen

/-- **The kernel at the pushed test function, times the shift, is the Gaussian characteristic value of the force
word.** -/
theorem cexp_chartShift_mul_eq_gaussCF (κ θ : ℝ) (nL nR : ℕ) (xLp xRp ρLp ρRp : ℕ → ℝ) (r : RecData)
    (φ : TestOn upperHalfPlaneOpens) :
    Complex.exp (Complex.I * (chartShift κ θ r φ : ℂ)) *
      Complex.exp (Complex.I * ((∫ z, stopMean κ nL nR xLp xRp ρLp ρRp (θ * chiC κ) r z *
          Chart.pushTest (isConformal_recChart r) φ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov (H \ stopHull r) (Chart.pushTest (isConformal_recChart r) φ)
          (Chart.pushTest (isConformal_recChart r) φ) : ℝ) : ℂ)) =
      gaussCF (forceWord κ nL nR (fun i => markPosL (rdrv r) (rtime r) (xLp i))
        (fun j => markPos (rdrv r) (rtime r) (xRp j)) ρLp ρRp (θ * chiC κ)) φ := by
  set hc := isConformal_recChart r
  set c := recChart r with hcdef
  set wd := forceWord κ nL nR (fun i => markPosL (rdrv r) (rtime r) (xLp i))
    (fun j => markPos (rdrv r) (rtime r) (xRp j)) ρLp ρRp (θ * chiC κ) with hwd
  set uS : ℂ → ℝ := fun y => wd.mean y + θ * chiC κ with huS
  have hmc : ContinuousOn wd.mean H :=
    LocalExt.continuousOn_of_isBoundedHarmonicExtension
      (BoundaryWord.isBoundedHarmonicExtension_mean _ (isSorted_forceWord _ _ _ _ _ _ _ _))
  have hlift : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H :=
    hc.continuousOn_lift_inv (LocalExt.continuousOn_lift_histChart (recHist r))
  -- the mean
  have hpt : ∀ w, stopMean κ nL nR xLp xRp ρLp ρRp (θ * chiC κ) r (c.2.1 w) * φ w =
      wd.mean w * φ w + θ * chiC κ * φ w - chiC κ * (c.2.2 (c.2.1 w) * φ w) := by
    intro w
    by_cases hw : w ∈ H
    · have hc' : c = Chart.id.loewner (rdrv r) (rtime r) := recChart_eq r
      have e1 : c.2.1 w = fwdMapInv (rdrv r) (rtime r) w := by rw [hc']; rfl
      have e2 : c.2.2 (c.2.1 w) = (logDerivFwd (rdrv r) (rtime r) (fwdMapInv (rdrv r) (rtime r) w)).im := by
        rw [e1, hc']
        change (logDerivFwd (rdrv r) (rtime r) (fwdMapInv (rdrv r) (rtime r) w)).im + 0 = _
        rw [add_zero]
      rw [e2, e1]
      unfold stopMean couplingMean
      rw [RS.fwdMap_fwdMapInv (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hw]
      ring
    · have h0 : φ w = 0 := φ.zero_on_compl hw
      simp only [h0, mul_zero, sub_zero, add_zero]
  have hI1 : Integrable fun w => wd.mean w * φ w :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hmc φ φ.tsupport_subset
  have hI0 : Integrable fun w => φ w := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hI2 : Integrable fun w => c.2.2 (c.2.1 w) * φ w :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hlift φ φ.tsupport_subset
  have hmean : (∫ z, stopMean κ nL nR xLp xRp ρLp ρRp (θ * chiC κ) r z * Chart.pushTest hc φ z) =
      (∫ w, wd.mean w * φ w) + θ * chiC κ * (∫ w, φ w) - chiC κ * ∫ w, c.2.2 (c.2.1 w) * φ w := by
    have hA : Integrable fun w => wd.mean w * φ w + θ * chiC κ * φ w := hI1.add (hI0.const_mul _)
    have hB : Integrable fun w => chiC κ * (c.2.2 (c.2.1 w) * φ w) := hI2.const_mul _
    rw [Chart.integral_mul_pushTest hc φ, integral_congr_ae (Eventually.of_forall hpt), integral_sub hA hB,
      integral_add hI1 (hI0.const_mul _), integral_const_mul, integral_const_mul]
  -- the variance
  have hvar : zeroGFFTestCov (H \ stopHull r) (Chart.pushTest hc φ) (Chart.pushTest hc φ) =
      zeroGFFTestCov H φ φ := by
    rw [← coe_dom_recChart r]
    exact Chart.zeroGFFTestCov_pushTest hc φ φ
  rw [hmean, hvar, ← Complex.exp_add]
  unfold gaussCF
  congr 1
  unfold chartShift
  rw [coe_upperHalfPlaneOpens]
  push_cast
  ring

/-! ### Conditional expectations identified on an event -/

/-- **A conditional expectation identified on an event from set integrals.** -/
theorem ae_condExp_eq_of_setIntegral_eq {Ω : Type*} {m mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsFiniteMeasure Q] (hm : m ≤ mΩ) {F : Set Ω} (hF : MeasurableSet[m] F) {X Y : Ω → ℂ}
    (hX : Integrable X Q) (hY : StronglyMeasurable[m] Y) (hYi : Integrable Y Q)
    (h : ∀ A, MeasurableSet[m] A → ∫ ω in A ∩ F, X ω ∂Q = ∫ ω in A ∩ F, Y ω ∂Q) :
    ∀ᵐ ω ∂Q, ω ∈ F → Q[X|m] ω = Y ω := by
  have hFm : MeasurableSet F := hm F hF
  have h1 : F.indicator Y =ᵐ[Q] Q[F.indicator X|m] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm (hX.indicator hFm)
      (fun s _ _ => (hYi.indicator hFm).integrableOn) (fun s hs _ => ?_)
      ((hY.indicator hF).aestronglyMeasurable)
    rw [setIntegral_indicator hFm, setIntegral_indicator hFm]
    exact (h s hs).symm
  have h2 : Q[F.indicator X|m] =ᵐ[Q] F.indicator (Q[X|m]) := condExp_indicator hX hF
  filter_upwards [h1, h2] with ω h1 h2 hω
  rw [indicator_of_mem hω] at h1
  rw [h1, h2, indicator_of_mem hω]

end StagedLaw

end Exist

end InteractingSLE
