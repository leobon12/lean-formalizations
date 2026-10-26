import SupercriticalConformalCovariance.ZBConformal.PositivePart
import LQGMetric.Field.ZeroBoundaryAffine

set_option autoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace Set Function
open QuantumZipper QuantumZipper.K3
open LQGMetric
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.ZBConformal

/-- Adapt the statement candidate to QuantumZipper's conformal map API. -/
theorem isConformalOnto {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) :
    IsConformalOnto φ U V where
  isOpen := U.isOpen
  diffOn := hφ.1
  injOn := hφ.2.injOn
  image_eq := hφ.2.image_eq
  deriv_ne := fun _x hx => QuantumZipper.CA.deriv_ne_zero_of_injOn U.isOpen hφ.1 hφ.2.injOn hx

/-- Positive test measures have matching pairings with smooth functions after pushforward. -/
theorem integral_pos_transport_measure {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (ψ : TestOn U)
    (f : ℂ → ℝ) (hf : Continuous f) :
    ∫ y, f y ∂(testMeasPos (confPushTest hφ ψ)) =
      ∫ y, f y ∂((testMeasPos ψ).restrict U |>.map φ) := by
  have hμ : IsFiniteMeasure (testMeasPos ψ) :=
    (K3.isGoodMeas_withDensity ψ.continuous ψ.hasCompactSupport).1
  have hμ' : IsFiniteMeasure (testMeasPos (confPushTest hφ ψ)) :=
    (K3.isGoodMeas_withDensity (confPushTest hφ ψ).continuous
      (confPushTest hφ ψ).hasCompactSupport).1
  have hcarry : (testMeasPos ψ) (U : Set ℂ)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 ψ.tsupport_subset)
      (testMeasPos_compl_tsupport ψ)
  have hres : (testMeasPos ψ).restrict U = testMeasPos ψ :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (by simpa [compl_def] using hcarry))
  have hae : AEMeasurable φ (testMeasPos ψ) := by
    rw [← hres]
    exact ContinuousOn.aemeasurable hφ.1.continuousOn U.isOpen.measurableSet
  rw [hres, integral_map hae hf.aestronglyMeasurable,
    K3.integral_testMeasPos_K3 (confPushTest hφ ψ).continuous.measurable,
    K3.integral_testMeasPos_K3 ψ.continuous.measurable]
  have h := integral_max_confPushTest hφ ψ f
  simpa only [mul_comm] using h

/-- Negative test measures have matching pairings with smooth functions after pushforward. -/
theorem integral_neg_transport_measure {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (ψ : TestOn U)
    (f : ℂ → ℝ) (hf : Continuous f) :
    ∫ y, f y ∂(testMeasNeg (confPushTest hφ ψ)) =
      ∫ y, f y ∂((testMeasNeg ψ).restrict U |>.map φ) := by
  have hμ : IsFiniteMeasure (testMeasNeg ψ) :=
    (K3.isGoodMeas_withDensity ψ.continuous.neg ψ.hasCompactSupport.neg).1
  have hμ' : IsFiniteMeasure (testMeasNeg (confPushTest hφ ψ)) :=
    (K3.isGoodMeas_withDensity (confPushTest hφ ψ).continuous.neg
      (confPushTest hφ ψ).hasCompactSupport.neg).1
  have hcarry : (testMeasNeg ψ) (U : Set ℂ)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 ψ.tsupport_subset)
      (testMeasNeg_compl_tsupport ψ)
  have hres : (testMeasNeg ψ).restrict U = testMeasNeg ψ :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (by simpa [compl_def] using hcarry))
  have hae : AEMeasurable φ (testMeasNeg ψ) := by
    rw [← hres]
    exact ContinuousOn.aemeasurable hφ.1.continuousOn U.isOpen.measurableSet
  rw [hres, integral_map hae hf.aestronglyMeasurable,
    K3.integral_testMeasNeg_K3 (confPushTest hφ ψ).continuous.measurable,
    K3.integral_testMeasNeg_K3 ψ.continuous.measurable]
  have h := integral_max_neg_confPushTest hφ ψ f
  simpa only [mul_comm] using h


/-- Dual Dirichlet norm transport from equality of its test-function pairings. -/
theorem dualNormSq_transport {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) {μ μ' : Measure ℂ}
    [IsFiniteMeasure μ]
    (hpair : ∀ f ∈ zeroSpace V,
      ∫ y, f y ∂μ' = ∫ y, f y ∂((μ.restrict U).map φ)) :
    dualNormSq V (zeroSpace V) μ' = dualNormSq U (zeroSpace U) μ := by
  rw [K3.dualNormSq_conformal (isConformalOnto hφ) μ]
  have h := LQGMetric.dualNormSq_eq_of_integral_eq_mul
    (D := (V : Set ℂ)) (V := zeroSpace V)
    (μ := μ') (ν := (μ.restrict U).map φ) (c := 1) (by
      intro f hf
      simpa using hpair f hf)
  simpa using h


/-- Covariance transport for finite measures whose pairings obey substitution. -/
theorem dualCov_transport {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) {μ₁ μ₂ μ₁' μ₂' : Measure ℂ}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₁'] [IsFiniteMeasure μ₂']
    (hpair₁ : ∀ f : ℂ → ℝ, Continuous f →
      ∫ y, f y ∂μ₁' = ∫ y, f y ∂((μ₁.restrict U).map φ))
    (hpair₂ : ∀ f : ℂ → ℝ, Continuous f →
      ∫ y, f y ∂μ₂' = ∫ y, f y ∂((μ₂.restrict U).map φ)) :
    dualCov V (zeroSpace V) μ₁' μ₂' = dualCov U (zeroSpace U) μ₁ μ₂ := by
  have hae₁ : AEMeasurable φ (μ₁.restrict U) :=
    ContinuousOn.aemeasurable hφ.1.continuousOn U.isOpen.measurableSet
  have hae₂ : AEMeasurable φ (μ₂.restrict U) :=
    ContinuousOn.aemeasurable hφ.1.continuousOn U.isOpen.measurableSet
  have hpairAdd : ∀ f ∈ zeroSpace V,
      ∫ y, f y ∂(μ₁' + μ₂') =
        ∫ y, f y ∂(((μ₁ + μ₂).restrict U).map φ) := by
    intro f hf
    have hfint₁' : Integrable f μ₁' := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    have hfint₂' : Integrable f μ₂' := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    have hfint₁ : Integrable f ((μ₁.restrict U).map φ) :=
      hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    have hfint₂ : Integrable f ((μ₂.restrict U).map φ) :=
      hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    rw [Measure.restrict_add, AEMeasurable.map_add₀ hae₁ hae₂,
      integral_add_measure hfint₁' hfint₂', integral_add_measure hfint₁ hfint₂,
      hpair₁ f hf.1.continuous, hpair₂ f hf.1.continuous]
  unfold dualCov
  rw [dualNormSq_transport hφ hpairAdd,
    dualNormSq_transport hφ (fun f hf => hpair₁ f hf.1.continuous),
    dualNormSq_transport hφ (fun f hf => hpair₂ f hf.1.continuous)]

/-- The zero-boundary GFF covariance is invariant under conformal pullback. -/
theorem zeroGFFTestCov_conformal {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (ψ χ : TestOn U) :
    zeroGFFTestCov V (confPushTest hφ ψ) (confPushTest hφ χ) =
      zeroGFFTestCov U ψ χ := by
  have : IsFiniteMeasure (testMeasPos ψ) :=
    (K3.isGoodMeas_withDensity ψ.continuous ψ.hasCompactSupport).1
  have : IsFiniteMeasure (testMeasNeg ψ) :=
    (K3.isGoodMeas_withDensity ψ.continuous.neg ψ.hasCompactSupport.neg).1
  have : IsFiniteMeasure (testMeasPos χ) :=
    (K3.isGoodMeas_withDensity χ.continuous χ.hasCompactSupport).1
  have : IsFiniteMeasure (testMeasNeg χ) :=
    (K3.isGoodMeas_withDensity χ.continuous.neg χ.hasCompactSupport.neg).1
  have : IsFiniteMeasure (testMeasPos (confPushTest hφ ψ)) :=
    (K3.isGoodMeas_withDensity (confPushTest hφ ψ).continuous
      (confPushTest hφ ψ).hasCompactSupport).1
  have : IsFiniteMeasure (testMeasNeg (confPushTest hφ ψ)) :=
    (K3.isGoodMeas_withDensity (confPushTest hφ ψ).continuous.neg
      (confPushTest hφ ψ).hasCompactSupport.neg).1
  have : IsFiniteMeasure (testMeasPos (confPushTest hφ χ)) :=
    (K3.isGoodMeas_withDensity (confPushTest hφ χ).continuous
      (confPushTest hφ χ).hasCompactSupport).1
  have : IsFiniteMeasure (testMeasNeg (confPushTest hφ χ)) :=
    (K3.isGoodMeas_withDensity (confPushTest hφ χ).continuous.neg
      (confPushTest hφ χ).hasCompactSupport.neg).1
  unfold zeroGFFTestCov
  rw [dualCov_transport hφ (integral_pos_transport_measure hφ ψ)
      (integral_pos_transport_measure hφ χ),
    dualCov_transport hφ (integral_pos_transport_measure hφ ψ)
      (integral_neg_transport_measure hφ χ),
    dualCov_transport hφ (integral_neg_transport_measure hφ ψ)
      (integral_pos_transport_measure hφ χ),
    dualCov_transport hφ (integral_neg_transport_measure hφ ψ)
      (integral_neg_transport_measure hφ χ)]

/-- Admissibility transfers from the target to the source under conformal pullback. -/
theorem zbAdmissible_of_conf {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (hadmV : ZBAdmissible V) :
    ZBAdmissible U := by
  intro ψ
  have h := hadmV (confPushTest hφ ψ)
  have : IsFiniteMeasure (testMeasPos ψ) :=
    (K3.isGoodMeas_withDensity ψ.continuous ψ.hasCompactSupport).1
  have : IsFiniteMeasure (testMeasNeg ψ) :=
    (K3.isGoodMeas_withDensity ψ.continuous.neg ψ.hasCompactSupport.neg).1
  have hposNorm := dualNormSq_transport hφ (μ := testMeasPos ψ)
    (μ' := testMeasPos (confPushTest hφ ψ))
    (fun f hf => integral_pos_transport_measure hφ ψ f hf.1.continuous)
  have hnegNorm := dualNormSq_transport hφ (μ := testMeasNeg ψ)
    (μ' := testMeasNeg (confPushTest hφ ψ))
    (fun f hf => integral_neg_transport_measure hφ ψ f hf.1.continuous)
  constructor
  · refine ⟨(K3.isGoodMeas_withDensity ψ.continuous ψ.hasCompactSupport).1,
      ⟨tsupport ψ, ψ.hasCompactSupport.isCompact,
        ψ.tsupport_subset.trans subset_closure,
        testMeasPos_compl_tsupport ψ⟩, ?_⟩
    rw [← hposNorm]
    exact h.1.2.2
  · refine ⟨(K3.isGoodMeas_withDensity ψ.continuous.neg ψ.hasCompactSupport.neg).1,
      ⟨tsupport ψ, ψ.hasCompactSupport.isCompact,
        ψ.tsupport_subset.trans subset_closure,
        testMeasNeg_compl_tsupport ψ⟩, ?_⟩
    rw [← hnegNorm]
    exact h.2.2.2
end SupercriticalConformalCovariance.ZBConformal
