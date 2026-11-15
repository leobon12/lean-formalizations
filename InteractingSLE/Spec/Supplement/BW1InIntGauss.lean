/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Impl.PiecewiseConstant
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# A uniform first-moment bound for the pairings of a GFF with bounded piecewise-constant data

Packet PROVE-BW1-INPUTS (the integrability clause of BW1's relative safe law). Two generic facts:

* **the maximum principle for piecewise-constant data** (`abs_le_of_isBoundedHarmonicExtension`): a bounded harmonic
  extension of piecewise-constant data `b` off its jumps is bounded on `ℍ` by any bound `M ≥ 0` of `|b|` off the jumps
  (it agrees on `ℍ` with the explicit step extension, a convex combination of the values);
* **the first moment of a pairing** (`lintegral_enorm_apply_le_of_isGFF`): for a GFF `X` with such data and a test
  function `φ`, `E‖X φ‖ ≤ M ∫ |φ| + ∫ |x| dN(0, v_φ)`, where `v_φ = zeroGFFTestCov φ φ` does not depend on the data
  (the centred part is the zero-boundary GFF, whose pairing has the law `N(0, v_φ)`).

The bound is uniform over all data bounded by `M`, which is what the integrability of a field that is conditionally a
GFF with bounded random data needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.BW1In

/-- **The maximum principle for piecewise-constant data**: a bounded harmonic extension of piecewise-constant data
bounded by `M ≥ 0` off the jumps is bounded by `M` on `ℍ`. -/
theorem abs_le_of_isBoundedHarmonicExtension {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y ∉ J, |b y| ≤ M) {u : ℂ → ℝ} (hu : IsBoundedHarmonicExtension b J u) :
    ∀ z ∈ QuantumZipper.H, |u z| ≤ M := by
  classical
  intro z hz
  have heq := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension J.finite_toSet
    (PiecewiseConstant.isBoundedHarmonicExtension_harmonicExtH_stepData hb) hu hz
  rw [heq]
  have hv : ∀ k, |(PiecewiseConstant.stepData b J).v k| ≤ M := by
    intro k
    simp only [PiecewiseConstant.stepData]
    split_ifs with h
    · exact hM _ h.choose_spec.1
    · rw [abs_zero]; exact hM0
  obtain ⟨h1, h2⟩ := (PiecewiseConstant.stepData b J).harmonicExtH_mem_Icc hz
  have hsup : (⨆ k, (PiecewiseConstant.stepData b J).v k) ≤ M :=
    ciSup_le fun k => (abs_le.1 (hv k)).2
  have hinf : -M ≤ ⨅ k, (PiecewiseConstant.stepData b J).v k :=
    le_ciInf fun k => (abs_le.1 (hv k)).1
  exact abs_le.2 ⟨hinf.trans h1, h2.trans hsup⟩

/-- The mean of a pairing is bounded by `M ∫ |φ|` when the extension is bounded by `M` on `ℍ`. -/
theorem abs_integral_mul_le {u : ℂ → ℝ} {M : ℝ} (hu : ∀ z ∈ QuantumZipper.H, |u z| ≤ M)
    (φ : TestOn upperHalfPlaneOpens) : |∫ z, u z * φ z| ≤ M * ∫ z, |φ z| := by
  have hφi : Integrable (fun z => φ z) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hb : ∀ z, ‖u z * φ z‖ ≤ M * |φ z| := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · have hzH : z ∈ QuantumZipper.H := φ.tsupport_subset hz
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hu z hzH) (abs_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero, norm_zero, abs_zero, le_refl]
  have h := norm_integral_le_of_norm_le (hφi.abs.const_mul M) (Eventually.of_forall hb)
  rw [Real.norm_eq_abs, integral_const_mul] at h
  exact h

/-- The law of the centred pairing of a GFF: `N(0, v_φ)` with `v_φ = zeroGFFTestCov φ φ`. -/
theorem map_centred_eq_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} (hX : IsGFFWithBoundaryData Q X b J)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀) (φ : TestOn upperHalfPlaneOpens) :
    Q.map (fun ω => X ω φ - ∫ z, u₀ z * φ z) =
      gaussianReal 0 (QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ).toNNReal := by
  have hZ := hX.2 u₀ hu₀
  have hG := hZ.gaussian.hasGaussianLaw_eval φ
  rw [hG.map_eq_gaussianReal, hZ.centered φ, ← covariance_self (hZ.measurable φ).aemeasurable,
    hZ.covariance_eq φ φ]

/-- The first absolute moment of `N(0, v)` is finite. -/
theorem lintegral_enorm_gaussianReal_lt_top (v : ℝ≥0) : ∫⁻ x, ‖x‖ₑ ∂(gaussianReal 0 v) < ⊤ := by
  have h : Integrable id (gaussianReal 0 v) := (memLp_id_gaussianReal 1).integrable le_rfl
  exact h.2

/-- **A uniform first-moment bound for the pairings of a GFF**: if the data are bounded by `M ≥ 0` off the jumps,
then `E‖X φ‖ ≤ M ∫ |φ| + ∫ ‖x‖ dN(0, v_φ)`. -/
theorem lintegral_enorm_apply_le_of_isGFF {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hX : IsGFFWithBoundaryData Q X b J) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ y ∉ J, |b y| ≤ M)
    (φ : TestOn upperHalfPlaneOpens) :
    ∫⁻ ω, ‖X ω φ‖ₑ ∂Q ≤ ENNReal.ofReal (M * ∫ z, |φ z|) +
      ∫⁻ x, ‖x‖ₑ ∂(gaussianReal 0 (QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ).toNNReal) := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  set m : ℝ := ∫ z, u₀ z * φ z with hm
  have hZm : Measurable fun ω => X ω φ - m := (hX.2 u₀ hu₀).measurable φ
  have hmb : |m| ≤ M * ∫ z, |φ z| :=
    abs_integral_mul_le (abs_le_of_isBoundedHarmonicExtension hb hM0 hM hu₀) φ
  have hpt : ∀ ω, ‖X ω φ‖ₑ ≤ ‖X ω φ - m‖ₑ + ENNReal.ofReal (M * ∫ z, |φ z|) := by
    intro ω
    calc ‖X ω φ‖ₑ = ‖(X ω φ - m) + m‖ₑ := by rw [sub_add_cancel]
      _ ≤ ‖X ω φ - m‖ₑ + ‖m‖ₑ := enorm_add_le _ _
      _ ≤ ‖X ω φ - m‖ₑ + ENNReal.ofReal (M * ∫ z, |φ z|) := by
          gcongr
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal hmb
  calc ∫⁻ ω, ‖X ω φ‖ₑ ∂Q ≤ ∫⁻ ω, (‖X ω φ - m‖ₑ + ENNReal.ofReal (M * ∫ z, |φ z|)) ∂Q := lintegral_mono hpt
    _ = ∫⁻ ω, ‖X ω φ - m‖ₑ ∂Q + ENNReal.ofReal (M * ∫ z, |φ z|) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ x, ‖x‖ₑ ∂(Q.map fun ω => X ω φ - m) + ENNReal.ofReal (M * ∫ z, |φ z|) := by
        rw [lintegral_map measurable_enorm hZm]
    _ = ENNReal.ofReal (M * ∫ z, |φ z|) +
        ∫⁻ x, ‖x‖ₑ ∂(gaussianReal 0 (QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ).toNNReal) := by
        rw [hm, map_centred_eq_gaussianReal hX hu₀ φ, add_comm]

end InteractingSLE.Theorem14.BW1In
