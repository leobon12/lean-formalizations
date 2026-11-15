/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.FlowReflect

/-!
# The zero-boundary covariance under the reflection `R(z) = −z̄`

Packet PROVE-LEMMA76C. The zero-boundary covariance (QuantumZipper's `zeroGFFTestCov`, the polarized dual Dirichlet
norm over `C_c^∞(U)`) is invariant under the isometry `R`:

* `testMeasPos_comp_reflectC`: `(φ ∘ R)⁺ dz` is the image of `φ⁺ dz` under `R` (and the same for `φ⁻`);
* `dirichletEnergyOn_comp_reflectC`: `E_U(f ∘ R) = E_{R(U)}(f)` (`‖D(f ∘ R)‖ = ‖Df‖ ∘ R`, `R` preserves volume);
* **`dualNormSq_map_reflectC`**: the dual norm of `μ ∘ R⁻¹` on `R(U)` is that of `μ` on `U` (the bijection
  `f ↦ f ∘ R` of the test spaces);
* **`zeroGFFTestCov_image_reflectC`**: `Cov_{R(U)}(φ, ψ) = Cov_U(φ ∘ R, ψ ∘ R)` for every `U`;
* **`isZBGFFProcess_refl`**: if `X` is a zero-boundary GFF process on `ℍ`, so is `φ ↦ −X(φ ∘ R)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal ComplexConjugate

open QuantumZipper (H zeroGFFTestCov testMeasPos testMeasNeg dualCov dualNormSq zeroSpace dirichletEnergyOn)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Sec7

namespace FlowReflect

open LP (reflectC)

/-! ### Measures -/

theorem measurable_reflectC : Measurable reflectC := LP.continuous_reflectC.measurable

theorem withDensity_comp_reflectC (g : ℂ → ℝ≥0∞) :
    (volume.withDensity fun z => g (reflectC z)) = (volume.withDensity g).map reflectC := by
  ext s hs
  rw [Measure.map_apply measurable_reflectC hs, withDensity_apply _ (measurable_reflectC hs),
    withDensity_apply _ hs]
  have h := measurePreserving_reflectC.setLIntegral_comp_preimage_emb measurableEmbedding_reflectC g
    (reflectC ⁻¹' s)
  rw [← h, ← preimage_comp]
  congr 2
  ext z
  simp only [mem_preimage, Function.comp_apply, LP.reflectC_reflectC]

theorem testMeasPos_comp_reflectC (φ : ℂ → ℝ) :
    testMeasPos (fun z => φ (reflectC z)) = (testMeasPos φ).map reflectC :=
  withDensity_comp_reflectC fun z => ENNReal.ofReal (φ z)

theorem testMeasNeg_comp_reflectC (φ : ℂ → ℝ) :
    testMeasNeg (fun z => φ (reflectC z)) = (testMeasNeg φ).map reflectC :=
  withDensity_comp_reflectC fun z => ENNReal.ofReal (-φ z)

/-! ### Dirichlet energy and the dual norm -/

theorem fderiv_comp_reflectC (f : ℂ → ℝ) (z : ℂ) :
    fderiv ℝ (fun w => f (reflectC w)) z = (fderiv ℝ f (reflectC z)).comp reflCLM :=
  reflLIE.toContinuousLinearEquiv.comp_right_fderiv (f := f) (x := z)

theorem norm_fderiv_comp_reflectC (f : ℂ → ℝ) (z : ℂ) :
    ‖fderiv ℝ (fun w => f (reflectC w)) z‖ = ‖fderiv ℝ f (reflectC z)‖ := by
  rw [fderiv_comp_reflectC]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ reflLIE

theorem preimage_reflectC_image (U : Set ℂ) : reflectC ⁻¹' (reflectC '' U) = U := by
  rw [preimage_reflectC, reflectC_image_image]

/-- `E_U(f ∘ R) = E_{R(U)}(f)`. -/
theorem dirichletEnergyOn_comp_reflectC (U : Set ℂ) (f : ℂ → ℝ) :
    dirichletEnergyOn U (fun w => f (reflectC w)) = dirichletEnergyOn (reflectC '' U) f := by
  unfold dirichletEnergyOn
  congr 1
  simp_rw [norm_fderiv_comp_reflectC]
  exact (measurePreserving_reflectC.setIntegral_image_emb measurableEmbedding_reflectC
    (fun z => ‖fderiv ℝ f z‖ ^ 2) U).symm

theorem comp_reflectC_mem_zeroSpace {U : Set ℂ} {f : ℂ → ℝ} (hf : f ∈ zeroSpace (reflectC '' U)) :
    (fun w => f (reflectC w)) ∈ zeroSpace U := by
  obtain ⟨hc, hs, ht⟩ := hf
  refine ⟨contDiff_comp_reflectC hc, hasCompactSupport_comp_reflectC hs, ?_⟩
  rw [tsupport_comp_reflectC]
  calc reflectC '' tsupport f ⊆ reflectC '' (reflectC '' U) := image_mono ht
    _ = U := reflectC_image_image U

theorem integral_map_reflectC (μ : Measure ℂ) (f : ℂ → ℝ) :
    ∫ z, f z ∂(μ.map reflectC) = ∫ z, f (reflectC z) ∂μ :=
  measurableEmbedding_reflectC.integral_map f

/-- One direction of the dual-norm transport. -/
theorem dualNormSq_map_reflectC_le (U : Set ℂ) (μ : Measure ℂ) :
    dualNormSq (reflectC '' U) (zeroSpace (reflectC '' U)) (μ.map reflectC) ≤ dualNormSq U (zeroSpace U) μ := by
  unfold dualNormSq
  refine iSup₂_le fun f hf => ?_
  have hg : (fun w => f (reflectC w)) ∈ {g ∈ zeroSpace U | 0 < dirichletEnergyOn U g} := by
    refine ⟨comp_reflectC_mem_zeroSpace hf.1, ?_⟩
    rw [dirichletEnergyOn_comp_reflectC]
    exact hf.2
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun g (_ : g ∈ {g ∈ zeroSpace U | 0 < dirichletEnergyOn U g}) =>
    ENNReal.ofReal ((∫ x, g x ∂μ) ^ 2 / dirichletEnergyOn U g)) _ hg)
  rw [integral_map_reflectC, dirichletEnergyOn_comp_reflectC]

theorem map_map_reflectC (μ : Measure ℂ) : (μ.map reflectC).map reflectC = μ := by
  rw [Measure.map_map measurable_reflectC measurable_reflectC]
  have e : reflectC ∘ reflectC = id := funext LP.reflectC_reflectC
  rw [e, Measure.map_id]

/-- **The dual Dirichlet norm under `R`**: `‖μ ∘ R⁻¹‖_{R(U)} = ‖μ‖_U`. -/
theorem dualNormSq_map_reflectC (U : Set ℂ) (μ : Measure ℂ) :
    dualNormSq (reflectC '' U) (zeroSpace (reflectC '' U)) (μ.map reflectC) = dualNormSq U (zeroSpace U) μ := by
  refine le_antisymm (dualNormSq_map_reflectC_le U μ) ?_
  have h := dualNormSq_map_reflectC_le (reflectC '' U) (μ.map reflectC)
  rwa [reflectC_image_image, map_map_reflectC] at h

theorem dualCov_map_reflectC (U : Set ℂ) (μ ν : Measure ℂ) :
    dualCov (reflectC '' U) (zeroSpace (reflectC '' U)) (μ.map reflectC) (ν.map reflectC) =
      dualCov U (zeroSpace U) μ ν := by
  unfold dualCov
  rw [← Measure.map_add _ _ measurable_reflectC, dualNormSq_map_reflectC, dualNormSq_map_reflectC,
    dualNormSq_map_reflectC]

theorem zeroGFFTestCov_image_reflectC_comp (U : Set ℂ) (f g : ℂ → ℝ) :
    zeroGFFTestCov (reflectC '' U) (fun z => f (reflectC z)) (fun z => g (reflectC z)) = zeroGFFTestCov U f g := by
  unfold zeroGFFTestCov
  simp only [testMeasPos_comp_reflectC, testMeasNeg_comp_reflectC, dualCov_map_reflectC]

/-- **The zero-boundary covariance under `R`**: `Cov_{R(U)}(φ, ψ) = Cov_U(φ ∘ R, ψ ∘ R)`. -/
theorem zeroGFFTestCov_image_reflectC (U : Set ℂ) (φ ψ : ℂ → ℝ) :
    zeroGFFTestCov (reflectC '' U) φ ψ =
      zeroGFFTestCov U (fun z => φ (reflectC z)) (fun z => ψ (reflectC z)) := by
  have h := zeroGFFTestCov_image_reflectC_comp U (fun z => φ (reflectC z)) (fun z => ψ (reflectC z))
  simp only [LP.reflectC_reflectC] at h
  exact h

/-- The covariance of `ℍ` is `R`-invariant. -/
theorem zeroGFFTestCov_H_reflectC (φ ψ : ℂ → ℝ) :
    zeroGFFTestCov H (fun z => φ (reflectC z)) (fun z => ψ (reflectC z)) = zeroGFFTestCov H φ ψ := by
  rw [← zeroGFFTestCov_image_reflectC, reflectC_image_H]

/-! ### The zero-boundary GFF process under `R` -/

/-- **`φ ↦ −X(φ ∘ R)` is a zero-boundary GFF process on `ℍ` when `X` is.** -/
theorem isZBGFFProcess_refl {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : TestOn upperHalfPlaneOpens → Ω → ℝ} (hX : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens X P) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => -X (reflTest φ) ω) P := by
  refine ⟨fun φ => (hX.measurable _).neg, ?_, fun φ => ?_, fun φ ψ => ?_⟩
  · have h := (hX.gaussian.comp_right reflTest).smul (fun _ => (-1 : ℝ))
    have e : (fun φ ω => -X (reflTest φ) ω) = fun t ω => (fun _ => (-1 : ℝ)) t • (X ∘ reflTest) t ω := by
      funext φ ω
      simp only [Function.comp_apply, smul_eq_mul, neg_one_mul]
    rw [e]
    exact h
  · rw [integral_neg, hX.centered, neg_zero]
  · have e1 : (fun ω => -X (reflTest φ) ω) = -X (reflTest φ) := rfl
    have e2 : (fun ω => -X (reflTest ψ) ω) = -X (reflTest ψ) := rfl
    rw [e1, e2, covariance_neg_left, covariance_neg_right, neg_neg, hX.covariance_eq]
    exact zeroGFFTestCov_H_reflectC φ ψ

end FlowReflect

end Sec7

end InteractingSLE
