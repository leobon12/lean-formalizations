/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField8Local

/-!
# The retained Gaussian kernel localized to a bounded weight

The random domain only needs to contain the deterministic test domain where
the weight is nonzero. This extends the existing whole-space kernel adapter
to marked avoidance events without imposing conditions off those events.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace

namespace InteractingSLE.WFS

open LQGMetric LQGMetric.MarkovZB LocalSets WholeField QuantumZipper
open QuantumZipper.K3 QuantumZipper.Thm11Asm

/-- Dirichlet pairings factor on the support of a bounded measurable weight. -/
theorem exists_const_integral_exp_lapTest_of_kernel_on
    {Ω : Type*} {𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h M : Ω → DistOn upperHalfPlaneOpens}
    {U : Opens ℂ} {V : Ω → Set ℂ} {W : Ω → ℂ}
    (h𝒦 : 𝒦 ≤ mΩ) (hU : U ≤ upperHalfPlaneOpens)
    (hV : ∀ᵐ ω ∂P, W ω ≠ 0 → IsOpen (V ω) ∧ V ω ⊆ H ∧
      (U : Set ℂ) ⊆ V ω ∧ IsHarmonicDistOn (M ω) (V ω))
    (hker : ∀ χ : TestOn upperHalfPlaneOpens,
      P[fun ω => Complex.exp (Complex.I * (h ω χ : ℂ)) | 𝒦] =ᵐ[P]
        fun ω => rangeKerCF (M ω) (V ω) χ)
    (hhm : Measurable h) (hWm : StronglyMeasurable[𝒦] W) (hWb : ∀ ω, ‖W ω‖ ≤ 1)
    (Ψ : TestOn upperHalfPlaneOpens) :
    ∃ J : ℂ, ∀ f f' : zsSub (U : Set ℂ),
      ∫ ω, W ω * Complex.exp (Complex.I * (h ω (lapTest U f - lapTest U f' + Ψ) : ℂ)) ∂P =
        ((Real.exp (-(1 / 2) * (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
          2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫)) : ℝ) : ℂ) * J := by
  refine ⟨∫ ω, W ω * rangeKerCF (M ω) (V ω) Ψ ∂P, fun f f' => ?_⟩
  set χ := lapTest U f - lapTest U f' + Ψ with hχ
  have hF : Integrable (fun ω => Complex.exp (Complex.I * (h ω χ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply χ).comp hhm)
  rw [integral_mul_condExp_of_bdd h𝒦 hWm hWb hF, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hker χ, hV] with ω hω hVω
  by_cases hW : W ω = 0
  · simp only [hW, zero_mul, mul_zero]
  obtain ⟨hVo, hVH, hUV, hMω⟩ := hVω hW
  rw [hω]
  have h0 := IsHarmonicDistOn.apply_lapTest_eq_zero hVo hMω hU hUV f
  have h0' := IsHarmonicDistOn.apply_lapTest_eq_zero hVo hMω hU hUV f'
  have eM : M ω χ = M ω Ψ := by
    rw [hχ, map_add (M ω), map_sub (M ω), h0, h0']
    ring
  simp only [rangeKerCF]
  rw [eM, zeroGFFTestCov_lapTest_sub_add hU hVo hVH hUV Ψ f f']
  rw [show Complex.I * (M ω Ψ : ℂ) - (((1 / 2 : ℝ) *
      (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
        2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫ + zeroGFFTestCov (V ω) Ψ Ψ) : ℝ) : ℂ) =
      ((-(1 / 2) * (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
        2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫) : ℝ) : ℂ) +
      (Complex.I * (M ω Ψ : ℂ) - (((1 / 2 : ℝ) * zeroGFFTestCov (V ω) Ψ Ψ : ℝ) : ℂ)) by
    push_cast; ring, Complex.exp_add, Complex.ofReal_exp]
  ring

end InteractingSLE.WFS
