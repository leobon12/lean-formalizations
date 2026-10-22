import HigherDimLQGMetric.ConvField.CenteredLimit
import HigherDimLQGMetric.Field.TestIntegral

/-! The unit-sphere average of translated convolution truncations is one compact test function. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

def l2b_meanTruncK (d n : ℕ) : Compacts (Rd d) :=
  ⟨closedBall 0 (2 * ((n : ℝ) + 1) + 2), isCompact_closedBall _ _⟩

private theorem l2b_meanTrunc_smooth (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (u : sphere (0 : Rd d) 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : Rd d => convKernelEps κ ε ((u : Rd d) - w) *
        radialProfile d (((n : ℝ) + 1)⁻¹ • (w - (u : Rd d)))) := by
  have hfull := l2b_contDiff_convTrunc_exp_uncurry hd hκ n
  have hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : Rd d => (((Real.log ε, (u : Rd d)) : ℝ × Rd d), w)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def, Function.uncurry_apply_pair, Real.exp_log hε] using
    hfull.comp hm

private theorem l2b_meanTrunc_support (_hd : 2 ≤ d)
    (_hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (n : ℕ)
    (u : sphere (0 : Rd d) 1) {w : Rd d}
    (hw : w ∉ (l2b_meanTruncK d n : Set (Rd d))) :
    convKernelEps κ ε ((u : Rd d) - w) *
      radialProfile d (((n : ℝ) + 1)⁻¹ • (w - (u : Rd d))) = 0 := by
  have hwfar : 2 * ((n : ℝ) + 1) + 2 < ‖w‖ := by
    simpa [l2b_meanTruncK, mem_closedBall, dist_zero_right] using hw
  have hu : ‖(u : Rd d)‖ = 1 := mem_sphere_zero_iff_norm.1 u.2
  have htri : ‖w‖ ≤ ‖w - (u : Rd d)‖ + 1 := by
    calc
      ‖w‖ = ‖(w - (u : Rd d)) + u‖ := by congr 1; abel
      _ ≤ ‖w - (u : Rd d)‖ + ‖(u : Rd d)‖ := norm_add_le _ _
      _ = _ := by rw [hu]
  have hfar : 2 * ((n : ℝ) + 1) ≤ ‖w - (u : Rd d)‖ := by linarith
  have hscale : 2 ≤ ‖((n : ℝ) + 1)⁻¹ • (w - (u : Rd d))‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by positivity))]
    rw [mul_comm]
    exact (le_mul_inv_iff₀ (by positivity : (0 : ℝ) < n + 1)).2 hfar
  rw [radialProfile_eq_zero hscale, mul_zero]

def l2b_sphereTruncFam (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    sphere (0 : Rd d) 1 → 𝓓^{⊤}_{l2b_meanTruncK d n}(Rd d, ℝ) :=
  testFamK (l2b_meanTruncK d n)
    (fun (u : sphere (0 : Rd d) 1) w => convKernelEps κ ε ((u : Rd d) - w) *
      radialProfile d (((n : ℝ) + 1)⁻¹ • (w - (u : Rd d))))
    (l2b_meanTrunc_smooth hd hκ hε n)
    (fun u _w hw => l2b_meanTrunc_support hd hκ n u hw)

theorem l2b_sphereTruncFam_apply (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (u : sphere (0 : Rd d) 1) (w : Rd d) :
    l2b_sphereTruncFam hd hκ hε n u w = convTrunc κ ε (u : Rd d) n w := by
  change convKernelEps κ ε ((u : Rd d) - w) *
    radialProfile d (((n : ℝ) + 1)⁻¹ • (w - (u : Rd d))) = _
  rw [l2b_convTrunc_apply hd hκ]

theorem l2b_continuous_sphereTruncFam (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    Continuous (l2b_sphereTruncFam hd hκ hε n) := by
  let Ψ : sphere (0 : Rd d) 1 → Rd d → ℝ := fun u w =>
    convKernelEps κ ε ((u : Rd d) - w) *
      radialProfile d (((n : ℝ) + 1)⁻¹ • (w - (u : Rd d)))
  have hD : ∀ i : ℕ, Continuous fun p : sphere (0 : Rd d) 1 × Rd d =>
      iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
    intro i
    have hfull := l2b_continuous_iteratedFDeriv_snd
      (l2b_contDiff_convTrunc_exp_uncurry hd hκ n) i
    have hm : Continuous (fun p : sphere (0 : Rd d) 1 × Rd d =>
        (((Real.log ε, (p.1 : Rd d)) : ℝ × Rd d), p.2)) := by fun_prop
    have he : (fun p : sphere (0 : Rd d) 1 × Rd d =>
        iteratedFDeriv ℝ i (Ψ p.1) p.2) =
        (fun p : (ℝ × Rd d) × Rd d =>
          iteratedFDeriv ℝ i
            (fun w => convKernelEps κ (Real.exp p.1.1) (p.1.2 - w) *
              radialProfile d (((n : ℝ) + 1)⁻¹ • (w - p.1.2))) p.2) ∘
          (fun p => (((Real.log ε, (p.1 : Rd d)) : ℝ × Rd d), p.2)) := by
      funext p
      simp only [Function.comp_apply, Ψ, Real.exp_log hε]
    rw [he]
    exact hfull.comp hm
  exact continuous_testFamK (l2b_meanTruncK d n) Ψ
    (l2b_meanTrunc_smooth hd hκ hε n)
    (fun u _w hw => l2b_meanTrunc_support hd hκ n u hw) hD

theorem l2b_exists_meanTruncTest (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ∃ I : 𝓓^{⊤}_{l2b_meanTruncK d n}(Rd d, ℝ),
      (∀ w, I w = ∫ u, l2b_sphereTruncFam hd hκ hε n u w ∂(sphereMeasure d)) ∧
      ∀ T : 𝓓^{⊤}_{l2b_meanTruncK d n}(Rd d, ℝ) →L[ℝ] ℝ,
        T I = ∫ u, T (l2b_sphereTruncFam hd hκ hε n u) ∂(sphereMeasure d) :=
  TestIntegral.exists_testIntegral (sphereMeasure d)
    (l2b_continuous_sphereTruncFam hd hκ hε n)

def l2b_meanTruncTest (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) : TestRd d :=
  TestFunction.ofSupportedIn (subset_univ _)
    (l2b_exists_meanTruncTest hd hκ hε n).choose

theorem l2b_meanTruncTest_apply (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (w : Rd d) :
    l2b_meanTruncTest hd hκ hε n w =
      ∫ u : Rd d, convTrunc κ ε u n w ∂(unitSphereProb d) := by
  change (l2b_exists_meanTruncTest hd hκ hε n).choose w = _
  rw [(l2b_exists_meanTruncTest hd hκ hε n).choose_spec.1 w]
  have hc : Continuous (fun u : Rd d => convTrunc κ ε u n w) := by
    have h := (continuous_eval_const w).comp
      ((l2b_continuous_convTrunc_exp hd hκ n).comp
        ((continuous_const : Continuous fun _ : Rd d => Real.log ε).prodMk
          continuous_id))
    convert h using 1
    funext u
    simp only [Function.comp_apply, Real.exp_log hε, id_eq]
  rw [integral_unitSphereProb_eq_sphereMeasure hc]
  apply integral_congr_ae
  filter_upwards with u
  exact l2b_sphereTruncFam_apply hd hκ hε n u w

theorem l2b_meanTruncTest_pair (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (T : DistRd d) :
    T (l2b_meanTruncTest hd hκ hε n) =
      ∫ u : Rd d, T (convTrunc κ ε u n) ∂(unitSphereProb d) := by
  have hspec := (l2b_exists_meanTruncTest hd hκ hε n).choose_spec.2
    (T.comp (TestFunction.ofSupportedInCLM ℝ
      (subset_univ ((l2b_meanTruncK d n : Set (Rd d))))))
  have hc : Continuous (fun u : Rd d => T (convTrunc κ ε u n)) := by
    have h := T.continuous.comp
      ((l2b_continuous_convTrunc_exp hd hκ n).comp
        ((continuous_const : Continuous fun _ : Rd d => Real.log ε).prodMk
          continuous_id))
    convert h using 1
    funext u
    simp only [Function.comp_apply, Real.exp_log hε, id_eq]
    rfl
  rw [integral_unitSphereProb_eq_sphereMeasure hc]
  change T (l2b_meanTruncTest hd hκ hε n) =
    ∫ u, T (convTrunc κ ε (u : Rd d) n) ∂(sphereMeasure d)
  have hEq : T (l2b_meanTruncTest hd hκ hε n) =
      ∫ u, T (TestFunction.ofSupportedIn (subset_univ _)
        (l2b_sphereTruncFam hd hκ hε n u)) ∂(sphereMeasure d) := hspec
  rw [hEq]
  apply integral_congr_ae
  filter_upwards with u
  exact congrArg T (by
    ext w
    exact l2b_sphereTruncFam_apply hd hκ hε n u w)

theorem l2b_integral_convTrunc_eq_center (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ε : ℝ) (n : ℕ) (z : Rd d) :
    (∫ w : Rd d, convTrunc κ ε z n w) =
      ∫ w : Rd d, convTrunc κ ε 0 n w := by
  have ht := l2b_testAffinePull_convTrunc hd hκ ε z 0 n
  simp only [zero_add] at ht
  rw [← ht, integral_testAffinePull (convTrunc κ ε 0 n) (by norm_num : (0 : ℝ) < 1) z]
  simp

theorem l2b_integral_meanTruncTest (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    (∫ w : Rd d, l2b_meanTruncTest hd hκ hε n w) =
      ∫ w : Rd d, convTrunc κ ε 0 n w := by
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have h := l2b_meanTruncTest_pair hd hκ hε n
    (ofCont (ContinuousMap.const (Rd d) 1))
  simp only [ofCont_const_apply, one_mul] at h
  rw [h]
  have he : (fun u : Rd d => ∫ w : Rd d, convTrunc κ ε u n w) =
      fun _ => ∫ w : Rd d, convTrunc κ ε 0 n w := by
    funext u
    exact l2b_integral_convTrunc_eq_center hd hκ ε n u
  rw [he]
  simp

def l2b_centeredTruncTest (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (x : Rd d) (n : ℕ) : TestRd0 d := by
  refine ⟨convTrunc κ ε x n - l2b_meanTruncTest hd hκ hε n, ?_⟩
  change (∫ w : Rd d, convTrunc κ ε x n w -
    l2b_meanTruncTest hd hκ hε n w) = 0
  rw [integral_sub (integrable_testOn _) (integrable_testOn _),
    l2b_integral_convTrunc_eq_center hd hκ ε n x,
    l2b_integral_meanTruncTest hd hκ hε n, sub_self]

theorem l2b_centeredTruncTest_pair (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (x : Rd d) (n : ℕ) (T : DistRd d) :
    T (l2b_centeredTruncTest hd hκ hε x n).1 =
      T (convTrunc κ ε x n) -
        ∫ u : Rd d, T (convTrunc κ ε u n) ∂(unitSphereProb d) := by
  rw [l2b_centeredTruncTest, map_sub, l2b_meanTruncTest_pair hd hκ hε n T]

theorem l2b_ae_centeredTrunc_tendsto (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ x : Rd d,
      Tendsto (fun n : ℕ => h ω (l2b_centeredTruncTest hd hκ hε x n).1)
        atTop (𝓝 (convMollify κ ε (h ω) x -
          ∫ u : Rd d, convMollify κ ε (h ω) u ∂(unitSphereProb d))) := by
  filter_upwards [l2b_ae_convMollify_tendsto d hd κ hκ P h hh,
    l2b_ae_tendsto_sphereMean_convTrunc d hd κ hκ P h hh] with ω hlim hmean
  intro ε hε x
  have hx := hlim ε hε x
  have hcv : Tendsto (fun n : ℕ => h ω (convTrunc κ ε x n)) atTop
      (𝓝 (convMollify κ ε (h ω) x)) := by
    simpa only [l2b_convMollify_eq_of_tendsto hx] using hx
  have ht := hcv.sub (hmean ε hε)
  convert ht using 1
  funext n
  exact l2b_centeredTruncTest_pair hd hκ hε x n (h ω)

end HigherDimLQGMetric
