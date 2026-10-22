import HigherDimLQGMetric.Trunc.Basic
import HigherDimLQGMetric.ConvField.ParamTest

/-!
# Smooth parameter dependence of the truncated test

We parameterize the scale by `ε = exp (2t)`, so its square root is `exp t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

def l2c_axisFactor (κ : Rd d → ℝ) (t r : ℝ) : ℝ :=
  convKernelEps κ (Real.exp (2 * t)) (r • HigherDimLFPP.e₁ d) *
    radBump (Real.exp t / 2) (Real.exp t) (r • HigherDimLFPP.e₁ d)

theorem l2c_sqrt_exp_two (t : ℝ) : Real.sqrt (Real.exp (2 * t)) = Real.exp t := by
  rw [show 2 * t = t + t by ring, Real.exp_add, ← sq, Real.sqrt_sq_eq_abs,
    abs_of_pos (Real.exp_pos t)]

private theorem radBump_exp_eq (t : ℝ) (x : Rd d) :
    radBump (Real.exp t / 2) (Real.exp t) x =
      (ContDiffBumpBase.ofInnerProductSpace (Rd d)).toFun 2
        ((2 * Real.exp (-t)) • x) := by
  unfold radBump
  have h : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have h1 : Real.exp t / (Real.exp t / 2) = 2 := by
    field_simp
  have h2 : (Real.exp t / 2)⁻¹ = 2 * Real.exp (-t) := by
    rw [Real.exp_neg]
    field_simp
  rw [h1, h2]

theorem l2c_contDiff_trunc_exp_uncurry (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry fun (q : ℝ × Rd d) (w : Rd d) =>
        convKernelEps κ (Real.exp (2 * q.1)) (q.2 - w) *
          radBump (Real.exp q.1 / 2) (Real.exp q.1) (q.2 - w)) := by
  have hform : (Function.uncurry fun (q : ℝ × Rd d) (w : Rd d) =>
        convKernelEps κ (Real.exp (2 * q.1)) (q.2 - w) *
          radBump (Real.exp q.1 / 2) (Real.exp q.1) (q.2 - w)) =
      fun p : (ℝ × Rd d) × Rd d =>
        (Real.exp (2 * p.1.1 * (-(d : ℝ))) *
          convKernel κ (Real.exp (-(2 * p.1.1)) • (p.1.2 - p.2))) *
          (ContDiffBumpBase.ofInnerProductSpace (Rd d)).toFun 2
            ((2 * Real.exp (-p.1.1)) • (p.1.2 - p.2)) := by
    funext p
    change convKernelEps κ (Real.exp (2 * p.1.1)) (p.1.2 - p.2) *
      radBump (Real.exp p.1.1 / 2) (Real.exp p.1.1) (p.1.2 - p.2) = _
    rw [radBump_exp_eq]
    change (Real.exp (2 * p.1.1)) ^ (-(d : ℝ)) *
      convKernel κ ((Real.exp (2 * p.1.1))⁻¹ • (p.1.2 - p.2)) * _ = _
    rw [← Real.exp_mul, ← Real.exp_neg]
  rw [hform]
  have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × Rd d) × Rd d => p.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × Rd d) × Rd d => p.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × Rd d) × Rd d => p.2) := contDiff_snd
  have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × Rd d) × Rd d =>
        (ContDiffBumpBase.ofInnerProductSpace (Rd d)).toFun 2
          ((2 * Real.exp (-p.1.1)) • (p.1.2 - p.2))) := by
    have ht : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : (ℝ × Rd d) × Rd d => 2 * Real.exp (-p.1.1)) :=
      contDiff_const.mul (Real.contDiff_exp.comp hu.neg)
    exact (ContDiffBumpBase.ofInnerProductSpace (Rd d)).smooth.comp_contDiff
      (contDiff_const.prodMk (ht.smul (hz.sub hw)))
      (fun _ => ⟨by norm_num, mem_univ _⟩)
  exact ((Real.contDiff_exp.comp ((contDiff_const.mul hu).mul contDiff_const)).mul
    ((convKernel_contDiff (by omega : 0 < d) hκ).comp
      ((Real.contDiff_exp.comp (contDiff_const.mul hu).neg).smul (hz.sub hw)))).mul hb

theorem l2c_continuous_axisFactor (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Continuous fun p : ℝ × ℝ => l2c_axisFactor κ p.1 p.2 := by
  have hmap : Continuous (fun p : ℝ × ℝ =>
      (((p.1, (0 : Rd d)) : ℝ × Rd d), -(p.2 • HigherDimLFPP.e₁ d))) := by
    fun_prop
  have hc := (l2c_contDiff_trunc_exp_uncurry hd hκ).continuous.comp hmap
  convert hc using 1
  funext p
  simp only [l2c_axisFactor, Function.comp_apply, Function.uncurry_apply_pair,
    zero_sub, neg_neg]

theorem l2c_axisFactor_eq_zero (hd : 2 ≤ d) (t r : ℝ)
    (hr : Real.exp t ≤ r) : l2c_axisFactor κ t r = 0 := by
  have hr0 : 0 ≤ r := (Real.exp_pos t).le.trans hr
  have hnorm : ‖r • HigherDimLFPP.e₁ d‖ = r := by
    rw [norm_smul, HigherDimLFPP.norm_e₁ (by omega : 0 < d),
      mul_one, Real.norm_eq_abs, abs_of_nonneg hr0]
  unfold l2c_axisFactor
  rw [l2c_radBump_eq_zero (by positivity)
    (by have hp := Real.exp_pos t; linarith) (hnorm.trans_ge hr), mul_zero]

theorem l2c_axisFactor_log {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    l2c_axisFactor κ (Real.log ε / 2) r =
      convKernelEps κ ε (r • HigherDimLFPP.e₁ d) *
        radBump (Real.sqrt ε / 2) (Real.sqrt ε)
          (r • HigherDimLFPP.e₁ d) := by
  unfold l2c_axisFactor
  rw [show 2 * (Real.log ε / 2) = Real.log ε by ring,
    Real.exp_log hε, ← Real.log_sqrt hε.le,
    Real.exp_log (Real.sqrt_pos.2 hε)]

set_option linter.style.haveILetI false in
theorem l2c_continuous_truncTest_exp (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Continuous fun q : ℝ × Rd d => truncTest κ (Real.exp (2 * q.1)) q.2 := by
  rw [continuous_iff_continuousAt]
  intro q₀
  let S : Set (ℝ × Rd d) :=
    Icc (q₀.1 - 1) (q₀.1 + 1) ×ˢ closedBall q₀.2 1
  have hSc : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hSc
  let K : Compacts (Rd d) :=
    ⟨closedBall q₀.2 (Real.exp (q₀.1 + 1) + 2), isCompact_closedBall _ _⟩
  let Ψ : S → Rd d → ℝ := fun q w =>
    convKernelEps κ (Real.exp (2 * q.1.1)) (q.1.2 - w) *
      radBump (Real.exp q.1.1 / 2) (Real.exp q.1.1) (q.1.2 - w)
  have hs : ∀ q : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ q) := by
    intro q
    have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : Rd d => ((q.1 : ℝ × Rd d), w)) :=
      contDiff_const.prodMk contDiff_id
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using
      (l2c_contDiff_trunc_exp_uncurry hd hκ).comp hmap
  have hK : ∀ q : S, ∀ w ∉ (K : Set (Rd d)), Ψ q w = 0 := by
    intro q w hw
    have hq₁ : q.1.1 ≤ q₀.1 + 1 := q.2.1.2
    have hq₂ : ‖q.1.2 - q₀.2‖ ≤ 1 := by
      simpa [mem_closedBall, dist_eq_norm] using q.2.2
    have hwfar : Real.exp (q₀.1 + 1) + 2 < ‖w - q₀.2‖ := by
      simpa [K, mem_closedBall, dist_eq_norm] using hw
    have htri : ‖w - q₀.2‖ ≤ ‖w - q.1.2‖ + ‖q.1.2 - q₀.2‖ := by
      calc
        ‖w - q₀.2‖ = ‖(w - q.1.2) + (q.1.2 - q₀.2)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have hdist : Real.exp q.1.1 ≤ ‖q.1.2 - w‖ := by
      rw [norm_sub_rev]
      have hexp : Real.exp q.1.1 ≤ Real.exp (q₀.1 + 1) :=
        Real.exp_le_exp.2 hq₁
      linarith
    dsimp [Ψ]
    rw [l2c_radBump_eq_zero (by positivity)
      (by have hp := Real.exp_pos q.1.1; linarith) hdist, mul_zero]
  have hD : ∀ i : ℕ, Continuous fun p : S × Rd d =>
      iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
    intro i
    have hfull := l2b_continuous_iteratedFDeriv_snd
      (l2c_contDiff_trunc_exp_uncurry hd hκ) i
    have hmap : Continuous (fun p : S × Rd d => ((p.1.1 : ℝ × Rd d), p.2)) := by
      fun_prop
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hfull.comp hmap
  have hc := continuous_testFamK K Ψ hs hK
    hD
  have he : (fun q : S => truncTest κ (Real.exp (2 * q.1.1)) q.1.2) =
      ofSuppRd K ∘ testFamK K Ψ hs hK := by
    funext q
    ext w
    rw [l2c_truncTest_apply hd hκ (Real.exp_pos _) q.1.2 w,
      l2c_sqrt_exp_two]
    rfl
  have hcont : Continuous (fun q : S => truncTest κ (Real.exp (2 * q.1.1)) q.1.2) := by
    rw [he]
    exact (ofSuppRd K).continuous.comp hc
  have hSOn : ContinuousOn
      (fun q : ℝ × Rd d => truncTest κ (Real.exp (2 * q.1)) q.2) S := by
    exact continuousOn_iff_continuous_domRestrict.mpr hcont
  have hnhds : S ∈ 𝓝 q₀ := by
    have hI : Icc (q₀.1 - 1) (q₀.1 + 1) ∈ 𝓝 q₀.1 := by
      exact Filter.mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith))
        Ioo_subset_Icc_self
    have hB : closedBall q₀.2 1 ∈ 𝓝 q₀.2 := by
      exact Filter.mem_of_superset (ball_mem_nhds q₀.2 (by norm_num)) ball_subset_closedBall
    rw [show q₀ = (q₀.1, q₀.2) from q₀.eta, nhds_prod_eq]
    exact Filter.prod_mem_prod hI hB
  exact hSOn.continuousAt hnhds

theorem l2c_continuousAt_truncTest (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {p : ℝ × Rd d} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × Rd d => truncTest κ q.1 q.2) p := by
  let F : ℝ × Rd d → ℝ × Rd d := fun q => (Real.log q.1 / 2, q.2)
  have hF : ContinuousAt F p :=
    (((Real.continuousAt_log hp.ne').comp continuousAt_fst).div_const 2).prodMk
      continuousAt_snd
  have hC : ContinuousAt
      (fun q : ℝ × Rd d => truncTest κ (Real.exp (2 * q.1)) q.2) (F p) :=
    (l2c_continuous_truncTest_exp hd hκ).continuousAt
  have heq : (fun q : ℝ × Rd d => truncTest κ q.1 q.2) =ᶠ[𝓝 p]
      (fun q => truncTest κ (Real.exp (2 * (Real.log q.1 / 2))) q.2) := by
    have hpos : {q : ℝ × Rd d | 0 < q.1} ∈ 𝓝 p :=
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
    filter_upwards [hpos] with q hq
    have he : Real.exp (2 * (Real.log q.1 / 2)) = q.1 := by
      rw [show 2 * (Real.log q.1 / 2) = Real.log q.1 by ring,
        Real.exp_log hq]
    rw [he]
  exact (hC.comp hF).congr_of_eventuallyEq heq

theorem l2c_continuousOn_truncMollify (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (T : DistRd d) :
    ContinuousOn (fun p : ℝ × Rd d => truncMollify κ p.1 T p.2)
      (Ioi 0 ×ˢ univ) := by
  intro p hp
  have hpos : 0 < p.1 := hp.1
  exact ((map_continuous T).continuousAt.comp
    (l2c_continuousAt_truncTest hd hκ hpos)).continuousWithinAt

end HigherDimLQGMetric
