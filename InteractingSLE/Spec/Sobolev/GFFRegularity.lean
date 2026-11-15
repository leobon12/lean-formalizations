import InteractingSLE.Spec.Sobolev.Fourier
import LQGMetric.Field.ZeroBoundaryVar
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Analysis.Complex.Harmonic.Analytic

/-!
# Local Sobolev regularity of the GFF: (SR2) and (SR1) of Aux. lemma 11

Source: `source/spec/p049-096.md`, Aux. lemma 11 (`#aux-11`, p. 83), (SR1) (`#id-SR1`) and the
Fourier bound (SR2) (`#id-SR2`, pp. 83–84).

For the zero-boundary GFF `h` on an open set `D` with finite Green covariance on compact subsets
(`LQGMetric.ZBAdmissible D`) and a cutoff `ζ ∈ 𝓓(D)`,

  (SR2) `E|(ζh)^(ξ)|² = Var⟨h, ζ cos(2π⟪·,ξ⟫)⟫ + Var⟨h, ζ sin(2π⟪·,ξ⟫)⟫ ≤ C_ζ / (1 + |ξ|²)`,
  (SR1) `E‖ζh‖²_{H^{-ε}} = ∫ E|(ζh)^(ξ)|² (1 + |ξ|²)^{-ε} dξ < ∞` for every `ε > 0` (Tonelli).

**Route.** The specification first localizes to a rectangle `Q ⋐ D` by the Markov decomposition
and treats the harmonic remainder separately. Here (SR2) is proved directly on `D`, which makes
the rectangle and the harmonic remainder unnecessary. The variance is the dual Dirichlet norm,
`Var⟨h, φ⟫ = sup_v (∫ v φ)² / (v, v)_∇` over `v ∈ C_c^∞(D)` (`LQGMetric.ofReal_zeroGFFTestCov_self`),
so it suffices to bound `|∫ v ζ cos(2π⟪·,ξ⟫)|` by `C (1 + |ξ|)^{-1} (v, v)_∇^{1/2}`:

* for bounded `ξ` by `∫ |v| |ζ|`, and for large `ξ` by integrating one derivative in the direction
  `ξ`, which costs `(2π|ξ|)^{-1} ∫ (|ζ| |∇v| + |v| |∇ζ|)`;
* the terms `∫ |v| χ` (`χ` a nonnegative cutoff) are bounded by the **L¹ Poincaré inequality**
  `∫ |v| χ ≤ Var⟨h, χ⟫^{1/2} (v, v)_∇^{1/2}`, obtained from the variational formula applied to the
  smooth functions `√(v² + η²) - η ∈ C_c^∞(D)`, whose Dirichlet energy is at most that of `v`
  (this replaces the Poincaré inequality on the rectangle).

## Main results

* `abs_integral_mul_le_sqrt` : `|∫ f φ| ≤ Var⟨h, φ⟫^{1/2} (f, f)_∇^{1/2}`;
* `integral_abs_mul_le` : the L¹ Poincaré inequality;
* `abs_integral_mul_cos_le`, `abs_integral_mul_sin_le` : one integration by parts;
* `zeroGFFTestCov_cosTest_le`, `zeroGFFTestCov_sinTest_le` : (SR2);
* `lintegral_negSobolevSq_lt_top` : (SR1) for the zero-boundary GFF.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function Real ProbabilityTheory
open scoped Distributions ContDiff ENNReal RealInnerProductSpace

namespace InteractingSLE.Sobolev

open LQGMetric TopologicalSpace QuantumZipper QuantumZipper.K3

/-! ### The dual Dirichlet norm -/

section Dual

variable {D : Opens ℂ}

/-- A function of `C_c^∞(D)` with zero Dirichlet energy vanishes. -/
theorem eq_zero_of_dirichletEnergyOn_eq_zero {f : ℂ → ℝ} (hf : f ∈ zeroSpace (D : Set ℂ))
    (hE : dirichletEnergyOn D f = 0) : f = 0 := by
  have hcont : Continuous (fun z => ‖fderiv ℝ f z‖ ^ 2) :=
    (hf.1.continuous_fderiv (by simp)).norm.pow 2
  have hint : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) D :=
    (hcont.integrable_of_hasCompactSupport ((hf.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun t : ℂ →L[ℝ] ℝ => ‖t‖ ^ 2) (by simp))).integrableOn
  have h0 : ∫ z in (D : Set ℂ), ‖fderiv ℝ f z‖ ^ 2 = 0 := by
    unfold dirichletEnergyOn at hE
    rcases mul_eq_zero.1 hE with h | h
    · exact absurd h (inv_ne_zero (by positivity))
    · exact h
  have hae : (fun z => ‖fderiv ℝ f z‖ ^ 2) =ᵐ[volume.restrict D] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => by positivity) hint).1 h0
  have hEq : EqOn (fun z => ‖fderiv ℝ f z‖ ^ 2) 0 D :=
    Measure.eqOn_open_of_ae_eq hae D.isOpen hcont.continuousOn continuousOn_const
  have hD : ∀ z, fderiv ℝ f z = 0 := by
    intro z
    by_cases hz : z ∈ (D : Set ℂ)
    · have := hEq hz
      simpa using this
    · by_contra h
      exact hz (hf.2.2 (support_fderiv_subset (𝕜 := ℝ) h))
  have hconst : ∀ x y, f x = f y :=
    is_const_of_fderiv_eq_zero (hf.1.differentiable (by simp)) hD
  obtain ⟨z, hz⟩ : ∃ z, z ∉ tsupport f := by
    by_contra h
    push Not at h
    exact hf.2.1.isCompact.ne_univ (eq_univ_of_forall h)
  funext x
  rw [hconst x z, image_eq_zero_of_notMem_tsupport hz]
  rfl

/-- `|∫ f φ| ≤ Var⟨h, φ⟫^{1/2} (f, f)_∇^{1/2}` for `f ∈ C_c^∞(D)`. -/
theorem abs_integral_mul_le_sqrt (hadm : ZBAdmissible D) (φ : TestOn D) {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace (D : Set ℂ)) :
    |∫ x, f x * φ x| ≤ √(zeroGFFTestCov D φ φ) * √(dirichletEnergyOn D f) := by
  by_cases hpos : ∃ g ∈ zeroSpace (D : Set ℂ), 0 < dirichletEnergyOn D g
  · have hV := isDNSpace_zeroSpace (D : Set ℂ)
    rw [← inner_zbRiesz_gradFeat hadm hpos φ hf]
    refine (abs_real_inner_le_norm _ _).trans (le_of_eq ?_)
    rw [zeroGFFTestCov_eq_inner hadm, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _),
      ← norm_gradFeat_sq (hV.smooth f hf) (hV.energy f hf), Real.sqrt_sq (norm_nonneg _)]
  · have hE : dirichletEnergyOn D f = 0 :=
      le_antisymm (not_lt.1 fun h => hpos ⟨f, hf, h⟩) (energy_nonneg _ _)
    rw [eq_zero_of_dirichletEnergyOn_eq_zero hf hE]
    simp only [Pi.zero_apply, zero_mul, integral_zero, abs_zero]
    positivity

theorem integral_sq_fderiv_eq {f : ℂ → ℝ}
    (hf : f ∈ zeroSpace (D : Set ℂ)) :
    ∫ x, ‖fderiv ℝ f x‖ ^ 2 = 2 * π * dirichletEnergyOn D f := by
  have h1 : ∫ x in (D : Set ℂ), ‖fderiv ℝ f x‖ ^ 2 = ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have : fderiv ℝ f x = 0 := by
      by_contra h
      exact hx (hf.2.2 (support_fderiv_subset (𝕜 := ℝ) h))
    simp [this]
  rw [← h1, dirichletEnergyOn]
  field_simp

/-- The smooth approximants `√(v² + η²) - η` of `|v|`. -/
def absApprox (η : ℝ) (v : ℂ → ℝ) (x : ℂ) : ℝ := √(v x ^ 2 + η ^ 2) - η

theorem absApprox_mem {η : ℝ} (hη : 0 < η) {v : ℂ → ℝ} (hv : v ∈ zeroSpace (D : Set ℂ)) :
    absApprox η v ∈ zeroSpace (D : Set ℂ) := by
  have hsupp : support (absApprox η v) ⊆ support v := by
    intro x hx
    by_contra h
    apply hx
    simp only [notMem_support] at h
    simp [absApprox, h, Real.sqrt_sq hη.le]
  refine ⟨?_, hv.2.1.mono hsupp, (closure_mono hsupp).trans hv.2.2⟩
  exact (((hv.1.pow 2).add contDiff_const).sqrt fun x => by positivity).sub contDiff_const

theorem norm_fderiv_absApprox_le {η : ℝ} (hη : 0 < η) {v : ℂ → ℝ}
    (hv : Differentiable ℝ v) (x : ℂ) :
    ‖fderiv ℝ (absApprox η v) x‖ ≤ ‖fderiv ℝ v x‖ := by
  have hpos : v x ^ 2 + η ^ 2 ≠ 0 := by positivity
  have h1 : HasFDerivAt (fun y => v y ^ 2 + η ^ 2) ((2 * v x ^ 1) • fderiv ℝ v x) x := by
    have := ((hv x).hasFDerivAt.pow 2).add_const (η ^ 2)
    simpa using this
  have h2 := (h1.sqrt hpos).sub_const η
  rw [show absApprox η v = fun y => √(v y ^ 2 + η ^ 2) - η from rfl, h2.fderiv, norm_smul,
    norm_smul]
  have hs : 0 < √(v x ^ 2 + η ^ 2) := Real.sqrt_pos.2 (by positivity)
  have habs : |v x| ≤ √(v x ^ 2 + η ^ 2) := Real.abs_le_sqrt (by nlinarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, pow_one, abs_of_pos (by positivity : 0 < 1 / (2 * √(v x ^ 2 + η ^ 2))),
    abs_mul, abs_two, ← mul_assoc]
  calc 1 / (2 * √(v x ^ 2 + η ^ 2)) * (2 * |v x|) * ‖fderiv ℝ v x‖
      = (|v x| / √(v x ^ 2 + η ^ 2)) * ‖fderiv ℝ v x‖ := by field_simp
    _ ≤ 1 * ‖fderiv ℝ v x‖ :=
        mul_le_mul_of_nonneg_right ((div_le_one hs).2 habs) (norm_nonneg _)
    _ = ‖fderiv ℝ v x‖ := one_mul _

theorem integrable_sq_fderiv {f : ℂ → ℝ} (hf : f ∈ zeroSpace (D : Set ℂ)) :
    Integrable (fun z => ‖fderiv ℝ f z‖ ^ 2) := by
  have hcont : Continuous (fun z => ‖fderiv ℝ f z‖ ^ 2) :=
    (hf.1.continuous_fderiv (by simp)).norm.pow 2
  have hcs : HasCompactSupport (fun z => ‖fderiv ℝ f z‖ ^ 2) :=
    (hf.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun t : ℂ →L[ℝ] ℝ => ‖t‖ ^ 2) (by simp)
  exact hcont.integrable_of_hasCompactSupport hcs

theorem integrableOn_sq_fderiv {f : ℂ → ℝ} (hf : f ∈ zeroSpace (D : Set ℂ)) :
    IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) D :=
  (integrable_sq_fderiv hf).integrableOn

theorem dirichletEnergyOn_absApprox_le {η : ℝ} (hη : 0 < η) {v : ℂ → ℝ}
    (hv : v ∈ zeroSpace (D : Set ℂ)) :
    dirichletEnergyOn D (absApprox η v) ≤ dirichletEnergyOn D v := by
  have hw := absApprox_mem hη hv
  have hvd : Differentiable ℝ v := hv.1.differentiable (by simp)
  have hmono : ∫ z in (D : Set ℂ), ‖fderiv ℝ (absApprox η v) z‖ ^ 2 ≤
      ∫ z in (D : Set ℂ), ‖fderiv ℝ v z‖ ^ 2 :=
    setIntegral_mono (integrableOn_sq_fderiv hw) (integrableOn_sq_fderiv hv) fun x =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_absApprox_le hη hvd x) 2
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **L¹ Poincaré inequality** from the finite Green covariance: for a nonnegative cutoff `ψ` and
`v ∈ C_c^∞(D)`, `∫ |v| ψ ≤ Var⟨h, ψ⟫^{1/2} (v, v)_∇^{1/2}`. -/
theorem integral_abs_mul_le (hadm : ZBAdmissible D) (ψ : TestOn D) (hψ : ∀ x, 0 ≤ ψ x)
    {v : ℂ → ℝ} (hv : v ∈ zeroSpace (D : Set ℂ)) :
    ∫ x, |v x| * ψ x ≤ √(zeroGFFTestCov D ψ ψ) * √(dirichletEnergyOn D v) := by
  have hψi : Integrable ψ := ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hψ0 : 0 ≤ ∫ x, ψ x := integral_nonneg hψ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set η := ε / ((∫ x, ψ x) + 1) with hηdef
  have hη : 0 < η := div_pos hε (by linarith)
  have hw := absApprox_mem hη hv
  have hwc : Continuous (absApprox η v) := hw.1.continuous
  have hint1 : Integrable (fun x => |v x| * ψ x) :=
    ((hv.1.continuous.abs).mul ψ.continuous).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_left
  have hint2 : Integrable (fun x => absApprox η v x * ψ x) :=
    (hwc.mul ψ.continuous).integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_left
  have hpt : ∀ x, |v x| * ψ x ≤ absApprox η v x * ψ x + η * ψ x := by
    intro x
    have : |v x| ≤ √(v x ^ 2 + η ^ 2) := Real.abs_le_sqrt (by nlinarith)
    have h2 : |v x| ≤ absApprox η v x + η := by simp only [absApprox]; linarith
    nlinarith [hψ x]
  have h1 : ∫ x, |v x| * ψ x ≤ (∫ x, absApprox η v x * ψ x) + η * ∫ x, ψ x := by
    calc ∫ x, |v x| * ψ x ≤ ∫ x, (absApprox η v x * ψ x + η * ψ x) :=
          integral_mono hint1 (hint2.add (hψi.const_mul η)) hpt
      _ = (∫ x, absApprox η v x * ψ x) + η * ∫ x, ψ x := by
          rw [integral_add hint2 (hψi.const_mul η), integral_const_mul]
  have h2 : ∫ x, absApprox η v x * ψ x ≤ √(zeroGFFTestCov D ψ ψ) * √(dirichletEnergyOn D v) :=
    (le_abs_self _).trans ((abs_integral_mul_le_sqrt hadm ψ hw).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (dirichletEnergyOn_absApprox_le hη hv))
        (Real.sqrt_nonneg _)))
  have h3 : η * ∫ x, ψ x ≤ ε := by
    rw [hηdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Cauchy–Schwarz: `∫ |ζ| |∇v| ≤ ‖ζ‖₂ (2π (v, v)_∇)^{1/2}`. -/
theorem integral_abs_mul_norm_fderiv_le {ζ : ℂ → ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    {v : ℂ → ℝ} (hv : v ∈ zeroSpace (D : Set ℂ)) :
    ∫ x, |ζ x| * ‖fderiv ℝ v x‖ ≤ √(∫ x, ζ x ^ 2) * √(2 * π * dirichletEnergyOn D v) := by
  have hDv : Continuous (fun x => ‖fderiv ℝ v x‖) := (hv.1.continuous_fderiv (by simp)).norm
  have hDvc : HasCompactSupport (fun x => ‖fderiv ℝ v x‖) := (hv.2.1.fderiv (𝕜 := ℝ)).norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (f := fun x => |ζ x|) (g := fun x => ‖fderiv ℝ v x‖)
    (Eventually.of_forall fun x => abs_nonneg _) (Eventually.of_forall fun x => norm_nonneg _)
    (hζ.abs.memLp_of_hasCompactSupport hζc.abs) (hDv.memLp_of_hasCompactSupport hDvc)
  have e1 : ∀ x, |ζ x| ^ (2 : ℝ) = ζ x ^ 2 := fun x => by rw [Real.rpow_two, sq_abs]
  have e2 : ∀ x, ‖fderiv ℝ v x‖ ^ (2 : ℝ) = ‖fderiv ℝ v x‖ ^ 2 := fun x => Real.rpow_two _
  simp only [e1, e2] at h
  rw [integral_sq_fderiv_eq hv, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  exact h

/-- A smooth cutoff with values in `[0, 1]`, equal to `1` on a compact `K ⊆ D`. -/
theorem exists_cutoff_testOn {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ χ : TestOn D, (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ EqOn χ 1 K := by
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_cthickening_subset_open D.isOpen hKD
  obtain ⟨χ, hχ, hrange, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (Metric.isOpen_thickening (δ := δ) (E := K)) hK.isClosed
    (Metric.self_subset_thickening hδ K)
  have hts : tsupport χ ⊆ Metric.cthickening δ K := by
    rw [tsupport, hsupp]
    exact Metric.closure_thickening_subset_cthickening δ K
  refine ⟨⟨χ, hχ, (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hδD⟩, fun x => ?_, fun x hx => (h1 x).1 hx⟩
  exact hrange (mem_range_self x)

end Dual

/-! ### One integration by parts in the direction `ξ` -/

section IBP

theorem abs_integral_mul_le_of_fderiv {f g h : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g) (hgb : ∀ x, |g x| ≤ 1) {ξ : ℂ} {c : ℝ}
    (hc : 0 < c) (hgh : ∀ x, fderiv ℝ g x ξ = c * h x) :
    |∫ x, f x * h x| ≤ c⁻¹ * ‖ξ‖ * ∫ x, ‖fderiv ℝ f x‖ := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hDf : Continuous (fun x => fderiv ℝ f x) := hf.continuous_fderiv (by simp)
  have hDg : Continuous (fun x => fderiv ℝ g x) := hg.continuous_fderiv (by simp)
  have hDfc : HasCompactSupport (fderiv ℝ f) := hfc.fderiv (𝕜 := ℝ)
  have hDfξ : HasCompactSupport (fun x => fderiv ℝ f x ξ) :=
    hDfc.comp_left (g := fun L : ℂ →L[ℝ] ℝ => L ξ) (by simp)
  have i1 : Integrable (fun x => fderiv ℝ f x ξ * g x) :=
    ((hDf.clm_apply continuous_const).mul hg.continuous).integrable_of_hasCompactSupport
      hDfξ.mul_right
  have i2 : Integrable (fun x => f x * fderiv ℝ g x ξ) :=
    (hf.continuous.mul (hDg.clm_apply continuous_const)).integrable_of_hasCompactSupport
      hfc.mul_right
  have i3 : Integrable (fun x => f x * g x) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
    (fun x _ => hfd x) (fun x _ => hgd x)
  have hrw : ∫ x, f x * fderiv ℝ g x ξ = c * ∫ x, f x * h x := by
    simp_rw [hgh]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hnorm : Integrable (fun x => ‖fderiv ℝ f x‖) :=
    hDf.norm.integrable_of_hasCompactSupport hDfc.norm
  have hbd : |∫ x, fderiv ℝ f x ξ * g x| ≤ ‖ξ‖ * ∫ x, ‖fderiv ℝ f x‖ := by
    rw [← integral_const_mul]
    refine abs_integral_le_integral_abs.trans
      (integral_mono i1.abs (hnorm.const_mul _) fun x => ?_)
    have h1 : |fderiv ℝ f x ξ| ≤ ‖fderiv ℝ f x‖ * ‖ξ‖ := by
      rw [← Real.norm_eq_abs]; exact (fderiv ℝ f x).le_opNorm ξ
    simp only [abs_mul]
    calc |fderiv ℝ f x ξ| * |g x| ≤ (‖fderiv ℝ f x‖ * ‖ξ‖) * 1 :=
          mul_le_mul h1 (hgb x) (abs_nonneg _) (by positivity)
      _ = ‖ξ‖ * ‖fderiv ℝ f x‖ := by ring
  have heq : ∫ x, f x * h x = -c⁻¹ * ∫ x, fderiv ℝ f x ξ * g x := by
    rw [hibp] at hrw
    field_simp
    linarith
  rw [heq, abs_mul, abs_neg, abs_of_pos (inv_pos.2 hc), mul_assoc]
  exact mul_le_mul_of_nonneg_left hbd (inv_pos.2 hc).le

theorem hasFDerivAt_trig_phase {t t' : ℝ → ℝ} (ht : ∀ s, HasDerivAt t (t' s) s) (ξ x : ℂ) :
    HasFDerivAt (fun y => t (2 * π * ⟪y, ξ⟫)) (t' (2 * π * ⟪x, ξ⟫) • phaseL ξ) x := by
  have h := (ht (phaseL ξ x)).comp_hasFDerivAt x (phaseL ξ).hasFDerivAt
  have e : (fun y => t (2 * π * ⟪y, ξ⟫)) = t ∘ phaseL ξ := by
    funext y; simp [phaseL_apply]
  rw [e, ← phaseL_apply]
  exact h

theorem phaseL_self (ξ : ℂ) : phaseL ξ ξ = 2 * π * ‖ξ‖ ^ 2 := by
  rw [phaseL_apply, real_inner_self_eq_norm_sq]

/-- `|∫ f cos(2π⟪·, ξ⟫)| ≤ (2π|ξ|)⁻¹ ∫ |∇f|`. -/
theorem abs_integral_mul_cos_le {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {ξ : ℂ} (hξ : ξ ≠ 0) :
    |∫ x, f x * Real.cos (2 * π * ⟪x, ξ⟫)| ≤ (2 * π * ‖ξ‖)⁻¹ * ∫ x, ‖fderiv ℝ f x‖ := by
  have hξ' : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hc : 0 < 2 * π * ‖ξ‖ ^ 2 := by positivity
  have h := abs_integral_mul_le_of_fderiv (ξ := ξ) (g := fun y => Real.sin (2 * π * ⟪y, ξ⟫))
    (h := fun x => Real.cos (2 * π * ⟪x, ξ⟫)) hf hfc
    (Real.contDiff_sin.comp (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)))
    (fun x => Real.abs_sin_le_one _) hc fun x => by
      rw [(hasFDerivAt_trig_phase Real.hasDerivAt_sin ξ x).fderiv]
      rw [smul_apply, smul_eq_mul, phaseL_self]
      ring
  refine h.trans (le_of_eq ?_)
  field_simp

/-- `|∫ f sin(2π⟪·, ξ⟫)| ≤ (2π|ξ|)⁻¹ ∫ |∇f|`. -/
theorem abs_integral_mul_sin_le {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {ξ : ℂ} (hξ : ξ ≠ 0) :
    |∫ x, f x * Real.sin (2 * π * ⟪x, ξ⟫)| ≤ (2 * π * ‖ξ‖)⁻¹ * ∫ x, ‖fderiv ℝ f x‖ := by
  have hξ' : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hc : 0 < 2 * π * ‖ξ‖ ^ 2 := by positivity
  have hd : ∀ s, HasDerivAt (fun s => -Real.cos s) (Real.sin s) s := fun s => by
    simpa using (Real.hasDerivAt_cos s).fun_neg
  have h := abs_integral_mul_le_of_fderiv (ξ := ξ) (g := fun y => -Real.cos (2 * π * ⟪y, ξ⟫))
    (h := fun x => Real.sin (2 * π * ⟪x, ξ⟫)) hf hfc
    ((Real.contDiff_cos.comp (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const))).neg)
    (fun x => by rw [abs_neg]; exact Real.abs_cos_le_one _) hc fun x => by
      rw [(hasFDerivAt_trig_phase hd ξ x).fderiv]
      rw [smul_apply, smul_eq_mul, phaseL_self]
      ring
  refine h.trans (le_of_eq ?_)
  field_simp

end IBP

/-! ### (SR2): the Fourier bound -/

section SR2

variable {D : Opens ℂ}

/-- Two bounds `|I| ≤ A √E` and `|I| ≤ r⁻¹ B √E` (for `r > 0`) give `I² ≤ 2(A² + B²)/(1 + r²) E`. -/
theorem sq_le_of_two_bounds {I A B E r : ℝ} (hE : 0 ≤ E) (hr : 0 ≤ r)
    (h1 : |I| ≤ A * √E) (h2 : 0 < r → |I| ≤ r⁻¹ * B * √E) :
    I ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) / (1 + r ^ 2) * E := by
  have hsE : √E ^ 2 = E := Real.sq_sqrt hE
  have hI : I ^ 2 = |I| ^ 2 := (sq_abs I).symm
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  rcases le_or_gt r 1 with hr1 | hr1
  · have h3 : I ^ 2 ≤ A ^ 2 * E := by
      rw [hI, ← hsE, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hr2 : r ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg B, mul_nonneg (sq_nonneg A) hE, mul_nonneg (sq_nonneg B) hE]
  · have hr0 : 0 < r := by linarith
    have h3 : I ^ 2 * r ^ 2 ≤ B ^ 2 * E := by
      have := h2 hr0
      rw [hI, ← hsE]
      have h4 : |I| * r ≤ B * √E := by
        rw [← le_div_iff₀ hr0]
        calc |I| ≤ r⁻¹ * B * √E := this
          _ = B * √E / r := by field_simp
      have h5 := pow_le_pow_left₀ (by positivity) h4 2
      rw [mul_pow, mul_pow] at h5
      linarith
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg A) hE, mul_nonneg (sq_nonneg B) hE, sq_nonneg I,
      mul_nonneg (mul_nonneg (sq_nonneg B) hE) (by linarith : (0 : ℝ) ≤ r ^ 2 - 1)]

/-- The variance is bounded by `B` if every `(∫ v φ)²` is at most `B (v, v)_∇`. -/
theorem zeroGFFTestCov_le_of_forall (hadm : ZBAdmissible D) {φ : TestOn D} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v ∈ zeroSpace (D : Set ℂ), (∫ x, v x * φ x) ^ 2 ≤ B * dirichletEnergyOn D v) :
    zeroGFFTestCov D φ φ ≤ B := by
  have hsup : zbVarSup D φ ≤ ENNReal.ofReal B := by
    refine iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hv.2]
    exact h v hv.1
  rw [← ofReal_zeroGFFTestCov_self hadm φ] at hsup
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hsup

/-- The two estimates of `|∫ v ζ t(2π⟪·, ξ⟫)|` (`t = cos, sin`, `v ∈ C_c^∞(D)`). -/
theorem abs_integral_trig_le (hadm : ZBAdmissible D) (ζ χ : TestOn D) (hχ : ∀ x, 0 ≤ χ x)
    (hχ1 : EqOn χ 1 (tsupport ζ)) {Z M : ℝ} (hZ : ∀ x, ‖ζ x‖ ≤ Z)
    (hM : ∀ x, ‖fderiv ℝ ζ x‖ ≤ M) {t : ℝ → ℝ} (ht : Continuous t) (htb : ∀ s, |t s| ≤ 1)
    (hibp : ∀ f : ℂ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ ξ : ℂ, ξ ≠ 0 →
      |∫ x, f x * t (2 * π * ⟪x, ξ⟫)| ≤ (2 * π * ‖ξ‖)⁻¹ * ∫ x, ‖fderiv ℝ f x‖)
    {v : ℂ → ℝ} (hv : v ∈ zeroSpace (D : Set ℂ)) (ξ : ℂ) :
    |∫ x, v x * (ζ x * t (2 * π * ⟪x, ξ⟫))| ≤
        Z * √(zeroGFFTestCov D χ χ) * √(dirichletEnergyOn D v) ∧
      (0 < ‖ξ‖ → |∫ x, v x * (ζ x * t (2 * π * ⟪x, ξ⟫))| ≤
        ‖ξ‖⁻¹ * (M * √(zeroGFFTestCov D χ χ) + √(∫ x, ζ x ^ 2) * √(2 * π)) *
          √(dirichletEnergyOn D v)) := by
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hvc : Continuous v := hv.1.continuous
  have htc : Continuous (fun x : ℂ => t (2 * π * ⟪x, ξ⟫)) :=
    ht.comp (continuous_const.mul (continuous_id.inner continuous_const))
  have hint_vχ : Integrable (fun x => |v x| * χ x) :=
    (hvc.abs.mul χ.continuous).integrable_of_hasCompactSupport χ.hasCompactSupport.mul_left
  have hζχ : ∀ x, |ζ x| ≤ Z * χ x := by
    intro x
    by_cases hx : x ∈ tsupport ζ
    · rw [hχ1 hx, Pi.one_apply, mul_one, ← Real.norm_eq_abs]; exact hZ x
    · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]; exact mul_nonneg hZ0 (hχ x)
  have hDζχ : ∀ x, ‖fderiv ℝ ζ x‖ ≤ M * χ x := by
    intro x
    by_cases hx : x ∈ tsupport ζ
    · rw [hχ1 hx, Pi.one_apply, mul_one]; exact hM x
    · have : fderiv ℝ ζ x = 0 := by
        by_contra h; exact hx (support_fderiv_subset (𝕜 := ℝ) h)
      rw [this, norm_zero]; exact mul_nonneg hM0 (hχ x)
  have hP := integral_abs_mul_le hadm χ hχ hv
  constructor
  · calc |∫ x, v x * (ζ x * t (2 * π * ⟪x, ξ⟫))|
        ≤ ∫ x, |v x * (ζ x * t (2 * π * ⟪x, ξ⟫))| := abs_integral_le_integral_abs
      _ ≤ ∫ x, Z * (|v x| * χ x) := by
          refine integral_mono ((hvc.mul (ζ.continuous.mul htc)).abs.integrable_of_hasCompactSupport
            (hv.2.1.mul_right.abs)) (hint_vχ.const_mul Z) fun x => ?_
          rw [abs_mul, abs_mul]
          calc |v x| * (|ζ x| * |t (2 * π * ⟪x, ξ⟫)|) ≤ |v x| * ((Z * χ x) * 1) :=
                mul_le_mul_of_nonneg_left (mul_le_mul (hζχ x) (htb _) (abs_nonneg _)
                  (mul_nonneg hZ0 (hχ x))) (abs_nonneg _)
            _ = Z * (|v x| * χ x) := by ring
      _ = Z * ∫ x, |v x| * χ x := integral_const_mul _ _
      _ ≤ Z * (√(zeroGFFTestCov D χ χ) * √(dirichletEnergyOn D v)) :=
          mul_le_mul_of_nonneg_left hP hZ0
      _ = Z * √(zeroGFFTestCov D χ χ) * √(dirichletEnergyOn D v) := by ring
  · intro hξ
    have hξ0 : ξ ≠ 0 := norm_pos_iff.1 hξ
    have hfd : ContDiff ℝ ∞ (fun x => v x * ζ x) := hv.1.mul ζ.contDiff
    have hfc : HasCompactSupport (fun x => v x * ζ x) := hv.2.1.mul_right
    have h1 := hibp _ hfd hfc ξ hξ0
    have heq : ∫ x, v x * (ζ x * t (2 * π * ⟪x, ξ⟫)) =
        ∫ x, (v x * ζ x) * t (2 * π * ⟪x, ξ⟫) := by
      congr 1; funext x; ring
    have hvd : Differentiable ℝ v := hv.1.differentiable (by simp)
    have hζd : Differentiable ℝ ζ := ζ.contDiff.differentiable (by simp)
    have hDf : ∀ x, ‖fderiv ℝ (fun x => v x * ζ x) x‖ ≤
        M * (|v x| * χ x) + |ζ x| * ‖fderiv ℝ v x‖ := by
      intro x
      rw [((hvd x).hasFDerivAt.fun_mul (hζd x).hasFDerivAt).fderiv]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have := hDζχ x
      nlinarith [abs_nonneg (v x), norm_nonneg (fderiv ℝ ζ x)]
    have hint_Df : Integrable (fun x => ‖fderiv ℝ (fun x => v x * ζ x) x‖) :=
      ((hfd.continuous_fderiv (by simp)).norm).integrable_of_hasCompactSupport
        (hfc.fderiv (𝕜 := ℝ)).norm
    have hint_ζDv : Integrable (fun x => |ζ x| * ‖fderiv ℝ v x‖) :=
      (ζ.continuous.abs.mul (hv.1.continuous_fderiv (by simp)).norm).integrable_of_hasCompactSupport
        ζ.hasCompactSupport.abs.mul_right
    have h2 : ∫ x, ‖fderiv ℝ (fun x => v x * ζ x) x‖ ≤
        (M * √(zeroGFFTestCov D χ χ) + √(∫ x, ζ x ^ 2) * √(2 * π)) *
          √(dirichletEnergyOn D v) := by
      calc ∫ x, ‖fderiv ℝ (fun x => v x * ζ x) x‖
          ≤ ∫ x, (M * (|v x| * χ x) + |ζ x| * ‖fderiv ℝ v x‖) :=
            integral_mono hint_Df ((hint_vχ.const_mul M).add hint_ζDv) hDf
        _ = M * (∫ x, |v x| * χ x) + ∫ x, |ζ x| * ‖fderiv ℝ v x‖ := by
            rw [integral_add (hint_vχ.const_mul M) hint_ζDv, integral_const_mul]
        _ ≤ M * (√(zeroGFFTestCov D χ χ) * √(dirichletEnergyOn D v)) +
              √(∫ x, ζ x ^ 2) * √(2 * π * dirichletEnergyOn D v) :=
            add_le_add (mul_le_mul_of_nonneg_left hP hM0)
              (integral_abs_mul_norm_fderiv_le ζ.continuous ζ.hasCompactSupport hv)
        _ = _ := by
            rw [Real.sqrt_mul (by positivity)]
            ring
    have hinv : (2 * π * ‖ξ‖)⁻¹ ≤ ‖ξ‖⁻¹ :=
      inv_anti₀ hξ (le_mul_of_one_le_left hξ.le (by linarith [Real.two_le_pi]))
    rw [heq]
    refine h1.trans ?_
    refine (mul_le_mul hinv h2 (integral_nonneg fun _ => norm_nonneg _)
      (inv_nonneg.2 hξ.le)).trans (le_of_eq ?_)
    ring

/-- **(SR2)**: `Var⟨h, ζ cos(2π⟪·,ξ⟫)⟫, Var⟨h, ζ sin(2π⟪·,ξ⟫)⟫ ≤ C_ζ / (1 + |ξ|²)`. -/
theorem exists_zeroGFFTestCov_trigTest_le (hadm : ZBAdmissible D) (ζ : TestOn D) :
    ∃ C, 0 ≤ C ∧ ∀ ξ, zeroGFFTestCov D (cosTest ζ ξ) (cosTest ζ ξ) ≤ C / (1 + ‖ξ‖ ^ 2) ∧
      zeroGFFTestCov D (sinTest ζ ξ) (sinTest ζ ξ) ≤ C / (1 + ‖ξ‖ ^ 2) := by
  obtain ⟨χ, hχ01, hχ1⟩ := exists_cutoff_testOn ζ.hasCompactSupport ζ.tsupport_subset
  obtain ⟨Z, hZ⟩ := ζ.continuous.bounded_above_of_compact_support ζ.hasCompactSupport
  obtain ⟨M, hM⟩ := (ζ.contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (ζ.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set A := Z * √(zeroGFFTestCov D χ χ)
  set B := M * √(zeroGFFTestCov D χ χ) + √(∫ x, ζ x ^ 2) * √(2 * π)
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  refine ⟨2 * (A ^ 2 + B ^ 2), by positivity, fun ξ => ⟨?_, ?_⟩⟩
  · refine zeroGFFTestCov_le_of_forall hadm (by positivity) fun v hv => ?_
    have h := abs_integral_trig_le hadm ζ χ (fun x => (hχ01 x).1) hχ1 hZ hM
      Real.continuous_cos Real.abs_cos_le_one
      (fun f hf hfc ξ hξ => abs_integral_mul_cos_le hf hfc hξ) hv ξ
    exact sq_le_of_two_bounds (energy_nonneg _ _) (norm_nonneg _) h.1 h.2
  · refine zeroGFFTestCov_le_of_forall hadm (by positivity) fun v hv => ?_
    have h := abs_integral_trig_le hadm ζ χ (fun x => (hχ01 x).1) hχ1 hZ hM
      Real.continuous_sin Real.abs_sin_le_one
      (fun f hf hfc ξ hξ => abs_integral_mul_sin_le hf hfc hξ) hv ξ
    exact sq_le_of_two_bounds (energy_nonneg _ _) (norm_nonneg _) h.1 h.2

end SR2

/-! ### Algebra of the negative Sobolev norm -/

section Algebra

variable {U : Opens ℂ}

theorem fourierSq_add_le (T S : DistOn U) (ζ : TestOn U) (ξ : ℂ) :
    fourierSq (T + S) ζ ξ ≤ 2 * fourierSq T ζ ξ + 2 * fourierSq S ζ ξ := by
  simp only [fourierSq, add_apply]
  nlinarith [sq_nonneg (T (cosTest ζ ξ) - S (cosTest ζ ξ)),
    sq_nonneg (T (sinTest ζ ξ) - S (sinTest ζ ξ))]

theorem negSobolevSq_add_le (ε : ℝ) (T S : DistOn U) (ζ : TestOn U) :
    negSobolevSq ε (T + S) ζ ≤ 2 * negSobolevSq ε T ζ + 2 * negSobolevSq ε S ζ := by
  unfold negSobolevSq
  rw [← lintegral_const_mul _ (measurable_fourierSq_mul T ζ _),
    ← lintegral_const_mul _ (measurable_fourierSq_mul S ζ _),
    ← lintegral_add_left ((measurable_fourierSq_mul T ζ _).const_mul _)]
  refine lintegral_mono fun ξ => ?_
  have hw := (sobWeight_pos (-ε) ξ).le
  have hT := fourierSq_nonneg T ζ ξ
  have hS := fourierSq_nonneg S ζ ξ
  calc ENNReal.ofReal (fourierSq (T + S) ζ ξ * sobWeight (-ε) ξ)
      ≤ ENNReal.ofReal (2 * (fourierSq T ζ ξ * sobWeight (-ε) ξ) +
          2 * (fourierSq S ζ ξ * sobWeight (-ε) ξ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_right (fourierSq_add_le T S ζ ξ) hw
        linarith
    _ = 2 * ENNReal.ofReal (fourierSq T ζ ξ * sobWeight (-ε) ξ) +
          2 * ENNReal.ofReal (fourierSq S ζ ξ * sobWeight (-ε) ξ) := by
        have e : ∀ a : ℝ, ENNReal.ofReal (2 * a) = 2 * ENNReal.ofReal a := fun a => by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        rw [ENNReal.ofReal_add (mul_nonneg two_pos.le (mul_nonneg hT hw))
          (mul_nonneg two_pos.le (mul_nonneg hS hw)), e, e]

theorem IsLocNegSobolev.add {ε : ℝ} {T S : DistOn U} (hT : IsLocNegSobolev ε T)
    (hS : IsLocNegSobolev ε S) : IsLocNegSobolev ε (T + S) := fun ζ =>
  lt_of_le_of_lt (negSobolevSq_add_le ε T S ζ)
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) (hT ζ),
      ENNReal.mul_lt_top (by simp) (hS ζ)⟩)

/-- A Fourier bound `|(ζT)^(ξ)|² ≤ C / (1 + |ξ|²)` gives `‖ζT‖²_{H^{-ε}} < ∞` for `ε > 0`. -/
theorem negSobolevSq_lt_top_of_fourierSq_le {ε : ℝ} (hε : 0 < ε) {T : DistOn U} {ζ : TestOn U}
    {C : ℝ} (hC : ∀ ξ, fourierSq T ζ ξ ≤ C / (1 + ‖ξ‖ ^ 2)) : negSobolevSq ε T ζ < ⊤ := by
  have hint : Integrable (fun ξ : ℂ => C * (1 + ‖ξ‖ ^ 2) ^ (-(2 + 2 * ε) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (by simp; linarith)).const_mul _
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_) hint.lintegral_lt_top
  have hr : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hw : (1 + ‖ξ‖ ^ 2) ^ (-(2 + 2 * ε) / 2) = (1 + ‖ξ‖ ^ 2)⁻¹ * sobWeight (-ε) ξ := by
    rw [sobWeight, show -(2 + 2 * ε) / 2 = -1 + -ε by ring, Real.rpow_add hr, Real.rpow_neg_one]
  rw [hw, ← mul_assoc, ← div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hC ξ) (sobWeight_pos _ _).le

end Algebra

/-! ### (SR1) -/

section SR1

variable {D : Opens ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem integral_sq_eq_zeroGFFTestCov {h : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P)
    (φ : TestOn D) : ∫ o, h o φ ^ 2 ∂P = zeroGFFTestCov D φ φ := by
  have hm : Measurable (fun o => h o φ) := hh.process.measurable φ
  have h1 := hh.process.covariance_eq φ φ
  rw [covariance_self hm.aemeasurable,
    variance_of_integral_eq_zero hm.aemeasurable (hh.process.centered φ)] at h1
  exact h1

theorem integrable_sq_apply [IsProbabilityMeasure P] {h : Ω → DistOn D}
    (hh : IsZeroBoundaryGFF D h P) (φ : TestOn D) : Integrable (fun o => h o φ ^ 2) P :=
  (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable_sq

/-- `E|(ζh)^(ξ)|² = Var⟨h, ζ cos⟫ + Var⟨h, ζ sin⟫`. -/
theorem integral_fourierSq [IsProbabilityMeasure P] {h : Ω → DistOn D}
    (hh : IsZeroBoundaryGFF D h P) (ζ : TestOn D) (ξ : ℂ) :
    ∫ o, fourierSq (h o) ζ ξ ∂P =
      zeroGFFTestCov D (cosTest ζ ξ) (cosTest ζ ξ) + zeroGFFTestCov D (sinTest ζ ξ) (sinTest ζ ξ) := by
  simp only [fourierSq]
  rw [integral_add (integrable_sq_apply hh _) (integrable_sq_apply hh _),
    integral_sq_eq_zeroGFFTestCov hh, integral_sq_eq_zeroGFFTestCov hh]

theorem measurable_uncurry_fourierSq {h : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P)
    (ζ : TestOn D) (s : ℝ) :
    Measurable (uncurry fun (o : Ω) (ξ : ℂ) =>
      ENNReal.ofReal (fourierSq (h o) ζ ξ * sobWeight s ξ)) := by
  have hmeas : Measurable (uncurry fun (ξ : ℂ) (o : Ω) => fourierSq (h o) ζ ξ * sobWeight s ξ) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun o => (continuous_fourierSq (h o) ζ).mul (continuous_sobWeight _))
      (fun ξ => (((hh.process.measurable (cosTest ζ ξ)).pow_const 2).add
        ((hh.process.measurable (sinTest ζ ξ)).pow_const 2)).mul_const _)
  exact ENNReal.measurable_ofReal.comp (hmeas.comp measurable_swap)

/-- **(SR1)** for the zero-boundary GFF: `E‖ζh‖²_{H^{-ε}(ℝ²)} < ∞` for every `ε > 0` and every
cutoff `ζ ∈ 𝓓(D)` (specification Aux. lemma 11). -/
theorem lintegral_negSobolevSq_lt_top [IsProbabilityMeasure P] (hadm : ZBAdmissible D)
    {h : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P) {ε : ℝ} (hε : 0 < ε) (ζ : TestOn D) :
    ∫⁻ o, negSobolevSq ε (h o) ζ ∂P < ⊤ := by
  obtain ⟨C, hC0, hC⟩ := exists_zeroGFFTestCov_trigTest_le hadm ζ
  unfold negSobolevSq
  rw [lintegral_lintegral_swap (measurable_uncurry_fourierSq hh ζ _).aemeasurable]
  have hint : Integrable (fun ξ : ℂ => 2 * C * (1 + ‖ξ‖ ^ 2) ^ (-(2 + 2 * ε) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (by simp; linarith)).const_mul _
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hint.lintegral_lt_top
  have hi : Integrable (fun o => fourierSq (h o) ζ ξ * sobWeight (-ε) ξ) P :=
    ((integrable_sq_apply hh _).add (integrable_sq_apply hh _)).mul_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun o =>
    mul_nonneg (fourierSq_nonneg _ _ _) (sobWeight_pos _ _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_mul_const, integral_fourierSq hh]
  have hr : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hw : (1 + ‖ξ‖ ^ 2) ^ (-(2 + 2 * ε) / 2) = (1 + ‖ξ‖ ^ 2)⁻¹ * sobWeight (-ε) ξ := by
    rw [sobWeight, show -(2 + 2 * ε) / 2 = -1 + -ε by ring, Real.rpow_add hr, Real.rpow_neg_one]
  rw [hw]
  have h1 := (hC ξ).1
  have h2 := (hC ξ).2
  have hsw := (sobWeight_pos (-ε) ξ).le
  calc (zeroGFFTestCov D (cosTest ζ ξ) (cosTest ζ ξ) +
        zeroGFFTestCov D (sinTest ζ ξ) (sinTest ζ ξ)) * sobWeight (-ε) ξ
      ≤ (C / (1 + ‖ξ‖ ^ 2) + C / (1 + ‖ξ‖ ^ 2)) * sobWeight (-ε) ξ :=
        mul_le_mul_of_nonneg_right (add_le_add h1 h2) hsw
    _ = 2 * C * ((1 + ‖ξ‖ ^ 2)⁻¹ * sobWeight (-ε) ξ) := by ring

/-- **(SR1)** after adding a deterministic mean in `H^{-ε}_loc(D)` (a smooth harmonic mean, or a
deterministic Cameron–Martin shift: `isLocNegSobolev_of_cameronMartin`). -/
theorem lintegral_negSobolevSq_add_lt_top [IsProbabilityMeasure P] (hadm : ZBAdmissible D)
    {h : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P) {ε : ℝ} (hε : 0 < ε) {m : DistOn D}
    (hm : IsLocNegSobolev ε m) (ζ : TestOn D) :
    ∫⁻ o, negSobolevSq ε (h o + m) ζ ∂P < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun o => negSobolevSq_add_le ε (h o) m ζ) ?_
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp),
    lintegral_const, measure_univ, mul_one]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp)
    (lintegral_negSobolevSq_lt_top hadm hh hε ζ), ENNReal.mul_lt_top (by simp) (hm ζ)⟩

/-- A deterministic **Cameron–Martin shift** `m(φ) = E[⟨h, φ⟩ Y]` (`Y ∈ L²`) lies in
`H^{-ε}_loc(D)` for every `ε > 0`: `|m(φ)|² ≤ E[Y²] Var⟨h, φ⟫` and (SR2). -/
theorem isLocNegSobolev_of_cameronMartin [IsProbabilityMeasure P] (hadm : ZBAdmissible D)
    {h : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P) {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    {m : DistOn D} (hm : ∀ φ, m φ = ∫ o, h o φ * Y o ∂P) {ε : ℝ} (hε : 0 < ε) :
    IsLocNegSobolev ε m := by
  intro ζ
  obtain ⟨C, hC0, hC⟩ := exists_zeroGFFTestCov_trigTest_le hadm ζ
  have hCS : ∀ φ : TestOn D, m φ ^ 2 ≤ (∫ o, Y o ^ 2 ∂P) * zeroGFFTestCov D φ φ := by
    intro φ
    have hX : MemLp (fun o => h o φ) 2 P := (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two
    have h1 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) Real.HolderConjugate.two_two
      (f := fun o => |h o φ|) (g := fun o => |Y o|)
      (Eventually.of_forall fun _ => abs_nonneg _) (Eventually.of_forall fun _ => abs_nonneg _)
      (by rw [ENNReal.ofReal_ofNat]; simpa only [Real.norm_eq_abs] using hX.norm)
      (by rw [ENNReal.ofReal_ofNat]; simpa only [Real.norm_eq_abs] using hY.norm)
    have e1 : ∀ a : ℝ, |a| ^ (2 : ℝ) = a ^ 2 := fun a => by rw [Real.rpow_two, sq_abs]
    simp only [e1] at h1
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, integral_sq_eq_zeroGFFTestCov hh] at h1
    have h2 : |m φ| ≤ √(zeroGFFTestCov D φ φ) * √(∫ o, Y o ^ 2 ∂P) := by
      rw [hm φ]
      refine abs_integral_le_integral_abs.trans (le_trans (le_of_eq ?_) h1)
      congr 1; funext o; rw [abs_mul]
    have h3 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs, mul_pow, Real.sq_sqrt (zeroGFFTestCov_self_nonneg hadm φ),
      Real.sq_sqrt (integral_nonneg fun o => sq_nonneg _)] at h3
    linarith
  set Y2 := ∫ o, Y o ^ 2 ∂P
  have hY2 : 0 ≤ Y2 := integral_nonneg fun o => sq_nonneg _
  refine negSobolevSq_lt_top_of_fourierSq_le hε (C := Y2 * (2 * C)) fun ξ => ?_
  have h1 := hCS (cosTest ζ ξ)
  have h2 := hCS (sinTest ζ ξ)
  have h3 := mul_le_mul_of_nonneg_left (hC ξ).1 hY2
  have h4 := mul_le_mul_of_nonneg_left (hC ξ).2 hY2
  calc fourierSq m ζ ξ = m (cosTest ζ ξ) ^ 2 + m (sinTest ζ ξ) ^ 2 := rfl
    _ ≤ Y2 * (C / (1 + ‖ξ‖ ^ 2)) + Y2 * (C / (1 + ‖ξ‖ ^ 2)) := by linarith
    _ = Y2 * (2 * C) / (1 + ‖ξ‖ ^ 2) := by ring

/-! ### Smooth (harmonic) deterministic means -/

/-- `ζ u` is smooth on `ℂ` if `ζ` is smooth with `tsupport ζ ⊆ W` and `u` is smooth on `W`. -/
theorem contDiff_mul_of_contDiffOn {ζ u : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W) (hζ : ContDiff ℝ ∞ ζ)
    (hζW : tsupport ζ ⊆ W) (hu : ContDiffOn ℝ ∞ u W) : ContDiff ℝ ∞ fun x => ζ x * u x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ W
  · exact hζ.contDiffAt.mul (hu.contDiffAt (hW.mem_nhds hx))
  · have hx' : x ∉ tsupport ζ := fun h => hx (hζW h)
    have hev : (fun x => ζ x * u x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- A function smooth on `D` (for instance a harmonic function) defines a distribution in
`H^{-ε}_loc(D)` for every `ε > 0`. -/
theorem isLocNegSobolev_ofFun {u : ℂ → ℝ} (hu : ContDiffOn ℝ ∞ u D) {ε : ℝ} (hε : 0 < ε) :
    IsLocNegSobolev ε (Distribution.ofFun D u volume ⊤ : DistOn D) := by
  intro ζ
  have hli : LocallyIntegrableOn u D volume := hu.continuousOn.locallyIntegrableOn D.isOpen.measurableSet
  have hf : ContDiff ℝ ∞ (fun x => ζ x * u x) :=
    contDiff_mul_of_contDiffOn D.isOpen ζ.contDiff ζ.tsupport_subset hu
  have hfc : HasCompactSupport (fun x => ζ x * u x) := ζ.hasCompactSupport.mul_right
  set A := ∫ x, |ζ x * u x|
  set B := ∫ x, ‖fderiv ℝ (fun x => ζ x * u x) x‖
  have key : ∀ (t : ℝ → ℝ), Continuous t → (∀ s, |t s| ≤ 1) →
      (∀ ξ : ℂ, ξ ≠ 0 → |∫ x, (ζ x * u x) * t (2 * π * ⟪x, ξ⟫)| ≤
        (2 * π * ‖ξ‖)⁻¹ * ∫ x, ‖fderiv ℝ (fun x => ζ x * u x) x‖) → ∀ ξ : ℂ,
      (∫ x, (ζ x * u x) * t (2 * π * ⟪x, ξ⟫)) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) / (1 + ‖ξ‖ ^ 2) * 1 := by
    intro t ht htb hibp ξ
    have hB0 : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
    refine sq_le_of_two_bounds zero_le_one (norm_nonneg _) ?_ fun hξ => ?_
    · rw [Real.sqrt_one, mul_one]
      refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
        (Eventually.of_forall fun _ => abs_nonneg _)
        ((hf.continuous.abs).integrable_of_hasCompactSupport hfc.abs)
        (Eventually.of_forall fun x => ?_))
      simp only
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (htb _)
    · rw [Real.sqrt_one, mul_one]
      refine (hibp ξ (norm_pos_iff.1 hξ)).trans ?_
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hξ
        (le_mul_of_one_le_left hξ.le (by linarith [Real.two_le_pi]))) hB0
  have hT : ∀ (t : ℝ → ℝ) (ξ : ℂ) (φ : TestOn D), (∀ x, φ x = ζ x * t (2 * π * ⟪x, ξ⟫)) →
      (Distribution.ofFun D u volume ⊤ : DistOn D) φ = ∫ x, (ζ x * u x) * t (2 * π * ⟪x, ξ⟫) := by
    intro t ξ φ hφ
    rw [Distribution.ofFun_apply hli]
    congr 1; funext x; rw [hφ x, smul_eq_mul]; ring
  refine negSobolevSq_lt_top_of_fourierSq_le hε (C := 2 * (2 * (A ^ 2 + B ^ 2))) fun ξ => ?_
  have h1 := key Real.cos Real.continuous_cos Real.abs_cos_le_one
    (fun ξ hξ => abs_integral_mul_cos_le hf hfc hξ) ξ
  have h2 := key Real.sin Real.continuous_sin Real.abs_sin_le_one
    (fun ξ hξ => abs_integral_mul_sin_le hf hfc hξ) ξ
  rw [mul_one] at h1 h2
  simp only [fourierSq]
  rw [hT Real.cos ξ (cosTest ζ ξ) (fun x => rfl), hT Real.sin ξ (sinTest ζ ξ) (fun x => rfl)]
  calc _ ≤ 2 * (A ^ 2 + B ^ 2) / (1 + ‖ξ‖ ^ 2) + 2 * (A ^ 2 + B ^ 2) / (1 + ‖ξ‖ ^ 2) :=
        add_le_add h1 h2
    _ = 2 * (2 * (A ^ 2 + B ^ 2)) / (1 + ‖ξ‖ ^ 2) := by ring

/-- **Aux. lemma 11, (SR1)**: a planar GFF `h = h⁰ + u` with deterministic harmonic mean `u` on
an open set `D` with finite Green covariance on compact subsets satisfies
`E‖ζh‖²_{H^{-ε}(ℝ²)} < ∞` for every `0 < ε` (in particular `0 < ε < 1`) and `ζ ∈ 𝓓(D)`. -/
theorem aux11_sr1 [IsProbabilityMeasure P] (hadm : ZBAdmissible D) {h : Ω → DistOn D}
    (hh : IsZeroBoundaryGFF D h P) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u D)
    {ε : ℝ} (hε : 0 < ε) (ζ : TestOn D) :
    ∫⁻ o, negSobolevSq ε (h o + Distribution.ofFun D u volume ⊤) ζ ∂P < ⊤ :=
  lintegral_negSobolevSq_add_lt_top hadm hh hε
    (isLocNegSobolev_ofFun (fun x hx => (HarmonicAt.analyticAt (hu x hx)).contDiffAt.contDiffWithinAt)
      hε) ζ

end SR1

end InteractingSLE.Sobolev
