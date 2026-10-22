import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import HigherDimLFPP.Frozen.IsLFPPKernel
import HigherDimLFPP.Paths.DistOn

/-!
# The Fourier transform of a radial `C_c^∞` kernel

Packet L1b (block B1), audit MA5 Details (a) A2.1 (`G(0) = 1`) and A2.3 (`G > 0`). Here
`𝓕 g(ζ) = ∫ e^{-2πi⟨x,ζ⟩} g(x) dx` is mathlib's (unitary) Fourier transform on `ℝ^d = Rd d`, and
`κ` is a kernel with `HigherDimLFPP.IsLFPPKernel κ` (smooth, `≥ 0`, compactly supported, radial,
`∫ κ² = 1`); `fun x => (κ x : ℂ)` is its complexification.

* `kernelSchwartz` — `κ` as a Schwartz function; `continuous_fourier_kernel`, `fourier_kernel_decay`.
* `fourier_kernel_eq_of_norm_eq`, `fourier_kernel_eq_norm_smul_e₁` — `𝓕κ` is radial
  (a reflection maps `ζ` to `ζ'`; `Real.fourier_comp_linearIsometry`).
* `integral_norm_sq_fourier_kernel` — Plancherel: `∫ |𝓕κ|² = ∫ κ² = 1`.
* `integral_norm_sq_fourier_kernel_polar` — polar coordinates:
  `∫ |𝓕κ|² = |S^{d-1}| ∫_0^∞ t^{d-1} |𝓕κ(t e₁)|² dt` with `|S^{d-1}| = 2π^{d/2}/Γ(d/2)`
  (`sphereArea_eq`).
* `fourierLine`, `differentiable_fourierLine`, `fourierLine_ofReal` — for a continuous compactly
  supported `g`, `t ↦ 𝓕g(ζ₀ + t v)` is the restriction to `ℝ` of an entire function of `t`.
* `fourier_eq_zero_of_far` — **a band-limited function with compact support vanishes**: if
  `𝓕g(ζ) = 0` whenever `‖ζ‖ > ρ`, then `𝓕g ≡ 0` (identity theorem along the lines `ζ₀ + ℝ e₁`).
  This replaces MA5 A2.3's Taylor/Bernstein argument on the `x` side by analyticity on the Fourier
  side; the conclusion (`G > 0`) is the same.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ### `κ` as a Schwartz function; radiality of `𝓕κ` -/

section Kernel

variable {κ : Rd d → ℝ}

theorem contDiff_ofReal_kernel (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Rd d => (κ x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hκ.contDiff

theorem hasCompactSupport_ofReal_kernel (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    HasCompactSupport (fun x : Rd d => (κ x : ℂ)) :=
  hκ.hasCompactSupport.comp_left Complex.ofReal_zero

/-- The complexified kernel `x ↦ (κ x : ℂ)` as a Schwartz function. -/
def kernelSchwartz (hκ : HigherDimLFPP.IsLFPPKernel κ) : SchwartzMap (Rd d) ℂ :=
  (hasCompactSupport_ofReal_kernel hκ).toSchwartzMap (contDiff_ofReal_kernel hκ)

theorem kernelSchwartz_apply (hκ : HigherDimLFPP.IsLFPPKernel κ) (x : Rd d) :
    kernelSchwartz hκ x = (κ x : ℂ) := rfl

theorem coe_fourier_kernelSchwartz (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ((𝓕 (kernelSchwartz hκ) : SchwartzMap (Rd d) ℂ) : Rd d → ℂ) =
      𝓕 (fun x : Rd d => (κ x : ℂ)) := by
  rw [SchwartzMap.fourier_coe]
  rfl

theorem continuous_fourier_kernel (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    Continuous (𝓕 (fun x : Rd d => (κ x : ℂ))) := by
  rw [← coe_fourier_kernelSchwartz hκ]
  exact (𝓕 (kernelSchwartz hκ)).continuous

/-- Schwartz decay of `𝓕κ`: `‖ζ‖^k ‖𝓕κ(ζ)‖ ≤ C`. -/
theorem fourier_kernel_decay (hκ : HigherDimLFPP.IsLFPPKernel κ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ζ : Rd d, ‖ζ‖ ^ k * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) ζ‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := (𝓕 (kernelSchwartz hκ)).decay k 0
  refine ⟨C, hC0, fun ζ => ?_⟩
  have := hC ζ
  rwa [norm_iteratedFDeriv_zero, coe_fourier_kernelSchwartz hκ] at this

/-- **Radiality of `𝓕κ`.** -/
theorem fourier_kernel_eq_of_norm_eq (hrad : ∀ z w : Rd d, ‖z‖ = ‖w‖ → κ z = κ w)
    {ζ ζ' : Rd d} (h : ‖ζ‖ = ‖ζ'‖) :
    𝓕 (fun x : Rd d => (κ x : ℂ)) ζ = 𝓕 (fun x : Rd d => (κ x : ℂ)) ζ' := by
  set A : Rd d ≃ₗᵢ[ℝ] Rd d := Submodule.reflection (Submodule.span ℝ {ζ - ζ'})ᗮ with hAdef
  have hA : A ζ = ζ' := Submodule.reflection_sub h
  have hcomp : (fun x : Rd d => (κ x : ℂ)) ∘ A = fun x : Rd d => (κ x : ℂ) := by
    funext x
    simp only [Function.comp_apply]
    rw [hrad (A x) x (A.norm_map x)]
  rw [← hA, ← Real.fourier_comp_linearIsometry A, hcomp]

theorem fourier_kernel_eq_norm_smul_e₁ (hd : 0 < d)
    (hrad : ∀ z w : Rd d, ‖z‖ = ‖w‖ → κ z = κ w) (ζ : Rd d) :
    𝓕 (fun x : Rd d => (κ x : ℂ)) ζ = 𝓕 (fun x : Rd d => (κ x : ℂ)) (‖ζ‖ • e₁ d) :=
  fourier_kernel_eq_of_norm_eq hrad (by
    rw [norm_smul, HigherDimLFPP.norm_e₁ hd, mul_one, norm_norm])

/-- **Plancherel**: `∫ ‖𝓕κ‖² = ∫ κ² = 1`. -/
theorem integral_norm_sq_fourier_kernel (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∫ ζ : Rd d, ‖𝓕 (fun x : Rd d => (κ x : ℂ)) ζ‖ ^ 2 = 1 := by
  have h := SchwartzMap.integral_norm_sq_fourier (kernelSchwartz hκ)
  rw [coe_fourier_kernelSchwartz hκ] at h
  rw [h, ← hκ.integral_sq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [kernelSchwartz_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- `|S^{d-1}| = d · vol(B(0,1)) = 2π^{d/2}/Γ(d/2)`. -/
theorem sphereArea_eq (hd : 0 < d) :
    (d : ℝ) * (volume (Metric.ball (0 : Rd d) 1)).toReal =
      2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [EuclideanSpace.volume_ball (Fin d) 0 1, Fintype.card_fin, ENNReal.ofReal_one, one_pow,
    one_mul, ENNReal.toReal_ofReal (by positivity)]
  have hd2 : (d : ℝ) / 2 ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity)
  rw [Real.Gamma_add_one hd2]
  have hpi : Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  rw [hpi]
  field_simp

/-- **Polar coordinates** for `‖𝓕κ‖²` (radial): `∫ ‖𝓕κ‖² = |S^{d-1}| ∫_0^∞ t^{d-1} ‖𝓕κ(t e₁)‖² dt`. -/
theorem integral_norm_sq_fourier_kernel_polar (hd : 0 < d)
    (hrad : ∀ z w : Rd d, ‖z‖ = ‖w‖ → κ z = κ w) :
    ∫ ζ : Rd d, ‖𝓕 (fun x : Rd d => (κ x : ℂ)) ζ‖ ^ 2 =
      2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2) *
        ∫ t in Ioi (0 : ℝ), t ^ (d - 1) * ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e₁ d)‖ ^ 2 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [finrank_euclideanSpace_fin]; exact hd)
  have hfun : (fun ζ : Rd d => ‖𝓕 (fun x : Rd d => (κ x : ℂ)) ζ‖ ^ 2) =
      fun ζ => (fun t : ℝ => ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e₁ d)‖ ^ 2) ‖ζ‖ := by
    funext ζ
    rw [fourier_kernel_eq_norm_smul_e₁ hd hrad ζ]
  have hpolar := integral_fun_norm_addHaar (volume : Measure (Rd d))
    (fun t : ℝ => ‖𝓕 (fun x : Rd d => (κ x : ℂ)) (t • e₁ d)‖ ^ 2)
  rw [hfun]
  refine hpolar.trans ?_
  rw [finrank_euclideanSpace_fin, ← sphereArea_eq hd, nsmul_eq_mul, smul_eq_mul,
    Measure.real_def]
  simp only [smul_eq_mul]
  ring

end Kernel

/-! ### Entire extension along lines and the vanishing theorem -/

section Line

variable {g : Rd d → ℂ}

/-- `fourierLine g ζ₀ v z = ∫ e^{-2πi(⟨x,ζ₀⟩ + z⟨x,v⟩)} g(x) dx`, an entire function of `z ∈ ℂ` that
equals `𝓕g(ζ₀ + t v)` at real `z = t`. -/
def fourierLine (g : Rd d → ℂ) (ζ₀ v : Rd d) (z : ℂ) : ℂ :=
  ∫ x : Rd d, Complex.exp (-(2 * Real.pi * Complex.I) * ((⟪x, ζ₀⟫ : ℂ) + z * (⟪x, v⟫ : ℂ))) * g x

theorem fourierLine_ofReal (g : Rd d → ℂ) (ζ₀ v : Rd d) (t : ℝ) :
    fourierLine g ζ₀ v t = 𝓕 g (ζ₀ + t • v) := by
  rw [fourierLine, Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, inner_add_right, real_inner_smul_right]
  congr 1
  push_cast
  ring_nf

/-- `fourierLine g ζ₀ v` is entire when `g` is continuous with compact support. -/
theorem differentiable_fourierLine (hg : Continuous g) (hgc : HasCompactSupport g)
    (ζ₀ v : Rd d) : Differentiable ℂ (fourierLine g ζ₀ v) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport g ⊆ Metric.closedBall 0 R :=
    hgc.isCompact.isBounded.subset_closedBall 0
  intro z₀
  -- integrand, its `z`-derivative, and a uniform bound on `ball z₀ 1`
  set c : ℂ := -(2 * Real.pi * Complex.I) with hc
  set F : ℂ → Rd d → ℂ := fun z x =>
    Complex.exp (c * ((⟪x, ζ₀⟫ : ℂ) + z * (⟪x, v⟫ : ℂ))) * g x with hF
  set F' : ℂ → Rd d → ℂ := fun z x =>
    Complex.exp (c * ((⟪x, ζ₀⟫ : ℂ) + z * (⟪x, v⟫ : ℂ))) * (c * (⟪x, v⟫ : ℂ)) * g x with hF'
  set B : ℝ := 2 * Real.pi * (|R| * ‖v‖) *
    Real.exp (2 * Real.pi * (|R| * ‖ζ₀‖ + (‖z₀‖ + 1) * (|R| * ‖v‖))) with hB
  have hcont : ∀ z : ℂ, Continuous (F z) := fun z => by
    simp only [hF]
    fun_prop
  have hcont' : ∀ z : ℂ, Continuous (F' z) := fun z => by
    simp only [hF']
    fun_prop
  have hgint : Integrable (fun x => ‖g x‖) := (hg.integrable_of_hasCompactSupport hgc).norm
  have hnormc : ‖c‖ = 2 * Real.pi := by
    rw [hc, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_two,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  -- the key pointwise bound
  have hbound : ∀ x : Rd d, ∀ z ∈ Metric.ball z₀ 1, ‖F' z x‖ ≤ B * ‖g x‖ := by
    intro x z hz
    by_cases hgx : g x = 0
    · simp [hF', hgx]
    have hxR : ‖x‖ ≤ |R| := by
      have := hR (subset_tsupport g hgx)
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self R)
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z z₀
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    have ha : |⟪x, ζ₀⟫| ≤ |R| * ‖ζ₀‖ :=
      (abs_real_inner_le_norm x ζ₀).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg _))
    have hb : |⟪x, v⟫| ≤ |R| * ‖v‖ :=
      (abs_real_inner_le_norm x v).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg _))
    have hexp : ‖Complex.exp (c * ((⟪x, ζ₀⟫ : ℂ) + z * (⟪x, v⟫ : ℂ)))‖ ≤
        Real.exp (2 * Real.pi * (|R| * ‖ζ₀‖ + (‖z₀‖ + 1) * (|R| * ‖v‖))) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
      rw [norm_mul, hnormc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ‖(⟪x, ζ₀⟫ : ℂ) + z * (⟪x, v⟫ : ℂ)‖ ≤ ‖(⟪x, ζ₀⟫ : ℂ)‖ + ‖z‖ * ‖(⟪x, v⟫ : ℂ)‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul]
        _ ≤ |R| * ‖ζ₀‖ + (‖z₀‖ + 1) * (|R| * ‖v‖) := by
            rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
            gcongr
    have hcb : ‖c * (⟪x, v⟫ : ℂ)‖ ≤ 2 * Real.pi * (|R| * ‖v‖) := by
      rw [norm_mul, hnormc, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    show ‖Complex.exp (c * ((⟪x, ζ₀⟫ : ℂ) + z * (⟪x, v⟫ : ℂ))) * (c * (⟪x, v⟫ : ℂ)) * g x‖ ≤
      B * ‖g x‖
    rw [norm_mul, norm_mul]
    calc ‖Complex.exp (c * ((⟪x, ζ₀⟫ : ℂ) + z * (⟪x, v⟫ : ℂ)))‖ * ‖c * (⟪x, v⟫ : ℂ)‖ * ‖g x‖
        ≤ Real.exp (2 * Real.pi * (|R| * ‖ζ₀‖ + (‖z₀‖ + 1) * (|R| * ‖v‖))) *
            (2 * Real.pi * (|R| * ‖v‖)) * ‖g x‖ := by gcongr
      _ = B * ‖g x‖ := by rw [hB]; ring
  have hderiv : ∀ x : Rd d, ∀ z : ℂ, HasDerivAt (fun w => F w x) (F' z x) z := by
    intro x z
    have h1 : HasDerivAt (fun w : ℂ => c * ((⟪x, ζ₀⟫ : ℂ) + w * (⟪x, v⟫ : ℂ)))
        (c * (⟪x, v⟫ : ℂ)) z := by
      have := ((hasDerivAt_id z).mul_const (⟪x, v⟫ : ℂ)).const_add (⟪x, ζ₀⟫ : ℂ) |>.const_mul c
      simpa using this
    exact (h1.cexp).mul_const (g x)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := F) (F' := F') (x₀ := z₀) (bound := fun x => B * ‖g x‖)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable)
    ((hcont z₀).integrable_of_hasCompactSupport (hgc.mul_left))
    (hcont' z₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x z hz => hbound x z hz)
    (hgint.const_mul B)
    (Filter.Eventually.of_forall fun x z _ => hderiv x z)
  exact hmain.2.differentiableAt

/-- If `𝓕g(ζ₀ + t v) = 0` for all `t > T`, then `𝓕g(ζ₀) = 0` (identity theorem). -/
theorem fourier_eq_zero_of_forall_gt (hg : Continuous g) (hgc : HasCompactSupport g)
    (ζ₀ v : Rd d) {T : ℝ} (h : ∀ t : ℝ, T < t → 𝓕 g (ζ₀ + t • v) = 0) : 𝓕 g ζ₀ = 0 := by
  have han : AnalyticOnNhd ℂ (fourierLine g ζ₀ v) univ := fun z _ =>
    (differentiable_fourierLine hg hgc ζ₀ v).analyticAt z
  -- the real points `T + 1 + 1/(n+1)` accumulate at `T + 1`
  set u : ℕ → ℂ := fun n => ((T + 1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hu
  have hlim : Tendsto u atTop (𝓝[≠] ((T + 1 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
    · have h1 : Tendsto (fun n : ℕ => T + 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (T + 1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h1
      exact (Complex.continuous_ofReal.tendsto _).comp h1
    · simp only [hu, mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] ((T + 1 : ℝ) : ℂ), fourierLine g ζ₀ v z = 0 := by
    refine hlim.frequently (Filter.Frequently.of_forall fun n => ?_)
    simp only [hu]
    rw [fourierLine_ofReal]
    apply h
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ _) hfreq (mem_univ ((0 : ℝ) : ℂ))
  rw [fourierLine_ofReal, zero_smul, add_zero] at hzero
  exact hzero

/-- **A compactly supported continuous function whose Fourier transform vanishes outside a ball has
vanishing Fourier transform** (MA5 A2.3, analyticity form). -/
theorem fourier_eq_zero_of_far (hd : 0 < d) (hg : Continuous g) (hgc : HasCompactSupport g)
    {ρ : ℝ} (h : ∀ ζ : Rd d, ρ < ‖ζ‖ → 𝓕 g ζ = 0) (ζ₀ : Rd d) : 𝓕 g ζ₀ = 0 := by
  refine fourier_eq_zero_of_forall_gt hg hgc ζ₀ (e₁ d) (T := ρ + ‖ζ₀‖) fun t ht => h _ ?_
  have hnt : ‖t • e₁ d‖ = |t| := by
    rw [norm_smul, HigherDimLFPP.norm_e₁ hd, mul_one, Real.norm_eq_abs]
  have htri : ‖t • e₁ d‖ ≤ ‖ζ₀ + t • e₁ d‖ + ‖ζ₀‖ := by
    calc ‖t • e₁ d‖ = ‖(ζ₀ + t • e₁ d) - ζ₀‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖ζ₀ + t • e₁ d‖ + ‖ζ₀‖ := norm_sub_le _ _
  rw [hnt] at htri
  linarith [le_abs_self t]

end Line

end HigherDimLQGMetric
