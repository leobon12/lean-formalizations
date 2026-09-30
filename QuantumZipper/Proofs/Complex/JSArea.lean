import QuantumZipper.Proofs.Analysis.Pushforward
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# EXT-JS nodes A2 and A1: area formula and Cauchy–area estimate

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 ("Cauchy–area estimate") and §3 (nodes A1, A2).

* A2 `volume_image_eq_lintegral_normSq_deriv`: for `h` holomorphic and injective on an open
  set `U`, `volume (h '' U) = ∫⁻ z in U, ‖h' z‖ₑ ^ 2` (area formula; mathlib's
  `lintegral_abs_det_fderiv_eq_addHaar_image` with Jacobian `‖h'‖²`,
  `QuantumZipper.abs_det_fderiv_eq_normSq`).
* `lintegral_ball_enorm_sq_ge`: disk sub-mean-value inequality
  `π ρ² ‖g w‖² ≤ ∫⁻_{B(w,ρ)} ‖g‖²` for `g` holomorphic on `B(w,ρ)` (mean value property of the
  holomorphic `g²` on circles, `DiffContOnCl.circleAverage`, then polar coordinates).
  Both are standard (change of variables with real Jacobian `|h'|²`; mean value property).
  In the blueprint they replace the Sobolev-norm input of Jones–Smirnov, *Removability theorems
  for Sobolev functions and quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2, estimate (12)
  (`literature/JonesSmirnov_Removability_ArkMat2000.pdf`).
* A1 `enorm_deriv_sq_le_volume_image` and `norm_deriv_le_sqrt_volume_image`,
  `ediam_image_sq_le_of_convex`, `ediam_image_rect_sq_le` (box diameter bound).

Deviation from the blueprint's A1 shape: the real-valued bound
`‖deriv h w‖ ≤ √((volume (h '' ball w ρ)).toReal) / (√π * ρ)` is false when the image has
infinite area (then `toReal = 0`); it is stated here with the hypothesis
`volume (h '' ball w ρ) ≠ ⊤`, and the main form is the `ℝ≥0∞` inequality, which needs none.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Real

namespace QuantumZipper.JS

/-! ### A2: the area formula -/

/-- **A2 (area formula).** For `h` holomorphic and injective on an open set `U`,
`volume (h '' U) = ∫⁻ z in U, ‖h' z‖ₑ ^ 2`. -/
theorem volume_image_eq_lintegral_normSq_deriv {U : Set ℂ} {h : ℂ → ℂ} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) (hinj : InjOn h U) :
    volume (h '' U) = ∫⁻ z in U, ‖deriv h z‖ₑ ^ 2 := by
  have hd : ∀ z ∈ U, HasFDerivWithinAt h (fderiv ℝ h z) U z := fun z hz =>
    ((hh.differentiableAt (hU.mem_nhds hz)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hU.measurableSet hd hinj]
  refine setLIntegral_congr_fun hU.measurableSet (fun z hz => ?_)
  rw [abs_det_fderiv_eq_normSq (hh.differentiableAt (hU.mem_nhds hz)),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-! ### Disk sub-mean-value inequality -/

private theorem circleMap_eq_add_polarCoord_symm (w : ℂ) (r θ : ℝ) :
    circleMap w r θ = w + Complex.polarCoord.symm (r, θ) := by
  simp [circleMap, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- Circle step: for `g` holomorphic on `B(w,ρ)` and `0 < r < ρ`,
`2π ‖g w‖² ≤ ∫⁻_{(-π,π)} ‖g(w + r e^{iθ})‖² dθ`. -/
private theorem circle_step {g : ℂ → ℂ} {w : ℂ} {ρ r : ℝ}
    (hg : DifferentiableOn ℂ g (ball w ρ)) (hr : 0 < r) (hrρ : r < ρ) :
    ENNReal.ofReal (2 * π) * ‖g w‖ₑ ^ 2 ≤
      ∫⁻ θ in Ioo (-π) π, ‖g (w + Complex.polarCoord.symm (r, θ))‖ₑ ^ 2 := by
  set G : ℂ → ℂ := fun z => g z ^ 2 with hGdef
  have hG : DifferentiableOn ℂ G (ball w ρ) := hg.pow 2
  have hcl : closedBall w |r| ⊆ ball w ρ := by
    rw [abs_of_pos hr]; exact closedBall_subset_ball hrρ
  have hmean : Real.circleAverage G w r = G w := (hG.diffContOnCl_ball hcl).circleAverage
  have hper : Function.Periodic (fun θ => G (circleMap w r θ)) (2 * π) :=
    fun θ => by simp [periodic_circleMap w r θ]
  have hint : ∫ θ in (0:ℝ)..2 * π, G (circleMap w r θ) =
      ∫ θ in Ioc (-π) π, G (circleMap w r θ) := by
    have := hper.intervalIntegral_add_eq (-π) 0
    rw [zero_add, show -π + 2 * π = π by ring] at this
    rw [← this, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hGw : G w = (2 * π)⁻¹ • ∫ θ in Ioc (-π) π, G (circleMap w r θ) := by
    rw [← hmean, Real.circleAverage_def, hint]
  have hkey : ‖g w‖ₑ ^ 2 ≤ ENNReal.ofReal ((2 * π)⁻¹) *
      ∫⁻ θ in Ioc (-π) π, ‖g (w + Complex.polarCoord.symm (r, θ))‖ₑ ^ 2 := by
    have h1 : ‖g w‖ₑ ^ 2 = ‖G w‖ₑ := by simp [hGdef, enorm_pow]
    rw [h1, hGw, enorm_smul]
    have h2 : ‖((2 * π)⁻¹ : ℝ)‖ₑ = ENNReal.ofReal ((2 * π)⁻¹) := by
      rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
    rw [h2]
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr (fun θ => ?_)
    simp [hGdef, enorm_pow, circleMap_eq_add_polarCoord_symm]
  have hIoo : ∫⁻ θ in Ioc (-π) π, ‖g (w + Complex.polarCoord.symm (r, θ))‖ₑ ^ 2 =
      ∫⁻ θ in Ioo (-π) π, ‖g (w + Complex.polarCoord.symm (r, θ))‖ₑ ^ 2 :=
    setLIntegral_congr Ioo_ae_eq_Ioc.symm
  rw [← hIoo]
  calc ENNReal.ofReal (2 * π) * ‖g w‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 * π) * (ENNReal.ofReal ((2 * π)⁻¹) *
          ∫⁻ θ in Ioc (-π) π, ‖g (w + Complex.polarCoord.symm (r, θ))‖ₑ ^ 2) := by gcongr
    _ = ∫⁻ θ in Ioc (-π) π, ‖g (w + Complex.polarCoord.symm (r, θ))‖ₑ ^ 2 := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- **Disk sub-mean-value inequality.** For `g` holomorphic on `B(w,ρ)`,
`π ρ² ‖g w‖² ≤ ∫⁻_{B(w,ρ)} ‖g‖²`. -/
theorem lintegral_ball_enorm_sq_ge {g : ℂ → ℂ} {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (ball w ρ)) :
    ENNReal.ofReal (π * ρ ^ 2) * ‖g w‖ₑ ^ 2 ≤ ∫⁻ z in ball w ρ, ‖g z‖ₑ ^ 2 := by
  set F : ℂ → ℝ≥0∞ := (ball (0 : ℂ) ρ).indicator (fun z => ‖g (w + z)‖ₑ ^ 2) with hFdef
  -- translate to the ball at `0`
  have htr : ∫⁻ z in ball w ρ, ‖g z‖ₑ ^ 2 = ∫⁻ z, F z := by
    rw [← lintegral_indicator measurableSet_ball,
      ← lintegral_add_left_eq_self _ w]
    refine lintegral_congr (fun z => ?_)
    simp only [hFdef, Set.indicator, mem_ball, dist_eq_norm]
    simp
  rw [htr, ← Complex.lintegral_comp_polarCoord_symm]
  set A : Set (ℝ × ℝ) := Ioo 0 ρ ×ˢ Ioo (-π) π with hA
  have hAsub : A ⊆ polarCoord.target := by
    intro p hp
    show p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π
    exact ⟨hp.1.1, hp.2⟩
  have hAmeas : MeasurableSet A := measurableSet_Ioo.prod measurableSet_Ioo
  set Φ : ℝ × ℝ → ℝ := fun p => p.1 * ‖g (w + Complex.polarCoord.symm p)‖ ^ 2 with hΦ
  have hmemball : ∀ p ∈ A, w + Complex.polarCoord.symm p ∈ ball w ρ := by
    rintro p ⟨hp1, -⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_polarCoord_symm,
      abs_of_pos hp1.1]
    exact hp1.2
  have heqA : ∀ p ∈ A, ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p) =
      ENNReal.ofReal (Φ p) := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1.1
    have hin : Complex.polarCoord.symm p ∈ ball (0 : ℂ) ρ := by
      have := hmemball p hp
      rwa [mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_zero_right, ← mem_ball] at this
    simp only [hFdef, Set.indicator_of_mem hin, hΦ, smul_eq_mul]
    rw [ENNReal.ofReal_mul hp1.le, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hcont : ContinuousOn Φ A := by
    have hgc : ContinuousOn g (ball w ρ) := hg.continuousOn
    have hpol : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
      simp only [Complex.polarCoord_symm_apply]; fun_prop
    have hc2 : ContinuousOn (fun p : ℝ × ℝ => g (w + Complex.polarCoord.symm p)) A :=
      hgc.comp (continuous_const.add hpol).continuousOn
        (fun p hp => hmemball p hp)
    exact continuous_fst.continuousOn.mul (hc2.norm.pow 2)
  have hmeasΦ : AEMeasurable (fun p => ENNReal.ofReal (Φ p)) (volume.restrict A) :=
    (hcont.aemeasurable hAmeas).ennreal_ofReal
  have hradial : ∫⁻ r in Ioo 0 ρ, ENNReal.ofReal r = ENNReal.ofReal (ρ ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le, integral_id]
      ring
    · exact (continuous_id.integrableOn_Icc (a := 0) (b := ρ)).mono_set Ioo_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr using hr.1.le
  calc ENNReal.ofReal (π * ρ ^ 2) * ‖g w‖ₑ ^ 2
      = (∫⁻ r in Ioo 0 ρ, ENNReal.ofReal r) * (ENNReal.ofReal (2 * π) * ‖g w‖ₑ ^ 2) := by
        rw [hradial, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring
    _ = ∫⁻ r in Ioo 0 ρ, ENNReal.ofReal r * (ENNReal.ofReal (2 * π) * ‖g w‖ₑ ^ 2) :=
        (lintegral_mul_const _ ENNReal.measurable_ofReal).symm
    _ ≤ ∫⁻ r in Ioo 0 ρ, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (Φ (r, θ)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2
          (Eventually.of_forall fun r hr => ?_))
        have hr0 : 0 ≤ r := hr.1.le
        calc ENNReal.ofReal r * (ENNReal.ofReal (2 * π) * ‖g w‖ₑ ^ 2)
            ≤ ENNReal.ofReal r *
                ∫⁻ θ in Ioo (-π) π, ‖g (w + Complex.polarCoord.symm (r, θ))‖ₑ ^ 2 := by
              gcongr; exact circle_step hg hr.1 hr.2
          _ = ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (Φ (r, θ)) := by
              rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              refine lintegral_congr (fun θ => ?_)
              simp only [hΦ]
              rw [ENNReal.ofReal_mul hr0, ENNReal.ofReal_pow (norm_nonneg _),
                ofReal_norm]
    _ = ∫⁻ p in A, ENNReal.ofReal (Φ p) := by
        rw [hA, Measure.volume_eq_prod, ← Measure.prod_restrict,
          lintegral_prod _ (by rw [Measure.prod_restrict]; exact hmeasΦ)]
    _ = ∫⁻ p in A, ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p) :=
        (setLIntegral_congr_fun hAmeas heqA).symm
    _ ≤ ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • F (Complex.polarCoord.symm p) :=
        lintegral_mono_set hAsub

/-! ### A1: Cauchy–area estimate -/

/-- **A1 (Cauchy–area estimate, `ℝ≥0∞` form).** For `h` holomorphic and injective on `B(w,ρ)`,
`π ρ² ‖h'(w)‖² ≤ area h(B(w,ρ))`. -/
theorem enorm_deriv_sq_le_volume_image {h : ℂ → ℂ} {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hh : DifferentiableOn ℂ h (ball w ρ)) (hinj : InjOn h (ball w ρ)) :
    ENNReal.ofReal (π * ρ ^ 2) * ‖deriv h w‖ₑ ^ 2 ≤ volume (h '' ball w ρ) := by
  rw [volume_image_eq_lintegral_normSq_deriv isOpen_ball hh hinj]
  exact lintegral_ball_enorm_sq_ge hρ (hh.deriv isOpen_ball)

/-- **A1 (diameter bound on a convex set).** Let `h` be holomorphic and injective on an open
set `U`, `Q` convex with `B(w,ρ) ⊆ U` for every `w ∈ Q`. Then
`π ρ² diam(h(Q))² ≤ diam(Q)² · area h(U)`. -/
theorem ediam_image_sq_le_of_convex {U Q : Set ℂ} {h : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) (hinj : InjOn h U) (hQ : Convex ℝ Q)
    (hball : ∀ w ∈ Q, ball w ρ ⊆ U) :
    ENNReal.ofReal (π * ρ ^ 2) * ediam (h '' Q) ^ 2 ≤ ediam Q ^ 2 * volume (h '' U) := by
  set V := volume (h '' U) with hV
  by_cases h0 : ediam Q = 0
  · have hs : (h '' Q).Subsingleton := (ediam_eq_zero_iff.1 h0).image h
    rw [ediam_eq_zero_iff.2 hs]; simp
  by_cases htop : V = ⊤
  · rw [htop, ENNReal.mul_top (pow_ne_zero 2 h0)]; exact le_top
  -- pointwise derivative bound
  set t : ℝ≥0 := Real.toNNReal (π * ρ ^ 2) with ht
  have htpos : 0 < t := Real.toNNReal_pos.2 (by positivity)
  set K : ℝ≥0 := NNReal.sqrt (V.toNNReal / t) with hK
  have hbound : ∀ w ∈ Q, ‖deriv h w‖₊ ≤ K := by
    intro w hw
    have h1 := enorm_deriv_sq_le_volume_image hρ (hh.mono (hball w hw))
      (hinj.mono (hball w hw))
    have h2 : (t : ℝ≥0∞) * (‖deriv h w‖₊ : ℝ≥0∞) ^ 2 ≤ (V.toNNReal : ℝ≥0∞) := by
      rw [ENNReal.coe_toNNReal htop]
      exact h1.trans (measure_mono (image_mono (hball w hw)))
    have h3 : t * ‖deriv h w‖₊ ^ 2 ≤ V.toNNReal := by exact_mod_cast h2
    rw [hK, NNReal.le_sqrt_iff_sq_le, le_div_iff₀ htpos, mul_comm]
    exact h3
  have hlip : LipschitzOnWith K h Q :=
    hQ.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => hh.differentiableAt (hU.mem_nhds (hball x hx (mem_ball_self hρ)))) hbound
  have hdiam : ediam (h '' Q) ≤ K * ediam Q := by
    refine ediam_le ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (hlip hx hy).trans (by gcongr; exact edist_le_ediam_of_mem hx hy)
  have hK2 : (t : ℝ≥0∞) * (K : ℝ≥0∞) ^ 2 = V := by
    rw [← ENNReal.coe_pow, hK, NNReal.sq_sqrt, ← ENNReal.coe_mul, mul_div_cancel₀ _ htpos.ne',
      ENNReal.coe_toNNReal htop]
  calc ENNReal.ofReal (π * ρ ^ 2) * ediam (h '' Q) ^ 2
      ≤ (t : ℝ≥0∞) * ((K : ℝ≥0∞) * ediam Q) ^ 2 := by
        rw [ENNReal.ofReal]; gcongr
    _ = ediam Q ^ 2 * V := by rw [mul_pow, ← mul_assoc, hK2, mul_comm]

/-- **A1 (box diameter bound).** For a closed rectangle `Q = [a,b] × [c,d]` and its open
`ρ`-enlargement `U = (a-ρ, b+ρ) × (c-ρ, d+ρ)`, if `h` is holomorphic and injective on `U` then
`π ρ² diam(h(Q))² ≤ ((b-a)² + (d-c)²) · area h(U)`. For the blueprint's top box / big box
(`b - a = ℓ`, `d - c = ℓ/2`, `ρ = ℓ/4`) this gives `diam(h(Q))² ≤ (20/π) · area h(Q*)`. -/
theorem ediam_image_rect_sq_le {a b c d ρ : ℝ} {h : ℂ → ℂ} (hρ : 0 < ρ)
    (hh : DifferentiableOn ℂ h (Ioo (a - ρ) (b + ρ) ×ℂ Ioo (c - ρ) (d + ρ)))
    (hinj : InjOn h (Ioo (a - ρ) (b + ρ) ×ℂ Ioo (c - ρ) (d + ρ))) :
    ENNReal.ofReal (π * ρ ^ 2) * ediam (h '' (Icc a b ×ℂ Icc c d)) ^ 2 ≤
      ENNReal.ofReal ((b - a) ^ 2 + (d - c) ^ 2) *
        volume (h '' (Ioo (a - ρ) (b + ρ) ×ℂ Ioo (c - ρ) (d + ρ))) := by
  have hU : IsOpen (Ioo (a - ρ) (b + ρ) ×ℂ Ioo (c - ρ) (d + ρ)) :=
    isOpen_Ioo.reProdIm isOpen_Ioo
  have hQ : Convex ℝ (Icc a b ×ℂ Icc c d) :=
    ((convex_Icc a b).linear_preimage Complex.reLm).inter
      ((convex_Icc c d).linear_preimage Complex.imLm)
  have hball : ∀ w ∈ Icc a b ×ℂ Icc c d,
      ball w ρ ⊆ Ioo (a - ρ) (b + ρ) ×ℂ Ioo (c - ρ) (d + ρ) := by
    intro w hw z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre := abs_lt.1 ((Complex.abs_re_le_norm (z - w)).trans_lt hz)
    have him := abs_lt.1 ((Complex.abs_im_le_norm (z - w)).trans_lt hz)
    rw [Complex.sub_re] at hre
    rw [Complex.sub_im] at him
    obtain ⟨⟨hw1, hw2⟩, ⟨hw3, hw4⟩⟩ := hw
    exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, ⟨by linarith [him.1], by linarith [him.2]⟩⟩
  have hdQ : ediam (Icc a b ×ℂ Icc c d) ^ 2 ≤ ENNReal.ofReal ((b - a) ^ 2 + (d - c) ^ 2) := by
    have hle : ediam (Icc a b ×ℂ Icc c d) ≤ ENNReal.ofReal (√((b - a) ^ 2 + (d - c) ^ 2)) := by
      refine ediam_le fun x hx y hy => ?_
      rw [edist_dist, Complex.dist_eq_re_im]
      refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
      obtain ⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩ := hx
      obtain ⟨⟨hy1, hy2⟩, ⟨hy3, hy4⟩⟩ := hy
      have e1 : (x.re - y.re) ^ 2 ≤ (b - a) ^ 2 :=
        sq_le_sq' (by linarith) (by linarith)
      have e2 : (x.im - y.im) ^ 2 ≤ (d - c) ^ 2 :=
        sq_le_sq' (by linarith) (by linarith)
      linarith
    calc ediam (Icc a b ×ℂ Icc c d) ^ 2
        ≤ ENNReal.ofReal (√((b - a) ^ 2 + (d - c) ^ 2)) ^ 2 := by gcongr
      _ = ENNReal.ofReal ((b - a) ^ 2 + (d - c) ^ 2) := by
        rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  exact (ediam_image_sq_le_of_convex hρ hU hh hinj hQ hball).trans (by gcongr)

end QuantumZipper.JS
