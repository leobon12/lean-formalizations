import QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import QuantumZipper.Proofs.Thm11.ForwardClock
import QuantumZipper.Proofs.Thm11.ForwardTamed
import QuantumZipper.SLE.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# RS S1-0: the one-point state of the forward Loewner flow and its radial generator

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §5, node S1-0 (see also
`blueprint/GIRSANOV_BLUEPRINT.md` §1).

For the sharp one-point estimate S1 the paper works with the **one-point state**

`(Z_t, L_t) = (f_t(z), log Υ_t) ∈ ℂ × ℝ`,  `Z_t = fwdMap W t z`,  `L_t = fwdLogCR W t z`,

where `f_t` is the centered forward Loewner flow (`fwdMap`) and `Υ_t` is the conformal radius at
the tip as seen from `z` (`fwdLogCR = log Im f_t − Re logDerivFwd`). While `Im f_t z ≥ c` the tamed
forward flow FD-4 agrees with `f_t`, so the state solves the additive-noise equation

`dZ = 2/Z dt − √κ dB`,  `dL = −4 (Im Z)²/‖Z‖⁴ dt`,

with (tamed) drift `opDrift c` and noise `opNoise κ`; `L` is driven by the drift only (the noise is
real and moves `Z` in the real direction). In the radial clock `ds = κ (Im Z)²/‖Z‖⁴ dt` the angle
`Θ = arg Z` performs `dΘ = (1 − 4/κ) cot Θ ds + dW` and `dL = −(4/κ) ds`, so the generator of a
test function `φ(L, arg Z)` factorizes as

`dynkinGen (opDrift c) (opNoise κ) (φ(·, arg ·)) (Z,L) = κ (Im Z)²/‖Z‖⁴ · radGen κ φ L (arg Z)`,

with `radGen κ φ L θ = −(4/κ) ∂_L φ + ½ ∂²_θ φ + (1 − 4/κ) (cos θ / sin θ) ∂_θ φ` the generator of
the *radial* (clock-time) motion. This is the content of `dynkinGen_opDrift_angle` (node S1-0).

The file has three blocks:

1. `Complex.arg` calculus on the open upper half plane: the local formula
   `arg z = π/2 − arctan (z.re/z.im)`, smoothness, and the first and second derivatives of
   `s ↦ arg (z + s v)`, `v ∈ ℂ`: `Im(v/z)` and `−Im((v/z)²)`. These are the real and imaginary
   parts of the derivatives of `s ↦ log (z + s v)` (`arg = Im ∘ log`) and are computed here from
   the arctan formula, since mathlib has no differentiability lemma for `Complex.arg`.
2. The one-point state `opDrift c`, `opNoise κ`, the radial generator `radGen`, and the generator
   identity `dynkinGen_opDrift_angle`.
3. The identification of the tamed state with the true one-point state (`opState_eq_tamed`),
   together with continuity of the tamed drift (`continuous_opDrift`).

Literature: **LZ** = G. Lawler, W. Zhou, *SLE curves and natural parametrization*, Ann. Probab. 41
(2013), arXiv:1006.4936: §2.1–2.1.2 (p. 12), Prop. 2.3 (p. 16), Lemma 2.2 (p. 14) — these page
numbers are LZ's, not Lawler's book's, as an earlier version of this docstring claimed (AUDIT8
R8-5); G. Lawler, B. Werness, arXiv:1011.3551, §2.3; G. Lawler, Park City notes
(`literature/0712.3256.pdf`), §3–4; A. Kemppainen (5.10)–(5.11), pp. 83–84. The proof route is the project's own (Itô-free) one, as in RS BP1
(`Proofs/RS/BasePointGen.lean`): `dynkinGen` is evaluated through its line-derivative reduction
(`FrozenMart.fderiv_apply_eq_deriv_line`, `FrozenMart.iteratedFDeriv_two_eq_deriv_deriv_line`),
i.e. by a second-order chain rule along the drift and the noise direction. Block 1 is an own
elementary proof.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace RS

open FrozenMart FwdClock FwdHolo

/-! ## 1. `Complex.arg` on the upper half plane -/

/-- On the open upper half plane, `arg z = π/2 − arctan (z.re/z.im)`. -/
theorem arg_eq_pi_div_two_sub_arctan {z : ℂ} (hz : 0 < z.im) :
    Complex.arg z = Real.pi / 2 - Real.arctan (z.re / z.im) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hx : z.re / ‖z‖ ∈ Set.Ioo (-(1 : ℝ)) 1 := by
    have h2 : z.re ^ 2 < ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [sq_pos_of_pos hz]
    have h3 : |z.re| < ‖z‖ := by
      have h4 : |z.re| < |‖z‖| := sq_lt_sq.mp h2
      rwa [abs_of_nonneg (norm_nonneg z)] at h4
    rw [abs_lt] at h3
    constructor
    · rw [lt_div_iff₀ hnorm]; linarith [h3.1]
    · rw [div_lt_iff₀ hnorm]; linarith [h3.2]
  have hsq : Real.sqrt (1 - (z.re / ‖z‖) ^ 2) = z.im / ‖z‖ := by
    have h1 : 1 - (z.re / ‖z‖) ^ 2 = (z.im / ‖z‖) ^ 2 := by
      rw [div_pow, div_pow, Complex.sq_norm, Complex.normSq_apply]
      field_simp
      ring
    rw [h1, Real.sqrt_sq (by positivity)]
  have harcsin : Real.arcsin (z.re / ‖z‖) = Real.arctan (z.re / z.im) := by
    rw [Real.arcsin_eq_arctan hx, hsq]
    field_simp
  rw [Complex.arg_of_im_pos hz, Real.arccos_eq_pi_div_two_sub_arcsin, harcsin]

/-- `Complex.arg` is smooth at every point of the open upper half plane. -/
theorem contDiffAt_arg {z : ℂ} (hz : 0 < z.im) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n Complex.arg z := by
  have hzmem : z.im ∈ Set.Ioi (0 : ℝ) := hz
  have hevim : ∀ᶠ x : ℂ in 𝓝 z, x.im ∈ Set.Ioi (0 : ℝ) :=
    Complex.continuous_im.continuousAt.eventually (isOpen_Ioi.mem_nhds hzmem)
  have hev : Complex.arg =ᶠ[𝓝 z] fun x : ℂ => Real.pi / 2 - Real.arctan (x.re / x.im) := by
    filter_upwards [hevim] with x hx
    exact arg_eq_pi_div_two_sub_arctan hx
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have h1 : ContDiffAt ℝ n (fun x : ℂ => x.re / x.im) z :=
    (Complex.reCLM.contDiff.contDiffAt).div (Complex.imCLM.contDiff.contDiffAt)
      (by simpa using hz.ne')
  exact contDiffAt_const.sub (Real.contDiff_arctan.contDiffAt.comp z h1)

/-- **First derivative of `arg` along a line.** For `0 < z.im` the curve `s ↦ arg (z + s•v)` has
derivative `Im(v/z)` at `0` (`arg = Im ∘ log`). -/
theorem hasDerivAt_arg_line {z : ℂ} (hz : 0 < z.im) (v : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.arg (z + s • v)) ((v / z).im) 0 := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hcont : ContinuousAt (fun s : ℝ => (z + s • v).im) 0 :=
    (Complex.continuous_im.continuousAt.comp (hasDerivAt_line z v 0).continuousAt)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < (z + s • v).im :=
    hcont.eventually (isOpen_Ioi.mem_nhds (by simpa using hz))
  have hre : HasDerivAt (fun s : ℝ => (z + s • v).re) v.re 0 := by
    have hfun : (fun s : ℝ => (z + s • v).re) = fun s => z.re + s * v.re := by
      funext s; simp [Complex.add_re]
    rw [hfun]
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const v.re).const_add z.re
  have him : HasDerivAt (fun s : ℝ => (z + s • v).im) v.im 0 := by
    have hfun : (fun s : ℝ => (z + s • v).im) = fun s => z.im + s * v.im := by
      funext s; simp [Complex.add_im]
    rw [hfun]
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const v.im).const_add z.im
  have hdiv : HasDerivAt (fun s : ℝ => (z + s • v).re / (z + s • v).im)
      ((v.re * z.im - z.re * v.im) / z.im ^ 2) 0 := by
    have h := hre.div him (by simpa using hz.ne')
    refine h.congr_deriv ?_
    simp only [zero_smul, add_zero]
  have harctan : HasDerivAt (fun s : ℝ => Real.arctan ((z + s • v).re / (z + s • v).im))
      (1 / (1 + (z.re / z.im) ^ 2) * ((v.re * z.im - z.re * v.im) / z.im ^ 2)) 0 := by
    refine hdiv.arctan.congr_deriv ?_
    simp only [zero_smul, add_zero]
  have hmain : HasDerivAt
      (fun s : ℝ => Real.pi / 2 - Real.arctan ((z + s • v).re / (z + s • v).im))
      (0 - 1 / (1 + (z.re / z.im) ^ 2) * ((v.re * z.im - z.re * v.im) / z.im ^ 2)) 0 :=
    (hasDerivAt_const (0 : ℝ) (Real.pi / 2)).sub harctan
  have hev' : (fun s : ℝ => Complex.arg (z + s • v)) =ᶠ[𝓝 0]
      fun s : ℝ => Real.pi / 2 - Real.arctan ((z + s • v).re / (z + s • v).im) := by
    filter_upwards [hev] with s hs
    exact arg_eq_pi_div_two_sub_arctan hs
  refine (hmain.congr_of_eventuallyEq hev').congr_deriv ?_
  rw [Complex.div_im, Complex.normSq_apply]
  have hn : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz0).ne'
  have hden : 1 + (z.re / z.im) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **Second derivative of `arg` along a line.** `d²/ds² arg (z + s v)|₀ = −Im((v/z)²)`. -/
theorem deriv_deriv_arg_line {z : ℂ} (hz : 0 < z.im) (v : ℂ) :
    deriv (deriv (fun s : ℝ => Complex.arg (z + s • v))) 0 = -(((v / z) ^ 2).im) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hcont : ContinuousAt (fun s : ℝ => (z + s • v).im) 0 :=
    (Complex.continuous_im.continuousAt.comp (hasDerivAt_line z v 0).continuousAt)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < (z + s • v).im :=
    hcont.eventually (isOpen_Ioi.mem_nhds (by simpa using hz))
  have hfun : deriv (fun t : ℝ => Complex.arg (z + t • v)) =ᶠ[𝓝 0]
      fun s : ℝ => (v / (z + s • v)).im := by
    filter_upwards [hev] with s hs
    have h₁ := hasDerivAt_arg_line hs v
    have h₂ : HasDerivAt (fun t : ℝ => t - s) 1 s := (hasDerivAt_id s).sub_const s
    have h₃ : HasDerivAt (fun t : ℝ => Complex.arg ((z + s • v) + (t - s) • v))
        ((v / (z + s • v)).im * 1) s :=
      HasDerivAt.comp_of_eq (h := fun t : ℝ => t - s) (x := s) h₁ h₂ (by simp)
    rw [mul_one] at h₃
    have heq : (fun t : ℝ => Complex.arg ((z + s • v) + (t - s) • v))
        = fun t : ℝ => Complex.arg (z + t • v) := by
      funext t; congr 1; rw [sub_smul]; abel
    rw [heq] at h₃
    exact h₃.deriv
  rw [hfun.deriv_eq]
  have hg : HasDerivAt (fun s : ℝ => v / (z + s • v)) (-(v ^ 2 / z ^ 2)) 0 := by
    have h := (hasDerivAt_const (0 : ℝ) v).div (hasDerivAt_line z v 0) (by simpa using hz0)
    refine h.congr_deriv ?_
    simp only [zero_smul, add_zero]
    field_simp
    ring
  have him : HasDerivAt (fun s : ℝ => (v / (z + s • v)).im) (-(v ^ 2 / z ^ 2)).im 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hg
    simpa only [Function.comp_def, Complex.imCLM_apply] using h
  rw [him.deriv, Complex.neg_im, div_pow]

/-! ## 2. The one-point state, the radial generator, and the generator identity -/

/-- The (tamed) drift of the one-point state `(Z, L)`:
`(2/proj c Z, −4 (Im proj c Z)²/‖proj c Z‖⁴)`. The taming is inactive while `Im Z ≥ c`
(`FwdHolo.proj_of_le`). -/
def opDrift (c : ℝ) (x : ℂ × ℝ) : ℂ × ℝ :=
  (2 / proj c x.1, -4 * (proj c x.1).im ^ 2 / ‖proj c x.1‖ ^ 4)

/-- The noise vector of the one-point state: `(−√κ, 0)`. -/
def opNoise (κ : ℝ) : ℂ × ℝ := ((-Real.sqrt κ : ℝ), 0)

/-- **The radial generator.** In the radial clock `ds = κ (Im Z)²/‖Z‖⁴ dt` the state is `(L, Θ)`
with `dΘ = (1 − 4/κ) cot Θ ds + dW`, `dL = −(4/κ) ds`; this is the generator of that motion,
acting on `φ(L, θ)`. -/
def radGen (κ : ℝ) (φ : ℝ → ℝ → ℝ) (L θ : ℝ) : ℝ :=
  -(4 / κ) * deriv (fun L' => φ L' θ) L + (1 / 2) * deriv (deriv (φ L)) θ
    + (1 - 4 / κ) * (Real.cos θ / Real.sin θ) * deriv (φ L) θ

/-! ### Elementary algebra of the clock change -/

theorem im_div_sq {Z : ℂ} (hZ : Z ≠ 0) (a : ℝ) :
    (((a : ℂ)) / Z ^ 2).im = -2 * a * Z.re * Z.im / ‖Z‖ ^ 4 := by
  have hn : ‖Z‖ ^ 4 ≠ 0 := by
    rw [show ‖Z‖ ^ 4 = (‖Z‖ ^ 2) ^ 2 by ring]
    exact pow_ne_zero 2 (pow_ne_zero 2 (norm_ne_zero_iff.mpr hZ))
  have hsq : (Z ^ 2).re = Z.re ^ 2 - Z.im ^ 2 := by rw [pow_two, Complex.mul_re]; ring
  have him : (Z ^ 2).im = 2 * Z.re * Z.im := by rw [pow_two, Complex.mul_im]; ring
  have hns : Complex.normSq (Z ^ 2) = ‖Z‖ ^ 4 := by
    rw [map_pow, ← Complex.sq_norm]; ring
  rw [Complex.div_im, hsq, him, hns]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, zero_sub]
  field_simp

theorem im_two_div_div {Z : ℂ} (hZ : Z ≠ 0) :
    ((2 : ℂ) / Z / Z).im = -4 * Z.re * Z.im / ‖Z‖ ^ 4 := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h2, div_div, ← pow_two, im_div_sq hZ (a := 2)]
  ring

theorem im_neg_sqrt_div {Z : ℂ} (hZ : Z ≠ 0) (κ : ℝ) :
    (((-Real.sqrt κ : ℝ) : ℂ) / Z).im = Real.sqrt κ * Z.im / ‖Z‖ ^ 2 := by
  have hn : ‖Z‖ ≠ 0 := norm_ne_zero_iff.mpr hZ
  rw [Complex.div_im, ← Complex.sq_norm]
  simp only [Complex.ofReal_neg, Complex.neg_re, Complex.neg_im, Complex.ofReal_im,
    Complex.ofReal_re, zero_mul, neg_zero]
  field_simp
  ring

theorem im_neg_sqrt_div_sq {Z : ℂ} (hZ : Z ≠ 0) {κ : ℝ} (hκ : 0 ≤ κ) :
    ((((-Real.sqrt κ : ℝ) : ℂ) / Z).im) ^ 2 = κ * Z.im ^ 2 / ‖Z‖ ^ 4 := by
  have hn : ‖Z‖ ≠ 0 := norm_ne_zero_iff.mpr hZ
  rw [im_neg_sqrt_div hZ κ, div_pow, mul_pow, Real.sq_sqrt hκ]
  field_simp

theorem neg_im_sq_neg_sqrt_div {Z : ℂ} (hZ : Z ≠ 0) {κ : ℝ} (hκ : 0 ≤ κ) :
    -((((-Real.sqrt κ : ℝ) : ℂ) / Z) ^ 2).im = 2 * κ * Z.re * Z.im / ‖Z‖ ^ 4 := by
  have e : (((-Real.sqrt κ : ℝ) : ℂ) / Z) ^ 2 = ((κ : ℝ) : ℂ) / Z ^ 2 := by
    rw [div_pow, Complex.ofReal_neg, neg_sq, ← Complex.ofReal_pow, Real.sq_sqrt hκ]
  rw [e, im_div_sq hZ (a := κ)]
  ring

theorem cos_arg_div_sin_arg {Z : ℂ} (hZ : 0 < Z.im) :
    Real.cos (Complex.arg Z) / Real.sin (Complex.arg Z) = Z.re / Z.im := by
  have h0 : Z ≠ 0 := fun h => by rw [h] at hZ; simp at hZ
  rw [Complex.cos_arg h0, Complex.sin_arg]
  have him : Z.im ≠ 0 := hZ.ne'
  field_simp

/-! ### The second-order chain rule -/

/-- One-dimensional chain rule, in the form of an eventual equality of the derivative. -/
theorem deriv_comp_eventuallyEq {ψ h : ℝ → ℝ} (hψ : ContDiffAt ℝ 2 ψ (h 0))
    (hh : ContDiffAt ℝ 2 h 0) :
    deriv (fun r : ℝ => ψ (h r)) =ᶠ[𝓝 0] fun r => deriv ψ (h r) * deriv h r := by
  have hhd : DifferentiableAt ℝ h 0 := hh.differentiableAt (by norm_num)
  have hevψ : ∀ᶠ r in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 ψ (h r) :=
    hhd.continuousAt.tendsto.eventually (hψ.eventually (by simp))
  filter_upwards [hevψ, hh.eventually (by simp)] with r h1 h2
  have hcomp : HasDerivAt (fun r : ℝ => ψ (h r)) (deriv ψ (h r) * deriv h r) r :=
    HasDerivAt.comp (h₂ := ψ) (h := h) (x := r) (h1.differentiableAt (by norm_num)).hasDerivAt
      (h2.differentiableAt (by norm_num)).hasDerivAt
  exact hcomp.deriv

/-- **One-dimensional second-order chain rule at `0`:**
`(ψ ∘ h)''(0) = ψ''(h 0) h'(0)² + ψ'(h 0) h''(0)`. -/
theorem deriv_deriv_comp_zero {ψ h : ℝ → ℝ} (hψ : ContDiffAt ℝ 2 ψ (h 0))
    (hh : ContDiffAt ℝ 2 h 0) :
    deriv (deriv (fun r : ℝ => ψ (h r))) 0
      = deriv (deriv ψ) (h 0) * deriv h 0 ^ 2 + deriv ψ (h 0) * deriv (deriv h) 0 := by
  have hhd : DifferentiableAt ℝ h 0 := hh.differentiableAt (by norm_num)
  have hdψ : DifferentiableAt ℝ (deriv ψ) (h 0) := by
    have h := (hψ.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    simpa [derivWithin_univ] using h
  have hdh : DifferentiableAt ℝ (deriv h) 0 := by
    have h := (hh.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    simpa [derivWithin_univ] using h
  have hev := deriv_comp_eventuallyEq hψ hh
  have hA : HasDerivAt (fun r : ℝ => deriv ψ (h r)) (deriv (deriv ψ) (h 0) * deriv h 0) 0 :=
    HasDerivAt.comp (h₂ := deriv ψ) (h := h) (x := (0 : ℝ)) hdψ.hasDerivAt hhd.hasDerivAt
  have hC : HasDerivAt (fun r : ℝ => deriv ψ (h r) * deriv h r)
      (deriv (deriv ψ) (h 0) * deriv h 0 * deriv h 0 + deriv ψ (h 0) * deriv (deriv h) 0) 0 :=
    (hA.mul hdh.hasDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => by simp only [Pi.mul_apply])
  rw [hev.deriv_eq, hC.deriv]
  ring

/-! ### The first-order chain rule for `φ(·, arg ·)` -/

/-- `fderiv` of a two-variable function at `(L, θ)`, split into its two partial derivatives. -/
theorem fderiv_uncurry_apply {φ : ℝ → ℝ → ℝ} {L θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry φ) (L, θ)) (a b : ℝ) :
    fderiv ℝ (Function.uncurry φ) (L, θ) (a, b)
      = deriv (fun L' => φ L' θ) L * a + deriv (φ L) θ * b := by
  have hLc : HasDerivAt (fun L' : ℝ => (L', θ)) ((1 : ℝ), (0 : ℝ)) L :=
    (hasDerivAt_id L).prodMk (hasDerivAt_const L θ)
  have hRc : HasDerivAt (fun θ' : ℝ => (L, θ')) ((0 : ℝ), (1 : ℝ)) θ :=
    (hasDerivAt_const θ L).prodMk (hasDerivAt_id θ)
  have h1 : HasDerivAt (fun L' : ℝ => Function.uncurry φ (L', θ))
      (fderiv ℝ (Function.uncurry φ) (L, θ) (1, 0)) L := by
    have hc := hasFDerivAt_iff_hasDerivAt.mp (h.hasFDerivAt.comp L hLc.hasFDerivAt)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, Function.comp_def] using hc
  have h2 : HasDerivAt (fun θ' : ℝ => Function.uncurry φ (L, θ'))
      (fderiv ℝ (Function.uncurry φ) (L, θ) (0, 1)) θ := by
    have hc := hasFDerivAt_iff_hasDerivAt.mp (h.hasFDerivAt.comp θ hRc.hasFDerivAt)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, Function.comp_def] using hc
  have e1 : fderiv ℝ (Function.uncurry φ) (L, θ) (1, 0) = deriv (fun L' => φ L' θ) L := by
    rw [← h1.deriv]
    rfl
  have e2 : fderiv ℝ (Function.uncurry φ) (L, θ) (0, 1) = deriv (φ L) θ := by
    rw [← h2.deriv]
    rfl
  have hsplit : (a, b) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, map_smul, e1, e2]
  simp only [smul_eq_mul]
  ring

/-- **First-order derivative of `φ(·, arg ·)` along the drift of the one-point state.** -/
theorem hasDerivAt_opAngle_line {φ : ℝ → ℝ → ℝ} {Z : ℂ} {L : ℝ} {q : ℝ} {v : ℂ}
    (hZ : 0 < Z.im) (hΦ : DifferentiableAt ℝ (Function.uncurry φ) (L, Complex.arg Z)) :
    HasDerivAt (fun s : ℝ => φ (L + s * q) (Complex.arg (Z + s • v)))
      (deriv (fun L' => φ L' (Complex.arg Z)) L * q
        + deriv (φ L) (Complex.arg Z) * ((v / Z).im)) 0 := by
  have hγ : HasDerivAt (fun s : ℝ => (L + s * q, Complex.arg (Z + s • v)))
      (q, (v / Z).im) 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).mul_const q).const_add L).prodMk
      (hasDerivAt_arg_line hZ v)
  have hpt : (L + (0 : ℝ) * q, Complex.arg (Z + (0 : ℝ) • v)) = (L, Complex.arg Z) := by simp
  have hΦ' : HasFDerivAt (Function.uncurry φ)
      (fderiv ℝ (Function.uncurry φ) (L, Complex.arg Z))
      (L + (0 : ℝ) * q, Complex.arg (Z + (0 : ℝ) • v)) := by
    rw [hpt]; exact hΦ.hasFDerivAt
  have hcomp := hΦ'.comp_hasDerivAt 0
    (f := fun s : ℝ => (L + s * q, Complex.arg (Z + s • v))) hγ
  refine (hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => rfl)).congr_deriv ?_
  exact fderiv_uncurry_apply hΦ q ((v / Z).im)

/-- **Second-order derivative of `ψ ∘ arg` along the noise direction `v`.** -/
theorem deriv_deriv_opAngle_noise {ψ : ℝ → ℝ} {Z : ℂ} (v : ℂ) (hZ : 0 < Z.im)
    (hψ : ContDiffAt ℝ 2 ψ (Complex.arg Z)) :
    deriv (deriv (fun s : ℝ => ψ (Complex.arg (Z + s • v)))) 0
      = deriv (deriv ψ) (Complex.arg Z) * ((v / Z).im) ^ 2
        + deriv ψ (Complex.arg Z) * (-(((v / Z) ^ 2).im)) := by
  have hh : ContDiffAt ℝ 2 (fun s : ℝ => Complex.arg (Z + s • v)) 0 := by
    have hlin : ContDiffAt ℝ 2 (fun s : ℝ => Z + s • v) 0 := by fun_prop
    have harg : ContDiffAt ℝ 2 Complex.arg (Z + (0 : ℝ) • v) := by
      simpa using contDiffAt_arg (n := 2) hZ
    simpa [Function.comp_def] using harg.comp 0 hlin
  have h0 : (fun s : ℝ => Complex.arg (Z + s • v)) 0 = Complex.arg Z := by simp
  have hψ' : ContDiffAt ℝ 2 ψ ((fun s : ℝ => Complex.arg (Z + s • v)) 0) := by
    rw [h0]; exact hψ
  rw [deriv_deriv_comp_zero hψ' hh]
  simp only [h0]
  rw [(hasDerivAt_arg_line hZ v).deriv, deriv_deriv_arg_line hZ v]

/-! ### S1-0: the radial generator identity -/

/-- **S1-0: the one-point radial generator.** For `κ > 0`, `c > 0`, `φ` whose two-variable
version is `C³` on `univ ×ˢ (0,π)`, and `Im Z ≥ c > 0`:

`L (φ(·, arg ·)) (Z,L) = κ (Im Z)²/‖Z‖⁴ · radGen κ φ L (arg Z)`,

where `L` is the Dynkin generator of `dU = opDrift c U dt + opNoise κ dB`
(`QuantumZipper.dynkinGen`). This is the factorization of the one-point generator into the radial
clock `ds = κ (Im Z)²/‖Z‖⁴ dt` (LZ §2.1, p. 12: the time change `∂_tσ = |Z|⁴/(Im Z)²` above (18);
LW §2.3, p. 10: the `P`-dynamics `dΘ = (1 − 4/κ) cot Θ ds + dW`; Kemppainen (5.10)–(5.11),
pp. 83–84). Note that LZ (18) itself, p. 12, is the `2a cot θ̂` dynamics under the *weighted*
measure `P*` (AUDIT8 R8-5), not the `P`-dynamics used here; `4/κ = 2a` with `a = 2/κ`. -/
theorem dynkinGen_opDrift_angle (hκ : 0 < κ) (hc : 0 < c) {φ : ℝ → ℝ → ℝ}
    (hφ : ContDiffOn ℝ 3 (Function.uncurry φ) (univ ×ˢ Ioo 0 Real.pi)) {Z : ℂ} {L : ℝ}
    (hZ : c ≤ Z.im) :
    dynkinGen (opDrift c) (opNoise κ) (fun x : ℂ × ℝ => φ x.2 (Complex.arg x.1)) (Z, L)
      = κ * Z.im ^ 2 / ‖Z‖ ^ 4 * radGen κ φ L (Complex.arg Z) := by
  have hZi : 0 < Z.im := hc.trans_le hZ
  have hZ0 : Z ≠ 0 := fun h => by rw [h] at hZi; simp at hZi
  have hargpos : 0 < Complex.arg Z := by
    refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hZi.le) (fun h => ?_)
    exact hZi.ne' (Complex.arg_eq_zero_iff.mp h.symm).2
  have harglt : Complex.arg Z < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hZi.ne')
  have hmem : (L, Complex.arg Z) ∈ univ ×ˢ Ioo (0 : ℝ) Real.pi := ⟨trivial, hargpos, harglt⟩
  have hΦ : ContDiffAt ℝ 3 (Function.uncurry φ) (L, Complex.arg Z) :=
    hφ.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hmem)
  have hF : ContDiffAt ℝ 2 (fun x : ℂ × ℝ => φ x.2 (Complex.arg x.1)) (Z, L) := by
    have hΨ : ContDiffAt ℝ 2 (fun x : ℂ × ℝ => (x.2, Complex.arg x.1)) (Z, L) :=
      contDiffAt_snd.prodMk ((contDiffAt_arg hZi).comp (Z, L) contDiffAt_fst)
    have h := (hΦ.of_le (m := 2) (by norm_num)).comp (Z, L) hΨ
    simpa [Function.comp_def, Function.uncurry] using h
  have hψ : ContDiffAt ℝ 2 (φ L) (Complex.arg Z) := by
    have hsec : ContDiffAt ℝ 3 (fun θ' : ℝ => (L, θ')) (Complex.arg Z) :=
      contDiffAt_const.prodMk contDiffAt_id
    have h := (hΦ.comp (Complex.arg Z) hsec).of_le (m := 2) (by norm_num)
    simpa [Function.comp_def, Function.uncurry] using h
  have hproj : proj c Z = Z := proj_of_le hZ
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hF.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line hF]
  have e1 : (fun s : ℝ => (fun x : ℂ × ℝ => φ x.2 (Complex.arg x.1))
        ((Z, L) + s • opDrift c (Z, L)))
      = fun s : ℝ =>
          φ (L + s * (-4 * Z.im ^ 2 / ‖Z‖ ^ 4)) (Complex.arg (Z + s • (2 / Z))) := by
    funext s
    simp only [opDrift, hproj, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul]
  have e2 : (fun s : ℝ => (fun x : ℂ × ℝ => φ x.2 (Complex.arg x.1))
        ((Z, L) + s • opNoise κ))
      = fun s : ℝ => φ L (Complex.arg (Z + s • (((-Real.sqrt κ : ℝ) : ℂ)))) := by
    funext s
    simp only [opNoise, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_zero, add_zero]
  rw [e1, e2, (hasDerivAt_opAngle_line (φ := φ) hZi (hΦ.differentiableAt (by norm_num))).deriv,
    deriv_deriv_opAngle_noise (ψ := φ L) (((-Real.sqrt κ : ℝ) : ℂ)) hZi hψ]
  rw [radGen, im_two_div_div hZ0, im_neg_sqrt_div_sq hZ0 hκ.le, neg_im_sq_neg_sqrt_div hZ0 hκ.le,
    cos_arg_div_sin_arg hZi]
  have hZim : Z.im ≠ 0 := hZi.ne'
  have hn : ‖Z‖ ≠ 0 := norm_ne_zero_iff.mpr hZ0
  have hκ0 : κ ≠ 0 := hκ.ne'
  field_simp
  ring

/-! ## 3. The tamed one-point state -/

/-- The `L`-field of the tamed one-point state: `−4 (Im proj c Z)²/‖proj c Z‖⁴`, which is
`(opDrift c x).2` (independent of the `L` coordinate). -/
def tamedLField (c : ℝ) (w : ℂ) : ℝ := -4 * (proj c w).im ^ 2 / ‖proj c w‖ ^ 4

theorem continuous_tamedLField {c : ℝ} (hc : 0 < c) : Continuous (tamedLField c) := by
  unfold tamedLField
  exact (continuous_const.mul ((Complex.continuous_im.comp (continuous_proj_tamed c)).pow 2)).div
    ((continuous_proj_tamed c).norm.pow 4)
    (fun w => pow_ne_zero 4 (norm_ne_zero_iff.mpr (proj_ne_zero_tamed hc w)))

theorem continuous_opDrift {c : ℝ} (hc : 0 < c) : Continuous (opDrift c) := by
  unfold opDrift
  refine (continuous_const.div ((continuous_proj_tamed c).comp continuous_fst)
    (fun x : ℂ × ℝ => proj_ne_zero_tamed hc x.1)).prodMk ?_
  exact (continuous_const.mul ((Complex.continuous_im.comp
    ((continuous_proj_tamed c).comp continuous_fst)).pow 2)).div
    (((continuous_proj_tamed c).comp continuous_fst).norm.pow 4)
    (fun x : ℂ × ℝ => pow_ne_zero 4 (norm_ne_zero_iff.mpr (proj_ne_zero_tamed hc x.1)))

/-- The tamed `log Υ` coordinate: the solution of `dL = tamedLField c Z̃ dt` started at `log (Im z)`.
While `Im f_s z ≥ c` this is `fwdLogCR` (`opState_eq_tamed`). For the SLE driver `W = √κ B` one
has `W 0 = 0` and the initial value is literally `log (Im z)`; note that
`Im (z − W 0) = Im z` in any case, so no hypothesis on `W 0` is needed. -/
def tamedLogCR (W : ℝ → ℝ) (c : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  Real.log z.im + ∫ s in (0 : ℝ)..t, tamedLField c (tamedZ W c z s)

/-- **S1-0: the tamed state is the true one-point state.** While `Im f_s z ≥ c` for `s ∈ [0,t]`,
the tamed state `(tamedZ, tamedLogCR)` agrees with `(fwdMap, fwdLogCR)`. -/
theorem opState_eq_tamed (hW : Continuous W) {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.im)
    {t : ℝ} (ht : 0 ≤ t) (him : ∀ s ∈ Icc (0 : ℝ) t, c ≤ (fwdMap W s z).im) :
    tamedZ W c z t = fwdMap W t z ∧ tamedLogCR W c z t = fwdLogCR W t z := by
  have hft : c ≤ (fwdMap W t z).im := him t ⟨ht, le_rfl⟩
  have halive : ∃ u, IsForwardSol W z t u := by
    by_contra h
    rw [fwdMap, dif_neg h] at hft
    simp only [Complex.zero_im] at hft
    linarith
  have hZeq : ∀ s ∈ Icc (0 : ℝ) t, tamedZ W c z s = fwdMap W s z :=
    tamedZ_eq_fwdMap hW hc ht hz halive him
  refine ⟨hZeq t ⟨ht, le_rfl⟩, ?_⟩
  have hderiv : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun r => fwdLogCR W r z)
      (tamedLField c (tamedZ W c z s)) (Icc 0 t) s := by
    intro s hs
    have h1 := hasDerivWithinAt_fwdLogCR hW hz halive hs
    rw [← hZeq s hs] at h1
    refine h1.congr_deriv ?_
    have hts : c ≤ (tamedZ W c z s).im := by rw [hZeq s hs]; exact him s hs
    rw [tamedLField, proj_of_le hts]
  have hcont : ContinuousOn (fun s => tamedLField c (tamedZ W c z s)) (Icc 0 t) :=
    (continuous_tamedLField hc).comp_continuousOn (continuousOn_tamedZ hW hc ht z)
  have hint : IntervalIntegrable (fun s => tamedLField c (tamedZ W c z s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]; exact hcont
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (fun s hs => (hderiv s hs).continuousWithinAt)
    (fun s hs => (hderiv s (Ioo_subset_Icc_self hs)).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)) hint
  have h0 : fwdLogCR W 0 z = Real.log z.im := by
    have hsol0 : ∃ u, IsForwardSol W z 0 u := by
      refine exists_isForwardSol_of_not_mem_fwdHull (le_refl 0) (show z ∈ H from hz) ?_
      intro hmem
      have hpos := swallowTime_pos hW hz
      rw [fwdHull] at hmem
      exact absurd hmem.2 (by rw [ENNReal.ofReal_zero]; exact not_le.mpr hpos)
    obtain ⟨u0, hu0⟩ := hsol0
    have hf0 : fwdMap W 0 z = z - (W 0 : ℂ) := by
      rw [fwdMap_eq hW hz hu0 ⟨le_rfl, le_rfl⟩, sol_zero hu0 le_rfl]
    have hL0 : logDerivFwd W 0 z = 0 := by
      rw [logDerivFwd, intervalIntegral.integral_same, neg_zero]
    rw [fwdLogCR, hf0, hL0, Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_re,
      sub_zero]
  rw [tamedLogCR, key, h0]
  ring

end RS
end QuantumZipper
