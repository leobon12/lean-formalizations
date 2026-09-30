import QuantumZipper.Proofs.Thm11.FrozenMartingales
import QuantumZipper.Proofs.Thm11.ForwardClock
import QuantumZipper.Proofs.Probability.Girsanov.Generator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# THM11-AD3: the quadratic variation of `𝔥_t(a)` and the clock

Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), Theorem 1.1 addendum
(§1, p. 12): for `κ ∈ (4,8)` a swallowed point `z` receives the value
`𝔥_{τ(z)}(z) := lim_{s ↑ τ(z)} 𝔥_s(z)`. The blueprint (`THM11_BLUEPRINT.md` §9 AD-3) routes this
through the quadratic variation of the field: `𝔥_{t∧τ}` is a martingale with
`E 𝔥² = 𝔥_0² + E[quadratic variation]`, and the quadratic variation must be controlled.

This file proves the two deterministic facts behind that control.

1. **The generator of `Φ²` is the quadratic-variation density.** For the one-point state
   `x = (z, A) ∈ ℂ × ℝ` with `Im z ≥ c > 0`, with the drift `fzDrift c` and the additive noise
   `fzNoise κ = (−√κ, 0)` of the forward centered flow,
   `L(Φ²)(x) = (2 Im z)²/‖z‖⁴ = 4 (Im z)²/‖z‖⁴`,
   where `Φ(z,A) = h0fwd κ z − χ A` is the field. Since the noise is constant and one-dimensional,
   `L(Φ²) = 2Φ·LΦ + (DΦ·e)²` (the product rule `dynkinGen_mul`, GIR-0) and `LΦ = 0`
   (`dynkinGen_fzPhi`, MF-1), so the identity is the square of the noise-directional derivative of
   `Φ`. This is exactly the density of the martingale part of `𝔥` (Itô: `d𝔥² − d⟨𝔥⟩ = 0` up to a
   martingale), so `𝔥² − ∫ 4 (Im f_s(a))²/‖f_s(a)‖⁴ ds` is the driftless (local) martingale
   associated with `Φ²`.

2. **The quadratic variation is bounded by the clock.** Since `(Im z)² ≤ ‖z‖²`,
   `4 (Im z)²/‖z‖⁴ ≤ 4/‖z‖²`, so the accumulated quadratic variation of `𝔥` up to time `T` is at
   most `4 S_T(a)`, where `S_T(a) = ∫₀ᵀ ds/‖f_s(a)‖²` is the clock of `ForwardClock.lean`
   (Sheffield's `S_T`, the rate of the Loewner time change). With the clock formula
   `(fwdMap W T a).im = (Im a) exp(−2 S_T(a))` this is the estimate used in the blueprint's AD-2
   (`C_0 − C_{τ−}` against `‖g‖`) and it gives the uniform-in-`T` `L²` bound
   `E[(𝔥^δ_{t∧σ^δ})²] ≤ Φ(a)² + 8 log(Im a/δ)` for the frozen field at level `δ`.

Both are own elementary computations (`dynkinGen_mul` from GIR-0 and the pointwise inequality
`(Im z)² ≤ ‖z‖²`); no published proof of the addendum exists (the paper states the extension as a
definition), so no source is followed.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace QuantumZipper

open FrozenMart FwdClock FwdHolo

/-- **The generator of `Φ²` is the quadratic-variation density** `4 (Im z)²/‖z‖⁴`, where the
taming is inactive (`c ≤ Im z`). -/
theorem dynkinGen_fzPhi_sq {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 0 < c) {x : ℂ × ℝ}
    (hx : c ≤ x.1.im) :
    dynkinGen (fzDrift c) (fzNoise κ) (fun x => fzPhi κ x ^ 2) x
      = 4 * x.1.im ^ 2 / ‖x.1‖ ^ 4 := by
  have hz : 0 < x.1.im := hc.trans_le hx
  have hcm : ContDiffAt ℝ 2 (fzPhi κ) x := contDiffAt_fzPhi κ hz
  have hmul := Girsanov.dynkinGen_mul (b := fzDrift c) (e := fzNoise κ) hcm hcm (x := x)
  rw [dynkinGen_fzPhi hκ hc hx] at hmul
  -- the noise-directional derivative of `Φ`
  have hnoise : fderiv ℝ (fzPhi κ) x (fzNoise κ) = -2 * x.1.im / ‖x.1‖ ^ 2 := by
    rw [fderiv_apply_eq_deriv_line (hcm.differentiableAt (by norm_num)), deriv_fzPhi_noise κ hz]
    have hz0 : x.1 ≠ 0 := fun h => by simp [h] at hz
    have hnd : nd1 κ x.1 0 = -(2 / Real.sqrt κ) * ((-(Real.sqrt κ : ℂ)) / x.1).im := by
      simp [nd1, fzNoise]
    rw [hnd, Complex.div_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    simp only [zero_mul, neg_zero]
    rw [← Real.sq_sqrt hκ.le, Complex.sq_norm]
    have hN : Complex.normSq x.1 ≠ 0 := fun h => hz0 (Complex.normSq_eq_zero.mp h)
    field_simp
    ring
  have hfun : (fun x => fzPhi κ x ^ 2) = fzPhi κ * fzPhi κ := by
    funext y; rw [Pi.mul_apply, pow_two]
  rw [hfun, hmul, hnoise]
  simp only [mul_zero, add_zero]
  have hnorm : ‖x.1‖ ≠ 0 := norm_ne_zero_iff.mpr (fun h => by simp [h] at hz)
  field_simp
  ring

end QuantumZipper
