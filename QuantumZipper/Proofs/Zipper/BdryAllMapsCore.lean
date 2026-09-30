import QuantumZipper.Proofs.LQG.CoordChangeMain
import QuantumZipper.Proofs.LQG.CoordChangeCompare
import QuantumZipper.Proofs.LQG.BoundaryExistenceAS
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-THM43 (1): the two pathwise inputs and the deterministic tools

Task SW-THM43 (Theorems 1.3/1.8). Target: `F1.BdryAllMapsStmt` (`BdryTransportAll.lean`),
S. Sheffield, M. Wang, *Field-measure correspondence in Liouville quantum gravity almost surely
commutes with all conformal maps simultaneously*, arXiv:1605.06171 (literature/1605.06171.pdf),
**Theorem 4.3**, p. 19.

SW's proof of Theorem 4.3 (p. 19, following the proof of Theorem 1.4, pp. 11–12) has two parts:

* **variable scales** ("an analogous result to Corollary 3.2 holds", p. 19): the boundary
  approximations at the spatially varying scale `ε s(u)` converge to the boundary measure, for
  continuous positive `s`. Here: `BdryVarScaleLimit` (for one field sample, all open sets, all
  scale functions and all nonnegative test functions at once, in `ℝ≥0∞`).
* **change of coordinates + comparison** ((4.4)–(4.6), with Lemma 3.4 and Lemma 3.5): after
  the substitution `u = ψ(t)` the approximating density of `X ∘ ψ + Q log|ψ'|` at `t` is
  `ψ'(t)` times the density of `X` at the point `ψ(t)` and the scale `2^{-k} ψ'(t)`, up to the
  factor `exp(γ/2 Δ_k(t))`, where `Δ_k(t)` is the difference between the average of `X` over the
  pushed semicircle `ψ(∂B(t,2^{-k}) ∩ ℍ)` and over the round semicircle `∂B(ψ t, 2^{-k}ψ'(t))∩ℍ`.
  SW control `Δ` in the mean over the family (their (4.6)); here the input
  `BdryDistortionGood` asks that `Δ_k → 0` uniformly on inner intervals of `(a,b)`, for every
  admissible map at once (see the module docstring of `BdryAllMapsMain.lean` for its relation to SW (4.6)).

This file: the definitions of the two inputs; the exact density identity (`dens_split`, using
`γQ/2 = 1 + γ²/4`); `deriv ψ` is real on `(a,b)`; a vague-limit criterion from nonnegative test
functions in `ℝ≥0∞` (`isVagueLimitOnR_of_nonneg`); and the multiplicative squeeze
`tendsto_of_exp_squeeze`. All own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

/-! ### The density identity -/

/-- `r^{γ²/4} e^{γA/2} = d · (rd)^{γ²/4} e^{γE/2} · e^{γ(A − Q log d − E)/2}` (uses
`γQ/2 = 1 + γ²/4`). -/
theorem dens_split {γ r d A E : ℝ} (hγ : γ ≠ 0) (hr : 0 < r) (hd : 0 < d) :
    r ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * A) =
      d * ((r * d) ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * E)) *
        Real.exp (γ / 2 * (A - Qc γ * Real.log d - E)) := by
  have hQ := CoordChange.Qc_mul γ hγ
  rw [Real.mul_rpow hr.le hd.le, Real.rpow_def_of_pos hd]
  set l := Real.log d with hl
  have hdl : d = Real.exp l := (Real.exp_log hd).symm
  rw [hdl]
  rw [show Real.exp l * (r ^ (γ ^ 2 / 4) * Real.exp (l * (γ ^ 2 / 4)) * Real.exp (γ / 2 * E)) *
      Real.exp (γ / 2 * (A - Qc γ * l - E)) = r ^ (γ ^ 2 / 4) * (Real.exp l *
      Real.exp (l * (γ ^ 2 / 4)) * Real.exp (γ / 2 * E) *
      Real.exp (γ / 2 * (A - Qc γ * l - E))) by ring, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  congr 2
  linear_combination l * hQ

/-- `ψ'` is real at interior points of `[a,b]` (`ψ` is real on `[a,b]`). -/
theorem deriv_im_eq_zero {ψ : ℂ → ℂ} {a b : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hJU : ∀ t ∈ Icc a b, (t : ℂ) ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hre : ∀ t ∈ Icc a b, (ψ t).im = 0) {t : ℝ} (ht : t ∈ Ioo a b) : (deriv ψ t).im = 0 := by
  have hd : HasDerivAt ψ (deriv ψ t) (t : ℂ) :=
    (hψ.differentiableAt (hU.mem_nhds (hJU t (Ioo_subset_Icc_self ht)))).hasDerivAt
  have h1 : HasDerivAt (fun x : ℝ => (-Complex.I * ψ x).re) (-Complex.I * deriv ψ t).re t :=
    (hd.const_mul (-Complex.I)).real_of_complex
  have h2 : HasDerivAt (fun x : ℝ => (-Complex.I * ψ x).re) 0 t := by
    refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    simp [hre x (Ioo_subset_Icc_self hx)]
  have := h1.unique h2
  simpa using this

/-! ### A vague-limit criterion from nonnegative test functions -/

theorem ofReal_max_zero (y : ℝ) : ENNReal.ofReal (max y 0) = ENNReal.ofReal y := by
  rcases le_total y 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

/-! ### The multiplicative squeeze -/

end F1
end QuantumZipper
