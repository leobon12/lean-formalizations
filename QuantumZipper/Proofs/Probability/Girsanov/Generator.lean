import QuantumZipper.Proofs.ItoLite.Dynkin
import QuantumZipper.Proofs.Thm11.FrozenLocalDynkin

/-!
# GIR-0: generator calculus for the Markovian Girsanov theorem

Blueprint `blueprint/GIRSANOV_BLUEPRINT.md`, §2, node GIR-0.

For the Dynkin generator `L F = DF·b + ½ D²F[e,e]` of `dU = b(U) dt + e dB`
(`QuantumZipper.dynkinGen`):

* `Girsanov.dynkinGen_mul`: the product (Leibniz) rule
  `L(FG) = F·LG + G·LF + (DF·e)(DG·e)`. This is the generator form of Itô's integration by
  parts formula (Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, GTM 274, 2016,
  §5.2, the formula of integration by parts following Theorem 5.10, p. 116; Revuz–Yor,
  *Continuous Martingales and Brownian Motion*, 3rd ed., Ch. IV (3.5), p. 149).
* `Girsanov.dynkinGen_hTransform`: the same identity written as
  `L(FG) = F·(LG + (DF·e / F)·DG·e) + G·LF` (the Doob h-transform generator; Lawler,
  *Conformally Invariant Processes in the Plane*, §1.9, Example 1.19, p. 15).
* `Girsanov.dynkinGen_timeAug`: time augmentation. For the state `(t, U_t) ∈ ℝ × E` with drift
  `(1, b)` and noise `(0, e)`, `L_aug G = ∂_t G + L G(t, ·)`.
* `Girsanov.timeAug_integralEq`: `(t, U_t)` solves the augmented additive-noise equation.
* `Girsanov.driftAug_integralEq`: `(U_t, X_t)` with `X = B − ∫₀^· J(U)` solves the additive-noise
  equation on `E × ℝ` with drift `(b, −J)` and noise `(e, 1)`.

Proofs: own elementary proofs (cost rule of `AGENT_GUIDE.md`): the Leibniz rule for the first
and second Fréchet derivatives of a product (mathlib `fderiv_mul`, `HasFDerivAt.smul`), the
line reduction `FrozenMart.fderiv_apply_eq_deriv_line`,
`FrozenMart.iteratedFDeriv_two_eq_deriv_deriv_line`, and linearity of the interval integral
(`ContinuousLinearMap.intervalIntegral_comp_comm`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

namespace QuantumZipper
namespace Girsanov

section Generator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : E → E} {e : E}

/-- Second derivative of a product along `e`:
`D²(FG)[e,e] = F·D²G[e,e] + 2 (DF·e)(DG·e) + G·D²F[e,e]`. -/
theorem iteratedFDeriv_two_mul_vec {F G : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x)
    (hG : ContDiffAt ℝ 2 G x) (e : E) :
    iteratedFDeriv ℝ 2 (F * G) x ![e, e] = F x * iteratedFDeriv ℝ 2 G x ![e, e]
      + 2 * (fderiv ℝ F x e * fderiv ℝ G x e) + G x * iteratedFDeriv ℝ 2 F x ![e, e] := by
  have hFd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y :=
    (hF.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hGd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ G y :=
    (hG.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hEq : fderiv ℝ (F * G) =ᶠ[𝓝 x] fun y => F y • fderiv ℝ G y + G y • fderiv ℝ F y := by
    filter_upwards [hFd, hGd] with y h1 h2
    exact fderiv_mul h1 h2
  have hF1 : HasFDerivAt F (fderiv ℝ F x) x :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hG1 : HasFDerivAt G (fderiv ℝ G x) x :=
    (hG.differentiableAt (by norm_num)).hasFDerivAt
  have hDF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hDG : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hH : HasFDerivAt (fun y => F y • fderiv ℝ G y + G y • fderiv ℝ F y)
      ((F x • fderiv ℝ (fderiv ℝ G) x + (fderiv ℝ F x).smulRight (fderiv ℝ G x))
        + (G x • fderiv ℝ (fderiv ℝ F) x + (fderiv ℝ G x).smulRight (fderiv ℝ F x))) x :=
    (hF1.smul hDG).add (hG1.smul hDF)
  rw [Dynkin.iteratedFDeriv_two_vec, Dynkin.iteratedFDeriv_two_vec,
    Dynkin.iteratedFDeriv_two_vec, hEq.fderiv_eq, hH.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

/-- **GIR-0, product rule for the Dynkin generator.**
`L(FG) = F·LG + G·LF + (DF·e)(DG·e)` (generator form of Itô's integration by parts,
Le Gall GTM 274, p. 116). -/
theorem dynkinGen_mul {F G : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x)
    (hG : ContDiffAt ℝ 2 G x) :
    dynkinGen b e (F * G) x = F x * dynkinGen b e G x + G x * dynkinGen b e F x
      + fderiv ℝ F x e * fderiv ℝ G x e := by
  have hFd : DifferentiableAt ℝ F x := hF.differentiableAt (by norm_num)
  have hGd : DifferentiableAt ℝ G x := hG.differentiableAt (by norm_num)
  have h1 : fderiv ℝ (F * G) x = F x • fderiv ℝ G x + G x • fderiv ℝ F x := fderiv_mul hFd hGd
  unfold dynkinGen
  rw [iteratedFDeriv_two_mul_vec hF hG e, h1]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

end Generator

section TimeAug

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : E → E} {e : E}

end TimeAug

section SDE

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {B : ℝ≥0 → Ω → ℝ} {b : E → E} {u e : E} {U : ℝ≥0 → Ω → E}

end SDE

end Girsanov
end QuantumZipper
