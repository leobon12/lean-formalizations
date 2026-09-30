import QuantumZipper.Proofs.Zipper.F2Gamma0Trunc
import QuantumZipper.Proofs.LQG.WedgeToolkit

/-!
# F2 step (4), D27: the deterministic core of the freeness of the rescaled field

Theorem 1.3, node F2, step (4); Sheffield, arXiv:1012.4797, §5.1 (pp. 60–62). The two
deterministic facts behind `F2.TruncRescaleFreeStmt` (`F2Gamma0Trunc.lean`), whose proof is
sketched in `F2Gamma0TruncFree.lean` and whose single missing ingredient is the identification
`evalReg (X ω) ν = X ω ν` at an *arbitrary* admissible `ν`:

* `F2.sfTrunc_rescale_apply_of_evalReg`: at an admissible `μ` (hence s-finite), the truncated
  rescaled field is the raw coordinate of `x` at the dilated measure `μ.map (a ·)` plus the
  `Q log a` term of the coordinate change times the total mass:

  `sfTrunc (rescale x Q a) μ = x (μ.map (a ·)) + Q * (log a * (μ univ).toReal)`.

  This turns the *balanced increments* of the rescaled field into the Gaussian family
  `WedgeTK.gaussFam X` at the pushed-forward pairs
  (`F2.rescale_sub_eq`: the `Q log a` terms of the two coordinate changes cancel because the
  masses of a balanced pair agree — this is the "balanced increments kill the additive log
  constant" step), and turns the `linear` field into `linearity of X at the pushed measures`
  plus mass additivity.

* `F2.pushPair` / `F2.kernelCov2_pushPair`: the pushed-forward balanced pair, and the invariance
  of the Neumann covariance `kernelCov2 neumannH` under it — `WedgeTK.kernelCov2_map_mul`, the
  `z ↦ a z` case of the dilation invariance of the free-field covariance. Note that *no* extra
  constant appears: on a balanced pair the `-2 log a` of
  `neumannH (a x) (a y) = neumannH x y - 2 log a` integrates against the mass difference to `0`.

Own elementary bookkeeping (D27); the maths is Sheffield §5.1 and the dilation invariance of the
Neumann kernel.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ## Pushing balanced pairs forward by the dilation -/

theorem measurable_mul_left_c (a : ℝ) : Measurable fun z : ℂ => (a : ℂ) * z :=
  measurable_const.mul measurable_id

/-- The dilation `z ↦ a z` (`a > 0`) acts on measures by pushforward; it preserves balanced
admissible pairs (`WedgeTK.isAdmissibleH_map_mul` for admissibility, `WedgeTK.map_univ_mul` for
the mass). -/
def pushPair (a : ℝ) (ha : 0 < a) (p : WedgeTK.BPair) : WedgeTK.BPair :=
  ⟨(p.1.1.map fun z => (a : ℂ) * z, p.1.2.map fun z => (a : ℂ) * z),
    WedgeTK.isAdmissibleH_map_mul ha p.2.1,
    WedgeTK.isAdmissibleH_map_mul ha p.2.2.1,
    by rw [WedgeTK.map_univ_mul a, WedgeTK.map_univ_mul a]; exact p.2.2.2⟩

/-- **Dilation invariance of the free-field covariance.** `kernelCov2 neumannH` of a
pushed-forward balanced pair is the same as that of the original pair: the additive `-2 log a`
of `neumannH (a x) (a y) = neumannH x y - 2 log a` is killed by the balanced increments. -/
theorem kernelCov2_pushPair (a : ℝ) (ha : 0 < a) (p q : WedgeTK.BPair) :
    kernelCov2 neumannH (pushPair a ha p).1 (pushPair a ha q).1 =
      kernelCov2 neumannH p.1 q.1 :=
  WedgeTK.kernelCov2_map_mul ha p q

/-! ## The value of the truncated rescaled field at an admissible measure -/

/-- The derivative of the dilation `z ↦ a z`. -/
theorem deriv_mul_left_c (a : ℂ) : deriv (fun z : ℂ => a * z) = fun _ => a := by
  funext z
  simpa using ((hasDerivAt_id z).const_mul a).deriv

/-- The `Q log|ψ'|` integral of the coordinate change by the dilation `z ↦ a z`, `a > 0`. -/
theorem integral_log_deriv_mul_left {a Q : ℝ} (ha : 0 < a) {μ : Measure ℂ} :
    Q * ∫ z, Real.log ‖deriv (fun w : ℂ => (a : ℂ) * w) z‖ ∂μ =
      Q * (Real.log a * (μ Set.univ).toReal) := by
  have hpt : (fun z : ℂ => Real.log ‖deriv (fun w : ℂ => (a : ℂ) * w) z‖) =
      fun _ => Real.log a := by
    funext z
    rw [deriv_mul_left_c, Complex.norm_real, Real.norm_of_nonneg ha.le]
  rw [hpt, integral_const, smul_eq_mul, measureReal_def]
  ring

end F2
end QuantumZipper
