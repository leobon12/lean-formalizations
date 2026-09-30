import QuantumZipper.Proofs.LQG.WedgeCRegB4d
import QuantumZipper.Proofs.LQG.WedgeInfTotal
import QuantumZipper.Proofs.Zipper.E6Read

/-!
# WEDGE-CREG (1): raw = regularized at the full circle coordinates of the reference wedge

`E6.WedgeRefCircleRegStmt γ α`: almost surely, for every `i`, the raw value of the canonical
reference wedge field `refField γ X A ω = canonical γ W_ω` at the folded circle `fcFull i` equals
its regularized value `evalReg`.

Route (own elementary argument). `canonical γ W = rescale W Q b` with `b = scaleParam γ W`. For a
regular `W` (a.s., since `W` is a.s. good, `LogSingGood.wedgeRefGoodAS_holds`) and `b > 0`
(a.s., from `WedgeInf.wedgeInfiniteTotal` through `WedgeCan4.ae_wedge_canonical_spec_of_inputs`),
both sides equal `F(b·fold(c), b r) + Q log b` (`RegClosure.rescale_fc_eq`,
`IsRegularWith.rescale'`, `RegClosure.foldH_mul_pos`), at **every** folded circle `fc(c, r)`,
`r > 0`, including circles touching `ℝ` and circles through `0`: the regularity of the wedge
field at the log-singular point is already contained in its goodness.

The file also records B4(d) without the `WedgeInfiniteTotal` hypothesis
(`wedgeRefReflectStmt_holds'`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace QuantumZipper
namespace WedgeCReg

/-- For a good sample with positive scale, the raw values of `canonical γ x` at folded circles
are its regularized values. -/
theorem canonical_fc_eq_evalReg {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x)
    (hs : 0 < scaleParam γ x) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    canonical γ x (foldedCircle c r) = evalReg (canonical γ x) (foldedCircle c r) := by
  obtain ⟨F, hF⟩ := hx.1
  show rescale x (Qc γ) (scaleParam γ x) (foldedCircle c r) =
    evalReg (rescale x (Qc γ) (scaleParam γ x)) (foldedCircle c r)
  rw [RegClosure.rescale_fc_eq hF _ hs c hr, (hF.rescale' _ hs).evalReg_fc c hr,
    RegClosure.foldH_mul_pos _ hs]

/-- **WEDGE-CREG (1): `E6.WedgeRefCircleRegStmt` holds** for `γ ∈ (0,2)` and `α < Q`. -/
theorem wedgeRefCircleRegStmt_holds {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    E6.WedgeRefCircleRegStmt γ α := by
  intro Ω' _ P' X A hP hX hA hI
  filter_upwards [WedgeCan4.ae_wedge_canonical_spec_of_inputs
      (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hα)
      hγ hγ2 hα hX hA hI,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A hP hX hA hI] with ω h3 h4 i
  exact canonical_fc_eq_evalReg h4 h3.1 _ (WedgeTK.fullIndex_pos i)

/-- **B4(d) for the reference wedge**, unconditionally for `γ ∈ (0,2)` and `α < Q`. -/
theorem wedgeRefReflectStmt_holds' {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    F1.WedgeRefReflectStmt γ α :=
  wedgeRefReflectStmt_holds hγ hγ2 hα (WedgeInf.wedgeInfiniteTotal hγ hγ2 hα)

end WedgeCReg
end QuantumZipper
