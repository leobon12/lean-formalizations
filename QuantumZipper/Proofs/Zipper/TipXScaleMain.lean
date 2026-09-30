import QuantumZipper.Proofs.Zipper.TipXScaleAe
import QuantumZipper.Proofs.Zipper.TipXScaleMom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TX-SC (scaling): `TipXPieceMomStmt` from the unit-piece moments

Task TX-SC (handoff `handoff/TIPX-ROUTE.md`, decision D51).

## The unit statements (TX-U1, TX-U2)
* `TipXUnitPieceMomStmt`: the unit piece `A_0(t)` (piece `η[1/4, 1] ∪ ±[1/2, 1]`), uniformly over
  `t ∈ [4, ∞)`, has an a.e.-measurable majorant `Ā_0` with `E[Ā_0^q] ≤ C` for normalized samples
  (`q > 0`, `C < ∞` depending only on `κ`);
* `TipXUnitTipMomStmt`: the same for the unit tip quantity `T_0(t)`.
The constants must not depend on the probability space: the reduction applies the unit statement
to the scaled pair `(B^{(k)}, X^{(k)})` for every `k` (for the true majorants the moment only
depends on the joint law, which is the same for all `k`; the uniform form states this).

## The reduction (`tipXPieceMom_of_unit`)
With `a = 2^{-k}` (`ae_piece_le_scaled`): `A_k(a² t') ≤ a^{2−κ/4} e^{(γ/2) h_a(0)} A^{(k)}_0(t')`,
`h_a(0) = ⟨X, fc(0, a)⟩` (`scFac_eq`); for `k ≥ k₀` (`4 a² ≤ s`) every `t ∈ [s, T]` is `a² t'`
with `t' ≥ 4`. The moment bound `E[A_k^p] ≤ (1 + C)^{1/2} 2^{−k(p(2−κ/4) − p²κ/2)}` is
`lintegral_scaled_moment_le` (Cauchy–Schwarz, `E e^{pγ h_a(0)} = 2^{k p² κ}`:
`lintegral_exp_evalReg_fc0_nrm`), and the rate is `< 1` for `p ≤ (8−κ)/(4κ)` since `κ < 4`.

Frontier inputs (hypotheses): `F2.ScaleGeomAeStmt'` (D45), `F2.TruncRescaleFreeStmt` (D27),
`YGoodAllStmt`. Own elementary bookkeeping (Sheffield arXiv:1012.4797, §5.1, pp. 60–62 for the
scaling rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-! ## The scaling constant -/

theorem rescale_fc01 (x : FieldSample) (Q : ℝ) {a : ℝ} (ha : 0 < a) :
    rescale x Q a (foldedCircle 0 1) = evalReg x (foldedCircle 0 a) + Q * Real.log a := by
  have hd : ∀ z : ℂ, deriv (fun z : ℂ => (a : ℂ) * z) z = a := fun z => by simp
  simp only [rescale, coordChange, hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
    integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [WedgeTK.fc_map_mul 0 1 ha]
  simp

theorem scFac_eq {κ : ℝ} (hκ : 0 < κ) (k : ℕ) (x : FieldSample) :
    scFac κ (radius k) x = ENNReal.ofReal (radius k ^ (2 - κ / 4) *
      Real.exp (Real.sqrt κ * evalReg x (foldedCircle 0 (radius k)) / 2)) := by
  have ha := radius_pos k
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hQ := GoodTransforms.gammaQ_bdry hγ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  unfold scFac scConst
  rw [FSMeas.sfTrunc_apply, rescale_fc01 _ _ ha, Real.rpow_def_of_pos ha,
    Real.rpow_def_of_pos ha, ← Real.exp_add, ← Real.exp_add]
  congr 2
  have e : Real.sqrt κ * (2 / Real.sqrt κ) = 2 := by field_simp
  linear_combination (Real.log (radius k)) * hQ + (Real.log (radius k) / 2) * e -
    (Real.log (radius k) / 4) * hsq + (Real.log (radius k) / 2) * hsq

/-! ## The reduction -/

theorem exists_radius_sq_le {s : ℝ} (hs : 0 < s) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → 4 * radius k ^ 2 ≤ s := by
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (show 0 < min (s / 4) 1 by positivity)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨k₀, fun k hk => ?_⟩
  have h1 : radius k ≤ radius k₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have h2 : radius k ≤ min (s / 4) 1 := h1.trans hk₀.le
  have h3 : radius k ^ 2 ≤ radius k := by
    rw [sq]; exact mul_le_of_le_one_left (radius_pos k).le (radius_le_one k)
  linarith [min_le_left (s / 4) 1]

end WedgeUnzip
end QuantumZipper
