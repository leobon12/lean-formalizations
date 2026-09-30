import QuantumZipper.Proofs.Thm18.G3FidProxy

/-!
# G3 area input (Theorem 1.8): the deterministic core

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, pp. 70–71): the zoom at the Palm point is
the shifted field plus the constant `C/γ`; the quantum area of a field with the constant `c`
added is `e^{γc}` times the area of the field (`LocalRule.qAreaMeasure_addConst'`), so on any
sample whose quantum area near the Palm point is positive the area of the zoom on a fixed
half-ball exceeds `1` for all large `C` (with `γ > 0`). This file proves that deterministic
statement in the form needed by `G3AreaStmt` (`G3G2Scale.lean`):

* `rawConverges_of_isLQGGood`: a good sample has converging raw dyadic circle averages on `ℍ`
  (regularity on `Hbar` restricted);
* `areaProxy_recon`: the area proxy of a field only depends on its raw coordinates;
* `areaProxy_addConst_of_good`: on a good sample, `areaProxy γ (addConst u c) a = e^{γc} ·
  areaProxy γ u a` — through the vague limit (`Prop16Area.G.isVagueLimitOn_H_of_good`), the
  scale of the vague limit (`LocalRule.IsVagueLimitOn.const_smul`) and F1
  (`Thm18Asm.areaProxy_eq_qAreaMeasure`);
* `areaProxy_addConst_mono_of_good`: monotonicity in the constant (needed for the union/continuity
  argument of `G3Area.lean`);
* `eventually_one_le_areaProxy_addConst_of_good`: the eventual lower bound `1 ≤ …` on a good
  sample with positive area.

The whole file is deterministic (no probability). Own elementary arguments (AGENT_GUIDE cost
rule), on top of the cited lemmas.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm

open LQGMeas LocalRule
open Factorization CoordsFull

/-! ## Raw convergence on `ℍ` -/

/-- A good sample has converging raw dyadic circle averages on the open half-plane. -/
theorem rawConverges_of_isLQGGood {γ : ℝ} {u : FieldSample} (hu : IsLQGGood γ u) :
    RawConverges u H :=
  fun k z hz => hu.1.rawConverges k z (H_subset_Hbar hz)

/-! ## The area proxy only reads the raw coordinates -/

/-- The area proxy of a field only depends on its raw coordinates. -/
theorem areaProxy_recon (γ : ℝ) (y : FieldSample) (a : ℝ) :
    areaProxy γ (reconstruct (coords y)) a = areaProxy γ y a := by
  have h : ∀ f, LQGMeas.areaFun γ f (reconstruct (coords y)) = LQGMeas.areaFun γ f y := by
    intro f
    unfold LQGMeas.areaFun
    rw [show reconstruct (coords y) = Prop16Area.recon y from rfl, Prop16Area.areaApprox_recon]
  simp only [areaProxy, h]

/-! ## Adding a constant -/

/-- **Constant shift of a good sample.** Adding a constant multiplies the area proxy of a
half-ball by `e^{γc}`. -/
theorem areaProxy_addConst_of_good {γ : ℝ} {u : FieldSample} (hu : IsLQGGood γ u) (c a : ℝ) :
    areaProxy γ (addConst u c) a = ENNReal.ofReal (Real.exp (γ * c)) * areaProxy γ u a := by
  have hraw := rawConverges_of_isLQGGood hu
  have hμ := Prop16Area.G.isVagueLimitOn_H_of_good hu
  have hμ' : IsVagueLimitOn H (areaApprox γ (addConst u c))
      (ENNReal.ofReal (Real.exp (γ * c)) • qAreaMeasure γ u) := by
    have he : areaApprox γ (addConst u c) =
        fun k => ENNReal.ofReal (Real.exp (γ * c)) • areaApprox γ u k :=
      funext (areaApprox_addConst hraw γ c)
    rw [he]
    exact IsVagueLimitOn.const_smul hμ ENNReal.ofReal_ne_top
  rw [areaProxy_eq_qAreaMeasure hμ' a, areaProxy_eq_qAreaMeasure hμ a,
    qAreaMeasure_addConst' hraw γ c, Measure.smul_apply, smul_eq_mul]

/-- On a good sample, the area proxy of a constant-shifted half-ball is monotone in the
constant (`γ > 0`). -/
theorem areaProxy_addConst_mono_of_good {γ : ℝ} (hγ : 0 < γ) {u : FieldSample}
    (hu : IsLQGGood γ u) {a c c' : ℝ} (hcc : c ≤ c') :
    areaProxy γ (addConst u c) a ≤ areaProxy γ (addConst u c') a := by
  rw [areaProxy_addConst_of_good hu c a, areaProxy_addConst_of_good hu c' a]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hcc hγ.le))) le_rfl

/-- **The area grows with the constant.** On a good sample whose half-ball of radius `a` has
positive area, the constant-shifted sample has area `≥ 1` there for all large constants. -/
theorem eventually_one_le_areaProxy_addConst_of_good {γ : ℝ} (hγ : 0 < γ) {u : FieldSample}
    (hu : IsLQGGood γ u) {a : ℝ} (ha : 0 < areaProxy γ u a) :
    ∀ᶠ c in atTop, 1 ≤ areaProxy γ (addConst u c) a := by
  rw [eventually_atTop]
  rcases eq_top_or_lt_top (areaProxy γ u a) with htop | hlt
  · refine ⟨0, fun c _ => ?_⟩
    rw [areaProxy_addConst_of_good hu c a, htop,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos (γ * c))).ne']
    exact le_top
  · have hA0 : areaProxy γ u a ≠ 0 := ha.ne'
    have htoReal : 0 < (areaProxy γ u a).toReal := ENNReal.toReal_pos hA0 hlt.ne
    refine ⟨max 0 (γ⁻¹ * (-(Real.log ((areaProxy γ u a).toReal))) + 1), fun c hc => ?_⟩
    have hc' : γ⁻¹ * (-(Real.log ((areaProxy γ u a).toReal))) + 1 ≤ c :=
      le_trans (le_max_right _ _) hc
    rw [areaProxy_addConst_of_good hu c a, ← ENNReal.ofReal_toReal hlt.ne,
      ← ENNReal.ofReal_mul (Real.exp_pos (γ * c)).le]
    refine ENNReal.one_le_ofReal.2 ?_
    have hlog : -(Real.log ((areaProxy γ u a).toReal)) ≤ γ * c := by
      have h1 := mul_le_mul_of_nonneg_left hc' hγ.le
      have h2 : γ * (γ⁻¹ * (-(Real.log ((areaProxy γ u a).toReal))) + 1) =
          -(Real.log ((areaProxy γ u a).toReal)) + γ := by
        rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul]
      rw [h2] at h1
      linarith
    calc (1 : ℝ) = ((areaProxy γ u a).toReal)⁻¹ * (areaProxy γ u a).toReal := by
          rw [inv_mul_cancel₀ htoReal.ne']
      _ ≤ Real.exp (γ * c) * (areaProxy γ u a).toReal := by
          refine mul_le_mul_of_nonneg_right ?_ htoReal.le
          rw [← Real.exp_log htoReal, ← Real.exp_neg]
          exact Real.exp_le_exp.2 hlog

end Thm18Asm
end QuantumZipper
