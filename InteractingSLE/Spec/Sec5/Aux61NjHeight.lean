/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61NjJump
import InteractingSLE.Spec.Sec5.Aux61CovWire

/-!
# The physical landing height on the eastern counterflow side and RefWin's bound

Packet PROVE-AUX61-NOJUMP, second target (orchestrator, after ruling R103a): in R103's per-outcome
family the landing height is the returned counterflow value `+ θχ + 2πχn` (`Aux61Cmp.CfAccess`'s
height clause, `n` the branch integer of the inherited lift). This file computes it and checks RefWin's
height bounds.

* **`returnedCfData_eq_of_extendFrom_mem_H`**: at a counterflow-chart point `x > 0` whose physical point
  is in `ℍ` (as at every window landing, `Aux61Cpt.ae_windowEvent_landing`), the returned word has
  the value `λ(16/κ) − πχ`: the hull-frame point `−1/x` lies between the left base image `g_s(0⁻) − w_s`
  and `0` (`WangWu.neg_rightImg_sub_lt_of_extendFrom_mem_H`), where the source's counterflow word
  (both marks at its seed, `cfPosL_source`) has height `−λ(16/κ)`;
* `sleLambda_sixteen_div`: `λ(16/κ) = λ − πχ/2`;
* **`eastHeight S n = λ − πχ + (θ₂ − θ₁)χ + 2πχn`** and `returned_add_eq_eastHeight`: the physical
  height with branch integer `n`;
* **`cumWeightRight_eastHeight`** (`n ≥ 0`: Aux. lemma 64's bound `λ − πχ ≤ v`, RefPos) and
  **`cumWeightLeft_eastHeight`** (`n ≥ 1`: Aux. lemma 65's reflected bound `λ + πχ ≤ v`, RefNeg);
  `refPos_of_eastHeight`, `refNeg_of_eastHeight`: the two RefWin words for an interval carrying it.

Deterministic. R48: no Theorem 1.2/1.3 input; R77: no post-contact kernel. Nothing here replaces a
source statement.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC fwdMapInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Aux61Nj
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign LawUnique GlueCond WangWu Cond44Ref Aux61GWord
open Aux61Cmp Sec7.StripSysField CrossCond.Word49 Aux61Kernel Aux61Cov
universe u

/-! ### The eastern returned value -/

theorem negInv_ofReal (x : ℝ) : negInv (x : ℂ) = ((-x⁻¹ : ℝ) : ℂ) := by
  simp [negInv]

/-- **The returned word at an eastern landing**: if the physical point of `x > 0` is in `ℍ`, the
returned value is `λ(16/κ) − πχ`. -/
theorem returnedCfData_eq_of_extendFrom_mem_H (S : SourceSetting.{u}) (p : S.Ω × HistorySpace 0 0)
    {γ : ℝ → ℂ} (hγ : IsLoewnerTrace (cfW S p) γ) (hw0 : cfW S p 0 = 0) {x : ℝ} (hx : 0 < x)
    (hF : extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (x : ℂ)) ∈ H) :
    returnedCfData S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR) (rationalTime S.s) p.2 x =
      sleLambda (16 / S.κ) - Real.pi * chiC S.κ := by
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  rw [negInv_ofReal] at hF
  have hlt := neg_rightImg_sub_lt_of_extendFrom_mem_H hγ hw hw0 hs hF
  have hxneg : -x⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hx)
  have hfilt : ∀ i, ¬ (-x⁻¹ < cfPosL S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
      (Sec4.regPath (cfStop (rationalTime S.s) p.2)) (rationalTime S.s) i) := by
    intro i hi
    rw [cfPosL_source] at hi
    have hc : cfW S p (rationalTime S.s) =
        Sec4.regPath (cfStop (rationalTime S.s) p.2) (rationalTime S.s) := rpath_coe _ _
    rw [hc] at hlt
    exact lt_irrefl _ (hlt.trans hi)
  simp only [returnedCfData, returnData, liftBoundary, not_lt.2 hx.le, ↓reduceIte, mul_zero, add_zero,
    forceBoundaryData, hxneg, cfOffset]
  rw [Finset.filter_false_of_mem fun i _ => hfilt i, Finset.sum_empty, add_zero, mul_one, sleLambda]
  ring

/-! ### The physical height and RefWin's bound -/

theorem sleLambda_sixteen_div {κ : ℝ} (hκ : 0 < κ) :
    sleLambda (16 / κ) = sleLambda κ - Real.pi * chiC κ / 2 := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hss : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ.le
  have h16 : Real.sqrt (16 / κ) = 4 / Real.sqrt κ := by
    rw [Real.sqrt_div' _ hκ.le, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [sleLambda, sleLambda, h16, chiC]
  field_simp
  nlinarith [hss]

/-- **The physical eastern height with branch integer `n`**: `λ − πχ + (θ₂ − θ₁)χ + 2πχn`. -/
def eastHeight (S : SourceSetting.{u}) (n : ℤ) : ℝ :=
  sleLambda S.κ - Real.pi * chiC S.κ + (S.θ₂ - S.θ₁) * chiC S.κ + 2 * Real.pi * chiC S.κ * n

/-- The returned value plus `θχ` plus `χ · 2πn` is the eastern height. -/
theorem returned_add_eq_eastHeight (S : SourceSetting.{u}) (n : ℤ) {v : ℝ}
    (hv : v = sleLambda (16 / S.κ) - Real.pi * chiC S.κ) :
    v + S.θ * chiC S.κ + chiC S.κ * (2 * Real.pi * n) = eastHeight S n := by
  rw [hv, sleLambda_sixteen_div S.κ_pos, eastHeight]
  simp only [SourceSetting.θ]
  ring

theorem pi_mul_chiC_eq {κ : ℝ} (hκ : 0 < κ) : Real.pi * chiC κ = sleLambda κ * (2 - κ / 2) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hss : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ.le
  rw [sleLambda, chiC]
  field_simp
  nlinarith [hss]

/-- **Aux. lemma 64's bound for `n ≥ 0`**: `λ − πχ ≤ v`, i.e. the right cumulative weight is at least
`κ/2 − 2` (RefPos). -/
theorem cumWeightRight_eastHeight (S : SourceSetting.{u}) {n : ℤ} (hn : 0 ≤ n) :
    S.κ / 2 - 2 ≤ Sec4.cumWeightRight S.κ (eastHeight S n) := by
  have hl : 0 < sleLambda S.κ := Sec4.sleLambda_pos S.κ_pos
  have hχ : 0 < chiC S.κ := Sec4.chiC_pos S.κ_pos S.κ_lt_four
  have hθ : 0 < S.θ₂ - S.θ₁ := sub_pos.2 S.angle_lt
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  have hpc := pi_mul_chiC_eq S.κ_pos
  have hge : sleLambda S.κ * (S.κ / 2 - 1) ≤ eastHeight S n := by
    rw [eastHeight]
    have h1 : 0 ≤ (S.θ₂ - S.θ₁) * chiC S.κ := (mul_pos hθ hχ).le
    have h2 : 0 ≤ 2 * Real.pi * chiC S.κ * n := by positivity
    nlinarith
  rw [Sec4.cumWeightRight, le_sub_iff_add_le, le_div_iff₀ hl]
  linarith

/-- **Aux. lemma 65's reflected bound for `n ≥ 1`**: `λ + πχ ≤ v`, i.e. the left cumulative weight is at
most `κ/2 − 4` (RefNeg). -/
theorem cumWeightLeft_eastHeight (S : SourceSetting.{u}) {n : ℤ} (hn : 1 ≤ n) :
    Sec4.cumWeightLeft S.κ (eastHeight S n) ≤ S.κ / 2 - 4 := by
  have hχ : 0 < chiC S.κ := Sec4.chiC_pos S.κ_pos S.κ_lt_four
  have hθ : 0 < S.θ₂ - S.θ₁ := sub_pos.2 S.angle_lt
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine (cumWeightLeft_le_of_high S.κ_pos ?_).le
  rw [eastHeight]
  have h1 : 0 < (S.θ₂ - S.θ₁) * chiC S.κ := mul_pos hθ hχ
  have h2 : 2 * Real.pi * chiC S.κ ≤ 2 * Real.pi * chiC S.κ * n := by
    have : 0 ≤ 2 * Real.pi * chiC S.κ := by positivity
    nlinarith
  nlinarith [Real.pi_pos]

/-- **RefPos for an interval right of the seed carrying the eastern height with `n ≥ 0`.** -/
theorem refPos_of_eastHeight (S : SourceSetting.{u}) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {a a' : ℝ} (ha : 0 ≤ a) {n : ℤ} (hn : 0 ≤ n)
    (hv : ∀ z ∈ Ioo a a', z ∉ J → b z = eastHeight S n) : RefPos S.κ b J (Ioo a a') :=
  ⟨S.κ_lt_four.le, hb, a, a', eastHeight S n, rfl, ha, hv, cumWeightRight_eastHeight S hn⟩

/-- **RefNeg for an interval left of the seed carrying the eastern height with `n ≥ 1`**, in the
reflected Aux. lemma 65 word shape. -/
theorem refNeg_of_eastHeight (S : SourceSetting.{u}) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {x₂ x₁ : ℝ} (h21 : x₂ < x₁) (h10 : x₁ < 0) {n : ℤ}
    (hn : 1 ≤ n) (hpos : ∀ z, 0 < z → b z = sleLambda S.κ)
    (hmid : ∀ z, x₁ < z → z < 0 → b z = -sleLambda S.κ)
    (hv : ∀ z, x₂ < z → z < x₁ → b z = eastHeight S n) (hlow : ∀ z, z < x₂ → b z = -sleLambda S.κ)
    {I : Set ℝ} (hI : I ⊆ Ioo x₂ x₁) : RefNeg S.κ b J I :=
  ⟨S.κ_lt_four, hb, x₂, x₁, eastHeight S n, h21, h10, hpos, hmid, hv, hlow,
    cumWeightLeft_eastHeight S hn, hI⟩

end InteractingSLE.Sec5.Aux61Nj
