/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CovFibre

/-!
# The window references on both sides of the seed, and the final wiring of (E1)

Packet PROVE-AUX61-R2C. Astra's follow-up 4 L190–L213 (ruling R71): in the restart chart the comparison interval
lies on one side of the seed. On the positive side Aux. lemma 64's word applies (`RefPos`, R5 proved:
`isSettingAvoiding_refPos`). On the negative side the actual height is `b > λ + πχ`, which is Aux. lemma 65's
reflected strong barrier (spec pp. 265–266: a left height `v` is excluded when `v ∉ (−λ + πχ, λ + πχ)`): the reference
word has heights `λ` on `(0, ∞)`, `−λ` on `(x₁, 0)` and on `(−∞, x₂)`, and `v` on `(x₂, x₁)`, with reflected first
partial sum `−v/λ − 1 ≤ κ/2 − 4` (`RefNeg`). Its avoidance needs the first-swallow table (SS1) of Aux. lemma 132 for
announced stopped references; it is the named input `R5NegStatement` here (the landed `G12Low` covers only the `x₂`
entry, for integrated evolutions).

* `RefNeg`, `R5NegStatement`, `RefWin := RefPos ∨ RefNeg`, `isSettingAvoiding_refWin`;
* `cumWeightLeft_le_of_high`: Astra's negative-side height `b > λ + πχ` gives `−b/λ − 1 < κ/2 − 4`;
* **`fwdNoEastCrosscutTgtQOn_of_actCover_refWin`**: (E1) in target-component form for every angle pair from the
  actual-fibre cover below the critical gap with window references, the negative-side R5 and Part A's counterflow
  regularity.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace InteractingSLE.Sec5.Aux61Cov

open Aux61Kernel Prop51G

universe u

/-- **Aux. lemma 65's reflected reference word** (a strongly attracting interval left of the seed): heights `λ` on
`(0, ∞)`, `−λ` on `(x₁, 0)` and on `(−∞, x₂)`, `v` on `(x₂, x₁)` with `−v/λ − 1 ≤ κ/2 − 4`; the avoided set `I` lies in
`(x₂, x₁)`. -/
def RefNeg (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (I : Set ℝ) : Prop :=
  κ < 4 ∧ IsPiecewiseConstantBoundaryData b J ∧ ∃ x₂ x₁ v : ℝ, x₂ < x₁ ∧ x₁ < 0 ∧
    (∀ z, 0 < z → b z = sleLambda κ) ∧ (∀ z, x₁ < z → z < 0 → b z = -sleLambda κ) ∧
    (∀ z, x₂ < z → z < x₁ → b z = v) ∧ (∀ z, z < x₂ → b z = -sleLambda κ) ∧
    Sec4.cumWeightLeft κ v ≤ κ / 2 - 4 ∧ I ⊆ Ioo x₂ x₁

/-- **R5 on the negative side** (named input): Aux. lemma 65 reflected, for announced stopped references — the
first-swallow table (SS1) of Aux. lemma 132 for local evolutions up to an announced stop. -/
def R5NegStatement : Prop := IsSettingAvoiding.{u} RefNeg

/-- **The window references**: Aux. lemma 64's word right of the seed or Aux. lemma 65's reflected word left of it. -/
def RefWin (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (I : Set ℝ) : Prop := RefPos κ b J I ∨ RefNeg κ b J I

theorem isSettingAvoiding_refWin (hneg : R5NegStatement.{u}) : IsSettingAvoiding.{u} RefWin :=
  isSettingAvoiding_refPos.or hneg

/-- Astra's negative-side height `b > λ + πχ` (L177–L178) satisfies the reflected strong barrier of Aux. lemma 65. -/
theorem cumWeightLeft_le_of_high {κ b : ℝ} (hκ : 0 < κ)
    (hb : sleLambda κ + Real.pi * QuantumZipper.chiC κ < b) : Sec4.cumWeightLeft κ b < κ / 2 - 4 := by
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  have hχ : Real.pi * QuantumZipper.chiC κ = sleLambda κ * (2 - κ / 2) := by
    rw [sleLambda, QuantumZipper.chiC]
    have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
    have hss : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ.le
    field_simp
    nlinarith [hss]
  rw [Sec4.cumWeightLeft, neg_div]
  have h1 : sleLambda κ * (3 - κ / 2) < b := by nlinarith
  have h2 : (3 - κ / 2) < b / sleLambda κ := by rw [lt_div_iff₀ hl]; linarith
  linarith

/-! ### The final wiring -/

/-- **(E1) in target-component form for every angle pair** from the actual-fibre cover below the critical gap with
the window references, the negative-side R5 and Part A's counterflow regularity. -/
theorem fwdNoEastCrosscutTgtQOn_of_actCover_refWin (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hcov : ActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) RefWin) (hneg : R5NegStatement.{u}) :
    FwdNoEastCrosscutTgtQOn.{u} fun _ _ _ => True :=
  fwdNoEastCrosscutTgtQOn_of_actCover_smallGap hreg hcov (isSettingAvoiding_refWin hneg)

/-- **R23's named input** from the actual-fibre cover with window references and the negative-side R5. -/
theorem restartWindowNullQOn_of_actCover_refWin {G : ℝ → ℝ → ℝ → Prop} (hcov : ActFibreCoverOn.{u} G RefWin)
    (hneg : R5NegStatement.{u}) : RestartWindowNullQOn.{u} G :=
  restartWindowNullQOn_of_actCover hcov (isSettingAvoiding_refWin hneg)

end InteractingSLE.Sec5.Aux61Cov
