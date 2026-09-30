import QuantumZipper.Statements.ConfigLaw

/-!
# Corollary 1.5, positive times: `Z^CAP_t` only reads the regularized field

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
the paper gives no proof). Blocker 2 of `handoff/COR15.md` (law transfer), deterministic part.

The zip-up map `zipCapUp γ t` reads its input configuration `x` only through the regularized
averages `avgReg x.1` of the field (the welding `R_h` through `qBoundaryMeasure`, the new field
through `evalReg`) and through the driver on `(0,∞)`. Hence:

* `zipCapUp_congr`: `RegEq x.1 x'.1` and `x.2 = x'.2` on `(0,∞)` give
  `zipCapUp γ t x = zipCapUp γ t x'` (literal equality);
* `zipCapUp_congr_configEq`: the same from `ConfigEq x x'`.

So any a.s. `ConfigEq` between two random configurations passes through `Z^CAP_t` (`t ≥ 0`)
pathwise, with no measurability requirement. Own elementary argument (unfolding definitions).
`qBoundaryMeasure_congr_regEq'` restates `F1.qBoundaryMeasure_congr_regEq`
(`Proofs/Zipper/F1Reflect.lean`) with the same proof, to avoid importing that module.
-/

noncomputable section

open MeasureTheory

namespace QuantumZipper
namespace Cor15Group

/-- `evalReg` only reads `avgReg`. -/
theorem evalReg_congr_regEq {x y : FieldSample} (h : RegEq x y) (ν : Measure ℂ) :
    evalReg x ν = evalReg y ν := by
  unfold evalReg
  simp only [h _ _]

/-- A coordinate change only reads `avgReg` of the input field. -/
theorem coordChange_congr_regEq {x y : FieldSample} (h : RegEq x y) (ψ : ℂ → ℂ) (Q : ℝ) :
    coordChange x ψ Q = coordChange y ψ Q := by
  funext μ
  unfold coordChange
  rw [evalReg_congr_regEq h]

/-- The quantum boundary measure only reads `avgReg` (as `F1.qBoundaryMeasure_congr_regEq`). -/
theorem qBoundaryMeasure_congr_regEq' {x y : FieldSample} (hxy : RegEq x y) (γ : ℝ) :
    qBoundaryMeasure γ x = qBoundaryMeasure γ y := by
  have : bdryApprox γ x = bdryApprox γ y := by
    funext k
    simp only [bdryApprox, hxy k]
  classical
  have e : ∀ z : FieldSample, qBoundaryMeasure γ z =
      (fun b : ℕ → Measure ℝ => if h : ∃ ν, IsVagueLimitR b ν then h.choose else 0)
        (bdryApprox γ z) := fun _ => by unfold qBoundaryMeasure; congr
  rw [e x, e y, this]

theorem weldHomR_congr_regEq {x y : FieldSample} (h : RegEq x y) (γ s : ℝ) :
    weldHomR γ x s = weldHomR γ y s := by
  unfold weldHomR
  rw [qBoundaryMeasure_congr_regEq' h]

theorem isWeldingDriver_congr_regEq {x y : FieldSample} (h : RegEq x y) (γ t : ℝ) :
    IsWeldingDriver γ x t = IsWeldingDriver γ y t := by
  funext W'
  unfold IsWeldingDriver
  simp only [weldHomR_congr_regEq h]

/-- The welding driver only reads `avgReg` (both are `Classical.epsilon` of the same
predicate). -/
theorem weldDriver_congr_regEq {x y : FieldSample} (h : RegEq x y) (γ t : ℝ) :
    weldDriver γ x t = weldDriver γ y t := by
  unfold weldDriver
  rw [isWeldingDriver_congr_regEq h]

/-- **`Z^CAP_t` (`t` arbitrary, zip-up branch) only reads the regularized field and the driver
on `(0,∞)`.** -/
theorem zipCapUp_congr {γ t : ℝ} {x x' : FieldSample × (ℝ → ℝ)} (h1 : RegEq x.1 x'.1)
    (h2 : ∀ u : ℝ, 0 < u → x.2 u = x'.2 u) : zipCapUp γ t x = zipCapUp γ t x' := by
  unfold zipCapUp
  simp only [weldDriver_congr_regEq h1, coordChange_congr_regEq h1]
  refine Prod.ext rfl (funext fun s => ?_)
  by_cases hs : s ≤ t
  · simp only [hs, ↓reduceIte]
  · simp only [hs, ↓reduceIte]
    rw [h2 _ (by linarith [not_le.mp hs])]

theorem zipCapUp_congr_configEq {γ t : ℝ} {x x' : FieldSample × (ℝ → ℝ)} (h : ConfigEq x x') :
    zipCapUp γ t x = zipCapUp γ t x' :=
  zipCapUp_congr h.1 fun u hu => h.2 u hu.le

end Cor15Group
end QuantumZipper
