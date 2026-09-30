import QuantumZipper.Proofs.Zipper.Cor15GrpCore
import QuantumZipper.Proofs.Zipper.Cor15Final
import QuantumZipper.Proofs.Zipper.Cor15GoodConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D42 (COR15-ZIPFIX): configurations equal up to an additive constant, and shift-equivariance
# of the capacity zipper

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.3, Corollary 1.5
(pp. 17–18) and §1.4: the zipped field is described only **modulo additive constants**. Decision
D42 (proposed): the D35 zip-side nodes are restated modulo a random additive constant; the group
algebra then needs that zipping/unzipping commute with additive constants. This file is the
deterministic part.

* `ConfigEqC x y c`: the regularized circle averages of `x.1` are those of `y.1` plus `c`
  (at every scale and point), and the drivers agree on `[0,∞)`. `ConfigEqC x y 0 ↔ ConfigEq x y`.
  The relation is phrased on `avgReg` directly, so it needs no convergence of raw averages
  (a `limUnder` of a shifted non-convergent sequence is junk, not junk plus `c`).
* `CCGood y ψ Q`: deterministic conditions at the field `y` under which the coordinate change
  `coordChange · ψ Q` transports `ConfigEqC`: at every dyadic folded circle `μ` read by `avgReg`
  of the output (`μ.map ψ` is a probability measure for every `ψ` at this mathlib pin),
  `avgReg y j` is integrable against `μ.map ψ` and
  `∫ avgReg y j d(μ.map ψ)` converges as `j → ∞`; and the raw folded-circle averages of the
  output converge.
* `zipCapDown_configEqC`, `zipCapUp_configEqC`: `D_t`, `U_t` map `x ∼_c y` to `D_t x ∼_c D_t y`,
  `U_t x ∼_c U_t y` when `CCGood` holds at `y` (for `U_t` the welding driver is unchanged by the
  constant with no condition at all: the boundary measure is multiplied by `e^{γc/2}`).

Own elementary arguments (bookkeeping of `limUnder` junk values; cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

/-- **Configurations equal up to the additive constant `c`**: `avgReg x.1 = avgReg y.1 + c` at
every scale and point, and the drivers agree on `[0,∞)`. -/
def ConfigEqC (x y : FieldSample × (ℝ → ℝ)) (c : ℝ) : Prop :=
  (∀ k z, avgReg x.1 k z = avgReg y.1 k z + c) ∧ ∀ u : ℝ, 0 ≤ u → x.2 u = y.2 u

theorem configEqC_zero_iff {x y : FieldSample × (ℝ → ℝ)} : ConfigEqC x y 0 ↔ ConfigEq x y := by
  simp only [ConfigEqC, add_zero, ConfigEq, RegEq]

theorem ConfigEqC.trans {x y z : FieldSample × (ℝ → ℝ)} {a b : ℝ} (h : ConfigEqC x y a)
    (h' : ConfigEqC y z b) : ConfigEqC x z (a + b) :=
  ⟨fun k w => by rw [h.1 k w, h'.1 k w]; ring, fun u hu => (h.2 u hu).trans (h'.2 u hu)⟩

theorem ConfigEqC.symm {x y : FieldSample × (ℝ → ℝ)} {a : ℝ} (h : ConfigEqC x y a) :
    ConfigEqC y x (-a) :=
  ⟨fun k w => by rw [h.1 k w]; ring, fun u hu => (h.2 u hu).symm⟩

theorem configEqC_of_configEq {x y : FieldSample × (ℝ → ℝ)} (h : ConfigEq x y) :
    ConfigEqC x y 0 :=
  configEqC_zero_iff.2 h

/-- `ConfigEq` on the right. -/
theorem ConfigEqC.of_configEq_right {x y y' : FieldSample × (ℝ → ℝ)} {a : ℝ}
    (h : ConfigEqC x y a) (e : ConfigEq y y') : ConfigEqC x y' a := by
  simpa only [add_zero] using h.trans (configEqC_of_configEq e)

/-- Two configurations with the same constant offset to a third are `ConfigEq`. -/
theorem ConfigEqC.configEq_of_same {x y z : FieldSample × (ℝ → ℝ)} {a : ℝ}
    (h : ConfigEqC x z a) (h' : ConfigEqC y z a) : ConfigEq x y := by
  have := h.trans h'.symm
  rw [add_neg_cancel] at this
  exact configEqC_zero_iff.1 this

/-! ## Coordinate changes -/

/-- Conditions at one measure `μ` (see `CCGood`). -/
def CCGoodAt (y : FieldSample) (ψ : ℂ → ℂ) (μ : Measure ℂ) : Prop :=
  (∀ j : ℕ, Integrable (fun w => avgReg y j w) (μ.map ψ)) ∧
    ∃ L, Tendsto (fun j => ∫ w, avgReg y j w ∂(μ.map ψ)) atTop (𝓝 L)

/-- **Deterministic good set for shift-equivariance of `coordChange · ψ Q` at the field `y`.**
Only the dyadic folded circles read by `avgReg` of the output enter. -/
def CCGood (y : FieldSample) (ψ : ℂ → ℂ) (Q : ℝ) : Prop :=
  (∀ k n : ℕ, ∀ z : ℂ, CCGoodAt y ψ (foldedCircle (dyadicRoundC n z) (radius k))) ∧
    ∀ k : ℕ, ∀ z : ℂ, ∃ l, Tendsto
      (fun n => coordChange y ψ Q (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)

/-- At one probability measure, a constant offset of `avgReg` passes to the coordinate change. -/
theorem coordChange_apply_of_shift {x y : FieldSample} {ψ : ℂ → ℂ} {Q c : ℝ}
    (h : ∀ j w, avgReg x j w = avgReg y j w + c) {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hg : CCGoodAt y ψ μ) : coordChange x ψ Q μ = coordChange y ψ Q μ + c := by
  obtain ⟨hint, L, hL⟩ := hg
  have hk : ∀ j : ℕ, ∫ w, avgReg x j w ∂(μ.map ψ) = ∫ w, avgReg y j w ∂(μ.map ψ) + c := by
    intro j
    simp_rw [h j]
    rw [integral_add (hint j) (integrable_const c)]
    simp
  have h2 : Tendsto (fun j => ∫ w, avgReg x j w ∂(μ.map ψ)) atTop (𝓝 (L + c)) := by
    simpa only [hk] using hL.add_const c
  unfold coordChange evalReg
  rw [h2.limUnder_eq, hL.limUnder_eq]
  ring

/-- **Shift-equivariance of a coordinate change** on the good set `CCGood` at `y`. -/
theorem avgReg_coordChange_of_shift {x y : FieldSample} {ψ : ℂ → ℂ} {Q c : ℝ}
    (h : ∀ j w, avgReg x j w = avgReg y j w + c) (hg : CCGood y ψ Q) (k : ℕ) (z : ℂ) :
    avgReg (coordChange x ψ Q) k z = avgReg (coordChange y ψ Q) k z + c := by
  obtain ⟨l, hl⟩ := hg.2 k z
  have e : (fun n => coordChange x ψ Q (foldedCircle (dyadicRoundC n z) (radius k))) =
      fun n => coordChange y ψ Q (foldedCircle (dyadicRoundC n z) (radius k)) + c :=
    funext fun n => coordChange_apply_of_shift h (hg.1 k n z)
  unfold avgReg
  rw [e, (hl.add_const c).limUnder_eq, hl.limUnder_eq]

/-! ## The welding driver does not see the constant -/

theorem bdryApprox_eq_of_shift {x y : FieldSample} {c : ℝ}
    (h : ∀ k z, avgReg x k z = avgReg y k z + c) (γ : ℝ) (k : ℕ) :
    bdryApprox γ x k = ENNReal.ofReal (Real.exp (γ * c / 2)) • bdryApprox γ y k := by
  unfold bdryApprox
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext s
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [mul_add, Real.exp_add]
  ring_nf

theorem qBoundaryMeasure_eq_of_shift {x y : FieldSample} {c : ℝ}
    (h : ∀ k z, avgReg x k z = avgReg y k z + c) (γ : ℝ) :
    qBoundaryMeasure γ x = ENNReal.ofReal (Real.exp (γ * c / 2)) • qBoundaryMeasure γ y := by
  set C := ENNReal.ofReal (Real.exp (γ * c / 2))
  have hC0 : C ≠ 0 := LocalRule.ofReal_exp_ne_zero _
  have hCT : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have he : bdryApprox γ x = fun k => C • bdryApprox γ y k :=
    funext (bdryApprox_eq_of_shift h γ)
  by_cases hex : ∃ ν, IsVagueLimitR (bdryApprox γ y) ν
  · obtain ⟨ν, hν⟩ := hex
    rw [qBoundaryMeasure_eq hν]
    refine qBoundaryMeasure_eq ?_
    rw [he]; exact BdryVague.IsVagueLimitR.const_smul hν ENNReal.ofReal_ne_top
  · have hex' : ¬∃ ν, IsVagueLimitR (bdryApprox γ x) ν := by
      rintro ⟨ν, hν⟩
      refine hex ⟨C⁻¹ • ν, ?_⟩
      have := BdryVague.IsVagueLimitR.const_smul hν (c := C⁻¹)
        (ENNReal.inv_ne_top.2 (LocalRule.ofReal_exp_ne_zero _))
      rw [he] at this
      simpa only [smul_smul, ENNReal.inv_mul_cancel hC0 hCT, one_smul] using this
    unfold qBoundaryMeasure
    rw [dif_neg hex, dif_neg hex', smul_zero]

/-- **The welding driver is unchanged by a constant offset of `avgReg`** (no condition). -/
theorem weldDriver_eq_of_shift {x y : FieldSample} {c : ℝ}
    (h : ∀ k z, avgReg x k z = avgReg y k z + c) (γ t : ℝ) :
    weldDriver γ x t = weldDriver γ y t := by
  have hw : ∀ s, weldHomR γ x s = weldHomR γ y s :=
    weldHomR_eq_of_smul (LocalRule.ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top
      (qBoundaryMeasure_eq_of_shift h γ)
  have : IsWeldingDriver γ x t = IsWeldingDriver γ y t := by
    funext W'
    unfold IsWeldingDriver
    simp only [hw]
  unfold weldDriver
  rw [this]

/-! ## Shift-equivariance of `D_t` and `U_t` -/

/-- **Unzipping commutes with additive constants** on the good set at `y`. -/
theorem zipCapDown_configEqC {γ t c : ℝ} (ht : 0 ≤ t) {x y : FieldSample × (ℝ → ℝ)}
    (h : ConfigEqC x y c) (hg : CCGood y.1 (fwdMapInv y.2 t) (Qc γ)) :
    ConfigEqC (zipCapDown γ t x) (zipCapDown γ t y) c := by
  have hF : fwdMapInv x.2 t = fwdMapInv y.2 t := grp_fwdMapInv_congr h.2 ht
  refine ⟨fun k z => ?_, fun u hu => ?_⟩
  · show avgReg (coordChange x.1 (fwdMapInv x.2 t) (Qc γ)) k z =
      avgReg (coordChange y.1 (fwdMapInv y.2 t) (Qc γ)) k z + c
    rw [hF]
    exact avgReg_coordChange_of_shift h.1 hg k z
  · show x.2 (t + max u 0) - x.2 t = y.2 (t + max u 0) - y.2 t
    rw [h.2 _ (add_nonneg ht (le_max_right u 0)), h.2 t ht]

/-- **Zipping commutes with additive constants** on the good set at `y`. -/
theorem zipCapUp_configEqC {γ t c : ℝ} {x y : FieldSample × (ℝ → ℝ)} (h : ConfigEqC x y c)
    (hg : CCGood y.1 (revMapInv (weldDriver γ y.1 t) t) (Qc γ)) :
    ConfigEqC (zipCapUp γ t x) (zipCapUp γ t y) c := by
  have hW : weldDriver γ x.1 t = weldDriver γ y.1 t := weldDriver_eq_of_shift h.1 γ t
  refine ⟨fun k z => ?_, fun u hu => ?_⟩
  · show avgReg (coordChange x.1 (revMapInv (weldDriver γ x.1 t) t) (Qc γ)) k z =
      avgReg (coordChange y.1 (revMapInv (weldDriver γ y.1 t) t) (Qc γ)) k z + c
    rw [hW]
    exact avgReg_coordChange_of_shift h.1 hg k z
  · simp only [zipCapUp, hW]
    by_cases hs : u ≤ t
    · simp only [hs, ↓reduceIte]
    · simp only [hs, ↓reduceIte]
      rw [h.2 _ (by linarith [not_le.mp hs])]

/-! ## The literal additive-constant form -/

end Cor15Group
end QuantumZipper
