import QuantumZipper.Proofs.Zipper.F1PStarShiftRegPt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, node F1 (D29): `PStarShiftRegStmt` from the wedge core statements

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 (rule (5.1)) and §5.4
(proof of Theorem 1.3, pp. 70–72, "by scaling"). Own elementary bookkeeping.

`F1.PStarShiftRegStmt` is proved from core P (`WedgeUnzip.PStarRealizeStmt`), W-G, W-X and W-C:
on the product extension of core P, the `P_*` field `Y` is `avgReg`-equal to `canonical γ Z`,
and the pointwise lemmas of `F1PStarShiftRegPt.lean` transport W-C (continuum limit of `Z` along
the pushed circles of the unscaled driver), W-G (regularity of the unzipped `Z`-fields) and W-X
(their exactness) to the shifted field `Y + k`, for every `k` at once. Positivity of
`scaleParam γ (Y + k)` for every real `k` on one null set follows from the integer case
(`ae_pos_scaleParam_addConst_pStar`) by monotonicity in `k` (`scaleParam_addConst_pos_all`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open Thm18Asm

/-- **Positivity of the shifted scale for all real shifts from the integer ones.** Adding `c`
multiplies the quantum area by `e^{γ c}`, so the set whose infimum is `scaleParam γ (Y + c)`
increases with `c`. -/
theorem scaleParam_addConst_pos_all {γ : ℝ} (hγ : 0 < γ) {Y : FieldSample} (hY : IsLQGGood γ Y)
    (h : ∀ n : ℤ, 0 < scaleParam γ (addConst Y n)) (k : ℝ) :
    0 < scaleParam γ (addConst Y k) := by
  set S : ℝ → Set ℝ := fun c =>
    {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ (addConst Y c) (Metric.ball 0 a ∩ H)} with hS
  have hsp : ∀ c : ℝ, scaleParam γ (addConst Y c) = sInf (S c) := fun c => rfl
  have hmono : ∀ c c' : ℝ, c ≤ c' → S c ⊆ S c' := by
    intro c c' hcc a ha
    refine ⟨ha.1, le_trans ha.2 ?_⟩
    rw [GoodSample.qAreaMeasure_addConst hY c, GoodSample.qAreaMeasure_addConst hY c',
      Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    gcongr
  set n : ℤ := ⌊k⌋
  have h1 : S n ⊆ S k := hmono _ _ (Int.floor_le k)
  have h2 : S k ⊆ S ((n + 1 : ℤ) : ℝ) := hmono _ _ (by push_cast; exact (Int.lt_floor_add_one k).le)
  have hne : (S n).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have := h n
    rw [hsp, hc, Real.sInf_empty] at this
    exact lt_irrefl _ this
  rw [hsp]
  refine lt_of_lt_of_le ?_ (csInf_le_csInf ⟨0, fun a ha => ha.1.le⟩ (hne.mono h1) h2)
  have := h (n + 1)
  rwa [hsp] at this

end F1
end QuantumZipper
