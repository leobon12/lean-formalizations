import QuantumZipper.Proofs.Zipper.E5PartsLvl
import QuantumZipper.Proofs.Zipper.E5Model2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-PARTS, part 4: the local rule for the D3⁺ model field (`LvlZoomVagueStmt`, proved)

Task E5-PARTS (Theorem 1.3, node E5; Sheffield, arXiv:1012.4797, §5.4, pp. 66–72).

`LvlZoomVagueStmt`: if `y₀ = x + ofFun(α(−log‖·‖))` is a good sample (`α = γ − 2/γ`,
`γ = √κ`) and `g` is continuous, the area approximations of the D3⁺ model field
`zoomModel γ α C ρ₀ x g = x + ofFun(α(−log‖·‖) + g + (C/γ − x(ρ₀)))` have a vague limit on
`halfDisc r`.

Proof (the local rule, as in `D3Plus.qAreaMeasureOn_zoomModel`):
1. the area limit of the good sample `y₀` is a vague limit of `areaApprox γ y₀` on `ℍ`
   (`GoodSample.areaR_radius`, `GoodSample.tendsto_one_goodFilter`), so on `halfDisc r`
   (`AtomlessUncond.isVagueLimitOn_restrict`);
2. `LocalRule.isVagueLimitOn_add_ofFun`: `y₀ + ofFun(g + c)` has a vague limit on `halfDisc r`;
3. on every dyadic folded circle inside `ball 0 r` the model field agrees with `y₀ + ofFun(g + c)`
   (additivity of the integral: `log‖·‖` is integrable on folded circles,
   `CoordReg.integrable_log_norm_foldedCircle`, and so is the continuous `g + c`,
   `E5.integrable_foldedCircle_of_continuousOn`), so `D3Plus.exists_isVagueLimitOn_halfDisc_iff`
   transfers the limit.

Own elementary bookkeeping (no new mathematics).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

/-- **`LvlZoomVagueStmt` holds.** -/
theorem lvlZoomVague_holds : LvlZoomVagueStmt := by
  intro κ _ _ x g ρ₀ C r _ hg hgood
  obtain ⟨hreg, -, μ, hμ⟩ := hgood
  obtain ⟨F, hF⟩ := hreg
  have hH : IsVagueLimitOn H (areaApprox (Real.sqrt κ)
      (x + ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖)) μ := by
    refine ⟨hμ.1, hμ.2.1, fun f hf hfc hfH => ?_⟩
    have h := (hμ.2.2 f hf hfc hfH).comp GoodSample.tendsto_one_goodFilter
    refine h.congr fun k => ?_
    simp only [Function.comp, goodRad, GoodSample.areaR_radius _ hF]
  have hU := D3Plus.isOpen_halfDisc r
  have hres := AtomlessUncond.isVagueLimitOn_restrict hU (D3Plus.halfDisc_subset_H r) hH
  have hφ : Continuous fun z => g z + (C / Real.sqrt κ - x ρ₀) := hg.add continuous_const
  have h1 := LocalRule.isVagueLimitOn_add_ofFun ⟨F, hF⟩ hU (D3Plus.halfDisc_subset_H r) hres
    isOpen_univ (subset_univ _) hφ.continuousOn
  have hag : D3Plus.AgreeNear
      (D3Plus.zoomModel (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) C ρ₀ x g)
      ((x + ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖) +
        ofFun fun z => g z + (C / Real.sqrt κ - x ρ₀)) r := by
    intro n k z hz
    have i1 : Integrable (fun w : ℂ => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖w‖)
        (foldedCircle (dyadicRoundC n z) (radius k)) :=
      (CoordReg.integrable_log_norm_foldedCircle _ _).neg.const_mul _
    have i2 : Integrable (fun w => g w + (C / Real.sqrt κ - x ρ₀))
        (foldedCircle (dyadicRoundC n z) (radius k)) :=
      integrable_foldedCircle_of_continuousOn hφ.continuousOn _ _ (radius_pos k) hz
    simp only [D3Plus.zoomModel, Pi.add_apply, ofFun]
    rw [add_assoc, ← integral_add i1 i2]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only
    ring
  exact (D3Plus.exists_isVagueLimitOn_halfDisc_iff hag).2 ⟨_, h1⟩

/-- **`E5LvlZoomParts3Stmt` from its conjunct (b) alone.** -/
theorem e5LvlZoomParts3Stmt_of_partsB (hB : E5LvlZoomPartsBStmt) : E5LvlZoomParts3Stmt :=
  e5LvlZoomParts3Stmt_of_vague lvlZoomVague_holds hB

end E5
end QuantumZipper
