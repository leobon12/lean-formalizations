import QuantumZipper.Proofs.Thm18.G2PalmLocCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 locality of the cut lengths from the goodness of the Palm field

Sheffield, arXiv:1012.4797, proof of Prop. 5.5 (p. 65): the length `ν_h[x + κ, 0]` is a function
of the field outside `B_κ(x)`. Given the goodness node `G2PalmGoodStmt γ`:

* `g2RootXCutLocStmt_of_good`: the `x`-side node `G2RootXCutLocStmt γ`;
* `g2RootRCutLenLocStmt_of_good`: the `R`-side node `G2RootRCutLenLocStmt γ`.

The witness is `locLen` (`G2PalmLocCore`) of the Palm field read on the folded circles missing
`B(x, κ/2)`, with the interval `[x + κ, 0]` (resp. `[0, y − κ]`) and width `κ/8`: it is
`condSigma`-measurable, and on the good event it equals the cut length
(`G2PalmLoc.locLen_restrict_eq`). Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw G2PalmLoc

/-- **Locality of the cut length, `x` side**, from the goodness of the Palm field. -/
theorem g2RootXCutLocStmt_of_good {γ : ℝ} (hG : G2PalmGoodStmt γ) : G2RootXCutLocStmt γ := by
  intro i m κ x hκ hκm hx
  have hB := ball_half_subset_of hκ hκm hx
  have hS := refS_ball_null_of hB i.inUnit₁
  have h1 : i.t₁ + i.r₁ = -(3 * i.η / 4) := by unfold G3Idx.t₁ G3Idx.r₁; ring
  have h2 := i.inUnit₁
  have hη := i.hη
  have hxt : x + m < i.t₁ + i.r₁ := by linarith [le_abs_self (x - i.t₁)]
  have hxl : i.t₁ - i.r₁ < x := by linarith [neg_abs_le (x - i.t₁)]
  have ht : -1 ≤ i.t₁ - i.r₁ := by linarith [neg_abs_le i.t₁]
  have hx0 : x ≠ 0 := (by linarith : x < 0).ne
  have hx1 : |x| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  refine ⟨fun ω => (locLen γ (restrictField (circOut x (κ / 2) x (κ / 2))
      (normField γ (xPalm γ x) ω)) (x + κ) 0 (κ / 8)).toReal,
    ENNReal.measurable_toReal.comp ((measurable_locLen γ _ _ _).comp
      (measurable_restrict_xPalm γ hS)), ?_⟩
  filter_upwards [hG x hx0 hx1] with ω hω
  rw [locLen_restrict_eq hω (by positivity) fun s hs => ?_]
  rw [mem_Icc] at hs
  rw [abs_of_pos (by linarith [hs.1])]
  linarith [hs.1]

/-- **Locality of the cut length, `R` side**, from the goodness of the Palm field. -/
theorem g2RootRCutLenLocStmt_of_good {γ : ℝ} (hG : G2PalmGoodStmt γ) :
    G2RootRCutLenLocStmt γ := by
  intro i m κ y hκ hκm hy
  have hB := ball_half_subset_of hκ hκm hy
  have hS := refS_ball_null_of hB i.inUnit₂
  have h1 : i.t₂ - i.r₂ = 3 * i.η / 4 := by unfold G3Idx.t₂ G3Idx.r₂; ring
  have h2 := i.inUnit₂
  have hη := i.hη
  have hyt : i.t₂ - i.r₂ < y - m := by linarith [neg_abs_le (y - i.t₂)]
  have hyr : y < i.t₂ + i.r₂ := by linarith [le_abs_self (y - i.t₂)]
  have ht : i.t₂ + i.r₂ ≤ 1 := by linarith [le_abs_self i.t₂]
  have hy0 : y ≠ 0 := (by linarith : 0 < y).ne'
  have hy1 : |y| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  refine ⟨fun ω => (locLen γ (restrictField (circOut y (κ / 2) y (κ / 2))
      (normField γ (xPalm γ y) ω)) 0 (y - κ) (κ / 8)).toReal,
    ENNReal.measurable_toReal.comp ((measurable_locLen γ _ _ _).comp
      (measurable_restrict_xPalm γ hS)), ?_⟩
  filter_upwards [hG y hy0 hy1] with ω hω
  rw [locLen_restrict_eq hω (by positivity) fun s hs => ?_]
  rw [mem_Icc] at hs
  rw [abs_of_neg (by linarith [hs.2])]
  linarith [hs.2]

end Thm18Asm
end QuantumZipper
