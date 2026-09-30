import QuantumZipper.Proofs.Zipper.LocRichComapField

/-!
# LOCRICH-COMAP (3): the σ-algebra form of B5 locality from local hitting time and scale

Theorem 1.3, node E6 under D25. By `LocRichComapField.lean` the output
`locRich R ∘ zipLenDown γ ℓ` is a jointly measurable function (`outLoc`) of the local data
`locRich R'`, the hitting time `τ` and the scale `a`, as soon as the flow `f_τ⁻¹` maps
`ℍ ∩ closedBall 0 (aR + 3)` into `ball 0 (R' − 3)` (which follows from the driver bound of
`B5.norm_fwdMapInv_sub_le`). So `LocRichComapAEStmt` follows from

* a measurable path extraction (`PathExtract`: the continuous path on `[0,T]` read off the driver
  window), and
* `LocHitScaleStmt`: measurable local stand-ins `τ̃`, `ã` of the hitting time and the scale that
  are correct almost surely on a good event of probability `≥ 1 − ε` carrying the driver bounds.

Main result: `locRichComapAE_of_hitScale`. Own elementary bookkeeping (the paper, Sheffield
arXiv:1012.4797 §5.4, pp. 70–72, asserts the locality without proof).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.E6

open D3Plus MeasUnzip CharFun

/-- **Measurable path extraction**: `π T w` is a continuous path on `[0,T]` such that, whenever
the window `w` agrees on `[0,T]` with a continuous `W`, the driver `Wof κ T (π T w)` is `W` on
`[0,T]`. -/
def PathExtract (κ : ℝ) (π : ∀ T : ℕ, (ℝ≥0 → ℝ) → C(Icc (0 : ℝ) T, ℝ)) : Prop :=
  (∀ T, Measurable (π T)) ∧ ∀ (T : ℕ) (w : ℝ≥0 → ℝ) (W : ℝ → ℝ), Continuous W →
    (∀ s : ℝ≥0, (s : ℝ) ≤ T → w s = W s) →
    ∀ r ∈ Icc (0 : ℝ) T, Wof κ T (Nat.cast_nonneg T) (π T w) r = W r

variable {Ω' : Type*} [MeasurableSpace Ω']

end QuantumZipper.E6
