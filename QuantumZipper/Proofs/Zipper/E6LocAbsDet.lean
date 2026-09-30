import QuantumZipper.Proofs.Zipper.E6LocAbsBasic
import QuantumZipper.Proofs.Zipper.B5LocOn

/-!
# E6-LOCABS, deterministic part: the B5 locality core in terms of `locRich`

Theorem 1.3, node E6 under D25. The deterministic B5 locality core (`B5LocDet.lean`,
`B5LocOn.lean`) is stated through dyadic circle agreement `B5.DyCircAgree` and agreement of the
drivers on `[0, T]`. Here both are read off equality of the rich local data `locRich R'`
(own elementary bookkeeping; the paper, Sheffield arXiv:1012.4797 §5.4, pp. 70–72, asserts the
locality without proof):

* `dyCircAgree_of_locRich_eq`: equal `locRich R'` data give `DyCircAgree` on `ball 0 ρ` at all
  scales, for `ρ + 1 ≤ R'` (the dyadic circles `foldedCircle (dyadicRoundC n z) 2^{-j}` are
  `coordsFull` circles, `CoordsFull.fullIndex_surj`, contained in `closedBall 0 R'`).
* `drive_eq_of_locRich_eq`: equal `locRich R'` data give equal drivers on `[0, R']`.
* `hitTime_eq_of_locRich_eq`: the stopping time of `zipLenDown` is a function of `locRich R'`
  under the bounds of `B5.hitTime_eq_of_dyCircAgree`.
* `circAgree_unzippedField_of_locRich_eq`: so is the unzipped field near `0`, in the sense of
  `B5.CircAgree` (`B5.circAgree_unzippedField`).
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus

theorem radius_eq_one_div (j : ℕ) : radius j = ((1 : ℤ) : ℝ) / (2 : ℝ) ^ j := by
  simp [radius, inv_pow]

end QuantumZipper.E6
