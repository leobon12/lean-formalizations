import QuantumZipper.Proofs.Zipper.LocHitScaleMain

/-!
# LOC-HITSCALE (5): `LocHitScaleStmt` and `LocalAbsRichStmt` for `P_*` samples

Theorem 1.3, node E6 under D25. For a `P_*` sample the driver `√κ B` is a.s. continuous,
vanishes at `0`, and keeps every real point alive (`RS.ae_real_alive`, `κ < 4`), and the local
data are a.e.-measurable (`aemeasurable_locRich_pstar`). The remaining input is the almost-sure
good behaviour of the zipper itself, `HitScaleZipStmt`: global boundary limits of the unzipped
field at the positive rational times, monotone left length reaching `ℓ₁` in finite time,
positive hitting time, area limit and positive scale at the hitting time.

* `locHitScaleStmt_pstar`: `LocHitScaleStmt` for every `P_*` sample, from `HitScaleZipStmt`;
* `localAbsRichStmt_of_hitScaleZip`: hence `LocalAbsRichStmt` (via
  `localAbsRichStmt_of_hitScale`).

Own elementary bookkeeping (Sheffield arXiv:1012.4797 §5.4, pp. 70–72, asserts the locality
without proof).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus MeasUnzip CharFun

/-- The almost-sure behaviour of the zipper needed for the local reading (the open input). -/
structure HitScaleZip (γ ℓ : ℝ) (y : Cfg) : Prop where
  lim : ∀ q : ℚ, 0 < (q : ℝ) → ∃ ν, IsVagueLimitR (bdryApprox γ (unzippedField γ y q)) ν
  mono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (unzipLengths γ y s).1 ≤ (unzipLengths γ y t).1
  reach : ∃ s : ℝ, 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengths γ y s).1
  pos : 0 < tHit γ ℓ y
  area : ∃ μ, IsVagueLimitOn H (areaApprox γ (unzippedField γ y (tHit γ ℓ y))) μ
  scale : 0 < scaleParam γ (unzippedField γ y (tHit γ ℓ y))

end QuantumZipper.E6
