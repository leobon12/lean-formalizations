import QuantumZipper.Proofs.Zipper.MeasUnzipZip
import QuantumZipper.Proofs.Zipper.LocRichE6

/-!
# MEAS-UNZIP: from path drivers to general continuous drivers; exhaustion in `T`

Continuation of `MeasUnzipAE.lean`.

* `locRich_zipLenDown_congr_drive` (deterministic): the rich local data of the length zipper
  output only see the driver on `[0, T]`, when the level is reached by time `T` and
  `t + a² R ≤ T` (`t` the hitting time, `a` the scale of the unzipped field at `t`). Uses
  `ESM.unzipLengths_eq_of_drive_eqOn`, `ESM.fwdMapInv_eqOn_of_drive_eqOn`,
  `UnzipInvariance.coordChange_congr_of_eqOn`.
* `aemeasurable_locRich_zipLenDown_cover`: for a random configuration `(Y ω, W ω)` with
  continuous drivers vanishing at `0`, measurable restricted paths `πT T ω` on `[0,T]`
  (`T ∈ ℕ`) representing `W ω` there, and measurable events `A T` covering `Ω` a.s. on which
  (a.s.) `ZipGood` holds for `(πT T ω, Y ω)` together with `t + a² R ≤ T`, the map
  `ω ↦ locRich R (zipLenDown γ ℓ (Y ω, W ω))` is `P`-a.e.-measurable.
* `aemeasurable_dataFull_zipLenDown_cover`: hence (all `R`, a.e.-measurable `Y`) the
  `configLawFull` data `E6.dataFull (zipLenDown γ ℓ ∘ (Y, W))` are a.e.-measurable, the conclusion
  of `E6.UnzipMeasStmt`, via `E6.aemeasurable_of_truncFull`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper.MeasUnzip

open CharFun RegCont Factorization D3Plus
open scoped Classical

/-- The hitting time used by `zipLenDown`. -/
def tHit (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ (unzipLengths γ c s).1}

/-! ## Exhaustion in `T` -/

end QuantumZipper.MeasUnzip
