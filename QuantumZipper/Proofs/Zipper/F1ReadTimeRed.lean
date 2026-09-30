import QuantumZipper.Proofs.Zipper.F1ReadTimeRd
import QuantumZipper.Proofs.Zipper.F1ReadTimePath
import QuantumZipper.Proofs.Zipper.F1ReadMeasRed
import QuantumZipper.Proofs.Zipper.F1LenRead
import QuantumZipper.Proofs.Zipper.F1EmbedBasic

/-!
# READLEN at a fixed time: assembly, `LenReadTimeStmt` from the fixed-time finiteness input

Theorem 1.3, node F1 (`F1.LenReadTimeStmt`), the fixed-time form of READLEN
(`F1ReadMeasRed.lean`, time `1`). By `F1ReadTimeRd`, `unzipLengths √κ (readCfg ·) t` is
a.e.-measurable for any law on the data space under which a.e. datum is good (`ReadGoodT`):

* the path part `PathGoodAll` holds a.s. for the law of `√κ B` (`F1ReadTimePath`,
  `ae_pathGoodAll`, at all times at once);
* the field part `FieldFinT` (finiteness of the approximating boundary measures of the unzipped
  field at time `t` on the windows `[-N, N]`) is transported from the configuration to the data
  law through the **measurable** event `finSetT κ t ht` (certificate `DyUC`, start at `0`,
  finiteness for the coordinate-rebuilt path surrogate, which has the same circle coordinates as
  the unzipped field, `coordsFull_unzip_eq_sur_t`). The remaining input is the natural
  fixed-time statement on the configuration:

  `WedgeUnzipFinTimeStmt γ α κ t`: a.s. `bdryApprox γ (unzippedField γ (Y, √κ B) t) k [-N, N] < ∞`
  for all `k, N` — the time-`t` analogue of `WedgeUnzipFinStmt` (which is time `1`), and its
  `P_*` form `PStarUnzipFinTimeStmt κ t`.

**`lenReadTimeStmt_of_wedgeUnzipFinTime`** and **`lenReadTimeStmt_of_pstarUnzipFinTime`**:
`(∀ κ, t ≥ 0, WedgeUnzipFinTimeStmt √κ (√κ − 2/√κ) κ t) → LenReadTimeStmt` and
`(∀ κ, t ≥ 0, PStarUnzipFinTimeStmt κ t) → LenReadTimeStmt`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open ESM CoordsFull

/-- The coordinate-rebuilt path surrogate of the unzipped field at time `t`, as a function of the
data. -/
def rdZT (κ t : ℝ) (ht : 0 ≤ t) (d : RdData) : FieldSample :=
  unzipFieldCoord κ t ht (rdField κ d.1.1, rdTimeD κ t d.2)

theorem measurable_rdZT (κ t : ℝ) (ht : 0 ≤ t) : Measurable (rdZT κ t ht) :=
  (measurable_unzipFieldCoord κ t ht).comp
    (((measurable_rdField κ).comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_rdTimeD κ t).comp measurable_snd))

end F1
end QuantumZipper
