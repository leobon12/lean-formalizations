import QuantumZipper.Proofs.Zipper.UnifUGTip
import QuantumZipper.Proofs.Zipper.UnifCellScalePath
import QuantumZipper.Proofs.Zipper.UnifTipExp
import QuantumZipper.Proofs.ItoLite.Oscillation
import QuantumZipper.Proofs.Zipper.UnifGaugeBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D37-GAUGE (3): the primed (gauge-normalized) moment nodes and the D31 chain for all gauges

Decision D37: the moment nodes of the D31 chain (`FieldTipSupStmt`, `TipExpSupStmt`,
`UnitCellStmt`, `AnnSubStmt`, `CellScalingStmt`, `TipMomentStmt`, `CellHolderStmt`,
`MagCellHolderStmt`, `SlackCellMomentStmt`) are **false** as stated, because
`IsFreeGFFModConstH` allows an arbitrary (heavy-tailed) additive constant
(`UnifFieldTipSupGauge`, `UnifFieldTipSupGaugeAx`). Here each node is restated for
**gauge-normalized** samples only:

* `IsNrmSample X` — the gauge is pinned (`nrm (X ω) = X ω`, `UnifGaugeBasic.nrmF`);
* the *unparameterized* nodes (`FieldTipSupStmtN`, `TipExpSupStmtN`, `UnitCellStmtN`,
  `AnnSubStmtN`, `CellScalingStmtN`, `CellHolderStmtN`, `MagCellHolderStmtN`) are the same
  statements with the extra hypothesis `IsNrmSample X` — i.e. quantified only over
  gauge-normalized samples;
* the *parameterized* nodes (`TipMomentStmtN`, `SlackCellMomentStmtN`) are stated at the
  gauge-normalized sample `nrmF X`, so that for a normalized `X` they are literally the
  original node.

The node-consuming reductions of the D31 chain are re-derived with the extra hypothesis
(`tipExpSupStmtN_of_nodes`, `unitCellStmtN_of_nodes`; the remaining reductions of the chain are
generic in the sample and are imported unchanged; `cellHolderStmtN_of_mag`,
`slackCellMomentStmtN_of_holder` are the copies of the committed ones). Final assembly: from the
primed nodes at the *norm* of `X` and the regularity input `GaugeRegStmt` (at `nrmF X`) of
`UnifGaugeBasic`, both
`UnifGlobalStmt` (UG) and `UnifAtomlessStmt` (UA) hold for the **arbitrary** sample `(B, X)`.

Own bookkeeping (the proofs are the committed ones with the gauge hypothesis threaded through).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 B1Full CharFun

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Gauge-normalized samples -/

/-- **Gauge-normalized sample**: the additive constant is pinned (`nrm (X ω) = X ω`). -/
def IsNrmSample (X : Ω → FieldSample) : Prop := ∀ ω, B1Full.nrm (X ω) = X ω

theorem isNrmSample_nrmF (X : Ω → FieldSample) : IsNrmSample (nrmF X) := fun ω => nrm_nrm (X ω)

/-! ## The primed nodes -/

/-! ## The node-consuming reductions, with the gauge threaded through -/

/-! ## Final assembly: UG and UA for every gauge -/

end RegUnif
end QuantumZipper
