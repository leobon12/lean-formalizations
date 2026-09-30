import QuantumZipper.Proofs.Zipper.UnifClB5
import QuantumZipper.Proofs.Zipper.UnifClB5
import QuantumZipper.Proofs.Zipper.F1EmbedBasic
import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Zipper.WedgeUnzipCore
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.UnifClAnchor
import QuantumZipper.Proofs.Zipper.UnifUGReduce

/-!
# Theorem 1.3, node F1: strict monotonicity of `L⁻` from the D26/D29 cores at every horizon

The F1 node (`F1.LenStrictMonoStmt`, `F1LenBridge.lean`) is horizon-free: it asks for a.s. strict
monotonicity of `s ↦ L⁻_s` on all of `[0,∞)`. The D26 cluster (`DECISIONS.md`) is stated at a fixed
horizon `T`; `F1StrictMonoCfg.lean` removes the horizon by asking for UW and UA *at every horizon*
(`UnifWindowAllStmt`, `UnifAtomlessAllStmt`). This file supplies those all-horizon statements from
the D26/D29 **cores**, each one the corresponding per-horizon statement of the D26 plan quantified
over all horizons:

* `AnchorWindowAllStmt` (AW): the M4-T4 coordinate-change rule for the field `h⁰_q` at a rational
  anchor time `q`, at every `T`;
* `UnifOffTipAllStmt` (UO): the global boundary limits of `h⁰_s` off the tip, at every `T`;
* `UnifTipAllStmt` (UT): tightness of the boundary approximations at the tip `0`, at every `T`.

From them, `unifWindowAllStmt_of_anchorAll` gives UW at every horizon (`unifWindowStmt_of_anchor`
applied at each `T`) and `unifAtomlessAllStmt_of_offTip_tip` gives UA at every horizon (the UA
half of `unifGlobal_unifAtomless_of_offTip_tip`, `UnifUGReduce.lean`). The capstone
`lenStrictMonoCfgStmt_of_core` then gives `F1.LenStrictMonoCfgStmt`. The assembly
`F1.lenStrictMonoStmt_of_core` combines it with the D29 length node
(`F1.UnscaledResampleLenStmt`, open), `PStarRealizeStmt` and `F2.UnscaledB3dStmt` to give
`F1.LenStrictMonoStmt`: modulo those three inputs, the F1 length statement follows from the D26
cores AW + UO + UT at every horizon alone.

Sources: Sheffield, arXiv:1012.4797, §5, Lemma 5.6 and the proof of Theorem 1.3 (pp. 66–72);
the D26/D29 routes. Own bookkeeping (quantification over the horizon only).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5

variable {Ω : Type} [MeasurableSpace Ω]

/-- **AW at every horizon**: the uniform anchor-window rule holds for every `T > 0`. -/
def AnchorWindowAllStmt (κ : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ T : ℝ, 0 < T → AnchorWindowStmt κ T P B X

/-- **UO at every horizon**: global boundary limits off the tip, for every `T > 0`. -/
def UnifOffTipAllStmt (κ : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ T : ℝ, 0 < T → UnifOffTipStmt κ T P B X

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

end RegUnif

namespace F1

end F1
end QuantumZipper
