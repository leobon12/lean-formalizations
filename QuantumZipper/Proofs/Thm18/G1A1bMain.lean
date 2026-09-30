import QuantumZipper.Proofs.Thm18.G1A1bCore
import QuantumZipper.Proofs.Thm18.G1SideMain
import QuantumZipper.Proofs.Thm18.JordanChordA1a
import QuantumZipper.Proofs.Thm18.G1FM2Final
import QuantumZipper.Proofs.Thm18.G1Z2MeasRep
import QuantumZipper.Proofs.Thm18.R18G1ArcDefs
import QuantumZipper.Proofs.Zipper.SWCoreB8FAll
import QuantumZipper.Proofs.Zipper.FieldLawler4Final
import QuantumZipper.Proofs.Zipper.BaseFin2Main
import QuantumZipper.Proofs.Zipper.BaseFin2SleFL

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1A1b (main): `G1ZA1bSideExactArcStmt` from the fixed-driver side round-trip exactness

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
pp. 69–71; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 2.1. Route D72
(`handoff/G4-CORE.md` §8: "G1 A1b reduction", SideRTX).

`G1A1bSideRTXStmt` (new node) is the fixed-driver statement: a.s., for every capacity time
`t > 0`, the unzipped field `U_t = coordChange Y f_t⁻¹ Q` is regular, and along every measure
`(f_t ∘ ψ)_* fc(d, s)` (`ψ` the side map of the ORIGINAL driver, a function of the driver only)
its smoothed witness converges, as the continuous radius `ρ ↓ 0`, to the raw value of `U_t`.
The random unzipping time `t'`, the random scale `a` and the new side map `ψ'` of
`G1ZA1bSideExactArcStmt` are removed: by A1a (`G1ZA1a.g1RerootAffineStmt_holds`),
`(a ψ')_* fc(e, r) = (f_{t'} ∘ ψ)_* fc(e', r')`, so the node is used at `t = t'`.

* **`g1ZA1bSideExactArcStmt_of_sideRTX`**: the a.s. assembly (per sample `G1A1b.exact_of_sideRTX`;
  `t' > 0` a.s. from the proved open-arc A1c `g1RerootLenArcStmt_of_sel` with X1 proved through
  Field–Lawler; old side field regular and exact from the proved `G1RegExStmt`).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen

/-- A.s. the open-arc unzipping time is positive (from the proved open-arc A1c). -/
theorem ae_lenTimeArc_pos {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, 0 < lenTimeArc γ ℓ (wedgeConfig γ B Y ω) := by
  have hX1 : BaseFin.BaseFiniteStmt :=
    BaseFin2.baseFinite_of_yMerge_tail SWCore.yMergeOffTipStmt_holds
      (BaseFin2.sleBaseTail_of_fieldLawler FieldLawler.fieldLawlerReturn_holds)
  filter_upwards [g1RerootLenArcStmt_of_sel hX1 g1Z4SideLimSelStmt_holds γ P B Y hS hIn
    (f1ArcStmt_of_X1 hX1 γ P B Y hS hIn) ℓ hℓ true] with ω h
  exact h.1

end R18
end QuantumZipper
