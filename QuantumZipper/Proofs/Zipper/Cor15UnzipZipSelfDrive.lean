import QuantumZipper.Proofs.Zipper.Cor15UnzipZipSelfGood
import QuantumZipper.Proofs.Zipper.Cor15RegWire
import QuantumZipper.Proofs.Zipper.Cor15PosDriver

/-!
# D35 core piece 3: the driver half of the round trip from the welding-driver reading

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
Continuation of `Cor15UnzipZipSelfGood` (decision D35, `DECISIONS.md`).

`zipCapDown_zipCapUp_snd` shows that the driver half of the round trip `D_a (U_a x) ≈ x` is
automatic once `x.2 0 = 0` and `weldDriver γ x.1 a 0 = 0`. The second condition is *readable
from the B1-FULL data* on the good set of `Cor15WeldReadStmt` (proved as `cor15WeldRead` from
Theorem 1.3 and Rohde–Schramm simplicity), and it holds a.s. at `D_a c` because there the
welding driver is `vrev (√κ B) a`, whose value at `0` is `0`
(`ae_eqOn_weldDriver_zipCapDown`, `B2.vrev_zero`).

Hence the node `Cor15UnzipZipGoodStmt` reduces to its **field half**:

* `Cor15UnzipZipFieldGoodStmt`: a measurable set `A` of B1-FULL data, charged a.s. by the data
  of `D_a c`, on which `RegEq (D_a (U_a x)).1 x.1` holds for every configuration `x` with
  `b1Data x ∈ A`;
* `cor15UnzipZipGoodStmt_of_fieldGood`: `Cor15UnzipZipGoodStmt` from it (discharging the driver
  half with `unzipZipHolds_iff_regEq` and the reading);
* `cor15UnzipZipSelfStmt_of_fieldGood`: `Cor15UnzipZipSelfStmt` from it.

Own elementary assembly; nothing new about the field half.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace QuantumZipper
namespace Cor15Group

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
/-- The driver of `zipCapDown γ a (grpCfg κ B X ω)` vanishes at `0` (it is
`drive κ B ω (a + 0) - drive κ B ω a`). -/
theorem b1Data_zipCapDown_snd_zero_ae :
    ∀ᵐ ω ∂P, (b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))).2 0 = 0 :=
  Eventually.of_forall fun ω => by
    simp only [b1Data, zipCapDown, NNReal.coe_zero, max_eq_left le_rfl, add_zero,
      sub_self]

end Cor15Group
end QuantumZipper
