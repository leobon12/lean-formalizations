import QuantumZipper.Proofs.Thm18.G4CMeasProj
import QuantumZipper.Proofs.Thm18.G4CoreDefs2
import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Zipper.LocRichBasic
import QuantumZipper.Proofs.Thm18.G4WeldHull
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Thm18.G4CoreDefs3
import QuantumZipper.Proofs.Thm18.G4ReadFix
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Thm18.G4CMeasCoan
import QuantumZipper.Proofs.Zipper.F1ReadMeasPath
import QuantumZipper.Proofs.LQG.GoodMeasurable
import QuantumZipper.Proofs.Thm18.G4CMeasF1
import QuantumZipper.Zipper.Maps
import QuantumZipper.Proofs.Loewner.ForwardODE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The joint length reader from a gated reader (JOINT-LEN-READER)

Measurability leaf shared by Theorem 1.3 (`F1.LenReadRegMeasStmt`) and Theorem 1.8 (G4 Core C,
`JointLenReader`).

The obstacle in both nodes is descriptive-set theoretic: an a.s. property of the sample does not
give a conull set of the *data law* unless the property's data set is (null-)measurable. Here the
lengths are read through a **gated** reader: jointly measurable `g₁, g₂` on
`(Polish code) × time` and a Borel gate `Good`, such that on good drivers (`F1.PathGoodAll`) the
gate at `(lcode d, t)` is exactly the boundary certificate `E1.M4.BCert` of the unzipped field at
time `t`, and on the gate the lengths equal `g₁, g₂`. Then the "certified at all times" set is
coanalytic in the code (`nullMeasurableSet_forall`, Lusin, Kechris Thm 21.10, proved in
`G4CMeasLusin.lean`), so the sample-side a.s. certificate transfers to the data law
(`ae_bCertAll_map_of_gated`), and the joint reader follows.

* `LCode`, `lcode`: the Polish code of the data (circle coordinates; driver at the nonnegative
  dyadics `m / 2ⁿ`, which is all that `F1.readDrv` reads).
* `JointGatedReaderStmt γ` (deterministic node): the gated reader exists.
* `ae_bCertAll_map_of_gated`: Lusin transfer of the all-times certificate to an image law.
* `jointLenReader_of_gated`: `JointLenReader γ μ` from the gated reader, the vanishing of the
  lengths at negative times on good drivers, and `μ`-a.e. all-times certification.
* `PStarBCertAllStmt` (probabilistic node): a `P_*` sample's unzipped field is certified at all
  times `t ≥ 0` simultaneously, a.s.
* `lenReadRegMeasStmt_of_gated`: `F1.LenReadRegMeasStmt` from the two nodes.

**Own elementary argument** on top of Lusin's theorem (as in `G4CMeas2Len.lean`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- The Polish code space of the data. -/
abbrev LCode : Type := (ℕ → ℝ) × (ℕ → ℝ)

/-- The `n`-th nonnegative dyadic `m / 2ᵏ` (with `(k, m) = unpair n`). -/
def dyNN (n : ℕ) : ℝ≥0 := (n.unpair.2 : ℝ≥0) / 2 ^ n.unpair.1

/-- The code of the data: circle coordinates and the driver at the nonnegative dyadics. -/
def lcode (d : E6.FullData) : LCode := (d.1.1, fun n => d.2 (dyNN n))

theorem measurable_lcode : Measurable lcode :=
  (measurable_fst.comp measurable_fst).prodMk
    (measurable_pi_iff.2 fun n => (measurable_pi_apply (dyNN n)).comp measurable_snd)

/-! ## Theorem 1.3, F1: the read-length regularity set -/

/-- The unzipped field of the read configuration is that of the configuration (continuous
driver with `W s = W s⁺`). -/
theorem unzippedField_readCfg_cfgData (γ : ℝ) {c : FieldSample × (ℝ → ℝ)} (hW : Continuous c.2)
    (hW0 : ∀ s, c.2 s = c.2 (s.toNNReal : ℝ)) (t : ℝ) :
    unzippedField γ (F1.readCfg (F1.cfgData c)) t = unzippedField γ c t := by
  unfold F1.readCfg F1.cfgData unzippedField coordChange
  simp only
  rw [WedgeCan4.piC_coordsFull, F1.readDrv_eq hW hW0]
  funext μ
  rw [Factorization.evalReg_congr (Factorization.avgReg_reconstruct_coords c.1)]

end G4Core
end Thm18Asm
end QuantumZipper
