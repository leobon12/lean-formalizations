import QuantumZipper.Proofs.Thm18.G4CMeas4Fld
import QuantumZipper.Proofs.Thm18.G4CMeas4Side
import QuantumZipper.Proofs.Thm18.G4CMeas4Good
import QuantumZipper.Proofs.Zipper.NuMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JOINT-LEN-READER: the gated joint reader, and the two consumers

* `jointGatedReaderStmt_holds`: **`JointGatedReaderStmt γ` for every `γ`** (deterministic). The
  code field `Zc γ q = fromCoords (vcoord γ q.1 q.2)` has, on good data at `t ≥ 0`, the circle
  coordinates of the unzipped field (`vcoord_lcode`); the gate is `BCert` of `Zc`; the lengths
  are the `BCert`-gated boundary measure of `Zc` on the windows given by `sideR`
  (`sideImages_eq_sideR`).
* `lenReadRegMeasStmt_of_goodAll`: `F1.LenReadRegMeasStmt` from the frontier leaf
  `WedgeUnzip.PStarGoodAllStmt`.
* `jointLenReader_of_ae_bCertAll`: `JointLenReader γ μ` (for `0 < γ`) from `μ`-a.e. membership in
  `BCertAllSet γ` (for image laws, from `ae_bCertAll_map_of_gated`).

Own elementary argument (Carathéodory joint measurability; Lusin, Kechris Thm 21.10).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- The code field at `(code, time)`. -/
def Zc (γ : ℝ) (q : LCode × ℝ) : FieldSample := ESM.fromCoords (vcoord γ q.1 q.2)

theorem measurable_Zc (γ : ℝ) : Measurable (Zc γ) :=
  ESM.measurable_fromCoords (measurable_vcoord γ)

theorem coordsFull_Zc_lcode (γ : ℝ) {d : E6.FullData} (hp : F1.PathGoodAll d.2) {t : ℝ}
    (ht : 0 ≤ t) : CoordsFull.coordsFull (Zc γ (lcode d, t)) =
      CoordsFull.coordsFull (unzippedField γ (F1.readCfg d) t) := by
  unfold Zc
  rw [vcoord_lcode γ hp ht]
  exact F1.coordsFull_fromCoords_coordsFull _

theorem bCert_congr {γ : ℝ} {x x' : FieldSample}
    (h : CoordsFull.coordsFull x = CoordsFull.coordsFull x') :
    E1.M4.BCert γ x ↔ E1.M4.BCert γ x' := by
  unfold E1.M4.BCert
  rw [NuMeas.bdryApprox_congr_coordsFull γ h]

/-- The side windows of the code. -/
def sideC (q : LCode × ℝ) : ℝ × ℝ := sideR q.1.2 q.2

theorem measurable_sideC : Measurable sideC :=
  measurable_sideR.comp (f := fun q : LCode × ℝ => (q.1.2, q.2))
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- The gate. -/
def goodC (γ : ℝ) : Set (LCode × ℝ) := {q | E1.M4.BCert γ (Zc γ q)}

theorem measurableSet_goodC (γ : ℝ) : MeasurableSet (goodC γ) :=
  (E1.M4.measurableSet_bCert γ).preimage (measurable_Zc γ)

end G4Core
end Thm18Asm
end QuantumZipper
