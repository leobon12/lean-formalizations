import QuantumZipper.Proofs.Thm18.R18RTLaw
import QuantumZipper.Proofs.Thm18.R18G1ArcWire
import QuantumZipper.Proofs.Thm18.R18G1ArcReg
import QuantumZipper.Proofs.Thm18.R18G1ArcLenDet
import QuantumZipper.Proofs.Thm18.G1ZA1cMain
import QuantumZipper.Proofs.Thm18.G1ZBdryTransp
import QuantumZipper.Proofs.Thm18.G1FM2Final
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1Z2MeasRep
import QuantumZipper.Proofs.Thm18.G1Z5Id
import QuantumZipper.Proofs.Thm18.G1ZB2CGeom
import QuantumZipper.Proofs.Thm18.G1ZZ1Main
import QuantumZipper.Proofs.Thm18.G1ZoomNodes
import QuantumZipper.Proofs.Thm18.G1ZoomPalmCov
import QuantumZipper.Proofs.Thm18.JordanChordA1a
import QuantumZipper.Proofs.Thm18.Thm18HeadlineV3
import QuantumZipper.Proofs.Thm18.R18E6A
import QuantumZipper.Proofs.Thm18.R18Zero
import QuantumZipper.Proofs.Thm18.R18ReadMeas
import QuantumZipper.Proofs.Thm18.R18RoundRaw
import QuantumZipper.Proofs.Zipper.Thm13FromFieldLawler
import QuantumZipper.Proofs.Thm18.R18RoundUpDet
import QuantumZipper.Proofs.Thm18.R18G4Nodes
import QuantumZipper.Proofs.Wire4
import QuantumZipper.Proofs.Zipper.WedgeLawReg
import QuantumZipper.Proofs.Zipper.AreaWinTransfer
import QuantumZipper.Proofs.Thm18.R18UpWeld
import QuantumZipper.Proofs.Thm18.G4ASepLog
import QuantumZipper.Proofs.Thm18.G4ASepBackLog
import QuantumZipper.Proofs.Thm18.G1Z3Fixed
import QuantumZipper.Proofs.Thm18.G4ASepDefs
import QuantumZipper.Proofs.Thm18.G4WeldUniq
import QuantumZipper.Proofs.Thm18.G4WeldRem
import QuantumZipper.Proofs.Thm18.G4WeldHull
import QuantumZipper.Proofs.LQG.WedgeBoundaryReg
import QuantumZipper.Proofs.Thm18.R18DownTime
import QuantumZipper.Proofs.Thm18.R18T4bWeld
import QuantumZipper.Proofs.Thm18.R18RTMeasDrv
import QuantumZipper.Proofs.Thm18.R18RTMask
import QuantumZipper.Proofs.Thm18.R18RTCore
import QuantumZipper.Proofs.Thm18.R18T8aDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6, unzipping case `s, t < 0` of clause (2) for the D82 maps

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (2), p. 26
(group law `Z_{s+t} = Z_s ∘ Z_t`), case `s, t < 0`, for the D82 maps (`zipLenMA`: unzipping acts on
the pieces). Route of handoff/R18-PLAN.md §6 (RT6 spec):

* `Z_{s+t} c₀ ≈ Z^A_{s+t} c₀` by RT2 at `c₀` (`MaskExactFullAStmt`, time `−(s+t)`);
* `Z^A_{s+t} c₀ ≈ Z^A_s (Z^A_t c₀)` by T8a (`g4GroupNegAStmt_of_X1`);
* `Z_s (Z_t c₀) = Z_s (Z^A_t c₀)` exactly, since `Z_s` reads only the masked data and RT2 at `c₀`
  (time `−t`) gives equal masked data;
* `Z_s (Z^A_t c₀) ≈ Z^A_s (Z^A_t c₀)`: RT2 at the unzipped wedge `c₁ = Z^A_t c₀`
  (`MaskExactUnzAStmt`, new node).

The plan proposed to obtain the last step by transferring the RT2 event from `c₀` to `c₁` with E6
on the full data. That transfer needs the event `{x : πd (offData (Z_s x)) = πd (offData (Z^A_s x))}`
to be a Borel function of `cfgData x`; RT3 reads the left side (`Dm`), but no Borel reading of the
unzipping `Z^A_s` of the *full* configuration is available at `c₁` (only along the wedge sample,
`LocLen.UnzipMeasArcStmt`), so the step is kept as the node `MaskExactUnzAStmt`: RT2 for the
unzipped wedge (same sources as RT2: Berestycki–Powell arXiv:2404.16642 Thm 8.16, Rem 8.10).

`≈` is `ConfigEqOff`; its transitivity and the passage from equal masked data are own elementary
bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- Equal masked circle coordinates and drivers give equality off the curve. -/
theorem rt6_configEqOff_of_πd {x y : FieldSample × (ℝ → ℝ)}
    (h : πd (offData x) = πd (offData y)) : ConfigEqOff x y := by
  have hdrv : ∀ u : ℝ, 0 ≤ u → x.2 u = y.2 u := fun u hu => by
    have e := congrArg (fun d : (ℕ → ℝ) × (ℝ≥0 → ℝ) => d.2 ⟨u, hu⟩) h
    exact e
  have hcur : curveOf x.2 = curveOf y.2 := curveOf_congr hdrv
  refine ⟨regEqOff_of_coordsOffU fun i hi => ?_, hdrv⟩
  have e := congrArg (fun d : (ℕ → ℝ) × (ℝ≥0 → ℝ) => d.1 i) h
  simp only [πd, offData, lawDataOff] at e
  rw [hcur, if_pos hi, if_pos hi] at e
  exact e

/-- **RT2 at the unzipped wedge** (open node): for `a, b > 0`, a.s. unzipping by `a` the pieces
of `c₁ = Z^A_{−b} c₀` and unzipping `c₁` itself give the same masked circle coordinates and
driver. This is `MaskExactAStmt` at the configuration `c₁` (which has the full-data law of `c₀`,
E6), i.e. "`h` may be defined arbitrarily on `η`" for the unzipped surface (Sheffield §4.1 p. 48;
Berestycki–Powell arXiv:2404.16642 Thm 8.16, Rem 8.10). -/
def MaskExactUnzAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ a : ℝ, 0 < a → ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂P,
      πd (offData (zipLenDownMA γ a (zipLenDownA γ b (wedgeAConfig γ B Y ω))).toPair) =
        πd (offData (zipLenDownA γ a (zipLenDownA γ b (wedgeAConfig γ B Y ω))).toPair)

end R18
end QuantumZipper
