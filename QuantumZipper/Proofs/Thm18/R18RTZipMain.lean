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
import QuantumZipper.Proofs.Thm18.R18RTNodes
import QuantumZipper.Proofs.Thm18.R18ZipReg
import QuantumZipper.Proofs.Thm18.R18E6A
import QuantumZipper.Proofs.Thm18.R18Arc
import QuantumZipper.Proofs.Thm18.R18RTDefs
import QuantumZipper.Proofs.Thm18.R18RTZipScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D82 RT5: the second round trip `Z_ℓ ∘ Z_{−ℓ}^{pieces} = id` off the curve

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), p. 26:
`Z^LEN_ℓ` is the inverse of `Z^LEN_{−ℓ}`, "a.s. uniquely defined via conformal welding"; the
zip-up acts on the pair of pieces `((D₁,h_{D₁}),(D₂,h_{D₂}))` (p. 17), so it only reads the field
off the curve. Route (handoff/R18-PLAN.md §6, RT5 spec):

1. `Z^{pieces}_{−ℓ} c₀ = zipLenDownMA ℓ c₀` and `Z_{−ℓ} c₀ = zipLenDownA ℓ c₀` have the same
   driver and carried area (`rt5_zipLenDownA_drv_area_eq_of_pullOff`, from the RT2 core) and the
   same masked data (`maskExactFull_of_pullCore`), hence agree at off-curve circles.
2. Congruence of the zip-up (`rt5_zipLenUpA_fld_congr`): same boundary measure (same welding
   driver, `lenWeldDriver_congr_bdry`), same area (same scale), fields equal off the curve, and
   the pulled-back circles stay at positive distance from the old curve (`Rt5FarPull`) ⇒ the
   zipped fields agree off the zipped curve (`evalReg_congr_of_regEqOff_far` inside `avgReg`).
3. Compose with T7b (`g4RoundDownA_of`).

Open inputs, both strictly smaller than `G4RoundDownMAStmt`: `Rt5BdryStmt` (equal quantum boundary
measures of the two unzipped fields: they agree off the curve, and the boundary measure has no atom
at `0`) and `Rt5FarPullStmt` (the geometric lemma FarPull of the plan). Positivity of the zip scale
is proved (`rt5_ae_zipScale_pos`, R18RTZipScale.lean). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G4Core

/-! ## Step 1: same driver and area after unzipping -/

/-! ## Step 2: congruence of the zip-up -/

/-- **FarPull** (plan §6, RT5) at a configuration `c`, with `p` its length-welding driver and
`a` the scale of the zipped area: every dyadic folded circle off the zipped curve
(the curve of `Z_ℓ c` scaled back by `a`), pulled back by the reverse map `revMapInv p`, stays
in the closed upper half-plane at positive distance from the old curve `curveOf c.drv`. -/
def Rt5FarPullGeo (γ ℓ : ℝ) (c : AreaConfig) : Prop :=
  ∀ (d : ℂ) (k : ℕ),
    CircleOff {w : ℂ | (((areaScale (zipWeldUpA γ (lenWeldDriver γ c.fld ℓ).1
        (lenWeldDriver γ c.fld ℓ).2 c).area)⁻¹ : ℝ) : ℂ) * w ∈ curveOf (zipLenUpA γ ℓ c).drv}
      d (radius k) →
    ∃ δ > 0, ∀ᵐ w ∂((foldedCircle d (radius k)).map
        (revMapInv (lenWeldDriver γ c.fld ℓ).2 (lenWeldDriver γ c.fld ℓ).1)),
      0 ≤ w.im ∧ ∀ q ∈ curveOf c.drv, δ ≤ dist w q

/-- FarPull together with positivity of the zip scale. -/
def Rt5FarPull (γ ℓ : ℝ) (c : AreaConfig) : Prop :=
  0 < areaScale (zipWeldUpA γ (lenWeldDriver γ c.fld ℓ).1 (lenWeldDriver γ c.fld ℓ).2 c).area ∧
    Rt5FarPullGeo γ ℓ c

/-! ## Step 3: the open inputs and the assembly -/

/-- **FarPull** (open, geometric): a.s. `Rt5FarPullGeo` holds at `Z^LEN_{−ℓ} c₀`. -/
def Rt5FarPullStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P, Rt5FarPullGeo γ ℓ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω))

theorem rt5_regEqOff_trans {K : Set ℂ} {x y z : FieldSample} (h1 : RegEqOff K x y)
    (h2 : RegEqOff K y z) : RegEqOff K x z := fun k w hw => (h1 k w hw).trans (h2 k w hw)

end R18
end QuantumZipper
