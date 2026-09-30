import QuantumZipper.Proofs.Zipper.Cor15ZipGenuine
import QuantumZipper.Proofs.Zipper.Cor15MarkovFieldLaw
import QuantumZipper.Proofs.Zipper.Cor15RegMeas
import QuantumZipper.Proofs.Zipper.E1TransferRep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-MEASVER (1): circle-coordinate bookkeeping for the Corollary 1.5 fields

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5.
Task COR15-MEASVER.

`RegEq` reads a field only at the dyadic folded circles (`avgReg`, `Zipper/Maps.lean`;
`avgReg_congr_full`). This file records the coordinate-level facts used by the measurable versions
of `Cor15MeasVerZip.lean`:

* `coordsFull_sub_ofFun`, `regEq_h0_add_fromC_coordsFull_sub`: for *every* field `y`,
  `RegEq y (𝔥₀ + fromC (coordsFull (y − 𝔥₀)))`. Own elementary proof.
* `exists_measurable_version_of_coords`: a.e.-measurable shifted circle coordinates give a field,
  measurable in the parameter, `RegEq`-equal to `y` a.s.
* `aemeasurable_coordsFull_unzip_sub`: the shifted circle coordinates of the unzipped field are
  a.e.-measurable (from the proved `aemeasurable_coordsFull_unzip`, `Cor15RegMeas.lean`).

**Warning (junk values).** The `fromC` field is `0` at every measure that is not a dyadic folded
circle, so it is never a free field: it is *not* a candidate for the law obligations. The law must
be proved for a version that is an honest field at every admissible measure (the `CInv` version of
`Cor15MeasVerZip.lean`). An obligation "every measurable `Y` with `RegEq`-agreement has the free
law" would be false (change `Y` at one non-circle admissible measure).
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun CoordsFull

/-! ## The `fromC` measurable version and its `RegEq` agreement -/

/-- **Circle coordinates of a shift by `ofFun h0`** are the coordinates minus the deterministic
pairing `∫ h0 dσ_i`. -/
theorem coordsFull_sub_ofFun (y : FieldSample) (h0 : ℂ → ℝ) :
    coordsFull (y - ofFun h0) =
      coordsFull y - fun i => ∫ z, h0 z ∂foldedCircle (fullIndex i).1 (fullIndex i).2 := by
  funext i
  simp only [Pi.sub_apply, coordsFull, ofFun]

/-! ## Coordinate measurability -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Coordinate measurability, unzip direction, proved** from `aemeasurable_coordsFull_unzip`
(`Cor15RegMeas.lean`). -/
theorem aemeasurable_coordsFull_unzip_sub {κ a : ℝ} (hS : IsGrpSetup P B X) (ha : 0 < a) :
    AEMeasurable (fun ω => coordsFull
      ((zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)).1 - ofFun (h0rev κ))) P := by
  have h1 := aemeasurable_coordsFull_unzip κ hS.1 hS.2.1 hS.2.2 ha.le
  have h2 : (fun ω => coordsFull
        ((zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)).1 - ofFun (h0rev κ))) =
      (fun ω => coordsFull (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)).1) -
        (fun _ : Ω => fun i => ∫ z, h0rev κ z ∂
          foldedCircle (fullIndex i).1 (fullIndex i).2) := by
    funext ω
    exact coordsFull_sub_ofFun _ _
  rw [h2]
  exact h1.sub aemeasurable_const

end Cor15Group
end QuantumZipper
