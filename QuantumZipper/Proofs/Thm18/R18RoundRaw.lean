import QuantumZipper.Proofs.Thm18.R18PosLaw
import QuantumZipper.Proofs.Thm18.R18OffCongr
import QuantumZipper.Proofs.Wire4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T9b: the raw masked round trip from off-curve regularity of the re-zipped field

`R18.G4RoundRawAStmt` (clause (3) of the paper-form Theorem 1.8, `t > 0`, `R18PosLaw.lean`) asks
the masked raw data of `Z^LEN_t (Z^LEN_{−t} c)` to agree a.s. with that of `c`, coordinate by
coordinate. Copy of `Thm18Asm.g4RoundRawStmt_of_reg` (`G4FactorReg.lean`) off the curve (D74):
the round trip gives `RegEqOff` of the fields and equal drivers on `[0,∞)` (hence equal curves,
`curveOf_congr`), off-curve regularized values then agree (`R18OffCongr.lean`), and the raw values
equal the regularized ones for the wedge field (`Wire4.wedgeZeroRegStmt`) and, by the remaining
node `G4ZipRegAStmt`, for the re-zipped field at off-curve circles and test functions.
Own elementary argument (a property of the regularized encoding).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The forward Loewner equation reads the driver only on `[0,∞)`. -/
theorem isForwardSol_congr {W V : ℝ → ℝ} (h : ∀ u : ℝ, 0 ≤ u → W u = V u) :
    IsForwardSol W = IsForwardSol V := by
  funext z T u
  apply propext
  unfold IsForwardSol
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun t ht => by rw [← h t ht.1]; exact h2 t ht⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun t ht => by rw [h t ht.1]; exact h2 t ht⟩

/-- The curve `curveOf W` depends only on `W` on `[0,∞)`. -/
theorem curveOf_congr {W V : ℝ → ℝ} (h : ∀ u : ℝ, 0 ≤ u → W u = V u) :
    curveOf W = curveOf V := by
  have hF := isForwardSol_congr h
  have hs : swallowTime W = swallowTime V := by
    funext z; unfold swallowTime; rw [hF]
  have hh : fwdHull W = fwdHull V := by
    funext T; unfold fwdHull; rw [hs]
  have hm : fwdMap W = fwdMap V := by
    funext T z; unfold fwdMap; rw [hF]
  have hi : fwdMapInv W = fwdMapInv V := by
    funext T w; unfold fwdMapInv; rw [hh, hm]
  have ht : trace W = trace V := by
    funext t; unfold trace; rw [hi]
  unfold curveOf
  rw [ht]

/-- **Off-curve regularity of the re-zipped field** (`t > 0`; off-curve copy of
`Thm18Asm.G4ZipRegStmt`): a.s. its raw values equal its regularized ones at every coordinate circle
that stays off its curve, and for each test function avoiding its curve, a.s. its raw pairing equals
the regularized one. -/
def G4ZipRegAStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → E6ALaw γ P B Y → LenEqArc γ P B Y →
    ∀ t : ℝ, 0 < t →
      (∀ᵐ ω ∂P, ∀ i : ℕ,
        CircleOff (curveOf (zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω))).drv)
            (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 →
        evalReg (zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω))).fld
            (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
          (zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω))).fld
            (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)) ∧
      ∀ ρ : TestFun H, ∀ᵐ ω ∂P,
        Disjoint (tsupport ρ.1)
            (curveOf (zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω))).drv) →
        pairTest (zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω))).fld ρ.1 =
          pairRaw (zipLenA γ t (zipLenDownA γ t (wedgeAConfig γ B Y ω))).fld ρ.1

end R18
end QuantumZipper
