import QuantumZipper.Proofs.Zipper.LocLenStmts
import QuantumZipper.Proofs.Thm18.LenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R8a: open-arc boundary positivity (statements)

Open-arc copies (substitution rule of `handoff/FOLLOW-PAPER-13.md` §1) of
`Thm18Asm.UnzipBdryPosStmt` (`Thm18/LenPos.lean`) and `WedgeUnzip.PStarBdryPosAllStmt`
(`T13Hard3Defs.lean`): the global boundary measure of the unzipped field is replaced by its
local boundary measure off the tip and the two root images, `(offSet W t)ᶜ`.

Paper: Sheffield arXiv:1012.4797 p. 56 (every subarc of the left side of `η[0,t]` has positive
quantum length); Berestycki–Powell arXiv:2404.16642 Def 8.12 p. 281.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- **Open-arc boundary positivity** (copy of `Thm18Asm.UnzipBdryPosStmt`): a.s., for every
`t > 0`, the local boundary measure of the unzipped field off `{O⁻_t, 0, O⁺_t}` charges every
nonempty open subinterval of `[O⁻_t, 0]`. -/
def UnzipBdryPosArcStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Asm.Thm18Setting γ P B Y → Thm18Asm.Thm18Inputs γ P B Y →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ u v : ℝ,
      (sideImages (drive (γ ^ 2) B ω) t).1 ≤ u → u < v → v ≤ 0 →
      0 < qBoundaryMeasureOn γ (unzippedField γ (wedgeConfig γ B Y ω) t)
        (offSet (drive (γ ^ 2) B ω) t)ᶜ (Ioo u v)

/-- **`P_*` form** (copy of `WedgeUnzip.PStarBdryPosAllStmt`). -/
def PStarBdryPosAllArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 < t → ∀ u v : ℝ,
      (sideImages (drive κ B' ω) t).1 ≤ u → u < v → v ≤ 0 →
      0 < qBoundaryMeasureOn (Real.sqrt κ) (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t)
        (offSet (drive κ B' ω) t)ᶜ (Ioo u v)

/-- `UnzipBdryPosArcStmt` from the `P_*` form (copy of
`Thm18Asm.unzipBdryPosStmt_of_pstarBdryPos`). -/
theorem unzipBdryPosArc_of_pStar (h : PStarBdryPosAllArcStmt) : UnzipBdryPosArcStmt := by
  intro γ Ω _ P _ B Y hS hIn
  have hP := Thm18Asm.isPStarSample_of_setting hS
  have hsγ : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hS.1.le
  filter_upwards [h (γ ^ 2) P Y B hP] with ω hω t ht u v hu huv hv
  have h1 := hω t ht u v hu huv hv
  rw [hsγ] at h1
  exact h1

end LocLen
end QuantumZipper
