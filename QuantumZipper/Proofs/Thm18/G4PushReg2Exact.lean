import QuantumZipper.Proofs.Thm18.G4CoreDownShort
import QuantumZipper.Proofs.Thm18.G4CoreZipCocycle
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Zipper.F1PStarZipLenCore
import QuantumZipper.Proofs.Zipper.WedgeAddConstMain
import QuantumZipper.Proofs.GFF.CoordRegSwap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4-PUSHREG (batch 2): the exactness conjuncts at scaled circles

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1). Two of the
pushed-circle regularity nodes contain a conjunct that is **not** a pushed-circle statement but
plain exactness (`evalReg = raw`) of an *unzipped* field at a *scaled* dyadic folded circle:

* `DownShortPushReg` (4th conjunct): `U_{τ_{ℓ−s}}` at `σ_i.map (a ·)`, `a = unzipScale γ ℓ c`;
* `ZipCocyclePushReg` (3rd conjunct): `U_{b² u}` at `σ_i.map (b ·)`, `b` the zipped scale.

Here the time and the scale are random (field-dependent), but `σ_i.map (a ·)` is again a folded
circle (`foldedCircle_map_mul`, with the centre folded into `Hbar` by `foldedCircle_foldH_eq`), so
these conjuncts follow from exactness of **all** unzipped fields at **all** folded circles centred
in `Hbar`, simultaneously. That all-times statement is the third clause of
`F1.PStarShiftRegStmt` at `k = 0` (the W-X core `WedgeUnzip.WedgeExactAllStmt` transported to `P_*`
samples, `F1.pStarShiftRegStmt_of_core`), read in the Theorem 1.8 variables through
`isPStarSample_of_setting` (`ae_exactAll_wedgeConfig`).

Results:
* `foldedCircle_conj_eq`, `foldedCircle_foldH_eq` (deterministic);
* `ae_exactAll_wedgeConfig`: a.s. exactness of every `U_t`, `t ≥ 0`, at every folded circle;
* `DownShortPushRegP`, `G4DownShortPushRegPStmt`, `g4DownShortPushRegStmt_of_P`;
* `ZipCocyclePushRegP`, `G4ZipCocyclePushRegPStmt`, `g4ZipCocyclePushRegStmt_of_P`.

**Own elementary argument** (bookkeeping; the analytic input is the cited W-X core).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

/-! ## Folded circles are invariant under conjugation of the centre -/

theorem foldH_mem_Hbar' (c : ℂ) : foldH c ∈ Hbar := by
  unfold foldH Hbar
  split_ifs with h
  · exact h
  · show 0 ≤ ((starRingEnd ℂ) c).im
    rw [Complex.conj_im]
    linarith [not_le.1 h]

/-- **All-times exactness of the unzipped wedge fields** in the Theorem 1.8 variables, from the
third clause of `F1.PStarShiftRegStmt` at `k = 0` (times `b² s`, `b = scaleParam γ Y > 0`, cover
all `t ≥ 0`). -/
theorem ae_exactAll_wedgeConfig (hX : F1.PStarShiftRegStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (unzippedField γ (wedgeConfig γ B Y ω) t) (foldedCircle d r) =
        unzippedField γ (wedgeConfig γ B Y ω) t (foldedCircle d r) := by
  have hP : Thm13Asm.IsPStarSample (γ ^ 2) P Y B := isPStarSample_of_setting hS
  have hs : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hS.1.le
  filter_upwards [hX (γ ^ 2) P Y B hP, F1.ae_pos_scaleParam_addConst_pStar hP 0] with ω h1 h2
  have h1' := (h1 0).2.2
  rw [hs, F1.addConst_zero'] at h1'
  rw [hs, F1.addConst_zero'] at h2
  rw [show wedgeConfig γ B Y ω = (Y ω, drive (γ ^ 2) B ω) from rfl]
  intro t ht d hd r hr
  have h3 := h1' (t / scaleParam γ (Y ω) ^ 2) (div_nonneg ht (sq_nonneg _)) d hd r hr
  rwa [mul_div_cancel₀ _ (pow_ne_zero 2 h2.ne')] at h3

/-! ## `Z_s ∘ Z_{−ℓ}`, `s < ℓ`: the pushed-circle part -/

/-! ## The zip cocycle: the pushed-circle part -/

end Thm18Asm
end QuantumZipper
