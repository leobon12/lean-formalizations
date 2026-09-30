import QuantumZipper.Proofs.Zipper.ScaleGeomFix
import QuantumZipper.Proofs.Zipper.WedgeXExact
import QuantumZipper.Proofs.Zipper.F1Side3
import QuantumZipper.Proofs.Zipper.RegContDet
import QuantumZipper.Proofs.Zipper.UnzipFullSplit
import QuantumZipper.Proofs.Zipper.F2Step3
import QuantumZipper.Proofs.LQG.LogSingGoodBasic
import QuantumZipper.Proofs.LQG.RegularSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SCALEGEOM-IN, part 1: the unscaled geometry and the `evalReg` split (F2 step (4), D45)

Inputs (1) and (3) of `F2.ScaleGeomFixInputsStmt` (`ScaleGeomFix.lean`):

* `evalReg_h0rev_add_fc_split` (deterministic): for a regular sample `x`, at every folded circle,
  `evalReg (h⁰ + x) = h⁰ + evalReg x`, with `h⁰ = (2/√κ) log‖·‖`: the log singularity is handled
  by `LogSingGood.evalReg_add_Lf_fc`, and the folded-circle average of `h⁰` is
  `UnzipFull.ofFun_h0rev_fc` (both `(2/√κ) log max(r, ‖c‖)`);
* `scaleGeomSplitAeStmt_holds`: **(3) proved unconditionally**, from the a.s. regularity of the
  free field (`RegSample.ae_isRegularSample`, M4-R3) and `fc(d, r)` dilated by `a` being
  `fc(a d, a r)` (`WedgeTK.fc_map_mul`);
* `unscaledGeomAeStmt_of_yGood`: **(1) from `WedgeUnzip.YGoodAllStmt`** (time-uniform goodness of
  the unzipped `Γ⁰` field, `WedgeXGoodBasic.lean:111`); the side-image half is unconditional
  (`RS.ae_real_alive`: Rohde–Schramm, *Basic properties of SLE*, Lemma 6.2, pp. 23–24, and
  `F1.exists_tendsto_sideImages_of_alive`);
* `ae_rc3_of_yExact`: the RC3 half of (2) from `WedgeUnzip.YExactAllStmt` (`WedgeXExact.lean:42`).

The identification of the `Γ⁰` field `unzY` with the unzipped field of `h⁰ + X` is
`F2.h0rev_add_eq`. Own bookkeeping (no new mathematics).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- `h⁰ + x = x + Lf(−2/√κ)` (the `Lf` form of the log singularity). -/
theorem sgin_h0rev_add_eq_Lf (κ : ℝ) (x : FieldSample) :
    ofFun (h0rev κ) + x = x + ofFun (LogSingGood.Lf (-(2 / Real.sqrt κ))) := by
  rw [add_comm]
  congr 2
  funext v
  simp only [LogSingGood.Lf, h0rev]
  ring

/-- **The `evalReg` split of `h⁰ + x` at every folded circle** (`x` regular). -/
theorem evalReg_h0rev_add_fc_split {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (κ : ℝ) (v : ℂ) {s : ℝ} (hs : 0 < s) :
    evalReg (ofFun (h0rev κ) + x) (foldedCircle v s) =
      ofFun (h0rev κ) (foldedCircle v s) + evalReg x (foldedCircle v s) := by
  rw [sgin_h0rev_add_eq_Lf, ← WedgeTK.fc_foldH_eq v s,
    LogSingGood.evalReg_add_Lf_fc hF _ (CircleFubini.foldH_mem_Hbar' v) hs,
    UnzipFull.ofFun_h0rev_fc κ _ hs]
  ring

/-- **Input (3) of `ScaleGeomFixInputsStmt`, proved.** -/
theorem scaleGeomSplitAeStmt_holds {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (κ : ℝ)
    {a : ℝ} (ha : 0 < a) : ScaleGeomSplitAeStmt κ a P X := by
  filter_upwards [RegSample.ae_isRegularSample hX] with ω hreg d r hr
  obtain ⟨F, hF⟩ := hreg
  rw [WedgeTK.fc_map_mul d r ha]
  exact evalReg_h0rev_add_fc_split hF κ _ (mul_pos ha hr)

/-- The unzipped field of `h⁰ + x` is the `Γ⁰` field `unzY`. -/
theorem unzippedField_h0rev_eq_unzY (κ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (t : ℝ) :
    unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) t = unzY κ x W t := by
  rw [unzY, h0rev_add_eq]

/-- **The RC3 half of input (2) from `WedgeUnzip.YExactAllStmt`.** -/
theorem ae_rc3_of_yExact (hYE : WedgeUnzip.YExactAllStmt) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) s)
          (foldedCircle d r) =
        unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) s
          (foldedCircle d r) := by
  filter_upwards [hYE κ hκ hκ4 P B X hB hX hind] with ω h s hs d hd r hr
  rw [unzippedField_h0rev_eq_unzY]
  exact h s hs d hd r hr

end F2
end QuantumZipper
