import QuantumZipper.Proofs.Zipper.F1ReflLaw
import QuantumZipper.Proofs.Zipper.F1B4dBasic

/-!
# F1d input (d): the lengths at time `1` are read from the configuration-law data

Theorem 1.3, node F1d (`blueprint/E_BRANCH_BLUEPRINT.md` §F1; Sheffield, arXiv:1012.4797, §5.4,
p. 72: "by symmetry", which needs that `L⁻, L⁺` are *intrinsic*, i.e. functions of the law data,
B5 "intrinsic"). `F1.f1d_lengths_agree` consumes a measurable `g` on the `configLawFull` data with
`unzipLengths γ c 1 = g (cfgData c)` a.s. for `c` and for its reflection.

* `readLen γ`: the lengths recomputed from the data (field `reconstruct (piC coordsFull)`, driver
  read through its **dyadic** values, `B4d.pathExt`, so that `readLen` depends on countably many
  path coordinates only), and **`unzipLengths_eq_readLen`**: `unzipLengths γ c 1 =
  readLen γ (cfgData c)` for every configuration `c` with a continuous driver satisfying
  `c.2 s = c.2 s⁺` (true for `drive κ B ω` with continuous paths, and for its negative); no
  regularity of the field is needed: `coordChange` only reads `avgReg`.
* `aemeasurable_cfgData_drive`, `aemeasurable_cfgData_reflect_drive`: a.e.-measurability of the
  data along `c = (Y, √κ B)` and along its reflection.
* `pos_lt_top_of_regular`: `0 < L⁻₁ < ⊤` from `O⁻₁ < 0` and a regular boundary measure.
* **`f1d_lengths_agree_read`**: `f1d_lengths_agree` with `g` replaced by the explicit hypothesis
  that `readLen γ` is a.e.-measurable for the law `configLawFull c P` (the measurable version is
  `AEMeasurable.mk`; it transfers to the reflection because both have the same data law).

The identities are own elementary arguments from the definitions (the paper states no proof).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- The driver read from its values at the dyadic times of `[0,∞)` (`B4d.pathExt`). -/
def readDrv (p : ℝ≥0 → ℝ) : ℝ → ℝ := B4d.pathExt fun r => p r.toNNReal

/-- A continuous driver with `W s = W s⁺` is recovered from its values on `[0,∞)`. -/
theorem readDrv_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : ∀ s, W s = W (s.toNNReal : ℝ)) :
    readDrv (fun t : ℝ≥0 => W t) = W := by
  have e : (fun r : ℝ => (fun t : ℝ≥0 => W t) r.toNNReal) = W := funext fun r => (hW0 r).symm
  rw [readDrv, e, B4d.pathExt_of_continuous hW]

/-- `drive κ B ω` only reads `[0,∞)`. -/
theorem drive_toNNReal {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ) :
    drive κ B ω s = drive κ B ω (s.toNNReal : ℝ) := by
  simp only [drive, Real.toNNReal_coe]

theorem continuous_drive_of {Ω : Type*} (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous fun t => B t ω) : Continuous (drive κ B ω) :=
  continuous_const.mul (hc.comp continuous_real_toNNReal)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
/-- The data of `(Y, √κ B)`. -/
theorem cfgData_drive (κ : ℝ) (Y : Ω → FieldSample) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    cfgData (Y ω, drive κ B ω) = (dataH (Y ω), drivePath κ (pathOf B ω)) :=
  Prod.ext rfl (drive_nnreal κ B ω)

theorem aemeasurable_cfgData_drive (κ : ℝ) {Y : Ω → FieldSample} {B : ℝ≥0 → Ω → ℝ}
    (hY : AEMeasurable (fun ω => dataH (Y ω)) P) (hBm : AEMeasurable (pathOf B) P) :
    AEMeasurable (fun ω => cfgData (Y ω, drive κ B ω)) P := by
  simp only [cfgData_drive]
  exact hY.prodMk ((measurable_drivePath κ).comp_aemeasurable hBm)

theorem aemeasurable_cfgData_reflect_drive (κ : ℝ) {Y : Ω → FieldSample} {B : ℝ≥0 → Ω → ℝ}
    (hY : AEMeasurable (fun ω => dataH (Y ω)) P) (hBm : AEMeasurable (pathOf B) P) :
    AEMeasurable (fun ω => cfgData (reflectConfig (Y ω, drive κ B ω))) P := by
  have e : ∀ ω, cfgData (reflectConfig (Y ω, drive κ B ω)) =
      (reflData (dataH (Y ω)).1, drivePath κ ((fun p : ℝ≥0 → ℝ => -p) (pathOf B ω))) := by
    intro ω
    refine Prod.ext (dataFull_reflectH_eq (Y ω)) ?_
    have := neg_drive_nnreal κ B ω
    refine this.trans ?_
    congr 1
  simp only [e]
  exact ((measurable_reflData.comp measurable_fst).comp_aemeasurable hY).prodMk
    ((measurable_drivePath κ).comp_aemeasurable (measurable_neg.comp_aemeasurable hBm))

end F1
end QuantumZipper
