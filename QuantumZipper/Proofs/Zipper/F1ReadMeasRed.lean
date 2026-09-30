import QuantumZipper.Proofs.Zipper.F1ReadMeas
import QuantumZipper.Proofs.Zipper.F1ReadMeasAlive

/-!
# READLEN, assembly: `ReadLenAEMeasStmt` from the finiteness of the boundary approximants

Theorem 1.3, node F1d input (d) (`F1.ReadLenAEMeasStmt`). By `F1ReadMeas`, `readLen √κ` is
a.e.-measurable for any law on the data space under which a.e. datum is good (`ReadGood`):

* the path part `PathGood` holds a.s. for the law of `√κ B` (`F1ReadMeasAlive`,
  `readPathGoodStmt_holds`, proved by running `RS.ae_real_alive` on the canonical space);
* the field part `FieldFin` (finiteness of the approximating boundary measures of the unzipped
  field on the windows `[-N, N]`) is transported from the configuration to the data law through
  the **measurable** event `finSet κ` (certificate `DyUC`, start at `0`, finiteness for the
  coordinate-rebuilt path surrogate, which has the same circle coordinates as the unzipped field,
  `coordsFull_unzip_eq_sur`). The remaining input is the natural statement on the configuration:

  `WedgeUnzipFinStmt γ α κ`: a.s. `bdryApprox γ (unzippedField γ (Y, √κ B) 1) k [-N, N] < ∞`
  for all `k, N`.

**`readLenAEMeasStmt_of_wedgeUnzipFin`**: `WedgeUnzipFinStmt γ α κ → ReadLenAEMeasStmt γ α κ`.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open ESM CoordsFull

/-- The coordinate-rebuilt path surrogate of the unzipped field, as a function of the data. -/
def rdZ (κ : ℝ) (d : RdData) : FieldSample :=
  unzipFieldCoord κ 1 zero_le_one (rdField κ d.1.1, rdPathD κ d.2)

theorem measurable_rdZ (κ : ℝ) : Measurable (rdZ κ) :=
  (measurable_unzipFieldCoord κ 1 zero_le_one).comp
    (((measurable_rdField κ).comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_rdPathD κ).comp measurable_snd))

/-- The unzipped field only reads the regularized averages of the field. -/
theorem unzippedField_reconstruct_coords (γ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (t : ℝ) :
    unzippedField γ (Factorization.reconstruct (WedgeCan4.piC (coordsFull x)), W) t =
      unzippedField γ (x, W) t := by
  have h : avgReg (Factorization.reconstruct (WedgeCan4.piC (coordsFull x))) = avgReg x := by
    rw [WedgeCan4.piC_coordsFull]; exact Factorization.avgReg_reconstruct_coords x
  unfold unzippedField
  funext μ
  simp only [coordChange, Factorization.evalReg_congr h]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The driver marginal of the configuration law. -/
theorem map_snd_configLawFull {P : Measure Ω} (κ : ℝ) {Y : Ω → FieldSample}
    {B : ℝ≥0 → Ω → ℝ} (hY : AEMeasurable (fun ω => dataH (Y ω)) P)
    (hBm : AEMeasurable (pathOf B) P) :
    (configLawFull (fun ω => (Y ω, drive κ B ω)) P).map Prod.snd =
      P.map fun ω => drivePath κ (pathOf B ω) := by
  rw [configLawFull_eq_map_cfgData, AEMeasurable.map_map_of_aemeasurable
    measurable_snd.aemeasurable (aemeasurable_cfgData_drive κ hY hBm)]
  congr 1
  funext ω
  simp only [Function.comp_apply, cfgData_drive]

end F1
end QuantumZipper
