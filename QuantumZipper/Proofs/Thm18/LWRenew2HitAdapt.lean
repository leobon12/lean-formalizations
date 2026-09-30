import QuantumZipper.Proofs.Thm18.LWFarDefs3
import QuantumZipper.Proofs.Thm18.LWFarCondStop
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.RS.TraceMain
import QuantumZipper.Proofs.RS.TraceShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWS-0′-HIT, part 1: adaptedness of the SLE trace and of the backward maps

For the natural filtration `𝓕` of the driving Brownian motion (`SMSetup`), and for **every**
sample point, `ω ↦ η(s) = sleTrace κ B ω s` and `ω ↦ f̂_s(w)` are `𝓕_s`-measurable: both only
depend on the driver on `[0,s]` (`RS.trace_congr_drive`, `ReverseFlow.revMap_congr_drive`), so
they are functions of the path stopped at `s`, whose coordinates are `𝓕_s`-measurable; the trace
of a continuous path vanishing at `0` equals the path-measurable version `G1Pkg.traceSel`.

Own elementary bookkeeping (standard: a functional of the path up to time `s` is
`𝓕_s`-measurable).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- The driving path stopped at the deterministic time `s`. -/
def hitStopPath (B : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : ℝ≥0 → Ω → ℝ := fun r ω => B (min r s) ω

lemma hitStopPath_coord_meas (hS : SMSetup P B 𝓕) (s r : ℝ≥0) :
    Measurable[𝓕 s] (hitStopPath B s r) :=
  (hS.adapted (min r s)).mono (𝓕.mono (min_le_right _ _)) le_rfl

lemma hitStopPath_meas (hS : SMSetup P B 𝓕) (s : ℝ≥0) :
    Measurable[𝓕 s] (fun ω (r : ℝ≥0) => hitStopPath B s r ω) := by
  exact @Measurable.of_eval Ω ℝ≥0 (fun _ => ℝ) (𝓕 s) _ _ fun r => hitStopPath_coord_meas hS s r

lemma hitStopPath_cont (hS : SMSetup P B 𝓕) (s : ℝ≥0) (ω : Ω) :
    Continuous fun r => hitStopPath B s r ω :=
  (hS.cont ω).comp (continuous_id.min continuous_const)

lemma hitStopPath_zero (hS : SMSetup P B 𝓕) (s : ℝ≥0) (ω : Ω) : hitStopPath B s 0 ω = 0 := by
  simp [hitStopPath, hS.zero]

lemma drive_hitStopPath_eqOn (κ : ℝ) (s : ℝ≥0) (ω : Ω) :
    EqOn (drive κ B ω) (drive κ (hitStopPath B s) ω) (Icc 0 (s : ℝ)) := by
  intro t ht
  simp only [drive, hitStopPath]
  rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 ht.2)]

/-- **The SLE trace is adapted, for every sample point.** -/
theorem measurable_sleTrace_adapt (hS : SMSetup P B 𝓕) (κ : ℝ) (s : ℝ≥0) :
    Measurable[𝓕 s] (fun ω => sleTrace κ B ω s) := by
  have heq : (fun ω => sleTrace κ B ω s) =
      fun ω => G1Pkg.traceSel κ (fun r => hitStopPath B s r ω) s := by
    funext ω
    rw [G1Pkg.traceSel_eq (hitStopPath_cont hS s ω) (hitStopPath_zero hS s ω) s.coe_nonneg]
    exact RS.trace_congr_drive (drive_continuous (hS.cont ω)) (drive_zero (hS.zero ω))
      (drive_continuous (hitStopPath_cont hS s ω)) (drive_zero (hitStopPath_zero hS s ω)) s.coe_nonneg
      (drive_hitStopPath_eqOn κ s ω)
  rw [heq]
  exact (measurable_pi_apply (s : ℝ)).comp ((G1Pkg.measurable_traceSel κ).comp (hitStopPath_meas hS s))

/-- **The backward Loewner maps are adapted, for every sample point.** -/
theorem measurable_fwdMapInv_adapt (hS : SMSetup P B 𝓕) (κ : ℝ) (s : ℝ≥0) {w : ℂ}
    (hw : 0 < w.im) : Measurable[𝓕 s] (fun ω => fwdMapInv (drive κ B ω) s w) := by
  have heq : (fun ω => fwdMapInv (drive κ B ω) s w) =
      fun ω => fwdMapInv (drive κ (hitStopPath B s) ω) s w := by
    funext ω
    have hW := drive_continuous (κ := κ) (hS.cont ω)
    have hW0 := drive_zero (κ := κ) (hS.zero ω)
    have hW' := drive_continuous (κ := κ) (hitStopPath_cont hS s ω)
    have hW'0 := drive_zero (κ := κ) (hitStopPath_zero hS s ω)
    rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ hW hW0 s.coe_nonneg hw,
      UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ hW' hW'0 s.coe_nonneg hw]
    refine ReverseFlow.revMap_congr_drive w fun q hq => ?_
    show drive κ B ω (↑s - q) - drive κ B ω ↑s = drive κ (hitStopPath B s) ω (↑s - q) - drive κ (hitStopPath B s) ω ↑s
    rw [drive_hitStopPath_eqOn κ s ω ⟨by linarith [hq.2], by linarith [hq.1]⟩,
      drive_hitStopPath_eqOn κ s ω ⟨s.coe_nonneg, le_rfl⟩]
  rw [heq]
  exact @RS.measurable_fwdMapInv_drive Ω (𝓕 s) (hitStopPath B s)
    (hitStopPath_coord_meas hS s) (hitStopPath_cont hS s) (hitStopPath_zero hS s) κ (s : ℝ) s.coe_nonneg
    w hw

end LWFar
end Thm18Asm
end QuantumZipper
