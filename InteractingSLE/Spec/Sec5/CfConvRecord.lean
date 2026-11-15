/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvChart

/-!
# Reading the stopped record and its chart from the coarse history

Packet PROVE-CFCHART2. The record is almost surely a measurable function of the stopped flow
history, and its chart agrees with the chart used by the canonical clause.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfConv

open LawUnique CfGiven CfChart Exist Exist.Staged Exist.StagedLaw
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47

section Record

variable {nL nR : ℕ}

/-- Read the deterministic-time record of the regularized driver of a stopped history. -/
def recordOfHistory (s : ℝ≥0) (y : HistorySpace nL nR) : RecData :=
  recOf (s : ℝ≥0∞) ((fun t => regDrvH y t), ⊤)

theorem measurable_recordOfHistory (s : ℝ≥0) : Measurable (recordOfHistory (nL := nL) (nR := nR) s) := by
  refine (measurable_pi_iff.2 fun q => ?_).prodMk (measurable_const.prodMk measurable_const)
  exact measurable_regDrvH_apply _

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {p : Ω × HistorySpace 0 0}

/-- On a good sample the record read from the coarse history is the actual stopped record. -/
theorem recordOfHistory_flowStop [MeasurableSpace Ω] (hg : IsGood47 W VL VR ζ p) :
    recordOfHistory s (flowStop W VL VR ζ s p) = recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1) := by
  apply Prod.ext
  · funext q
    change fReg W VL VR ζ s p _ = W _ p.1
    simp only [hg.1.1, min_eq_left le_top]
    have hle : (min (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (s : ℝ≥0∞)).toNNReal ≤ s := by
      rw [← ENNReal.coe_min, ENNReal.toNNReal_coe]
      exact min_le_right _ _
    simpa only [fDrv, Real.toNNReal_coe] using
      eqOn_fReg hg ⟨NNReal.coe_nonneg _, by exact_mod_cast hle⟩
  · simp only [recordOfHistory, recOf, readRec, retOf, hg.1.1]

/-- The full record chart is the field chart of the coarse construction. -/
theorem fChart_eq_cfChart [MeasurableSpace Ω] (hg : IsGood47 W VL VR ζ p)
    (he : IsRegularDriver ((fun t => W t p.1), ζ p.1)) :
    fChart W VL VR ζ s p = cfChart (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1)) := by
  have hlt : (s : ℝ≥0∞) < ζ p.1 := by rw [hg.1.1]; exact ENNReal.coe_lt_top
  have hgood := isDrvGood_recOf_of_lt he hlt
  have htime : rtime (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1)) = s := by
    rw [rtime_recOf_coe, min_eq_left hlt.le, ENNReal.toNNReal_coe]
  have hr : EqOn (fReg W VL VR ζ s p)
      (rdrv (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1))) (Icc 0 (s : ℝ)) := by
    intro r hr
    rw [rdrv_recOf_eq he hgood (ne_top_of_lt (lt_of_le_of_lt (min_le_left _ _) ENNReal.coe_lt_top))
      (by rw [htime]; exact hr.2)]
    exact eqOn_fReg hg hr
  unfold cfChart
  rw [recChart_eq, htime]
  change (Chart.id.loewner (fReg W VL VR ζ s p) s).trans _ = _
  congr 1
  exact LocalExt.id_loewner_congr continuous_fReg.continuousOn (continuous_rdrv _).continuousOn
    s.coe_nonneg (lt_add_one (s : ℝ)) hr

end Record

section Filtration

variable {Z Ω : Type*} [MeasurableSpace Z] [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR mL mR : ℕ}
  {W : ℝ≥0 → Z → ℝ} {VL : Fin nL → ℝ≥0 → Z → ℝ} {VR : Fin nR → ℝ≥0 → Z → ℝ}
  {ζ : Z → ℝ≥0∞} {s : ℝ≥0} {E : Set (Z × HistorySpace 0 0)} {xL : Fin mL → ℝ} {xR : Fin mR → ℝ}
  {ι : Ω → Z × HistorySpace 0 0}

/-- The actual record generates only sets already observed by the raw image filtration up to null sets. -/
theorem recordSigma_le_aeSigma (hι : Measurable ι) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hgood : ∀ᵐ ω ∂P, IsGood47 W VL VR ζ (ι ω)) (t : ℝ≥0) :
    MeasurableSpace.comap (fun ω => recOf (s : ℝ≥0∞) ((fun r => W r (ι ω).1), ζ (ι ω).1)) inferInstance ≤
      aeSigma P (Coupling.filtrationComap (qRaw xL xR W VL VR ζ s E) hι t) := by
  have hY : Measurable[Coupling.filtrationComap (qRaw xL xR W VL VR ζ s E) hι t]
      (fun ω => flowStop W VL VR ζ s (ι ω)) := fun B hB =>
    ⟨_, measurable_flowStop_qRaw hX t hB, rfl⟩
  apply comap_le_aeSigma ((measurable_recordOfHistory s).comp hY)
  filter_upwards [hgood] with ω hg
  exact (recordOfHistory_flowStop hg).symm

end Filtration

end InteractingSLE.Sec5.CfConv
