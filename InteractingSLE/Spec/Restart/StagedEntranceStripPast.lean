/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StagedEntranceInst
import InteractingSLE.Spec.Sec7.StripDetPath
import InteractingSLE.Spec.Supplement.KernelTower2
import InteractingSLE.Spec.Exist.StagedLaw3Trans
import InteractingSLE.Spec.Sec7.ContinuityProbBase
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit

/-!
# The strip system's restart: the two pasts and the record chart

Packet PROVE-STAGEDLOC2 (strip instance of `StagedEntrance.isEntranceHistoryLocal_of_restart_isFlowLine`). For a
two-angle staged history `E` (`StripSys.twoAngleSpec θ₀ q₀ θ`, rational switching time `q₀ > 0`) whose two pieces
live forever, and a path `α` that is a generating trace of the concatenated driver `catPath (E 0).1 q₀ (E 1).1`:

* **`traceAt_recW_eq`**, **`histDriver_frozenPath_eq`**: the first record and the path up to `q₀` determine each other
  (the trace is the measurable trace evaluation of the record driver; the driver is read off the path history);
* **`ae_condExpKernel_pastSigma_eq`**: hence the staged past `pastSigma … 1` (the first record) and Lemma 6.2's past
  `StagedEntrance.pastSigma α q₀` (the stopped path history) have the same regular conditional laws almost surely;
* **`frontier_recChart`**: the record chart's domain is the unbounded component of `ℍ ∖ α([0, q₀])`, so its frontier in
  `ℍ` lies on `α([0, q₀])` (the hypothesis `hfr` of the gluing theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Restart

namespace StagedEntrance

namespace Strip

open Sec6 Exist.Staged Exist.StagedLaw Sec7.StripSideHeightProb

/-! ### Deterministic: the first piece read off the joined trace -/

section Det

variable {e₀ e₁ : (ℝ≥0 → ℝ) × ℝ≥0∞} {q₀ : ℝ≥0} {α : ℝ≥0 → ℂ}

/-- A regular driver of infinite lifetime is continuous. -/
theorem continuous_of_regular_top {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) (h2 : e.2 = ⊤) :
    Continuous e.1 :=
  continuousOn_univ.1 (he.1.mono fun t _ => show (t : ℝ≥0∞) < e.2 by rw [h2]; exact ENNReal.coe_lt_top)

/-- The concatenated driver of two regular drivers of infinite lifetime is continuous. -/
theorem continuous_catPath_of_regular (h₀ : IsRegularDriver e₀) (h₁ : IsRegularDriver e₁) (h₀2 : e₀.2 = ⊤)
    (h₁2 : e₁.2 = ⊤) : Continuous (catPath e₀.1 q₀ e₁.1) :=
  continuous_catPath (continuous_of_regular_top h₀ h₀2) (continuous_of_regular_top h₁ h₁2) h₁.2.1

/-- The stopped history of a path frozen after `t₀`, read through `t₀`, is that of the path. -/
theorem histOf_pathCoord_frozenPath (γ : ℝ≥0 → ℂ) (t₀ : ℝ≥0) :
    histOf (pathCoord (frozenPath γ t₀)) (t₀ : ℝ≥0∞) = histOf (pathCoord γ) (t₀ : ℝ≥0∞) := by
  unfold histOf
  congr 1
  funext q
  unfold stopCoord
  split_ifs with hq
  · exact frozenPath_of_le (ENNReal.coe_le_coe.1 hq)
  · rfl

/-- **The joined trace before `q₀` is the measurable trace evaluation of the first record's driver.** -/
theorem traceAt_recW_eq (h₀ : IsRegularDriver e₀) (h₁ : IsRegularDriver e₁) (h₀2 : e₀.2 = ⊤) (h₁2 : e₁.2 = ⊤)
    (hα : IsGeneratingTrace (catPath e₀.1 q₀ e₁.1) ⊤ α) {s : ℝ≥0} (hs : s ≤ q₀) :
    LP.traceAt s (recW (recOf (q₀ : ℝ≥0∞) e₀)) = α s := by
  have hlt : (q₀ : ℝ≥0∞) < e₀.2 := by rw [h₀2]; exact ENNReal.coe_lt_top
  have hW := Sec7.StripMark.recW_recOf_of_lt h₀ hlt (Sec7.StripMark.isDrvGood_recOf_of_lt h₀ hlt)
  rw [LP.traceAt_congr (w' := catPath e₀.1 q₀ e₁.1) fun r hr => by
    rw [hW, min_eq_left (hr.trans hs), catPath_of_le (hr.trans hs)]]
  exact LP.traceAt_eq_of_isGeneratingTrace hα (continuous_catPath_of_regular h₀ h₁ h₀2 h₁2).continuousOn
    (catPath_zero h₀.2.1) ENNReal.coe_lt_top

/-- The joined trace is a generating trace of the first driver on `[0, q₀]`. -/
theorem isGeneratingTrace_first (hα : IsGeneratingTrace (catPath e₀.1 q₀ e₁.1) ⊤ α) :
    IsGeneratingTrace e₀.1 (q₀ : ℝ≥0∞) α :=
  IsGeneratingTrace.of_eqOn_lt hα fun _ ht => (catPath_of_le (ENNReal.coe_lt_coe.1 ht).le).symm

/-- **The first driver is read off the stopped path history of the joined trace.** -/
theorem histDriver_frozenPath_eq (h₀ : IsRegularDriver e₀) (h₀2 : e₀.2 = ⊤) (hq₀ : 0 < q₀)
    (hα : IsGeneratingTrace (catPath e₀.1 q₀ e₁.1) ⊤ α) {s : ℝ≥0} (hs : s ≤ q₀) :
    Sec7.StripMark.histDriver q₀ (histOf (pathCoord (frozenPath α q₀)) (q₀ : ℝ≥0∞)) s = e₀.1 s := by
  rw [histOf_pathCoord_frozenPath]
  exact Sec7.StripMark.histDriver_eq (continuous_of_regular_top h₀ h₀2) h₀.2.1 hq₀ (isGeneratingTrace_first hα) hs

end Det

/-! ### The two pasts determine each other -/

section Maps

/-- The record of a piece stopped at `q₀`, read off a driver. -/
def recOfDriver (q₀ : ℝ≥0) (W : ℝ≥0 → ℝ) : RecData :=
  ((fun q : ℚ => W (min (q : ℝ).toNNReal q₀)), (q₀ : ℝ≥0∞), false)

theorem measurable_recOfDriver (q₀ : ℝ≥0) : Measurable (recOfDriver q₀) := by
  refine Measurable.prodMk (measurable_pi_iff.2 fun q : ℚ => ?_) measurable_const
  exact measurable_pi_apply _

/-- The staged past (one record) read off Lemma 6.2's past (the stopped path history). -/
def pastOfHist (q₀ : ℝ≥0) (y : Fin 1 → Hist) : PastData 1 :=
  fun _ => recOfDriver q₀ (Sec7.StripMark.histDriver q₀ (y 0))

theorem measurable_pastOfHist (q₀ : ℝ≥0) : Measurable (pastOfHist q₀) :=
  measurable_pi_iff.2 fun _ => (measurable_recOfDriver q₀).comp
    ((Sec7.StripMark.measurable_histDriver q₀).comp (measurable_pi_apply 0))

/-- Lemma 6.2's past (the stopped path history) read off the staged past: the measurable trace of the record driver. -/
def histOfPast (q₀ : ℝ≥0) (R : PastData 1) : Fin 1 → Hist :=
  fun _ => histOf (pathCoord fun s => LP.traceAt s (recW (R (Fin.last 0)))) (q₀ : ℝ≥0∞)

theorem measurable_recW : Measurable recW := by
  refine measurable_pi_iff.2 fun s => ?_
  exact Measurable.comp (g := fun p : LocalExt.DrivingHist 0 0 × ℝ≥0 => LocalExt.histDrv p.1 p.2)
    (f := fun r : RecData => (recHist r, s)) LocalExt.measurable_histDrv
    (measurable_recHist.prodMk measurable_const)

theorem measurable_histOfPast (q₀ : ℝ≥0) : Measurable (histOfPast q₀) := by
  refine measurable_pi_iff.2 fun _ => ?_
  have hw : Measurable fun R : PastData 1 => recW (R (Fin.last 0)) :=
    measurable_recW.comp (measurable_pi_apply _)
  have hc : Measurable fun R : PastData 1 => pathCoord fun s => LP.traceAt s (recW (R (Fin.last 0))) :=
    measurable_pi_iff.2 fun q => (LP.measurable_traceAt _).comp hw
  exact measurable_histOf.comp (measurable_const.prodMk hc)

end Maps

section Kernel

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {q₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {αc : Ω → ℝ≥0 → ℂ}

omit mΩ [StandardBorelSpace Ω] in
/-- **The first record from the stopped path history.** -/
theorem pastMap_eq_pastOfHist {ω : Ω} (h₀ : IsRegularDriver (E 0 ω)) (h₀2 : (E 0 ω).2 = ⊤) (hq₀ : 0 < q₀)
    (hα : IsGeneratingTrace (catPath (E 0 ω).1 q₀ (E 1 ω).1) ⊤ (αc ω)) :
    pastMap κ b jumps (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) E 1 ω =
      pastOfHist q₀ fun _ => histOf (pathCoord (frozenPath (αc ω) q₀)) (q₀ : ℝ≥0∞) := by
  funext i
  have hi : i = Fin.last 0 := Subsingleton.elim _ _
  subst hi
  rw [Sec7.StripDet.pastMap_one_last ω, Sec7.StripMark.recOf_of_lt (by rw [h₀2]; exact ENNReal.coe_lt_top)]
  change _ = recOfDriver q₀ _
  unfold recOfDriver
  congr 1
  funext q
  exact (histDriver_frozenPath_eq h₀ h₀2 hq₀ hα (min_le_right _ _)).symm

omit mΩ [StandardBorelSpace Ω] in
/-- **The stopped path history from the first record.** -/
theorem pastHist_eq_histOfPast {ω : Ω} (h₀ : IsRegularDriver (E 0 ω)) (h₁ : IsRegularDriver (E 1 ω))
    (h₀2 : (E 0 ω).2 = ⊤) (h₁2 : (E 1 ω).2 = ⊤)
    (hα : IsGeneratingTrace (catPath (E 0 ω).1 q₀ (E 1 ω).1) ⊤ (αc ω)) :
    (fun _ : Fin 1 => histOf (pathCoord (frozenPath (αc ω) q₀)) (q₀ : ℝ≥0∞)) =
      histOfPast q₀ (pastMap κ b jumps (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) E 1 ω) := by
  funext i
  rw [histOfPast, Sec7.StripDet.pastMap_one_last ω, histOf_pathCoord_frozenPath]
  unfold histOf
  congr 1
  funext q
  unfold stopCoord
  split_ifs with hq
  · exact (traceAt_recW_eq h₀ h₁ h₀2 h₁2 hα (ENNReal.coe_le_coe.1 hq)).symm
  · rfl

/-- **The two pasts have the same regular conditional laws.** If almost surely both pieces live forever and `αc` is a
generating trace of the concatenated driver, the staged past before the continuation (`pastSigma … 1`, the first
record) and Lemma 6.2's past (`StagedEntrance.pastSigma αc q₀`, the stopped path history) determine each other up to
null sets, so their regular conditional kernels agree almost surely. -/
theorem ae_condExpKernel_pastSigma_eq (hE : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hq₀ : 0 < q₀) (hαm : ∀ t, Measurable fun ω => αc ω t)
    (hζ : ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 q₀ (E 1 ω).1) ⊤ (αc ω)) :
    ∀ᵐ ω₀ ∂P, condExpKernel P (_root_.InteractingSLE.pastSigma κ b jumps (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) E 1)
      ω₀ = condExpKernel P (StagedEntrance.pastSigma αc q₀) ω₀ := by
  have hf : Measurable (pastMap κ b jumps (Sec7.StripSys.twoAngleSpec θ₀ q₀ θ) E 1) :=
    Measurable.of_comap_le (by rw [← pastSigma_eq_comap]; exact hE.2.1 1)
  rw [pastSigma_eq_comap]
  exact KernelTower.ae_condExpKernel_comap_eq hf (measurable_pastHist hαm) (measurable_pastOfHist q₀)
    (measurable_histOfPast q₀)
    (by filter_upwards [hζ, htr] with ω hω hα; exact pastMap_eq_pastOfHist (hreg 0 ω) hω.1 hq₀ hα)
    (by filter_upwards [hζ, htr] with ω hω hα
        exact pastHist_eq_histOfPast (hreg 0 ω) (hreg 1 ω) hω.1 hω.2 hα)

end Kernel

/-! ### The frontier of the record chart -/

section Frontier

variable {e₀ e₁ : (ℝ≥0 → ℝ) × ℝ≥0∞} {q₀ : ℝ≥0} {α : ℝ≥0 → ℂ}

/-- **The record chart's domain is the unbounded component of `ℍ ∖ α([0, q₀])`.** -/
theorem dom_recChart_eq (h₀ : IsRegularDriver e₀) (h₁ : IsRegularDriver e₁) (h₀2 : e₀.2 = ⊤) (h₁2 : e₁.2 = ⊤)
    (hα : IsGeneratingTrace (catPath e₀.1 q₀ e₁.1) ⊤ α) :
    ∃ z₀, ((recChart (recOf (q₀ : ℝ≥0∞) e₀)).dom : Set ℂ) = connectedComponentIn (H \ α '' Icc 0 q₀) z₀ := by
  have hlt : (q₀ : ℝ≥0∞) < e₀.2 := by rw [h₀2]; exact ENNReal.coe_lt_top
  have hg := Sec7.StripMark.isDrvGood_recOf_of_lt h₀ hlt
  have hW := Sec7.StripMark.recW_recOf_of_lt h₀ hlt hg
  obtain ⟨⟨z₀, -, hcomp⟩, -⟩ := hα.2.2 q₀ ENNReal.coe_lt_top
  refine ⟨z₀, ?_⟩
  rw [coe_dom_recChart, hcomp]
  have htime : rtime (recOf (q₀ : ℝ≥0∞) e₀) = (q₀ : ℝ) := by
    rw [rtime, Sec7.StripMark.recOf_of_lt hlt, ENNReal.toNNReal_coe]
  have hcat : Continuous fun s : ℝ => catPath e₀.1 q₀ e₁.1 s.toNNReal :=
    (continuous_catPath_of_regular h₀ h₁ h₀2 h₁2).comp continuous_real_toNNReal
  unfold stopHull
  rw [htime, YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_rdrv _) hcat q₀.coe_nonneg fun r hr => ?_]
  have hr' : r.toNNReal ≤ q₀ := Real.toNNReal_le_iff_le_coe.2 hr.2
  change recW (recOf (q₀ : ℝ≥0∞) e₀) r.toNNReal = _
  rw [hW, min_eq_left hr', catPath_of_le hr']

/-- **`hfr` for the record chart**: a point of `ℍ` on the frontier of the record chart's domain lies on `α([0, q₀])`. -/
theorem frontier_recChart (h₀ : IsRegularDriver e₀) (h₁ : IsRegularDriver e₁) (h₀2 : e₀.2 = ⊤) (h₁2 : e₁.2 = ⊤)
    (hα : IsGeneratingTrace (catPath e₀.1 q₀ e₁.1) ⊤ α) :
    ∀ z ∈ H, z ∈ closure ((recChart (recOf (q₀ : ℝ≥0∞) e₀)).dom : Set ℂ) →
      z ∉ (recChart (recOf (q₀ : ℝ≥0∞) e₀)).dom → z ∈ α '' Icc 0 q₀ := by
  obtain ⟨z₀, hdom⟩ := dom_recChart_eq h₀ h₁ h₀2 h₁2 hα
  have hK : IsCompact (α '' Icc 0 q₀) :=
    isCompact_Icc.image_of_continuousOn (hα.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  exact mem_of_mem_closure_dom hK.isClosed hdom

end Frontier

end Strip

end StagedEntrance

end Restart

end InteractingSLE
