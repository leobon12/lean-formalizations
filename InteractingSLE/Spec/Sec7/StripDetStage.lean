/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripDet
import InteractingSLE.Spec.Exist.StagedLawMain

/-!
# A launched piece of a staged history is field-determined when the stage word satisfies (4.4)

Packet PROVE-STRIPSYS21, item (i) (ruling R48). The R48-safe form of the determination step of a staged history
(PROVE-T14-SB7's `ae_recOf_eq_stageRec` uses `Theorem12ParamStatement` and Theorem 1.3, allowed for Theorem 1.4 only):

* **`ae_stageDrv_eq`**: for a staged history of a GFF and a stage witness `(β, Y)` at instruction `k` (PROVE-STAGEDLAW's
  `StageLaw` body: `β` read off the retained past, `Y` the field read in the launch chart, a GFF with the data of `β`
  under the regular conditional law given the retained past), if almost surely at a launch the angle-`θ_k` flow-line
  word of `β` satisfies (4.4), then almost surely at a launch the lifetime is infinite and the launched driver and its
  lifetime are `AdmCode.admDrv (β, Y)` before the lifetime. Inputs: the word-measurable Theorem 1.2 on (4.4) words
  (`AdmCode.Theorem12ParamCond44Statement`, proved from the §4.2 reference), no Theorem 1.2/1.3.

Proof: under `condExpKernel P (pastSigma k) ω₀` the staged history makes the piece the flow-line driver of the
chart field `h'` of some piecewise-constant data; `h'` is the field `Y` almost surely (both are the chart transport of
`h` by the chart of `ω₀`, which the kernel does not move: `ae_ae_run_eq`), so it is a GFF with the data of `β ω₀` and
the piece is its flow-line driver for that word (`isFlowLineDriver_word`); then
`AdmCode.ae_admDrv_eq_of_ae_condExpKernel`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripDet

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw AdmCode

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A launched piece is field-determined when its stage word satisfies (4.4)** (R48-safe). -/
theorem ae_stageDrv_eq (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hβ : Measurable[pastSigma κ b jumps spec E k] β) (hY : Measurable Y)
    (hpath : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1 w)) QuantumZipper.H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 1 0 (QuantumZipper.chiC κ)
        (h ω) (Y ω))
    (hker : ∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) Y (β ω₀).fn (β ω₀).jumps)
    (h44w : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      Sec4.Cond44 κ (flowLineRhoL κ (β ω).fn (β ω).jumps 0 (instrAngle spec k))
        (flowLineRhoR κ (β ω).fn (β ω).jumps 0 (instrAngle spec k))) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → (E k ω).2 = ⊤ ∧
      (admDrv h44 hκ hκ4 (instrAngle spec k) (β ω, Y ω)).2 = (E k ω).2 ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < (E k ω).2 → (admDrv h44 hκ hκ4 (instrAngle spec k) (β ω, Y ω)).1 t = (E k ω).1 t := by
  have hB := runMeasStatement.{u}
  have hEm : ∀ j < k, Measurable (E j) := fun j _ => hE.1 j
  have hreg' : ∀ j < k, ∀ ω, IsRegularDriver (E j ω) := fun j _ => hreg j
  have hpm : Measurable (pastMap κ b jumps spec E k) := measurable_pastMap hB hb spec hEm hreg' k le_rfl
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hLm : MeasurableSet {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    measurableSet_launch_self hB hb hEm hreg'
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps spec E k]
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
    measurableSet_pastSigma_of_run hB hb spec hEm hreg' hLm fun ω ω' he hω => by
      change (ExplState.run κ b jumps spec (fun j => E j ω') (k + 1)).2.2.2.1 k ≠ none
      rw [← launches_run_succ_of_run_eq spec he]
      exact hω
  have hW : ∀ t, Measurable fun ω => (E k ω).1 t := fun t =>
    (measurable_pi_apply t).comp (measurable_fst.comp (hE.1 k))
  have hL : Measurable fun ω => (E k ω).2 := measurable_snd.comp (hE.1 k)
  have hWc : ∀ ω, ContinuousOn (fun t => (E k ω).1 t) {t | (t : ℝ≥0∞) < (E k ω).2} := fun ω => (hreg k ω).1
  refine ae_admDrv_eq_of_ae_condExpKernel h44 hκ hκ4 (instrAngle spec k) h𝒢 hL𝒢 hβ hY hW hL hWc ?_
  filter_upwards [hE.2.2.2 k, hker, h44w, hpath, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hpath,
    ae_ae_run_eq hB hb spec hEm hreg' (P := P)] with ω₀ hstg hk₀ h44₀ hp₀ hpK hrunK hl
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨hspec, -, hc⟩ := eq_launch_of_launches spec _ hcθ
  have hθ : instrAngle spec k = θ := by unfold instrAngle; rw [hspec]
  obtain ⟨b', J', h', hb', hT', hfl⟩ := hstg c θ hcθ
  obtain ⟨hconf, hlift, -⟩ := hp₀ hl
  rw [← hc] at hconf hlift
  have hh'e : h' = fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) :=
    funext fun ω => (hT' ω).eq_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift)
  have hh'm : Measurable h' := by
    rw [hh'e]; exact (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
  have hYh' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), h' ω = Y ω := by
    filter_upwards [hpK, hrunK] with ω hpω hrω
    have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq spec hrω]; exact hl
    obtain ⟨-, -, hT⟩ := hpω hlω
    rw [hrω, ← hc] at hT
    exact IsChartTransport.unique hconf (hT' ω) hT
  have hG : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' (β ω₀).fn
      (β ω₀).jumps := isGFFWithBoundaryData_congr_ae (hk₀ hl) hh'm (hYh'.mono fun ω hω => hω.symm)
  refine ⟨h44₀ hl, h', hYh', ?_⟩
  rw [hθ]
  exact isFlowLineDriver_word hκ hG hb' hfl

end StripDet

end Sec7

end InteractingSLE
