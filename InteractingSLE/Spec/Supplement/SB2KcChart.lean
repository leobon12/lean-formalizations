/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KcPartition
import InteractingSLE.Spec.Supplement.SB2KEntry

/-!
# K2's conditional chart field with countably many force types

The countable-profile stage witness is converted to a field read through the
fixed launch chart under the conditional law. Recentering it at any measurable
entry preserves the countable profile cover. This supplies `hG` and the
countable type cover for the same word, rather than unrelated witnesses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw WalkInf Supp8.Q3Stop

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
  [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The stage-witness field, frozen in the launch sample's chart, has the
conditional GFF law of that same witness's word. -/
theorem ae_condChartField_of_stageWitness (k : ℕ)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ)
    {β : Ω → Restart.BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y) (hhm : Measurable h) :
    ∀ᵐ ω₀ ∂P,
      (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
      ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (Cond.runChart κ b jumps spec E k ω₀) 1 0 (chiC κ)
          (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)
          h' (β ω₀).fn (β ω₀).jumps := by
  have hpath := hW.2.2.1
  filter_upwards [hpath, hW.2.2.2,
    Cond.ae_ae_runChart_eq (P := P) k (fun j _ => hreg j) h𝒢,
    CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b)
      (jumps := jumps) spec (fun j _ => hreg j) h𝒢 le_rfl,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hpath]
      with ω₀ hp₀ hg₀ hc₀ hrun₀ hpk₀ hl₀
  obtain ⟨hconf, hcont, -⟩ := hp₀ hl₀
  have hct₀ : ∀ f : DistOn upperHalfPlaneOpens,
      IsChartTransport (Cond.runChart κ b jumps spec E k ω₀) 1 0 (chiC κ) f
        (Chart.chartTransport hconf 1 0 (chiC κ) f) := fun f =>
    Chart.isChartTransport_chartTransport hconf
      (Chart.locallyIntegrableOn_of_continuousOn hcont) 1 0 (chiC κ) f
  refine ⟨fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω),
    fun ω => hct₀ (h ω), ?_⟩
  refine isGFFWithBoundaryData_congr_ae (hg₀ hl₀)
    ((Chart.measurable_chartTransport hconf 1 0 (chiC κ)).comp hhm) ?_
  filter_upwards [hc₀, hrun₀, hpk₀] with ω hcω hrunω hpω
  have hlω : (ExplState.run κ b jumps spec (fun j => E j ω)
      (k + 1)).2.2.2.1 k ≠ none := by
    rw [launches_run_succ_of_run_eq spec hrunω]
    exact hl₀
  obtain ⟨-, -, hYω⟩ := hpω hlω
  have hYω' : IsChartTransport (Cond.runChart κ b jumps spec E k ω₀) 1 0
      (chiC κ) (h ω) (Y ω) := by
    rw [← hcω]
    exact hYω
  exact IsChartTransport.unique hconf hYω' (hct₀ (h ω))

/-- K2's `hG` and a countable force-type cover for the same conditional word,
in the version chart recentered at a past-measurable entry. -/
theorem exists_k2Word_countable_types (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) (θ : ℝ) {m : Ω → ℝ}
    (hm : Measurable[pastSigma κ b jumps spec E k] m) :
    ∃ (cw : Ω → Restart.BoundaryWord) (T : Set WordType),
      Measurable[pastSigma κ b jumps spec E k] cw ∧ T.Countable ∧
      (∀ᵐ ω ∂P,
        (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
          angleWordType κ θ (cw ω) ∈ T) ∧
      ∀ᵐ ω₀ ∂P,
        (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
        IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
        ∃ h' : Ω → DistOn upperHalfPlaneOpens,
          (∀ ω, IsChartTransport ((verChart κ b jumps spec E k ω₀).recenter (m ω₀))
            1 0 (chiC κ) (h ω) (h' ω)) ∧
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀)
            h' (cw ω₀).fn (cw ω₀).jumps := by
  obtain ⟨β, Y, T, hW, hT, hcw, hcover⟩ :=
    exists_stageWitness_countable_types hκ hb hh hE hreg k θ hm
  refine ⟨fun ω => BoundaryWord.shiftW (m ω) (β ω), T, hcw, hT, hcover, ?_⟩
  have hG := ae_condChartField_of_stageWitness k hreg (hE.2.1 k) hW hh.1
  filter_upwards [hG, ae_verChart_eq_runChart hR hreg k, hW.2.2.1]
    with ω₀ hG₀ hver hp hlaunch
  obtain ⟨h', hct, hgff⟩ := hG₀ hlaunch
  obtain ⟨hc, hlc, -⟩ := hp hlaunch
  have hc' := hc.recenter (m ω₀)
  have hT' : ∀ ω, IsChartTransport ((Cond.runChart κ b jumps spec E k ω₀).recenter (m ω₀))
      1 0 (chiC κ) (h ω) (Chart.chartTransport hc' 1 0 (chiC κ) (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport hc'
      (Chart.locallyIntegrableOn_of_continuousOn (Chart.continuousOn_recenter_lift hlc))
      1 0 (chiC κ) (h ω)
  have he : (fun ω => Chart.chartTransport hc' 1 0 (chiC κ) (h ω)) =
      fun ω => Exist.flowField (m ω₀) 0 (h' ω) :=
    funext fun ω => eq_flowField_of_recenter hc hlc (hct ω) (hT' ω)
  refine ⟨(BoundaryWord.shiftW (m ω₀) (β ω₀)).isPiecewiseConstantBoundaryData,
    fun ω => Chart.chartTransport hc' 1 0 (chiC κ) (h ω), ?_, ?_⟩
  · rw [hver]
    exact hT'
  · rw [he, BoundaryWord.jumps_shiftW,
      show (BoundaryWord.shiftW (m ω₀) (β ω₀)).fn =
        fun y => (β ω₀).fn (y + m ω₀) from funext (BoundaryWord.fn_shiftW _ _)]
    exact Supp9.IsGFFWithBoundaryData.recenter (β ω₀).isPiecewiseConstantBoundaryData
      (m ω₀) hgff

end InteractingSLE.Theorem14.SB.Lv
