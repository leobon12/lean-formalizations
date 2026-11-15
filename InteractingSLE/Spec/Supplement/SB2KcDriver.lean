/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KcLaunch

/-!
# A canonical conditional driver in the SB2 launch chart

The existing conditional-driver construction for staged histories applies to
any conditional chart field indexed by a standard Borel past record. Thus the
existence of the driver in clause (1) follows directly from the chart-field
law and Theorems 1.2--1.3. Identifying this candidate with the actual erased
upper flow, including its lifetime, remains the separate clause (3) of SB2.
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

open Exist.Staged Exist.StagedLaw WalkInf

/-- A conditional chart GFF admits one measurable, everywhere regular canonical
conditional driver. This is the existing staged construction with the boundary
word factored through its past record by Doob--Dynkin. -/
theorem exists_condFlowLineDriverOn_of_chartField
    (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
    {r : Ω → R} (hr : Measurable r) {F : Set Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {cw : Ω → Restart.BoundaryWord}
    (hcw : Measurable[MeasurableSpace.comap r inferInstance] cw)
    {c : Ω → Chart} (hc : IsMeasChart (MeasurableSpace.comap r inferInstance) c)
    (hcc : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P
      (MeasurableSpace.comap r inferInstance) ω₀), c ω = c ω₀)
    (hG : ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
      ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P
          (MeasurableSpace.comap r inferInstance) ω₀) h' (cw ω₀).fn (cw ω₀).jumps) :
    ∃ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      Measurable D ∧ (∀ ω, IsRegularDriver (D ω)) ∧
      IsCondFlowLineDriverOn κ θ (MeasurableSpace.comap r inferInstance) P F h c
        (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps)
        (fun t ω => (D ω).1 t) (fun ω => (D ω).2) := by
  obtain ⟨β, hβm, hβ⟩ := hcw.exists_eq_measurable_comp
  have hcm := hc.mono hr.comap_le
  let Y : Ω → DistOn upperHalfPlaneOpens :=
    fun ω => Chart.chartTransport (hc.1 ω) 1 0 (chiC κ) (h ω)
  have hYm : Measurable Y :=
    Chart.measurable_chartTransport_random' hc.1 hcm.2.2.2.1 hcm.2.2.2.2.1
      hcm.2.2.2.2.2.2 hc.2.1 hhm 1 0 (chiC κ)
  obtain ⟨D, hDm, hDreg, hD⟩ := exists_flowDrv_condKernel (P := P) h12p h13 hκ hr
    (fun x => ((β x).fn, (β x).jumps)) θ
    (wordMeasStatement.1.comp hβm) (wordMeasStatement.2.1.comp hβm)
    ((wordMeasStatement.2.2 κ θ).comp hβm) hYm
  refine ⟨D, hDm, hDreg, ?_⟩
  filter_upwards [hG, hcc, hD] with ω₀ hG₀ hcc₀ hD₀ hF
  obtain ⟨hpc, h', hct, hgff⟩ := hG₀ hF
  have hYh : ∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap r inferInstance) ω₀),
      Y ω = h' ω := by
    filter_upwards [hcc₀] with ω hcω
    have ht : IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (Y ω) := by
      rw [← hcω]
      exact CondDriverBridge.isChartTransport_chartTransport_of_continuousOn
        (hc.1 ω) (hc.2.1 ω) 1 0 (chiC κ) (h ω)
    exact IsChartTransport.unique (hc.1 ω₀) ht (hct ω)
  have he : β (r ω₀) = cw ω₀ := (congrFun hβ ω₀).symm
  refine ⟨hpc, h', hct, ?_⟩
  simpa only [he] using hD₀ h' (he.symm ▸ hpc) hYh (he.symm ▸ hgff)

/-- Clause (1) of `SB2DriverLinkAmbStatement` at every launch after the first:
a canonical conditional driver exists in the actual entry chart. This asserts
no relation between its trace and an erased upper flow. -/
theorem exists_condFlowLineDriverOn_launch
    (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {w : ExplSpec}
    (hw : w = boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (hS : IsStagedHistory κ b jumps P h w (E w))
    (hR : StagedPiecesRegular κ b jumps P w (E w))
    (hreg : ∀ j ω, IsRegularDriver (E w j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps →
      b t + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (k : ℕ) (θ : ℝ) {u : ℝ} (hu : u ≤ 0) :
    ∃ (cw : Ω → Restart.BoundaryWord) (D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
      Measurable[pastSigma κ b jumps w (E w) (k + 1)] cw ∧
      Measurable D ∧ (∀ ω, IsRegularDriver (D ω)) ∧
      IsCondFlowLineDriverOn κ θ (pastSigma κ b jumps w (E w) (k + 1)) P
        (launchSet κ b jumps E (k + 1)) h
        (fun ω => (launchChart κ b jumps E (k + 1) ω).recenter
          (launchEntry κ b jumps E (k + 1) u ω))
        (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps)
        (fun t ω => (D ω).1 t) (fun ω => (D ω).2) := by
  obtain ⟨m, cw, _, hm, hcw, hmc, heq, hG, hcc, -⟩ :=
    exists_k2Launch_countable_types hκ hb hh hw hS hR hreg hamb k θ hu
  have hr := measurable_pastMap (κ := κ) runMeasStatement hb w
    (fun j _ => hS.1 j) (fun j _ => hreg j) (k + 1) le_rfl
  obtain ⟨D, hDm, hDreg, hD⟩ := exists_condFlowLineDriverOn_of_chartField
    h12p h13 hκ θ hr hh.1 hcw hmc hcc hG
  refine ⟨cw, D, hcw, hDm, hDreg, hD.congr_chart ?_⟩
  exact heq.mono fun ω he hF => ⟨(he hF).symm, rfl, rfl⟩

end InteractingSLE.Theorem14.SB.Lv
