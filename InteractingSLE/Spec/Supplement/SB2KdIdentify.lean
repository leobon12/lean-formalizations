/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KcDriver
import InteractingSLE.Spec.Supplement.SB2KdClock
import InteractingSLE.Spec.Supplement.SB2CondGen

/-!
# Conditional realization and the erased remainder

Canonical code agreement is the probabilistic input. A forward clock is the
geometric input. These adapters combine the two without assuming a conditional
law or a canonical-trace link for the geometric remainder.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Restart WalkInf

/-- Realize a geometric driver under the conditional laws once its canonical
code is identified in the measurable version chart. -/
theorem isCondFlowLineDriverOn_of_codeMatch
    (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)
    {Ω : Type u} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h𝒢 : 𝒢 ≤ mΩ) {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    {h : Ω → DistOn upperHalfPlaneOpens} {cw : Ω → BoundaryWord}
    (hcw : Measurable[𝒢] cw) {c : Ω → Chart} (hc : IsMeasChart 𝒢 c)
    (hcc : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀)
    (hG : ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
      ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) h' (cw ω₀).fn (cw ω₀).jumps)
    {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hWm : ∀ t, Measurable (W t)) (hVm : Measurable V)
    (hWc : ∀ ω, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < V ω})
    (hcode : ∀ᵐ ω ∂P, ω ∈ F →
      IsDriverCodeMatch (driverCode h12p hκ θ
        (cw ω, Chart.chartTransport (hc.1 ω) 1 0 (chiC κ) (h ω)))
        (fun t => W t ω) (V ω)) :
    IsCondFlowLineDriverOn κ θ 𝒢 P F h c
      (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps) W V := by
  filter_upwards [hG, hcc,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hcode,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hF,
    Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P) h𝒢 hcw]
    with ω₀ hG₀ hcc₀ hcode₀ hF₀ hcw₀ hmem
  obtain ⟨hpc, h', hct, hgff⟩ := hG₀ hmem
  refine ⟨hpc, h', hct,
    Cond.isFlowLineDriver_of_driverCodeMatch_univ h12p hκ θ h13 (cw ω₀)
      hgff hWm hVm hWc ?_⟩
  filter_upwards [hcode₀, hF₀ hmem, hcw₀, hcc₀] with ω hcodeω hFω hcwω hcω
  have hY : Chart.chartTransport (hc.1 ω) 1 0 (chiC κ) (h ω) = h' ω := by
    apply IsChartTransport.unique (hc.1 ω₀) _ (hct ω)
    rw [← hcω]
    exact CondDriverBridge.isChartTransport_chartTransport_of_continuousOn
      (hc.1 ω) (hc.2.1 ω) 1 0 (chiC κ) (h ω)
  simpa only [hcwω, hY] using hcodeω hFω

/-- A conditional flow driver with a geometric trace and clock has the source's
canonical-trace remainder link under almost every conditional law. -/
theorem ae_remainderLink_of_condDriver_trace
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {θ : ℝ}
    {Ω : Type u} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h𝒢 : 𝒢 ≤ mΩ) {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {m : Ω → ℝ}
    {bc : Ω → ℝ → ℝ} {jc : Ω → Finset ℝ}
    {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {η γ : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {L : Ω → ℝ}
    (hcond : IsCondFlowLineDriverOn κ θ 𝒢 P F h
      (fun ω => (c ω).recenter (m ω)) bc jc W V)
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀ ∧ m ω = m ω₀)
    (hreg : ∀ ω, IsRegularDriver ((fun t => W t ω), V ω))
    (hgeom : ∀ᵐ ω ∂P, ω ∈ F →
      IsGeneratingTrace (fun t => W t ω) (V ω) (γ ω) ∧
      IsRemainderLink (c ω) (η ω) (ζ ω) (L ω)
        (fun t => γ ω t + m ω) (V ω)) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      IsRemainderLink (c ω₀) (η ω) (ζ ω) (L ω)
        (fun t => GW2aSingle.chosenTrace W V ω t + m ω₀) (V ω) := by
  filter_upwards [hcond, hcc,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hgeom,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hF]
    with ω₀ hcond₀ hcc₀ hgeom₀ hF₀ hmem
  obtain ⟨-, _, -, hfl⟩ := hcond₀ hmem
  filter_upwards [GW2aSingle.ae_chosenTrace h13 hκ hfl,
    hcc₀ hmem, hgeom₀, hF₀ hmem] with ω hchosen hcm hgeomω hFω
  obtain ⟨hgen, hclock⟩ := hgeomω hFω
  rw [← hcm.1, ← hcm.2]
  apply hclock.congr_rel
  intro s hs
  rw [IsGeneratingTrace.eq_of_le hchosen.1 hgen (hreg ω).1 (hreg ω).2.1 hs.le]

end InteractingSLE.Theorem14.SB.Lv
