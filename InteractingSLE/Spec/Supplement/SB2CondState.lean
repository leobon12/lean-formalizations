/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CondGen
import InteractingSLE.Spec.Supplement.GW2aConnLaw

/-!
# The retained conditional field of a staged prefix, in the form of the generic identification

Packet PROVE-T14-SB2COND. Lemma SB2 conditions on a retained finite prefix of one staged history (SB2(1): the lower-walk
prefix `A`; SB2(2): the upper own history `A`) and reads the field in a chart of the current domain: "Retain the full
marked first history [...] At every rational ordinary time of the other history, its marked union with `A` has the
Gaussian local-set kernel" (p. 631). The two kernel hypotheses of `isCondFlowLineDriverOn_of_markedKernel` that only
concern the retained prefix — the conditional chart field (`hG`) and the kernel-almost sure constancy of the chart
(`hcc`) — are supplied, for `𝒢 = pastSigma k` and the chart of the state after `k` instructions, by GW1's staged law at
a living state (`GW2aConn.IsStateWitness`, produced for every boundary-continued program by `GW2aConn.exists_inv`):

* **`ae_ae_runChart_eq`**: the run chart after `k` instructions is kernel-almost surely constant given `pastSigma k`;
* **`ae_condChartField_of_stateWitness`**: almost surely on the living event, the field read in the frozen run chart
  of `ω₀` is, under `condExpKernel P (pastSigma k) ω₀`, the GFF of the witness word (`hG` of
  `isCondFlowLineDriverOn_of_markedKernel` with `F` the living event);
* **`exists_condChartField_of_isStagedHistory`**: for every staged history of a program rooted at `0` without the GW2
  flag (e.g. the lower walk `boundaryWalkSpec b jumps (−π/2) true`, SB2(1)'s retained prefix) and every `k`, a
  `pastSigma k`-measurable word with that conditional chart field (`GW2aConn.exists_inv` + the previous item).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Cond

open Restart Exist.StagedLaw Exist.Staged

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The chart of the state after `k` instructions. -/
def runChart (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (ω : Ω) : Chart :=
  (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1

/-- **The run chart after `k` instructions is kernel-almost surely constant given the retained past** `pastSigma k`
(`CondDriverBridge.ae_ae_run_eq_of_le`). -/
theorem ae_ae_runChart_eq (k : ℕ) (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω))
    (h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
      runChart κ b jumps spec E k ω = runChart κ b jumps spec E k ω₀ := by
  filter_upwards [CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) spec hreg h𝒢
    le_rfl] with ω₀ hω₀
  filter_upwards [hω₀] with ω hω
  simp only [runChart, hω]

/-- **The retained conditional field at a living state** (GW1's staged law, `GW2aConn.IsStateWitness`): almost
surely on the living event after `k` instructions, the witness word is piecewise constant and the field read in the
frozen run chart of `ω₀` is, under `condExpKernel P (pastSigma k) ω₀`, the GFF of the witness word. This is the
hypothesis `hG` of `isCondFlowLineDriverOn_of_markedKernel` for `𝒢 = pastSigma k`, the run chart and the living
event. -/
theorem ae_condChartField_of_stateWitness (k : ℕ) (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω))
    (h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ) {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : GW2aConn.IsStateWitness κ b jumps P h spec E k β Y) (hhm : Measurable h) :
    ∀ᵐ ω₀ ∂P, GW2aConn.IsLive (ExplState.run κ b jumps spec (fun j => E j ω₀) k) →
      IsPiecewiseConstantBoundaryData (β ω₀).fn (β ω₀).jumps ∧
      ∃ h' : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω, IsChartTransport (runChart κ b jumps spec E k ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' (β ω₀).fn (β ω₀).jumps := by
  obtain ⟨-, -, hpath, hgff⟩ := hW
  filter_upwards [hpath, hgff, ae_ae_runChart_eq (P := P) k hreg h𝒢,
    CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) spec hreg h𝒢 le_rfl,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hpath] with ω₀ hp₀ hg₀ hc₀ hrun₀ hpk₀ hl₀
  obtain ⟨hconf, hcont, -⟩ := hp₀ hl₀
  set c₀ := runChart κ b jumps spec E k ω₀ with hc₀def
  have hct₀ : ∀ f : DistOn upperHalfPlaneOpens,
      IsChartTransport c₀ 1 0 (chiC κ) f (Chart.chartTransport hconf 1 0 (chiC κ) f) := fun f =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hcont) 1 0 (chiC κ) f
  refine ⟨(β ω₀).isPiecewiseConstantBoundaryData, fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω),
    fun ω => hct₀ (h ω), ?_⟩
  refine Exist.StagedLaw.isGFFWithBoundaryData_congr_ae (hg₀ hl₀)
    ((Chart.measurable_chartTransport hconf 1 0 (chiC κ)).comp hhm) ?_
  filter_upwards [hc₀, hrun₀, hpk₀] with ω hcω hrunω hpω
  have hlω : GW2aConn.IsLive (ExplState.run κ b jumps spec (fun j => E j ω) k) := by rw [hrunω]; exact hl₀
  obtain ⟨-, -, hYω⟩ := hpω hlω
  have hYω' : IsChartTransport c₀ 1 0 (chiC κ) (h ω) (Y ω) := by
    have e : (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 = c₀ := hcω
    rw [← e]
    exact hYω
  exact IsChartTransport.unique hconf hYω' (hct₀ (h ω))

/-- **The retained conditional field of every GW1-type staged prefix** (`GW2aConn.exists_inv`, Lemma GW1's
classification at a living state, followed by `ae_condChartField_of_stateWitness`): for a staged history of a program
rooted at `0` without the GW2 flag, with drivers regular at every sample, and every `k`, there is a
`pastSigma k`-measurable boundary word `β` such that, almost surely on the living event after `k` instructions, the
field read in the frozen run chart is, under `condExpKernel P (pastSigma k) ω₀`, the GFF of `β ω₀`. -/
theorem exists_condChartField_of_isStagedHistory (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hgw : spec.2.1 = false) (hx₀ : spec.1 = 0)
    (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∃ β : Ω → BoundaryWord, Measurable[pastSigma κ b jumps spec E k] β ∧
      ∀ᵐ ω₀ ∂P, GW2aConn.IsLive (ExplState.run κ b jumps spec (fun j => E j ω₀) k) →
        IsPiecewiseConstantBoundaryData (β ω₀).fn (β ω₀).jumps ∧
        ∃ h' : Ω → DistOn upperHalfPlaneOpens,
          (∀ ω, IsChartTransport (runChart κ b jumps spec E k ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' (β ω₀).fn (β ω₀).jumps := by
  obtain ⟨-, -, βt, Yt, -, hWt, -⟩ := GW2aConn.exists_inv hκ hb hh hgw hx₀ hE hreg k
  exact ⟨βt, hWt.1, ae_condChartField_of_stateWitness k (fun j _ => hreg j) (hE.2.1 k) hWt hh.1⟩

end InteractingSLE.Theorem14.SB.Cond
