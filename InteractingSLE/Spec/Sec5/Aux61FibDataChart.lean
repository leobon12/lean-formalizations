/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibDataClock
import InteractingSLE.Spec.Restart.ChartMeas
import InteractingSLE.Spec.Sec5.Aux61FibAssembly
import InteractingSLE.Spec.Sec7.Lemma71KData

/-!
# The glued-space fibre objects, II: the chart path, the chart field and the code of a restart

Packet PROVE-AUX61-FIBDATA (piece (G) of `planning/handoffs/PROVE-AUX61-FIB.md`). On any measurable space `X` (the
glued space), a **random chart** `c : X → Chart` (measurable in the sense of
`Aux61Restart.HasOriginalTargetRestartChart`:
domain events and the indicator-extended forward map and lift are measurable — `IsMeasChart`) and a **random physical
path** `ρ` on a finite random interval `[0, U]` (the restarted flow line `η(t + ·)`) give:

* `chartOf E c` (`c` on the event `E`, `Chart.id` off it): conformal and measurable everywhere;
* **`chartPath E c ρ U x u = lim_{z → ρ x (min u (U x)), z ∈ dom} fwd z`** (`0` off `E`): measurable at every time
  (`IsChartPathSpec.measurable_chartPath`, through `Restart.measurable_of_tendsto_nhdsWithin`), and on `E` the given
  continuous chart limit path (`chartPath_eq`); hence `IsPathSpec` (`IsChartPathSpec.isPathSpec`) and the capacity-time
  reading of `Aux61FibDataClock`;
* **`chartFieldOf E c a k h x`**, the field read in the chart, `h ∘ ψ + a + k · lift ∘ ψ` (`Lemma71K.chartField`),
  measurable (`measurable_chartFieldOf`, through `Chart.measurable_chartTransport_random'`);
* **`rsCode E c ρ U a k h`** `= fibRead (chartFieldOf …) (capPath …) (capEnd …)`: **the code `Y` of the restart**, a
  measurable map to `Aux61Fib.FibCode` (`measurable_rsCode`) whose decoded field, trace and lifetime are the chart
  field,
  the chart path in relative capacity time and its capacity lifetime (`rsCode_field`, `rsCode_trace`, `rsCode_life`).

The spec `IsChartPathSpec` lists the pathwise facts (chart limits along a continuous path from `0`) as hypotheses on the
explicit objects; it is discharged on the glued space from the restart chart's geometry. Generic: no glued space, no
source statement replaced. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.Aux61FibData

open Restart

variable {X : Type*} [MeasurableSpace X]

/-! ### Measurable random charts -/

/-- **A measurable random chart**: the domain events and the indicator-extended forward map and lift are measurable
(the measurability clauses of `Aux61Restart.HasOriginalTargetRestartChart`). -/
structure IsMeasChart (c : X → Chart) : Prop where
  dom : ∀ z, MeasurableSet {x | z ∈ (c x).dom}
  fwd : ∀ z, Measurable ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z)
  lift : ∀ z, Measurable ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z)

open scoped Classical in
/-- The chart on the event `E`, the identity chart off it. -/
def chartOf (E : Set X) (c : X → Chart) (x : X) : Chart := if x ∈ E then c x else Chart.id

omit [MeasurableSpace X] in
theorem chartOf_of_mem {E : Set X} {c : X → Chart} {x : X} (hx : x ∈ E) : chartOf E c x = c x := by
  simp [chartOf, hx]

omit [MeasurableSpace X] in
theorem chartOf_of_notMem {E : Set X} {c : X → Chart} {x : X} (hx : x ∉ E) : chartOf E c x = Chart.id := by
  simp [chartOf, hx]

theorem coe_dom_id : ((Chart.id : Chart).dom : Set ℂ) = H := by
  rw [Chart.isConformal_id.coe_dom]
  exact image_id' H

omit [MeasurableSpace X] in
/-- The chart of the event is conformal everywhere. -/
theorem isConformal_chartOf {E : Set X} {c : X → Chart} (hconf : ∀ x ∈ E, (c x).IsConformal) (x : X) :
    (chartOf E c x).IsConformal := by
  by_cases hx : x ∈ E
  · rw [chartOf_of_mem hx]; exact hconf x hx
  · rw [chartOf_of_notMem hx]; exact Chart.isConformal_id

/-- The chart of a measurable event is a measurable random chart. -/
theorem IsMeasChart.chartOf {E : Set X} (hE : MeasurableSet E) {c : X → Chart} (hc : IsMeasChart c) :
    IsMeasChart (chartOf E c) := by
  classical
  have hdom : ∀ z, {x | z ∈ (Aux61FibData.chartOf E c x).dom} = (E ∩ {x | z ∈ (c x).dom}) ∪ (Eᶜ ∩ {_x | z ∈ H}) := by
    intro z; ext x
    by_cases hx : x ∈ E
    · simp [chartOf_of_mem hx, hx]
    · simp only [mem_ofPred_eq, chartOf_of_notMem hx, mem_union, mem_inter_iff, hx, false_and, mem_compl_iff,
        not_false_eq_true, true_and, false_or]
      rw [← SetLike.mem_coe, coe_dom_id]
  have hdm : ∀ z, MeasurableSet {x | z ∈ (Aux61FibData.chartOf E c x).dom} := fun z => by
    rw [hdom z]
    exact (hE.inter (hc.dom z)).union (hE.compl.inter (MeasurableSet.const _))
  refine ⟨hdm, fun z => ?_, fun z => ?_⟩
  · have e : ({x | z ∈ (Aux61FibData.chartOf E c x).dom}.indicator fun x => (Aux61FibData.chartOf E c x).1 z) =
        E.piecewise ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z) (fun _ => if z ∈ H then z else 0) := by
      funext x
      by_cases hx : x ∈ E
      · simp [Set.indicator, Set.piecewise, chartOf_of_mem hx, hx]
      · have hz : z ∈ (Chart.id : Chart).dom ↔ z ∈ H := by rw [← SetLike.mem_coe, coe_dom_id]
        simp only [Set.indicator, Set.piecewise, mem_ofPred_eq, chartOf_of_notMem hx, hx, ite_false, hz]
        split_ifs <;> rfl
    rw [e]
    exact (hc.fwd z).piecewise hE measurable_const
  · have e : ({x | z ∈ (Aux61FibData.chartOf E c x).dom}.indicator fun x => (Aux61FibData.chartOf E c x).2.2 z) =
        E.piecewise ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z) (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ E
      · simp [Set.indicator, Set.piecewise, chartOf_of_mem hx, hx]
      · simp [Set.indicator, Set.piecewise, chartOf_of_notMem hx, hx, Chart.id]
    rw [e]
    exact (hc.lift z).piecewise hE measurable_const

/-! ### The chart path -/

open scoped Classical in
/-- **The chart path** of the physical path `ρ` on `[0, U]` (time clamped; `0` off `E`): the forward-chart limit at the
path point along the chart domain. -/
def chartPath (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (U : X → ℝ≥0) (x : X) (u : ℝ≥0) : ℂ :=
  if x ∈ E then limUnder (𝓝[((c x).dom : Set ℂ)] (ρ x (min u (U x)))) (c x).1 else 0

/-- **The chart-path data**: measurability (event, end time, path at each time, the random chart) and, on the event,
chart limits at every path point along one continuous path from `0` (the chart path). -/
structure IsChartPathSpec (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (U : X → ℝ≥0) : Prop where
  measurableSet : MeasurableSet E
  measU : Measurable U
  measρ : ∀ u, Measurable fun x => ρ x u
  contρ : ∀ x ∈ E, ContinuousOn (ρ x) (Iic (U x))
  chart : IsMeasChart c
  mem : ∀ x ∈ E, ∀ u : ℝ≥0, u ≤ U x → ρ x u ∈ closure ((c x).dom : Set ℂ)
  path : ∀ x ∈ E, ∃ γ₀ : ℝ≥0 → ℂ, ContinuousOn γ₀ (Iic (U x)) ∧ γ₀ 0 = 0 ∧
    ∀ u : ℝ≥0, u ≤ U x → Tendsto (c x).1 (𝓝[((c x).dom : Set ℂ)] (ρ x u)) (𝓝 (γ₀ u))

namespace IsChartPathSpec

variable {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {U : X → ℝ≥0} (hs : IsChartPathSpec E c ρ U)
include hs

/-- On the event the chart path is the chart limit path. -/
theorem chartPath_eq {x : X} (hx : x ∈ E) {γ₀ : ℝ≥0 → ℂ}
    (hγ₀ : ∀ u : ℝ≥0, u ≤ U x → Tendsto (c x).1 (𝓝[((c x).dom : Set ℂ)] (ρ x u)) (𝓝 (γ₀ u))) {u : ℝ≥0}
    (hu : u ≤ U x) : chartPath E c ρ U x u = γ₀ u := by
  have hne : (𝓝[((c x).dom : Set ℂ)] (ρ x u)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hs.mem x hx u hu)
  simp only [chartPath, hx, ite_true, min_eq_left hu]
  exact (hγ₀ u hu).limUnder_eq

/-- The forward-chart limit at the clamped path point exists on the event. -/
theorem tendsto_chartPath {x : X} (hx : x ∈ E) (u : ℝ≥0) :
    Tendsto (c x).1 (𝓝[((c x).dom : Set ℂ)] (ρ x (min u (U x)))) (𝓝 (chartPath E c ρ U x u)) := by
  obtain ⟨γ₀, -, -, hγ₀⟩ := hs.path x hx
  have hu : min u (U x) ≤ U x := min_le_right _ _
  have h := hγ₀ _ hu
  have heq : chartPath E c ρ U x u = γ₀ (min u (U x)) := by
    have hne : (𝓝[((c x).dom : Set ℂ)] (ρ x (min u (U x)))).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 (hs.mem x hx _ hu)
    simp only [chartPath, hx, ite_true]
    exact h.limUnder_eq
  rw [heq]
  exact h

/-- **The chart path is measurable** at every time. -/
theorem measurable_chartPath (u : ℝ≥0) : Measurable fun x => chartPath E c ρ U x u := by
  classical
  have hcm := hs.chart.chartOf hs.measurableSet
  set q : X → ℂ := fun x => if x ∈ E then ρ x (min u (U x)) else 0 with hq
  have hqm : Measurable q :=
    measurable_piecewise_eval hs.measurableSet hs.measρ (s := fun x => min u (U x))
      (measurable_const.min hs.measU) fun x hx => (hs.contρ x hx).mono (Iic_subset_Iic.2 (min_le_right _ _))
  have hDo : ∀ x, IsOpen ((chartOf E c x).dom : Set ℂ) := fun x => (chartOf E c x).dom.isOpen
  have hqD : ∀ x, q x ∈ closure ((chartOf E c x).dom : Set ℂ) := fun x => by
    by_cases hx : x ∈ E
    · simp only [hq, hx, ite_true, chartOf_of_mem hx]
      exact hs.mem x hx _ (min_le_right _ _)
    · simp only [hq, hx, ite_false, chartOf_of_notMem hx, coe_dom_id, closure_H]
      show (0 : ℂ).im ≥ 0
      simp
  have hlim : ∀ x, Tendsto (chartOf E c x).1 (𝓝[((chartOf E c x).dom : Set ℂ)] (q x))
      (𝓝 (chartPath E c ρ U x u)) := fun x => by
    by_cases hx : x ∈ E
    · simp only [hq, hx, ite_true, chartOf_of_mem hx]
      exact hs.tendsto_chartPath hx u
    · simp only [hq, hx, ite_false, chartOf_of_notMem hx, chartPath]
      exact tendsto_id.mono_left nhdsWithin_le_nhds
  exact measurable_of_tendsto_nhdsWithin hDo hcm.dom hcm.fwd hqm hqD hlim

/-- **The chart path is a path spec**: `IsPathSpec E (chartPath E c ρ U) U`. -/
theorem isPathSpec : IsPathSpec E (chartPath E c ρ U) U := by
  refine ⟨hs.measurableSet, hs.measU, hs.measurable_chartPath, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨γ₀, hγc, -, hγ₀⟩ := hs.path x hx
    exact hγc.congr fun u hu => hs.chartPath_eq hx hγ₀ hu
  · obtain ⟨γ₀, -, h0, hγ₀⟩ := hs.path x hx
    rw [hs.chartPath_eq hx hγ₀ zero_le, h0]

end IsChartPathSpec

/-! ### The chart field -/

/-- **The field read in the chart**: `h ∘ ψ + a + k · lift ∘ ψ` for the chart of the event (`Lemma71K.chartField`). -/
def chartFieldOf (E : Set X) (c : X → Chart) (a k : ℝ) (h : X → DistOn upperHalfPlaneOpens) (x : X) :
    DistOn upperHalfPlaneOpens :=
  Sec7.Lemma71K.chartField (chartOf E c x) a k (h x)

/-- **The chart field is measurable** (a measurable random chart with continuous lifts transports a measurable field
measurably). -/
theorem measurable_chartFieldOf {E : Set X} (hE : MeasurableSet E) {c : X → Chart} (hc : IsMeasChart c)
    (hconf : ∀ x ∈ E, (c x).IsConformal) (hliftc : ∀ x ∈ E, ContinuousOn (c x).2.2 (c x).dom)
    {h : X → DistOn upperHalfPlaneOpens} (hh : Measurable h) (a k : ℝ) :
    Measurable (chartFieldOf E c a k h) := by
  classical
  have hcm := hc.chartOf hE
  have hconf' := isConformal_chartOf hconf
  have hlc : ∀ x, ContinuousOn (chartOf E c x).2.2 (chartOf E c x).dom := fun x => by
    by_cases hx : x ∈ E
    · rw [chartOf_of_mem hx]; exact hliftc x hx
    · rw [chartOf_of_notMem hx]; exact continuousOn_const
  have e : chartFieldOf E c a k h = fun x => Chart.chartTransport (hconf' x) 1 a k (h x) := by
    funext x
    simp only [chartFieldOf, Sec7.Lemma71K.chartField, hconf' x, ↓reduceDIte]
  rw [e]
  exact Chart.measurable_chartTransport_random' hconf' hcm.dom hcm.fwd hcm.lift hlc hh 1 a k

/-! ### The code of a restart -/

/-- **The code of a restart** (`Y` of the glued-space fibres): the chart field, the chart path in relative capacity
time, and its capacity lifetime. -/
def rsCode (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (U : X → ℝ≥0) (a k : ℝ)
    (h : X → DistOn upperHalfPlaneOpens) (x : X) : Aux61Fib.FibCode :=
  Aux61Fib.fibRead (chartFieldOf E c a k h) (capPath E (chartPath E c ρ U) U) (capEnd E (chartPath E c ρ U) U) x

section Code

variable {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {U : X → ℝ≥0} {a k : ℝ}
  {h : X → DistOn upperHalfPlaneOpens}

omit [MeasurableSpace X] in
theorem rsCode_field (x : X) : (rsCode E c ρ U a k h x).field = chartFieldOf E c a k h x := rfl

omit [MeasurableSpace X] in
theorem rsCode_life (x : X) : (rsCode E c ρ U a k h x).life = capEnd E (chartPath E c ρ U) U x := rfl

variable (hs : IsChartPathSpec E c ρ U) (hclk : ∀ x ∈ E, IsClockOn (chartClock (chartPath E c ρ U x)) (U x))
include hs hclk

/-- **The code of a restart is measurable.** -/
theorem measurable_rsCode (hconf : ∀ x ∈ E, (c x).IsConformal)
    (hliftc : ∀ x ∈ E, ContinuousOn (c x).2.2 (c x).dom) (hh : Measurable h) :
    Measurable (rsCode E c ρ U a k h) :=
  Aux61Fib.measurable_fibRead (measurable_chartFieldOf hs.measurableSet hs.chart hconf hliftc hh a k)
    (hs.isPathSpec.measurable_capEnd hclk) hs.isPathSpec.measurable_capPath
    (hs.isPathSpec.continuousOn_capPath hclk) (hs.isPathSpec.capPath_zero hclk)

/-- **Decoding the code returns the chart path in capacity time** on its closed lifetime. -/
theorem rsCode_trace (x : X) {u : ℝ≥0} (hu : (u : ℝ≥0∞) ≤ capEnd E (chartPath E c ρ U) U x) :
    (rsCode E c ρ U a k h x).trace u = capPath E (chartPath E c ρ U) U x u :=
  Aux61Fib.fibRead_trace (hs.isPathSpec.measurable_capEnd hclk) hs.isPathSpec.measurable_capPath
    (hs.isPathSpec.continuousOn_capPath hclk) (hs.isPathSpec.capPath_zero hclk) x hu

end Code

end InteractingSLE.Sec5.Aux61FibData
