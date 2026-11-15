/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibDataGood
import InteractingSLE.Spec.Sec5.Aux61FibDisint

/-!
# The glued-space fibre objects, IV: the exit time of a restart from its window

Packet PROVE-AUX61-FIBDATA (the clock `e` of piece (G), `planning/handoffs/PROVE-AUX61-FIB.md`). The restarted path
`ρ` runs in the chart domain until it first meets a closed random set `F` (the retained boundary `K ∪ ℝ`): before the
**hitting time** `hitTime ρ F` its chart image `inPath` is the forward chart at the path point (`0` at the start).
The clock of the restart is the **first exit of the chart image from the window `V`**, capped at the hitting time:

* `hitTime ρ F x = inf {u | ρ x u ∈ F x}` is measurable (`measurable_hitTime`, a countable description of visits to
  a random closed set, as `Aux61Fib.visit_closed_iff`);
* `inPath E c ρ T x u` (the chart image before `T`) is continuous on `[0, T)` and measurable at every time;
* **`exitTime E c ρ T V x = sup {a ∈ ℚ≥0 | a < T x, inPath x ([0, a]) ⊆ V}`** is measurable (`measurable_exitTime`);
  before it the chart image is in `V`, and it is the first exit from `V` when it comes before `T`
  (`inPath_mem_of_lt_exitTime`, `inPath_exitTime_notMem`).

Generic (any measurable space, random chart, path and closed set). R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61FibData

open Restart

variable {X : Type*} [MeasurableSpace X]

/-! ### The hitting time of a random closed set -/

/-- **The first time the path meets the random set** (`⊤` if never). -/
def hitTime (ρ : X → ℝ≥0 → ℂ) (F : X → Set ℂ) (x : X) : ℝ≥0∞ := ⨅ (u : ℝ≥0) (_ : ρ x u ∈ F x), (u : ℝ≥0∞)

omit [MeasurableSpace X] in
/-- Before the hitting time the path is off the set. -/
theorem notMem_of_lt_hitTime {ρ : X → ℝ≥0 → ℂ} {F : X → Set ℂ} {x : X} {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < hitTime ρ F x) : ρ x u ∉ F x := fun h =>
  absurd (iInf₂_le u h : hitTime ρ F x ≤ u) (not_le.2 hu)

omit [MeasurableSpace X] in
/-- For a continuous path and a closed set, the hitting time is attained when finite. -/
theorem hitTime_le_iff {ρ : X → ℝ≥0 → ℂ} {F : X → Set ℂ} {x : X} (hc : Continuous (ρ x)) (hF : IsClosed (F x))
    (a : ℝ≥0) : hitTime ρ F x ≤ a ↔ ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤ a ∧ ρ x u ∈ F x := by
  constructor
  · intro h
    -- the set of hitting times in `[0, a]` is compact and nonempty
    set S : Set ℝ≥0 := {u | ρ x u ∈ F x} with hS
    have hSc : IsClosed S := hF.preimage hc
    by_contra hne
    push Not at hne
    -- every hitting time exceeds `a`; then the infimum is at least the least one, which exceeds `a`
    have hgt : ∀ u ∈ S, a < u := fun u hu => by
      by_contra hle
      exact hne u (ENNReal.coe_le_coe.2 (not_lt.1 hle)) hu
    by_cases hSe : S.Nonempty
    · set m := sInf S with hmdef
      have hm : m ∈ S := hSc.csInf_mem hSe (OrderBot.bddBelow S)
      have hle : (m : ℝ≥0∞) ≤ hitTime ρ F x :=
        le_iInf₂ fun u hu => ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow S) hu)
      have := (ENNReal.coe_lt_coe.2 (hgt m hm)).trans_le hle
      exact absurd h (not_le.2 this)
    · have htop : hitTime ρ F x = ⊤ := by
        refine iInf₂_eq_top.2 fun u hu => absurd ⟨u, hu⟩ hSe
      rw [htop] at h
      exact absurd h (not_le.2 ENNReal.coe_lt_top)
  · rintro ⟨u, hu, hF'⟩
    exact (iInf₂_le u hF').trans hu

/-- **The hitting time of a random closed set is measurable**, for paths continuous for every sample, sets closed and
nonempty for every sample, and distances to the set measurable. -/
theorem measurable_hitTime {ρ : X → ℝ≥0 → ℂ} (hρm : ∀ u, Measurable fun x => ρ x u)
    (hρc : ∀ x, Continuous (ρ x)) {F : X → Set ℂ} (hF : ∀ x, IsClosed (F x)) (hFne : ∀ x, (F x).Nonempty)
    (hFm : ∀ z, Measurable fun x => infDist z (F x)) : Measurable (hitTime ρ F) := by
  have hd : Measurable fun p : ℂ × X => infDist p.1 (F p.2) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun z x => infDist z (F x))
      (fun x => continuous_infDist_pt _) hFm
  refine measurable_of_Iic fun y => ?_
  induction y using ENNReal.recTopCoe with
  | top => simp
  | coe a => ?_
  show MeasurableSet {x | hitTime ρ F x ≤ a}
  have e : {x | hitTime ρ F x ≤ a} = ⋃ N : ℕ, ⋂ n : ℕ, ⋃ q : ℚ,
      {x | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (a : ℝ≥0∞) ∧ (q : ℝ).toNNReal ≤ (N : ℝ≥0) ∧
        infDist (ρ x (q : ℝ).toNNReal) (F x) < 1 / ((n : ℝ) + 1)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    rw [hitTime_le_iff (hρc x) (hF x)]
    exact Aux61Fib.visit_closed_iff (U := fun _ => (a : ℝ≥0∞)) hρc (hF x) (hFne x) x
  rw [e]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => ?_
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter ?_)
  exact measurableSet_lt (hd.comp ((hρm _).prodMk measurable_id)) measurable_const

/-! ### The chart image before the hitting time -/

open scoped Classical in
/-- **The chart image of the path before `T`**: the forward chart limit at the path point (`0` off `E` and from `T`
on). -/
def inPath (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (x : X) (u : ℝ≥0) : ℂ :=
  if x ∈ E ∧ (u : ℝ≥0∞) < T x then limUnder (𝓝[((c x).dom : Set ℂ)] (ρ x u)) (c x).1 else 0

/-- **The restart data**: measurable event, end time, path and random chart; on the event the chart is conformal,
the path is continuous, starts in the closure of the chart domain where the forward chart tends to `0`, and lies in the
chart domain at positive times before `T`. -/
structure IsRestartSpec (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) : Prop where
  measurableSet : MeasurableSet E
  measT : Measurable T
  measρ : ∀ u, Measurable fun x => ρ x u
  contρ : ∀ x ∈ E, Continuous (ρ x)
  chart : IsMeasChart c
  conf : ∀ x ∈ E, (c x).IsConformal
  start_mem : ∀ x ∈ E, ρ x 0 ∈ closure ((c x).dom : Set ℂ)
  start_lim : ∀ x ∈ E, Tendsto (c x).1 (𝓝[((c x).dom : Set ℂ)] (ρ x 0)) (𝓝 0)
  inside : ∀ x ∈ E, ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u ∈ (c x).dom

/-- The forward map of a conformal chart is continuous at every point of its domain. -/
theorem continuousAt_fwd {c : Chart} (hc : c.IsConformal) {z : ℂ} (hz : z ∈ c.dom) : ContinuousAt c.1 z :=
  (hc.differentiableOn_fwd.continuousOn).continuousAt (c.dom.isOpen.mem_nhds hz)

namespace IsRestartSpec

variable {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} (hs : IsRestartSpec E c ρ T)
include hs

/-- **The forward chart has a limit at every path point before `T`**: the chart value at positive times, `0` at the
start. -/
theorem tendsto_inPath {x : X} (hx : x ∈ E) {u : ℝ≥0} (huT : (u : ℝ≥0∞) < T x) :
    Tendsto (c x).1 (𝓝[((c x).dom : Set ℂ)] (ρ x u)) (𝓝 (inPath E c ρ T x u)) := by
  have hcl : ρ x u ∈ closure ((c x).dom : Set ℂ) := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with rfl | hu0
    · exact hs.start_mem x hx
    · exact subset_closure (hs.inside x hx u hu0 huT)
  have hne : (𝓝[((c x).dom : Set ℂ)] (ρ x u)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hlim : ∃ w, Tendsto (c x).1 (𝓝[((c x).dom : Set ℂ)] (ρ x u)) (𝓝 w) := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with rfl | hu0
    · exact ⟨0, hs.start_lim x hx⟩
    · exact ⟨_, (continuousAt_fwd (hs.conf x hx) (hs.inside x hx u hu0 huT)).tendsto.mono_left
        nhdsWithin_le_nhds⟩
  obtain ⟨w, hw⟩ := hlim
  have e : inPath E c ρ T x u = w := by
    simp only [inPath, hx, huT, and_self, ite_true]
    exact hw.limUnder_eq
  rw [e]
  exact hw

theorem inPath_zero {x : X} (hx : x ∈ E) (h0T : 0 < T x) : inPath E c ρ T x 0 = 0 := by
  have h1 := hs.tendsto_inPath hx (u := 0) (by simpa using h0T)
  have hne : (𝓝[((c x).dom : Set ℂ)] (ρ x 0)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hs.start_mem x hx)
  exact tendsto_nhds_unique h1 (hs.start_lim x hx)

theorem inPath_eq_fwd {x : X} (hx : x ∈ E) {u : ℝ≥0} (hu0 : 0 < u) (huT : (u : ℝ≥0∞) < T x) :
    inPath E c ρ T x u = (c x).1 (ρ x u) := by
  have hin := hs.inside x hx u hu0 huT
  have hne : (𝓝[((c x).dom : Set ℂ)] (ρ x u)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hin)
  exact tendsto_nhds_unique (hs.tendsto_inPath hx huT)
    ((continuousAt_fwd (hs.conf x hx) hin).tendsto.mono_left nhdsWithin_le_nhds)

/-- **The chart image is continuous before `T`.** -/
theorem continuousOn_inPath {x : X} (hx : x ∈ E) :
    ContinuousOn (inPath E c ρ T x) {u : ℝ≥0 | (u : ℝ≥0∞) < T x} := by
  intro u hu
  have hTo : {u : ℝ≥0 | (u : ℝ≥0∞) < T x} ∈ 𝓝 u :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hu
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with rfl | hu0
  · -- at the start: along positive times the chart value tends to `0`
    have h0 := hs.inPath_zero hx (by simpa using hu)
    refine (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    rw [h0]
    have hρ : Tendsto (ρ x) (𝓝[>] 0) (𝓝[((c x).dom : Set ℂ)] (ρ x 0)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨((hs.contρ x hx).tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hTo] with v hv hvT
      exact hs.inside x hx v hv hvT
    have hpos : Tendsto (inPath E c ρ T x) (𝓝[>] 0) (𝓝 0) := by
      refine ((hs.start_lim x hx).comp hρ).congr' ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hTo] with v hv hvT
      exact (hs.inPath_eq_fwd hx hv hvT).symm
    have hat : Tendsto (inPath E c ρ T x) (pure 0) (𝓝 0) := by
      rw [tendsto_pure_left]
      intro s hs0
      rw [h0]
      exact mem_of_mem_nhds hs0
    have hsplit : 𝓝 (0 : ℝ≥0) = 𝓝[>] 0 ⊔ pure 0 := by
      rw [← nhdsWithin_univ, show (univ : Set ℝ≥0) = Ioi 0 ∪ {0} by
        ext v; simp]
      rw [nhdsWithin_union, nhdsWithin_singleton]
    rw [hsplit]
    exact hpos.sup hat
  · have hin := hs.inside x hx u hu0 hu
    have hca : ContinuousAt (fun v => (c x).1 (ρ x v)) u :=
      (continuousAt_fwd (hs.conf x hx) hin).comp ((hs.contρ x hx).continuousAt)
    refine (hca.congr ?_).continuousWithinAt
    filter_upwards [hTo, lt_mem_nhds hu0] with v hvT hv0
    exact (hs.inPath_eq_fwd hx hv0 hvT).symm

/-- **The chart image is measurable** at every time. -/
theorem measurable_inPath (u : ℝ≥0) : Measurable fun x => inPath E c ρ T x u := by
  classical
  set G : Set X := E ∩ {x | (u : ℝ≥0∞) < T x} with hG
  have hGm : MeasurableSet G := hs.measurableSet.inter (measurableSet_lt measurable_const hs.measT)
  have hcm := hs.chart.chartOf hGm
  set q : X → ℂ := fun x => if x ∈ G then ρ x u else 0 with hq
  have hqm : Measurable q := Measurable.ite hGm (hs.measρ u) measurable_const
  have hDo : ∀ x, IsOpen ((chartOf G c x).dom : Set ℂ) := fun x => (chartOf G c x).dom.isOpen
  have hqD : ∀ x, q x ∈ closure ((chartOf G c x).dom : Set ℂ) := fun x => by
    by_cases hx : x ∈ G
    · simp only [hq, hx, ite_true, chartOf_of_mem hx]
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with rfl | hu0
      · exact hs.start_mem x hx.1
      · exact subset_closure (hs.inside x hx.1 u hu0 hx.2)
    · simp only [hq, hx, ite_false, chartOf_of_notMem hx, coe_dom_id, closure_H]
      show (0 : ℂ).im ≥ 0
      simp
  have hlim : ∀ x, Tendsto (chartOf G c x).1 (𝓝[((chartOf G c x).dom : Set ℂ)] (q x))
      (𝓝 (inPath E c ρ T x u)) := fun x => by
    by_cases hx : x ∈ G
    · simp only [hq, hx, ite_true, chartOf_of_mem hx]
      exact hs.tendsto_inPath hx.1 hx.2
    · have hneg : ¬ (x ∈ E ∧ (u : ℝ≥0∞) < T x) := by simpa [hG] using hx
      have h0 : inPath E c ρ T x u = 0 := by
        simp only [inPath, hneg, ↓reduceIte]
      simp only [hq, hx, ite_false, chartOf_of_notMem hx, h0]
      exact tendsto_id.mono_left nhdsWithin_le_nhds
  exact measurable_of_tendsto_nhdsWithin hDo hcm.dom hcm.fwd hqm hqD hlim

end IsRestartSpec

/-! ### The exit time from the window -/

/-- **The window event at level `a`**: before `T`, the chart image stays in `V` on `[0, a]`. -/
def winEv (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (V : Set ℂ) (a : ℝ≥0) : Set X :=
  {x | x ∈ E ∧ (a : ℝ≥0∞) < T x ∧ ∀ u : ℝ≥0, u ≤ a → inPath E c ρ T x u ∈ V}

open scoped Classical in
/-- **The exit time of the chart image from the window**, capped at `T`: the supremum of the rational levels `a` at
which the chart image has stayed in `V` on `[0, a]` before `T`. -/
def exitTime (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (V : Set ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ a : ℚ≥0, if x ∈ winEv E c ρ T V (a : ℝ≥0) then (((a : ℝ≥0) : ℝ≥0∞)) else 0

namespace IsRestartSpec

variable {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} (hs : IsRestartSpec E c ρ T)
  {V : Set ℂ}
include hs

theorem measurableSet_winEv (hV : IsOpen V) (a : ℝ≥0) : MeasurableSet (winEv E c ρ T V a) := by
  classical
  set G : Set X := E ∩ {x | (a : ℝ≥0∞) < T x} with hG
  have hGm : MeasurableSet G := hs.measurableSet.inter (measurableSet_lt measurable_const hs.measT)
  set Γ : X → ℝ≥0 → ℂ := fun x u => if x ∈ G then inPath E c ρ T x (min u a) else 0 with hΓ
  have hΓm : ∀ u, Measurable fun x => Γ x u := fun u =>
    Measurable.ite hGm (hs.measurable_inPath _) measurable_const
  have hΓc : ∀ x, Continuous (Γ x) := fun x => by
    by_cases hx : x ∈ G
    · simp only [hΓ, hx, ite_true]
      refine (hs.continuousOn_inPath hx.1).comp_continuous (continuous_id.min continuous_const) fun u => ?_
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hx.2
    · simp only [hΓ, hx, ite_false]
      exact continuous_const
  have hvis := Aux61Fib.measurableSet_visit hΓm hΓc (measurable_const (a := ((a : ℝ≥0) : ℝ≥0∞)))
    hV.isClosed_compl
  have e : winEv E c ρ T V a = G \ {x | ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤ (a : ℝ≥0∞) ∧ Γ x u ∈ Vᶜ} := by
    ext x
    simp only [winEv, mem_ofPred_eq, Set.mem_sdiff, hG, mem_inter_iff, not_exists, not_and, mem_compl_iff, not_not]
    constructor
    · rintro ⟨hxE, haT, hin⟩
      refine ⟨⟨hxE, haT⟩, fun u hu => ?_⟩
      have hu' : u ≤ a := ENNReal.coe_le_coe.1 hu
      simp only [hΓ, show x ∈ G from ⟨hxE, haT⟩, ite_true, min_eq_left hu']
      exact hin u hu'
    · rintro ⟨⟨hxE, haT⟩, hin⟩
      refine ⟨hxE, haT, fun u hu => ?_⟩
      have := hin u (ENNReal.coe_le_coe.2 hu)
      simpa only [hΓ, show x ∈ G from ⟨hxE, haT⟩, ite_true, min_eq_left hu] using this
  rw [e]
  exact hGm.diff hvis

theorem measurable_exitTime (hV : IsOpen V) : Measurable (exitTime E c ρ T V) := by
  classical
  exact Measurable.iSup fun a => Measurable.ite (hs.measurableSet_winEv hV _) measurable_const measurable_const

omit [MeasurableSpace X] hs in
theorem exitTime_le (x : X) : exitTime E c ρ T V x ≤ T x := by
  refine iSup_le fun a => ?_
  split_ifs with h
  · exact h.2.1.le
  · exact zero_le

omit [MeasurableSpace X] hs in
/-- **Before the exit time the chart image is in the window** (and the time is before `T`). -/
theorem lt_exitTime {x : X} {u : ℝ≥0} (hu : (u : ℝ≥0∞) < exitTime E c ρ T V x) :
    (u : ℝ≥0∞) < T x ∧ inPath E c ρ T x u ∈ V := by
  classical
  obtain ⟨a, ha⟩ := lt_iSup_iff.1 hu
  by_cases h : x ∈ winEv E c ρ T V (a : ℝ≥0)
  · simp only [h, ↓reduceIte] at ha
    exact ⟨ha.trans h.2.1, h.2.2 u (ENNReal.coe_le_coe.1 ha.le)⟩
  · simp only [h, ↓reduceIte] at ha
    exact absurd ha (not_lt.2 zero_le)

/-- A neighbourhood of a time before `T` on which the chart image stays in the (open) window. -/
theorem eventually_mem_of_lt {x : X} (hx : x ∈ E) (hV : IsOpen V) {u : ℝ≥0} (huT : (u : ℝ≥0∞) < T x)
    (huV : inPath E c ρ T x u ∈ V) : ∀ᶠ v : ℝ≥0 in 𝓝 u, (v : ℝ≥0∞) < T x ∧ inPath E c ρ T x v ∈ V := by
  have hTo : {v : ℝ≥0 | (v : ℝ≥0∞) < T x} ∈ 𝓝 u :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds huT
  have hc : ContinuousAt (inPath E c ρ T x) u := (hs.continuousOn_inPath hx).continuousAt hTo
  filter_upwards [hTo, hc.preimage_mem_nhds (hV.mem_nhds huV)] with v hv hvV
  exact ⟨hv, hvV⟩

omit [MeasurableSpace X] hs in
/-- If the chart image is in the window on `[0, u)` and on a neighbourhood of `u` before `T`, the exit time exceeds
`u`. -/
theorem lt_exitTime_of {x : X} (hx : x ∈ E) {u : ℝ≥0}
    (hbefore : ∀ v : ℝ≥0, v < u → inPath E c ρ T x v ∈ V)
    (hnear : ∀ᶠ v : ℝ≥0 in 𝓝 u, (v : ℝ≥0∞) < T x ∧ inPath E c ρ T x v ∈ V) : (u : ℝ≥0∞) < exitTime E c ρ T V x := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hnear
  obtain ⟨a, hua, haε⟩ := exists_rat_btwn (show (u : ℝ) < u + ε by linarith)
  have ha0 : (0 : ℝ) ≤ a := (NNReal.coe_nonneg u).trans hua.le
  set a' : ℚ≥0 := ⟨a, by exact_mod_cast ha0⟩ with ha'
  have ha'r : ((a' : ℝ≥0) : ℝ) = a := Real.ext_cauchy rfl
  have hwin : x ∈ winEv E c ρ T V (a' : ℝ≥0) := by
    have hnearv : ∀ v : ℝ≥0, u ≤ v → (v : ℝ) ≤ a → (v : ℝ≥0∞) < T x ∧ inPath E c ρ T x v ∈ V := by
      intro v huv hva
      refine hball ?_
      rw [NNReal.dist_eq, abs_lt]
      constructor <;> linarith [NNReal.coe_le_coe.2 huv]
    refine ⟨hx, (hnearv (a' : ℝ≥0) ?_ ha'r.le).1, fun v hv => ?_⟩
    · rw [← NNReal.coe_le_coe, ha'r]; exact hua.le
    · rcases lt_or_ge v u with hvu | huv
      · exact hbefore v hvu
      · exact (hnearv v huv (by rw [← ha'r]; exact_mod_cast hv)).2
  have hle : (((a' : ℝ≥0) : ℝ≥0∞)) ≤ exitTime E c ρ T V x := by
    refine le_iSup_of_le a' ?_
    simp only [hwin, ↓reduceIte, le_refl]
  refine lt_of_lt_of_le ?_ hle
  refine ENNReal.coe_lt_coe.2 ?_
  rw [← NNReal.coe_lt_coe, ha'r]
  exact hua

/-- **The exit time is positive** when the window contains the start `0` and `T` is positive. -/
theorem exitTime_pos {x : X} (hx : x ∈ E) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V) (h0T : 0 < T x) :
    0 < exitTime E c ρ T V x := by
  have h0T' : ((0 : ℝ≥0) : ℝ≥0∞) < T x := by simpa using h0T
  have h := lt_exitTime_of hx (u := 0) (fun v hv => absurd hv (not_lt.2 zero_le))
    (hs.eventually_mem_of_lt hx hV h0T' (by rw [hs.inPath_zero hx h0T]; exact hV0))
  simpa using h

/-- **At an exit before `T` the chart image is outside the window.** -/
theorem inPath_exitTime_notMem {x : X} (hx : x ∈ E) (hV : IsOpen V)
    (hlt : exitTime E c ρ T V x < T x) :
    inPath E c ρ T x (exitTime E c ρ T V x).toNNReal ∉ V := by
  have hne : exitTime E c ρ T V x ≠ ⊤ := ne_top_of_lt hlt
  set e := (exitTime E c ρ T V x).toNNReal with he
  have hee : (e : ℝ≥0∞) = exitTime E c ρ T V x := ENNReal.coe_toNNReal hne
  intro heV
  have heT : (e : ℝ≥0∞) < T x := hee ▸ hlt
  have h := lt_exitTime_of hx (u := e) (fun v hv => (lt_exitTime (by rw [← hee]; exact_mod_cast hv)).2)
    (hs.eventually_mem_of_lt hx hV heT heV)
  rw [hee] at h
  exact lt_irrefl _ h

end IsRestartSpec

end InteractingSLE.Sec5.Aux61FibData
