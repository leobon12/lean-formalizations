/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibDataExit

/-!
# The glued-space fibre objects, V: the code of a restart killed at its window exit

Packet PROVE-AUX61-FIBDATA (pieces (G) and (P) of `planning/handoffs/PROVE-AUX61-FIB.md`). For restart data
`IsRestartSpec E c ρ T` (a random chart, a physical path in the chart domain before the hitting time `T` of the
retained boundary, chart value `0` at the start) and an open window `V ∋ 0` with nonempty complement:

* `exitEv E c ρ T V = E ∩ {0 < T} ∩ {exitTime < ⊤}` and `exitNN = exitTime.toNNReal` (measurable);
* the only further pathwise input is the **landing** (`IsLanding`): when the chart image stays in the window up to the
  hitting time, the forward chart has a limit at the hit point, outside the window (Astra's follow-up 4, L215–L224:
  the prime-end coordinate of a continuous physical first endpoint);
* **`IsRestartSpec.isChartPathSpec_exit`**: then `IsChartPathSpec (exitEv …) c ρ (exitNN …)`;
* **`IsRestartSpec.isClockOn_exit`**: if the physical path is injective before `T`, the relative capacity clock of the
  chart path is a clock (it is a simple path from `0`, interior before the exit);
* **`IsRestartSpec.measurable_exitCode`**: the code `exitCode … = rsCode (exitEv …) c ρ (exitNN …) a k h` is measurable;
* **`IsRestartSpec.pathGood_exitCode`**: on `exitEv`, `PathGood d (exitCode … x)` for every `d : FibData` with
  `d.V = V` and `d.ℓ = clr V` — the path facts (P) of the fibre code.

Generic. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.Aux61FibData

open Restart Aux61Fib

variable {X : Type*} [MeasurableSpace X]

/-- **The event of a finite window exit** (with a positive hitting time). -/
def exitEv (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (V : Set ℂ) : Set X :=
  E ∩ {x | 0 < T x} ∩ {x | exitTime E c ρ T V x < ⊤}

/-- The window exit time as a finite time. -/
def exitNN (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (V : Set ℂ) (x : X) : ℝ≥0 :=
  (exitTime E c ρ T V x).toNNReal

/-- **The landing**: when the chart image stays in the window up to a finite hitting time, the forward chart has a
limit at the hit point, and that limit is outside the window. -/
def IsLanding (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (V : Set ℂ) : Prop :=
  ∀ x ∈ E, 0 < T x → exitTime E c ρ T V x = T x → T x < ⊤ →
    ∃ L : ℂ, L ∉ V ∧ Tendsto (c x).1 (𝓝[((c x).dom : Set ℂ)] (ρ x (T x).toNNReal)) (𝓝 L)

/-- **The code of a restart killed at its window exit.** -/
def exitCode (E : Set X) (c : X → Chart) (ρ : X → ℝ≥0 → ℂ) (T : X → ℝ≥0∞) (V : Set ℂ) (a k : ℝ)
    (h : X → DistOn upperHalfPlaneOpens) (x : X) : FibCode :=
  rsCode (exitEv E c ρ T V) c ρ (exitNN E c ρ T V) a k h x

namespace IsRestartSpec

variable {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} (hs : IsRestartSpec E c ρ T)
  {V : Set ℂ}
include hs

theorem measurableSet_exitEv (hV : IsOpen V) : MeasurableSet (exitEv E c ρ T V) :=
  (hs.measurableSet.inter (measurableSet_lt measurable_const hs.measT)).inter
    (measurableSet_lt (hs.measurable_exitTime hV) measurable_const)

omit [MeasurableSpace X] hs in
theorem coe_exitNN {x : X} (hx : x ∈ exitEv E c ρ T V) :
    ((exitNN E c ρ T V x : ℝ≥0) : ℝ≥0∞) = exitTime E c ρ T V x :=
  ENNReal.coe_toNNReal hx.2.ne

/-- The physical path before the exit lies in the chart domain or its closure (at the start). -/
theorem mem_closure_of_le {x : X} (hx : x ∈ exitEv E c ρ T V) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < T x) :
    ρ x u ∈ closure ((c x).dom : Set ℂ) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with rfl | hu0
  · exact hs.start_mem x hx.1.1
  · exact subset_closure (hs.inside x hx.1.1 u hu0 hu)

/-- The physical path at a finite hitting time is in the closure of the chart domain. -/
theorem mem_closure_at_T {x : X} (hx : x ∈ exitEv E c ρ T V) (hT : T x < ⊤) :
    ρ x (T x).toNNReal ∈ closure ((c x).dom : Set ℂ) := by
  have hTT : ((T x).toNNReal : ℝ≥0∞) = T x := ENNReal.coe_toNNReal hT.ne
  have hpos : 0 < (T x).toNNReal := by
    rw [← ENNReal.coe_lt_coe, hTT]; simpa using hx.1.2
  have hlim : Tendsto (ρ x) (𝓝[<] (T x).toNNReal) (𝓝 (ρ x (T x).toNNReal)) :=
    ((hs.contρ x hx.1.1).tendsto _).mono_left nhdsWithin_le_nhds
  have := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hpos] with v hv
  exact hs.inside x hx.1.1 v hv.1 (by rw [← hTT]; exact ENNReal.coe_lt_coe.2 hv.2)

/-- **The chart limit path at a window exit.** -/
theorem exists_exit_path (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V) (hland : IsLanding E c ρ T V) {x : X}
    (hx : x ∈ exitEv E c ρ T V) :
    ∃ γ₀ : ℝ≥0 → ℂ, ContinuousOn γ₀ (Iic (exitNN E c ρ T V x)) ∧ γ₀ 0 = 0 ∧
      (∀ u : ℝ≥0, u ≤ exitNN E c ρ T V x → Tendsto (c x).1 (𝓝[((c x).dom : Set ℂ)] (ρ x u)) (𝓝 (γ₀ u))) ∧
      (∀ r : ℝ≥0, r < exitNN E c ρ T V x → γ₀ r = inPath E c ρ T x r) ∧ γ₀ (exitNN E c ρ T V x) ∉ V ∧
      ρ x (exitNN E c ρ T V x) ∈ closure ((c x).dom : Set ℂ) := by
  have hxE := hx.1.1
  have h0T := hx.1.2
  have he := coe_exitNN hx
  set e := exitNN E c ρ T V x with he_def
  have hepos : 0 < e := by
    have := hs.exitTime_pos hxE hV hV0 h0T
    rw [← he] at this; exact_mod_cast this
  have heT : (e : ℝ≥0∞) ≤ T x := he ▸ exitTime_le x
  have hlt : ∀ r : ℝ≥0, r < e → (r : ℝ≥0∞) < T x := fun r hr => (ENNReal.coe_lt_coe.2 hr).trans_le heT
  rcases lt_or_eq_of_le heT with hlT | heqT
  · -- the exit comes before the hitting time: the chart image itself
    refine ⟨inPath E c ρ T x, (hs.continuousOn_inPath hxE).mono fun r hr =>
      (ENNReal.coe_le_coe.2 (mem_Iic.1 hr)).trans_lt hlT, hs.inPath_zero hxE h0T, fun u hu =>
      hs.tendsto_inPath hxE ((ENNReal.coe_le_coe.2 hu).trans_lt hlT), fun r _ => rfl, ?_,
      hs.mem_closure_of_le hx hlT⟩
    exact hs.inPath_exitTime_notMem hxE hV (he ▸ hlT)
  · -- the chart image stays in the window up to the hitting time: the landing point
    have hTfin : T x < ⊤ := heqT ▸ ENNReal.coe_lt_top
    have heT' : e = (T x).toNNReal := by rw [← heqT]; rfl
    obtain ⟨L, hLV, hL⟩ := hland x hxE h0T (he.symm.trans heqT) hTfin
    rw [← heT'] at hL
    refine ⟨fun u => if u < e then inPath E c ρ T x u else L, ?_, ?_, fun u hu => ?_,
      fun r hr => by simp only [hr, ↓reduceIte],
      by simpa using hLV, ?_⟩
    · intro u hu
      rcases lt_or_eq_of_le (mem_Iic.1 hu) with hue | rfl
      · have hc : ContinuousAt (inPath E c ρ T x) u := (hs.continuousOn_inPath hxE).continuousAt
          ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds (hlt u hue))
        refine (hc.congr ?_).continuousWithinAt
        filter_upwards [gt_mem_nhds hue] with v hv
        simp only [hv, ite_true]
      · -- the left limit at `e` is the landing point
        have hρ : Tendsto (ρ x) (𝓝[<] e) (𝓝[((c x).dom : Set ℂ)] (ρ x e)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨((hs.contρ x hxE).tendsto e).mono_left nhdsWithin_le_nhds, ?_⟩
          filter_upwards [Ioo_mem_nhdsLT hepos] with v hv
          exact hs.inside x hxE v hv.1 (hlt v hv.2)
        have hleft : Tendsto (fun u => if u < e then inPath E c ρ T x u else L) (𝓝[<] e) (𝓝 L) := by
          refine (hL.comp hρ).congr' ?_
          filter_upwards [Ioo_mem_nhdsLT hepos] with v hv
          simp only [Function.comp_apply, hv.2, ite_true]
          exact (hs.inPath_eq_fwd hxE hv.1 (hlt v hv.2)).symm
        rw [ContinuousWithinAt]
        simp only [lt_irrefl, ↓reduceIte]
        have hsplit : 𝓝[≤] e = 𝓝[<] e ⊔ pure e := by
          rw [← Iio_union_right, nhdsWithin_union, nhdsWithin_singleton]
        rw [hsplit]
        refine hleft.sup ?_
        rw [tendsto_pure_left]
        intro s hs'
        simpa using mem_of_mem_nhds hs'
    · simp only [hepos, ite_true]
      exact hs.inPath_zero hxE h0T
    · rcases lt_or_eq_of_le hu with hue | rfl
      · simp only [hue, ite_true]
        exact hs.tendsto_inPath hxE (hlt u hue)
      · simpa using hL
    · rw [heT']
      exact hs.mem_closure_at_T hx hTfin

/-- **The chart-path spec at the window exit.** -/
theorem isChartPathSpec_exit (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V) (hland : IsLanding E c ρ T V) :
    IsChartPathSpec (exitEv E c ρ T V) c ρ (exitNN E c ρ T V) := by
  refine ⟨hs.measurableSet_exitEv hV, ENNReal.measurable_toNNReal.comp (hs.measurable_exitTime hV), hs.measρ,
    fun x hx => (hs.contρ x hx.1.1).continuousOn, hs.chart, fun x hx u hu => ?_, fun x hx => ?_⟩
  · obtain ⟨γ₀, -, -, -, -, -, hcl⟩ := hs.exists_exit_path hV hV0 hland hx
    rcases lt_or_eq_of_le hu with hue | rfl
    · have heT : ((exitNN E c ρ T V x : ℝ≥0) : ℝ≥0∞) ≤ T x := (coe_exitNN hx) ▸ exitTime_le x
      exact hs.mem_closure_of_le hx ((ENNReal.coe_lt_coe.2 hue).trans_le heT)
    · exact hcl
  · obtain ⟨γ₀, hc, h0, hlim, -⟩ := hs.exists_exit_path hV hV0 hland hx
    exact ⟨γ₀, hc, h0, hlim⟩

/-- **The chart path at the window exit is a simple path from `0`, interior before the exit, outside the window at
the exit**, when the physical path is injective before the hitting time. -/
theorem chartPath_exit_facts (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V) (hland : IsLanding E c ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x}) {x : X} (hx : x ∈ exitEv E c ρ T V) :
    let γ := chartPath (exitEv E c ρ T V) c ρ (exitNN E c ρ T V) x
    let e := exitNN E c ρ T V x
    ContinuousOn γ (Iic e) ∧ γ 0 = 0 ∧ InjOn γ (Iic e) ∧ (∀ r : ℝ≥0, 0 < r → r < e → γ r ∈ H) ∧
      γ e ∈ Hbar ∧ (∀ r : ℝ≥0, r < e → γ r ∈ V) ∧ γ e ∉ V := by
  intro γ e
  have hxE := hx.1.1
  have hspec := hs.isChartPathSpec_exit hV hV0 hland
  obtain ⟨γ₀, hc, h0, hlim, hint, hout, -⟩ := hs.exists_exit_path hV hV0 hland hx
  have hγ : ∀ u : ℝ≥0, u ≤ e → γ u = γ₀ u := fun u hu => hspec.chartPath_eq hx hlim hu
  have heT : (e : ℝ≥0∞) ≤ T x := (coe_exitNN hx) ▸ exitTime_le x
  have hlt : ∀ r : ℝ≥0, r < e → (r : ℝ≥0∞) < T x := fun r hr => (ENNReal.coe_lt_coe.2 hr).trans_le heT
  have hin : ∀ r : ℝ≥0, r < e → γ r ∈ V := fun r hr => by
    rw [hγ r hr.le, hint r hr]
    exact (lt_exitTime (by rw [← coe_exitNN hx]; exact ENNReal.coe_lt_coe.2 hr)).2
  have houtγ : γ e ∉ V := by rw [hγ e le_rfl]; exact hout
  have hfwd : ∀ r : ℝ≥0, 0 < r → r < e → γ r = (c x).1 (ρ x r) := fun r hr0 hr => by
    rw [hγ r hr.le, hint r hr, hs.inPath_eq_fwd hxE hr0 (hlt r hr)]
  have hH : ∀ r : ℝ≥0, 0 < r → r < e → γ r ∈ H := fun r hr0 hr => by
    rw [hfwd r hr0 hr]
    exact (hs.conf x hxE).fwd_mem (hs.inside x hxE r hr0 (hlt r hr))
  refine ⟨(hspec.isPathSpec).cont x hx, (hspec.isPathSpec).zero x hx, ?_, hH, ?_, hin, houtγ⟩
  · have hz : γ 0 = 0 := (hspec.isPathSpec).zero x hx
    intro u hu v hv huv
    rcases lt_or_eq_of_le (mem_Iic.1 hu) with hue | hue <;>
      rcases lt_or_eq_of_le (mem_Iic.1 hv) with hve | hve
    · -- two times before the exit
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with hu0 | hu0 <;>
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ v) with hv0 | hv0
      · rw [← hu0, ← hv0]
      · rw [← hu0, hz] at huv
        exact absurd (huv ▸ hH v hv0 hve : (0 : ℂ) ∈ H) (by simp [QuantumZipper.H])
      · rw [← hv0, hz] at huv
        exact absurd (huv.symm ▸ hH u hu0 hue : (0 : ℂ) ∈ H) (by simp [QuantumZipper.H])
      · rw [hfwd u hu0 hue, hfwd v hv0 hve] at huv
        have hρ : ρ x u = ρ x v := by
          rw [← (hs.conf x hxE).inv_fwd (hs.inside x hxE u hu0 (hlt u hue)),
            ← (hs.conf x hxE).inv_fwd (hs.inside x hxE v hv0 (hlt v hve)), huv]
        exact hinj x hxE (hlt u hue) (hlt v hve) hρ
    · exact absurd (huv ▸ hin u hue) (hve ▸ houtγ)
    · exact absurd (huv.symm ▸ hin v hve) (hue ▸ houtγ)
    · rw [hue, hve]
  · -- the exit point is in `ℍ̄`: a limit of interior points, or `0`
    have hepos : 0 < e := by
      have := hs.exitTime_pos hxE hV hV0 hx.1.2
      rw [← coe_exitNN hx] at this; exact_mod_cast this
    have hcw : ContinuousWithinAt γ (Iic e) e := (hspec.isPathSpec).cont x hx e (mem_Iic.2 le_rfl)
    have := nhdsLT_neBot_of_exists_lt ⟨0, hepos⟩
    have hl : Tendsto γ (𝓝[<] e) (𝓝 (γ e)) := hcw.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
    refine closure_H ▸ mem_closure_of_tendsto hl ?_
    filter_upwards [Ioo_mem_nhdsLT hepos] with r hr
    exact hH r hr.1 hr.2

/-- **The relative capacity clock of the chart path at the window exit is a clock.** -/
theorem isClockOn_exit (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V) (hland : IsLanding E c ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x}) :
    ∀ x ∈ exitEv E c ρ T V,
      IsClockOn (chartClock (chartPath (exitEv E c ρ T V) c ρ (exitNN E c ρ T V) x)) (exitNN E c ρ T V x) :=
  fun x hx => by
    obtain ⟨hc, h0, hi, hH, hUH, -, -⟩ := hs.chartPath_exit_facts hV hV0 hland hinj hx
    exact (isClockOn_chartClock_of_injOn hc hi h0 hH hUH).1

/-- **The code of a restart killed at its window exit is measurable.** -/
theorem measurable_exitCode (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V) (hland : IsLanding E c ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x}) (hliftc : ∀ x ∈ E, ContinuousOn (c x).2.2 (c x).dom)
    {h : X → DistOn upperHalfPlaneOpens} (hh : Measurable h) (a k : ℝ) :
    Measurable (exitCode E c ρ T V a k h) :=
  measurable_rsCode (hs.isChartPathSpec_exit hV hV0 hland) (hs.isClockOn_exit hV hV0 hland hinj)
    (fun x hx => hs.conf x hx.1.1) (fun x hx => hliftc x hx.1.1) hh

/-- **The path facts of the fibre code at the window exit**: `PathGood d` for every fibre datum whose window is `V`
and whose clearance is that of `V`. -/
theorem pathGood_exitCode (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V) (hland : IsLanding E c ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x}) {a k : ℝ} {h : X → DistOn upperHalfPlaneOpens}
    (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) {x : X} (hx : x ∈ exitEv E c ρ T V) :
    PathGood d (exitCode E c ρ T V a k h x) := by
  obtain ⟨-, -, hi, hH, hUH, hin, hout⟩ := hs.chartPath_exit_facts hV hV0 hland hinj hx
  have hne : d.Vᶜ.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hemp
    have hb := d.buffer_compact.isBounded.subset (d.V_sub.trans subset_closure)
    rw [hemp] at hb
    exact NormedSpace.unbounded_univ ℝ ℂ hb
  subst hdV
  exact (hs.isChartPathSpec_exit hV hV0 hland).pathGood_rsCode (hs.isClockOn_exit hV hV0 hland hinj) hx hi hH
    hUH d (hℓ.trans rfl) hV hne hin hout

end IsRestartSpec

end InteractingSLE.Sec5.Aux61FibData
