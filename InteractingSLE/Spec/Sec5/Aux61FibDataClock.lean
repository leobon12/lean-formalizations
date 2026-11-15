/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ClockMeasClock
import InteractingSLE.Spec.Sec6.DrivingUnconditional

/-!
# The glued-space fibre objects, I: reading a random simple path in relative capacity time

Packet PROVE-AUX61-FIBDATA. The code of a restart fibre (`Aux61Fib.FibCode`) records the restarted chart path in
**relative half-plane capacity time** (the decoded driver `FibCode.driver` is the Loewner driver of the decoded
trace). This file turns a random path `γ`, given in any parametrization on a finite random interval `[0, U]`, into
that reading, measurably:

* `clampPath E γ U x r = γ x (min r (U x))` on the event `E` (`0` off it): continuous in `r` for every `x`,
  measurable in `x` for every `r` (`continuous_clampPath`, `measurable_clampPath`);
* `capClock E γ U x r = hcapHit (clampPath x [0, r]) / 2` (measurable; `capClock_eq`: on `E` it is the relative
  capacity clock `Restart.chartClock` of `γ x` on `[0, U x]`);
* `capPath E γ U x u = clampPath x (a_x⁻¹ u)` and `capEnd E γ U x = a_x(U x)` (the path read in capacity time and its
  capacity lifetime), measurable (`measurable_capPath`, `measurable_capEnd`), `capPath x` continuous on
  `[0, capEnd x]` for every `x` (`continuousOn_capPath`), starting at `0`, with the same image as `γ x` on `[0, U x]`
  (`image_capPath`), and **parametrized by capacity**: `chartClock (capPath x) u = u` (`chartClock_capPath`);
* **`isClockOn_chartClock_of_injOn`**: for a simple path from `0` that stays in `ℍ` at interior times (it may end on
  `ℝ`), the relative capacity clock is a clock and a continuous Loewner driver generates the fillings (Proposition
  6.12, `Sec6.exists_driver_of_drivingCriteria`, with the criteria checked for simple paths).

The clock hypothesis `IsClockOn (chartClock (γ x)) (U x)` is exactly what `isClockOn_chartClock_of_injOn` supplies
for simple paths. Generic: no glued space, no chart. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61FibData

open Restart

/-! ### Simple paths: the clock and the driver -/

section Simple

variable {γ : ℝ≥0 → ℂ} {U : ℝ≥0}

/-- **The relative capacity clock of a simple path is a clock, and the path generates a Loewner chain** (Proposition
6.12 for simple paths): if `γ` is continuous and injective on `[0, U]`, `γ 0 = 0`, `γ` lies in `ℍ` at times in
`(0, U)` and in `ℍ̄` at `U`, then `chartClock γ` vanishes at `0`, is continuous and strictly increasing on `[0, U]`,
and a continuous driver `W` (`W 0 = 0`) has hull `fill(γ[0, t])` at capacity time `chartClock γ t`. -/
theorem isClockOn_chartClock_of_injOn (hc : ContinuousOn γ (Iic U)) (hi : InjOn γ (Iic U)) (h0 : γ 0 = 0)
    (hH : ∀ r : ℝ≥0, 0 < r → r < U → γ r ∈ H) (hU : γ U ∈ Hbar) :
    IsClockOn (chartClock γ) U ∧ ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ U →
      0 ≤ chartClock γ t ∧ QuantumZipper.fwdHull W (chartClock γ t) = fillH (γ '' Icc 0 t) := by
  -- the degenerate interval
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ U) with hU0 | hUpos
  · subst hU0
    have hfill0 : fillH (γ '' Icc 0 0) = ∅ := by
      rw [Icc_self, image_singleton, h0]
      exact YuanCharacterisation.fillH_eq_empty_of_subset (by simp)
    have hcl0 : chartClock γ 0 = 0 := by
      unfold chartClock
      rw [hfill0]
      unfold ConformalImage.hcapSet
      split_ifs with h
      · exact div_eq_zero_iff.2 (Or.inl (HPHull.hcap_eq_zero_of_eq_empty _ rfl))
      · ring
    have hsub : {r : ℝ≥0 | (r : ℝ≥0∞) ≤ ((0 : ℝ≥0) : ℝ≥0∞)}.Subsingleton := fun a ha b hb => by
      have ha0 : a = 0 := le_antisymm (by exact_mod_cast ha) zero_le
      have hb0 : b = 0 := le_antisymm (by exact_mod_cast hb) zero_le
      rw [ha0, hb0]
    refine ⟨⟨hcl0, fun a ha b hb hab => absurd (hsub ha hb) hab.ne, hsub.continuousOn _,
      fun h => absurd h ENNReal.coe_ne_top⟩, fun _ => 0, continuous_const, rfl, fun t ht => ?_⟩
    have ht0 : t = 0 := le_antisymm ht zero_le
    subst ht0
    refine ⟨hcl0.ge, ?_⟩
    rw [hcl0, QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const, hfill0]
  set S : ℝ := (U : ℝ) with hSdef
  have hS : 0 < S := NNReal.coe_pos.2 hUpos
  have hmaps : MapsTo Real.toNNReal (Icc 0 S) (Iic U) := fun r hr => by
    simpa [hSdef] using Real.toNNReal_le_toNNReal hr.2
  have hcR : ContinuousOn (realPath γ) (Icc 0 S) := hc.comp continuous_real_toNNReal.continuousOn hmaps
  have hinj : InjOn (realPath γ) (Icc 0 S) := fun a ha b hb hab => by
    have := hi (hmaps ha) (hmaps hb) hab
    rw [← Real.coe_toNNReal a ha.1, ← Real.coe_toNNReal b hb.1, this]
  have hHbar : ∀ r : ℝ≥0, r ≤ U → γ r ∈ Hbar := fun r hr => by
    rcases eq_or_lt_of_le hr with rfl | hrU
    · exact hU
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with rfl | hr0
    · rw [h0]; show (0 : ℂ).im ≥ 0; simp
    · exact H_subset_Hbar (hH r hr0 hrU)
  have hHb : MapsTo (realPath γ) (Icc 0 S) Hbar := fun r hr => hHbar _ (hmaps hr)
  have h0R : realPath γ 0 = 0 := by simp [realPath, h0]
  have hHo : MapsTo (realPath γ) (Ioo 0 S) H := fun r hr => by
    have hr0 : 0 < r.toNNReal := Real.toNNReal_pos.2 hr.1
    have hrU : r.toNNReal < U := (Real.toNNReal_lt_iff_lt_coe hr.1.le).2 hr.2
    exact hH _ hr0 hrU
  -- criterion (a): later points are outside the filling of an initial piece (up to closure at the end)
  have ha : Sec6.DrivingCriterionA (realPath γ) S := by
    rintro t ⟨ht0, htS⟩ _ ⟨r, hr, rfl⟩
    have hcr : ContinuousOn (realPath γ) (Icc 0 r) := hcR.mono (Icc_subset_Icc_right hr.2)
    have hir : InjOn (realPath γ) (Icc 0 r) := hinj.mono (Icc_subset_Icc_right hr.2)
    -- the open piece `(t, r)` lies in `ℍ ∖ fill(γ[0, t])`; the endpoint is in its closure
    have hmem : ∀ u ∈ Ioo t r, realPath γ u ∈ H \ fillH (realPath γ '' Icc 0 t) := by
      intro u hu
      have hcu : ContinuousOn (realPath γ) (Icc 0 u) := hcR.mono (Icc_subset_Icc_right (hu.2.le.trans hr.2))
      have hiu : InjOn (realPath γ) (Icc 0 u) := hinj.mono (Icc_subset_Icc_right (hu.2.le.trans hr.2))
      have hHu : MapsTo (realPath γ) (Ioc 0 u) H := fun v hv =>
        hHo ⟨hv.1, lt_of_le_of_lt hv.2 (hu.2.trans_le hr.2)⟩
      exact YuanCharacterisation.mem_H_diff_fillH_of_lt hcu hiu h0R hHu ht0.le hu.1 le_rfl
    have hlim : Tendsto (realPath γ) (𝓝[<] r) (𝓝 (realPath γ r)) := by
      have hcw := (hcR r ⟨(ht0.trans hr.1).le, hr.2⟩).mono_of_mem_nhdsWithin (s := Iio r)
        (mem_of_superset (Ioo_mem_nhdsLT hr.1) fun u hu => ⟨(ht0.trans hu.1).le, hu.2.le.trans hr.2⟩)
      exact hcw
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hr.1] with u hu using hmem u hu
  have hR : interior {u ∈ Ioo 0 S | (realPath γ u).im = 0} = ∅ := by
    refine subset_empty_iff.1 ((interior_mono fun u hu => ?_).trans (interior_empty).le)
    exact (ne_of_gt (show (0 : ℝ) < (realPath γ u).im from hHo hu.1)) hu.2
  have hb : Sec6.DrivingCriterionB (realPath γ) S := Sec6.drivingCriterionB_of_injOn hinj hR
  obtain ⟨W, hW, hW0, σ, hσ0, hσm, hσc, hσK⟩ := Sec6.exists_driver_of_drivingCriteria hS hcR h0R
    (Sec6.hasSimpleApproxOn_of_injOn hS hcR hinj h0R hHb) ha hb
  -- the clock is `σ` on `[0, U]`
  have hclock : ∀ t : ℝ≥0, t ≤ U → chartClock γ t = σ t := by
    intro t ht
    have ht' : (t : ℝ) ∈ Icc 0 S := ⟨t.2, NNReal.coe_le_coe.2 ht⟩
    obtain ⟨hσt, hK, -⟩ := hσK t ht'
    rw [realPath_image_Icc γ (NNReal.coe_nonneg t), Real.toNNReal_coe] at hK
    have := hcap_fwdHull hW hW0 hσt
    unfold chartClock
    rw [← hK, ConformalImage.hcapSet_eq (isHPHull_fwdHull hW hσt), this]
    ring
  have hle : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ (U : ℝ≥0∞) ↔ r ≤ U := fun r => ENNReal.coe_le_coe
  refine ⟨⟨by rw [hclock 0 zero_le]; exact_mod_cast hσ0, fun a ha b hb hab => ?_, ?_,
    fun h => absurd h ENNReal.coe_ne_top⟩, W, hW, hW0, fun t ht => ?_⟩
  · have ha' : a ≤ U := (hle a).1 ha
    have hb' : b ≤ U := (hle b).1 hb
    rw [hclock a ha', hclock b hb']
    exact hσm ⟨a.2, NNReal.coe_le_coe.2 ha'⟩ ⟨b.2, NNReal.coe_le_coe.2 hb'⟩ (NNReal.coe_lt_coe.2 hab)
  · refine (hσc.comp NNReal.continuous_coe.continuousOn fun t ht =>
      ⟨t.2, NNReal.coe_le_coe.2 ((hle t).1 ht)⟩).congr fun t ht => hclock t ((hle t).1 ht)
  · have ht' : (t : ℝ) ∈ Icc 0 S := ⟨t.2, NNReal.coe_le_coe.2 ht⟩
    obtain ⟨hσt, hK, -⟩ := hσK t ht'
    rw [realPath_image_Icc γ (NNReal.coe_nonneg t), Real.toNNReal_coe] at hK
    rw [hclock t ht]
    exact ⟨hσt, hK⟩

end Simple

/-! ### The random reading -/

section Random

variable {X : Type*} [MeasurableSpace X]

open scoped Classical in
/-- The path clamped to `[0, U]` (`0` off the event `E`). -/
def clampPath (E : Set X) (γ : X → ℝ≥0 → ℂ) (U : X → ℝ≥0) (x : X) (r : ℝ≥0) : ℂ :=
  if x ∈ E then γ x (min r (U x)) else 0

open scoped Classical in
/-- The measurable relative capacity clock of the clamped path (`0` off `E`). -/
def capClock (E : Set X) (γ : X → ℝ≥0 → ℂ) (U : X → ℝ≥0) (x : X) (r : ℝ≥0) : ℝ :=
  if x ∈ E then (WholeField.hcapHit (clampPath E γ U x '' Icc 0 r)).toReal / 2 else 0

open scoped Classical in
/-- **The path read in relative capacity time** (`0` off `E`). -/
def capPath (E : Set X) (γ : X → ℝ≥0 → ℂ) (U : X → ℝ≥0) (x : X) (u : ℝ≥0) : ℂ :=
  if x ∈ E then clampPath E γ U x (invClock (capClock E γ U x) (U x) u) else 0

open scoped Classical in
/-- **The capacity lifetime** `a_x(U x)` (`0` off `E`). -/
def capEnd (E : Set X) (γ : X → ℝ≥0 → ℂ) (U : X → ℝ≥0) (x : X) : ℝ≥0∞ :=
  if x ∈ E then ENNReal.ofReal (capClock E γ U x (U x)) else 0

/-- **The data of a random path on a finite random interval**: the event is measurable, the end time and the path at
each time are measurable, and on the event the path is continuous on `[0, U]` and starts at `0`. -/
structure IsPathSpec (E : Set X) (γ : X → ℝ≥0 → ℂ) (U : X → ℝ≥0) : Prop where
  measurableSet : MeasurableSet E
  measU : Measurable U
  measγ : ∀ r, Measurable fun x => γ x r
  cont : ∀ x ∈ E, ContinuousOn (γ x) (Iic (U x))
  zero : ∀ x ∈ E, γ x 0 = 0

variable {E : Set X} {γ : X → ℝ≥0 → ℂ} {U : X → ℝ≥0}

omit [MeasurableSpace X] in
theorem clampPath_of_mem {x : X} (hx : x ∈ E) (r : ℝ≥0) : clampPath E γ U x r = γ x (min r (U x)) := by
  simp [clampPath, hx]

omit [MeasurableSpace X] in
theorem clampPath_of_le {x : X} (hx : x ∈ E) {r : ℝ≥0} (hr : r ≤ U x) : clampPath E γ U x r = γ x r := by
  rw [clampPath_of_mem hx, min_eq_left hr]

omit [MeasurableSpace X] in
theorem clampPath_of_notMem {x : X} (hx : x ∉ E) (r : ℝ≥0) : clampPath E γ U x r = 0 := by
  simp [clampPath, hx]

omit [MeasurableSpace X] in
/-- On the event the clamped path has the image of the path on initial intervals inside `[0, U]`. -/
theorem image_clampPath {x : X} (hx : x ∈ E) {r : ℝ≥0} (hr : r ≤ U x) :
    clampPath E γ U x '' Icc 0 r = γ x '' Icc 0 r :=
  image_congr fun _ hv => clampPath_of_le hx (hv.2.trans hr)

omit [MeasurableSpace X] in
/-- After the end time the clamped path does not grow. -/
theorem image_clampPath_min {x : X} (hx : x ∈ E) (r : ℝ≥0) :
    clampPath E γ U x '' Icc 0 r = clampPath E γ U x '' Icc 0 (min r (U x)) := by
  apply Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨min v (U x), ⟨zero_le, min_le_min_right _ hv.2⟩, ?_⟩
    rw [clampPath_of_mem hx, clampPath_of_mem hx, min_eq_left (min_le_right _ _)]
  · exact image_mono (Icc_subset_Icc_right (min_le_left _ _))

namespace IsPathSpec

variable (hs : IsPathSpec E γ U)
include hs

/-- The clamped path is continuous for every sample. -/
theorem continuous_clampPath (x : X) : Continuous (clampPath E γ U x) := by
  by_cases hx : x ∈ E
  · have h : clampPath E γ U x = γ x ∘ fun r => min r (U x) := funext fun r => clampPath_of_mem hx r
    rw [h]
    exact (hs.cont x hx).comp_continuous (continuous_id.min continuous_const) fun r => mem_Iic.2 (min_le_right _ _)
  · have h : clampPath E γ U x = fun _ => 0 := funext fun r => clampPath_of_notMem hx r
    rw [h]
    exact continuous_const

/-- The clamped path is measurable at every time. -/
theorem measurable_clampPath (r : ℝ≥0) : Measurable fun x => clampPath E γ U x r := by
  classical
  have h := measurable_piecewise_eval hs.measurableSet hs.measγ (s := fun x => min r (U x))
    (measurable_const.min hs.measU) fun x hx => (hs.cont x hx).mono (Iic_subset_Iic.2 (min_le_right _ _))
  exact h

/-- The clamped path is jointly measurable. -/
theorem measurable_uncurry_clampPath : Measurable fun p : ℝ≥0 × X => clampPath E γ U p.2 p.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun r x => clampPath E γ U x r)
    (fun x => hs.continuous_clampPath x) hs.measurable_clampPath

/-- **On the event the measurable clock is the relative capacity clock** of the clamped path. -/
theorem capClock_eq {x : X} (hx : x ∈ E) : capClock E γ U x = chartClock (clampPath E γ U x) := by
  funext r
  have hc := (hs.continuous_clampPath x).continuousOn (s := Icc 0 r)
  have h0 : (clampPath E γ U x 0).im ≤ 0 := by
    rw [clampPath_of_le hx zero_le, hs.zero x hx]; simp
  have hF := isHPHull_fillH_image hc h0
  simp only [capClock, hx, ite_true, chartClock]
  rw [hcapHit_image_eq hc h0, ENNReal.toReal_ofReal]
  rw [ConformalImage.hcapSet_eq hF]
  exact HPHull.hcap_nonneg _

/-- On `[0, U]` the clock is the relative capacity clock of the path itself. -/
theorem capClock_eq_chartClock {x : X} (hx : x ∈ E) {r : ℝ≥0} (hr : r ≤ U x) :
    capClock E γ U x r = chartClock (γ x) r := by
  rw [hs.capClock_eq hx]
  simp only [chartClock]
  rw [image_clampPath hx hr]

theorem measurable_capClock (r : ℝ≥0) : Measurable fun x => capClock E γ U x r := by
  classical
  have h := ((measurable_hcapHit_image hs.continuous_clampPath hs.measurable_clampPath r).ennreal_toReal).div_const
    (2 : ℝ)
  exact Measurable.ite hs.measurableSet h measurable_const

theorem measurable_invClock (u : ℝ≥0) :
    Measurable fun x => invClock (capClock E γ U x) (U x : ℝ≥0∞) u := by
  classical
  refine Measurable.iSup fun q => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  refine (MeasurableSet.const _).inter ((measurableSet_le measurable_const
    (measurable_coe_nnreal_ennreal.comp hs.measU)).inter ?_)
  exact measurableSet_lt (hs.measurable_capClock _) measurable_const

theorem measurable_capPath (u : ℝ≥0) : Measurable fun x => capPath E γ U x u := by
  classical
  have h := hs.measurable_uncurry_clampPath.comp ((hs.measurable_invClock u).prodMk measurable_id)
  exact Measurable.ite hs.measurableSet h measurable_const

variable (hclk : ∀ x ∈ E, IsClockOn (chartClock (γ x)) (U x))
include hclk

/-- **The measurable clock is a clock on `[0, U]`** on the event. -/
theorem isClockOn_capClock {x : X} (hx : x ∈ E) : IsClockOn (capClock E γ U x) (U x) := by
  have hle : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ (U x : ℝ≥0∞) → r ≤ U x := fun r hr => ENNReal.coe_le_coe.1 hr
  have heq : EqOn (capClock E γ U x) (chartClock (γ x)) {r : ℝ≥0 | (r : ℝ≥0∞) ≤ (U x : ℝ≥0∞)} :=
    fun r hr => hs.capClock_eq_chartClock hx (hle r hr)
  obtain ⟨h0, hm, hc, -⟩ := hclk x hx
  refine ⟨(heq (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ (U x : ℝ≥0∞) by simp)).trans h0, ?_, hc.congr heq,
    fun h => absurd h ENNReal.coe_ne_top⟩
  intro a ha b hb hab
  rw [heq ha, heq hb]
  exact hm ha hb hab

/-- The measurable clock is continuous for every sample. -/
theorem continuous_capClock (x : X) : Continuous (capClock E γ U x) := by
  by_cases hx : x ∈ E
  · have h : capClock E γ U x = fun r => capClock E γ U x (min r (U x)) := by
      funext r
      rw [hs.capClock_eq hx]
      simp only [chartClock]
      rw [image_clampPath_min hx r, image_clampPath_min hx (min r (U x)), min_eq_left (min_le_right _ _)]
    rw [h]
    exact (hs.isClockOn_capClock hclk hx).continuousOn.comp_continuous (continuous_id.min continuous_const)
      fun r => ENNReal.coe_le_coe.2 (min_le_right _ _)
  · have : capClock E γ U x = fun _ => 0 := by funext r; simp [capClock, hx]
    rw [this]
    exact continuous_const

theorem measurable_capEnd : Measurable (capEnd E γ U) := by
  classical
  have hj : Measurable fun p : ℝ≥0 × X => capClock E γ U p.2 p.1 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun r x => capClock E γ U x r)
      (fun x => hs.continuous_capClock hclk x) hs.measurable_capClock
  have hv : Measurable fun x => capClock E γ U x (U x) := hj.comp (hs.measU.prodMk measurable_id)
  exact Measurable.ite hs.measurableSet (ENNReal.measurable_ofReal.comp hv) measurable_const

omit [MeasurableSpace X] hs hclk in
/-- On the event the capacity lifetime is `capLife` of the clock. -/
theorem capEnd_eq_capLife {x : X} (hx : x ∈ E) :
    capEnd E γ U x = capLife (capClock E γ U x) (U x : ℝ≥0∞) := by
  simp [capEnd, capLife, hx]

/-- **The path in capacity time is continuous** on `[0, capEnd]` for every sample. -/
theorem continuousOn_capPath (x : X) :
    ContinuousOn (capPath E γ U x) {u : ℝ≥0 | (u : ℝ≥0∞) ≤ capEnd E γ U x} := by
  by_cases hx : x ∈ E
  · have ha := hs.isClockOn_capClock hclk hx
    have h : capPath E γ U x = fun u => clampPath E γ U x (invClock (capClock E γ U x) (U x) u) := by
      funext u; simp [capPath, hx]
    rw [h, capEnd_eq_capLife hx]
    exact (hs.continuous_clampPath x).continuousOn.comp ha.continuousOn_invClock fun _ _ => mem_univ _
  · have : capPath E γ U x = fun _ => 0 := by funext u; simp [capPath, hx]
    rw [this]
    exact continuousOn_const

/-- The path in capacity time starts at `0`. -/
theorem capPath_zero (x : X) : capPath E γ U x 0 = 0 := by
  by_cases hx : x ∈ E
  · have ha := hs.isClockOn_capClock hclk hx
    have h0 : (0 : ℝ≥0∞) ≤ capLife (capClock E γ U x) (U x : ℝ≥0∞) := zero_le
    obtain ⟨hU, hz⟩ := ha.invClock_spec (u := 0) (by exact_mod_cast h0)
    have hinv : invClock (capClock E γ U x) (U x) 0 = 0 := by
      have := ha.strictMonoOn.injOn hU (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ (U x : ℝ≥0∞) by simp)
        (by rw [hz, ha.zero]; simp)
      exact this
    simp only [capPath, hx, ite_true, hinv]
    rw [clampPath_of_le hx zero_le, hs.zero x hx]
  · simp [capPath, hx]

/-- **Reading in capacity time**: on the event, every capacity time `u ≤ capEnd` is the clock value of a unique
original time `r ≤ U`, and the path in capacity time is the path at `r`. -/
theorem capPath_spec {x : X} (hx : x ∈ E) {u : ℝ≥0} (hu : (u : ℝ≥0∞) ≤ capEnd E γ U x) :
    invClock (capClock E γ U x) (U x) u ≤ U x ∧
      chartClock (γ x) (invClock (capClock E γ U x) (U x) u) = u ∧
      capPath E γ U x u = γ x (invClock (capClock E γ U x) (U x) u) := by
  have ha := hs.isClockOn_capClock hclk hx
  rw [capEnd_eq_capLife hx] at hu
  obtain ⟨hU, hz⟩ := ha.invClock_spec hu
  have hU' : invClock (capClock E γ U x) (U x) u ≤ U x := ENNReal.coe_le_coe.1 hU
  refine ⟨hU', ?_, ?_⟩
  · rw [← hs.capClock_eq_chartClock hx hU', hz]
  · simp only [capPath, hx, ite_true]
    rw [clampPath_of_le hx hU']

/-- On the event the path in capacity time traces the same set as the path on `[0, U]`. -/
theorem image_capPath {x : X} (hx : x ∈ E) :
    capPath E γ U x '' {u : ℝ≥0 | (u : ℝ≥0∞) ≤ capEnd E γ U x} = γ x '' Iic (U x) := by
  have ha := hs.isClockOn_capClock hclk hx
  have himg := ha.image_invClock
  apply Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hU, -, he⟩ := hs.capPath_spec hclk hx hu
    exact ⟨_, hU, he.symm⟩
  · rintro _ ⟨r, hr, rfl⟩
    have hr' : r ∈ {r : ℝ≥0 | (r : ℝ≥0∞) ≤ (U x : ℝ≥0∞)} := ENNReal.coe_le_coe.2 hr
    rw [← himg] at hr'
    obtain ⟨u, hu, hur⟩ := hr'
    rw [← capEnd_eq_capLife hx] at hu
    refine ⟨u, hu, ?_⟩
    rw [(hs.capPath_spec hclk hx hu).2.2, hur]

/-- **The path in capacity time is parametrized by capacity**: the relative capacity clock of `capPath x` is the
identity on `[0, capEnd]`. -/
theorem chartClock_capPath {x : X} (hx : x ∈ E) {u : ℝ≥0} (hu : (u : ℝ≥0∞) ≤ capEnd E γ U x) :
    chartClock (capPath E γ U x) u = u := by
  have ha := hs.isClockOn_capClock hclk hx
  obtain ⟨hU, hcl, -⟩ := hs.capPath_spec hclk hx hu
  rw [← hcl]
  simp only [chartClock]
  congr 3
  -- the images of `[0, u]` and `[0, a⁻¹ u]` agree
  have hcapL := capEnd_eq_capLife (γ := γ) (U := U) hx
  apply Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hvu : (v : ℝ≥0∞) ≤ capEnd E γ U x := (ENNReal.coe_le_coe.2 hv.2).trans hu
    obtain ⟨hvU, -, hve⟩ := hs.capPath_spec hclk hx hvu
    refine ⟨_, ⟨zero_le, ?_⟩, hve.symm⟩
    rw [hcapL] at hu hvu
    exact ha.strictMonoOn_invClock.monotoneOn hvu hu hv.2
  · rintro _ ⟨r, hr, rfl⟩
    have hrU : r ≤ U x := hr.2.trans hU
    have hr' : (r : ℝ≥0∞) ≤ (U x : ℝ≥0∞) := ENNReal.coe_le_coe.2 hrU
    set v := (capClock E γ U x r).toNNReal with hv
    have hvc : (v : ℝ≥0∞) ≤ capLife (capClock E γ U x) (U x : ℝ≥0∞) := ha.coe_toNNReal_le_capLife hr'
    have hinv : invClock (capClock E γ U x) (U x) v = r := ha.invClock_apply hr'
    rw [← hcapL] at hvc
    refine ⟨v, ⟨zero_le, ?_⟩, ?_⟩
    · -- `v ≤ u` by monotonicity of the clock
      have hmono := ha.strictMonoOn.monotoneOn hr' (ENNReal.coe_le_coe.2 hU) hr.2
      have hz := (hs.capPath_spec hclk hx hu).2.1
      rw [← hs.capClock_eq_chartClock hx hU] at hz
      rw [hz] at hmono
      rw [hv]
      exact Real.toNNReal_le_iff_le_coe.2 hmono
    · rw [(hs.capPath_spec hclk hx hvc).2.2, hinv]

end IsPathSpec

end Random

end InteractingSLE.Sec5.Aux61FibData
