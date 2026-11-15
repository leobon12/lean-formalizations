/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Cross

/-!
# J32's readers are causal (reader consistency, deterministic part)

Packet PROVE-GW2-GEOM2, ruling R111, item (3). Every J32 reader evaluated at times up to `w` depends on the joined
record only through its driver on `[0, w]` (and its lifetime being at least `w`): two record pairs with the same
counterflow record whose joined drivers agree on `[0, w]` give the same

* capacity readers and running maxima on `[0, w]` (`forwardCapacity_congr_le`, `runMax_congr_le`);
* inverse clocks at levels reached by `w` (`clockInverse_congr_le`, which also lands in `[0, w]`);
* physical and root-chart tips up to `w` (`physicalTipRead_congr_le`, `rootTipRead_congr_le`);
* capacity tips and capacity drivers at levels reached by `w` (`capacityTipRead_congr_le`,
  `capacityDriverRead_congr_le`);
* stage drivers whose levels are reached by `w` (`stageDriverRead_congr_le`).

This is the deterministic half of the a.s. reader consistency: the candidate's future record (horizon `T + cap`)
and the next history's record (horizon `q'`) have the same joined driver on `[0, q']`
(`futureJoined_eq_joinDrv_query`), so their readers agree on the query window.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootB23 RootJ32

section Causal

variable {x : ℝ} {s w : ℝ≥0} {p₁ r r' : RecData}

theorem forwardCapacity_congr_le (hdrv : ∀ y : ℝ≥0, y ≤ w → rdrv r y = rdrv r' y) {t : ℝ≥0}
    (htw : t ≤ w) :
    RootH29.forwardCapacity x s t (p₁, r) = RootH29.forwardCapacity x s t (p₁, r') :=
  forwardCapacity_congr x s t p₁ fun y hy => by
    have hy0 : 0 ≤ y := hy.1
    have h := hdrv y.toNNReal ((Real.toNNReal_le_iff_le_coe.2 hy.2).trans htw)
    rwa [Real.coe_toNNReal _ hy0] at h

theorem runMax_congr_le (hdrv : ∀ y : ℝ≥0, y ≤ w → rdrv r y = rdrv r' y) {t : ℝ≥0}
    (htw : t ≤ w) : runMax x s t (p₁, r) = runMax x s t (p₁, r') := by
  unfold runMax
  congr 1
  funext q
  by_cases hq : ((q : ℝ)).toNNReal ≤ t
  · simp only [hq, ↓reduceIte]
    rw [forwardCapacity_congr_le hdrv (hq.trans htw)]
  · simp only [hq, ↓reduceIte]

/-- J32's inverse clock lands in `[0, w]` at levels reached by `w`. -/
theorem clockInverse_le_of_level {p : RecData × RecData} {v : ℝ≥0} (hwv : w ≤ v) {u : ℝ≥0}
    (hu : ((Real.arctan u).toNNReal : ℝ) ≤ runMax x s w p) : clockInverse x s v u p ≤ w := by
  unfold clockInverse
  rw [invClock_eq_of_monotoneOn hwv ((monotone_runMax x s p).monotoneOn _) hu]
  exact invClock_le_horizon _

theorem clockInverse_congr_le (hdrv : ∀ y : ℝ≥0, y ≤ w → rdrv r y = rdrv r' y) {v v' : ℝ≥0}
    (hwv : w ≤ v) (hwv' : w ≤ v') {u : ℝ≥0}
    (hu : ((Real.arctan u).toNNReal : ℝ) ≤ runMax x s w (p₁, r)) :
    clockInverse x s v u (p₁, r) = clockInverse x s v' u (p₁, r') := by
  have hu' : ((Real.arctan u).toNNReal : ℝ) ≤ runMax x s w (p₁, r') := by
    rwa [← runMax_congr_le hdrv le_rfl]
  unfold clockInverse
  rw [invClock_eq_of_monotoneOn hwv ((monotone_runMax x s _).monotoneOn _) hu,
    invClock_eq_of_monotoneOn hwv' ((monotone_runMax x s _).monotoneOn _) hu']
  exact invClock_congr_le (fun t ht => runMax_congr_le hdrv ht) _

/-- **The physical tip is causal**: up to `w`, it reads the record's driver on `[0, w]` only. -/
theorem physicalTipRead_congr_le (hdrv : ∀ y : ℝ≥0, y ≤ w → rdrv r y = rdrv r' y)
    (hr : (w : ℝ≥0∞) ≤ r.2.1) (hr' : (w : ℝ≥0∞) ≤ r'.2.1) (h0 : 0 < r.2.1) (h0' : 0 < r'.2.1)
    {t : ℝ≥0} (htw : t ≤ w) :
    RootA22.physicalTipRead (r, t) = RootA22.physicalTipRead (r', t) := by
  have key : ∀ τ : ℝ≥0, τ ≤ t → (τ : ℝ≥0∞) < r.2.1 → (τ : ℝ≥0∞) < r'.2.1 →
      RootU19.recordTrace r τ = RootU19.recordTrace r' τ := by
    intro τ hτ h1 h2
    simp only [RootU19.recordTrace, LP.drivingTrace, h1, h2, ↓reduceIte]
    exact LP.traceAt_congr fun y hy => hdrv y (hy.trans (hτ.trans htw))
  change (if (t : ℝ≥0∞) = 0 then RootU19.recordTrace r 0 else limUnder atTop fun n =>
      RootU19.recordTrace r (LP.dyadicBelow n (t : ℝ≥0∞).toNNReal)) =
    (if (t : ℝ≥0∞) = 0 then RootU19.recordTrace r' 0 else limUnder atTop fun n =>
      RootU19.recordTrace r' (LP.dyadicBelow n (t : ℝ≥0∞).toNNReal))
  by_cases ht0 : (t : ℝ≥0∞) = 0
  · simp only [ht0, ↓reduceIte]
    exact key 0 zero_le (by rw [ENNReal.coe_zero]; exact h0) (by rw [ENNReal.coe_zero]; exact h0')
  · simp only [ht0, ↓reduceIte, ENNReal.toNNReal_coe]
    have htpos : 0 < t := pos_iff_ne_zero.2 fun h => ht0 (by rw [h, ENNReal.coe_zero])
    congr 1
    funext n
    have hlt := LP.dyadicBelow_lt htpos n
    have hlw : ((LP.dyadicBelow n t : ℝ≥0) : ℝ≥0∞) < (w : ℝ≥0∞) :=
      ENNReal.coe_lt_coe.2 (hlt.trans_le htw)
    exact key _ hlt.le (hlw.trans_le hr) (hlw.trans_le hr')

theorem rootTipRead_congr_le (hdrv : ∀ y : ℝ≥0, y ≤ w → rdrv r y = rdrv r' y)
    (hr : (w : ℝ≥0∞) ≤ r.2.1) (hr' : (w : ℝ≥0∞) ≤ r'.2.1) (h0 : 0 < r.2.1) (h0' : 0 < r'.2.1)
    {t : ℝ≥0} (htw : t ≤ w) :
    RootH29.rootTipRead x s t (p₁, r) = RootH29.rootTipRead x s t (p₁, r') := by
  change RootH29.rootChartRead x s (p₁, RootA22.physicalTipRead (r, t)) =
    RootH29.rootChartRead x s (p₁, RootA22.physicalTipRead (r', t))
  rw [physicalTipRead_congr_le hdrv hr hr' h0 h0' htw]

theorem capacityTipRead_congr_le (hdrv : ∀ y : ℝ≥0, y ≤ w → rdrv r y = rdrv r' y)
    (hr : (w : ℝ≥0∞) ≤ r.2.1) (hr' : (w : ℝ≥0∞) ≤ r'.2.1) (h0 : 0 < r.2.1) (h0' : 0 < r'.2.1)
    {v v' : ℝ≥0} (hwv : w ≤ v) (hwv' : w ≤ v') {u : ℝ≥0}
    (hu : ((Real.arctan u).toNNReal : ℝ) ≤ runMax x s w (p₁, r)) :
    capacityTipRead x s v u (p₁, r) = capacityTipRead x s v' u (p₁, r') := by
  have hu' : ((Real.arctan u).toNNReal : ℝ) ≤ runMax x s w (p₁, r') := by
    rwa [← runMax_congr_le hdrv le_rfl]
  unfold capacityTipRead
  rw [clockInverse_congr_le hdrv hwv hwv' hu]
  exact rootTipRead_congr_le hdrv hr hr' h0 h0' (clockInverse_le_of_level hwv' hu')

/-- Levels below a reached level are reached. -/
theorem level_le_of_le {p : RecData × RecData} {u u' : ℝ≥0} (huu' : u ≤ u')
    (hu : ((Real.arctan u').toNNReal : ℝ) ≤ runMax x s w p) :
    ((Real.arctan u).toNNReal : ℝ) ≤ runMax x s w p :=
  le_trans (NNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal
    (Real.arctan_strictMono.monotone (NNReal.coe_le_coe.2 huu')))) hu

theorem capacityDriverRead_congr_le (hdrv : ∀ y : ℝ≥0, y ≤ w → rdrv r y = rdrv r' y)
    (hr : (w : ℝ≥0∞) ≤ r.2.1) (hr' : (w : ℝ≥0∞) ≤ r'.2.1) (h0 : 0 < r.2.1) (h0' : 0 < r'.2.1)
    {v v' : ℝ≥0} (hwv : w ≤ v) (hwv' : w ≤ v') {u : ℝ≥0}
    (hu : ((Real.arctan u).toNNReal : ℝ) ≤ runMax x s w (p₁, r)) :
    capacityDriverRead x s v u (p₁, r) = capacityDriverRead x s v' u (p₁, r') := by
  unfold capacityDriverRead
  exact traceDriverRead_congr_prefix fun t ht =>
    capacityTipRead_congr_le hdrv hr hr' h0 h0' hwv hwv' (level_le_of_le ht.2 hu)

/-- **A reached level, from a clock**: on a clock window `[0, w]`, every capacity attained at a time `τ ≤ w` is a
level reached by `w`. -/
theorem level_le_runMax_of_clock {p : RecData × RecData}
    (hm : MonotoneOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 w))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 w))
    {τ : ℝ≥0} (hτ : τ ≤ w) {u : ℝ≥0} (hu : (u : ℝ) ≤ RootH29.forwardCapacity x s τ p) :
    ((Real.arctan u).toNNReal : ℝ) ≤ runMax x s w p := by
  have hlev : (((Real.arctan u).toNNReal : ℝ≥0) : ℝ) = Real.arctan u :=
    Real.coe_toNNReal _ (Real.arctan_nonneg.2 (NNReal.coe_nonneg u))
  rw [hlev]
  refine le_trans ?_ (monotone_runMax x s p hτ)
  show _ ≤ runMax x s τ p
  rw [runMax_eq_of_clock (hm.mono (Icc_subset_Icc le_rfl hτ)) (hc.mono (Icc_subset_Icc le_rfl hτ)) le_rfl]
  exact Real.arctan_strictMono.monotone hu

theorem stageDriverRead_congr_le (hdrv : ∀ y : ℝ≥0, y ≤ w → rdrv r y = rdrv r' y)
    (hr : (w : ℝ≥0∞) ≤ r.2.1) (hr' : (w : ℝ≥0∞) ≤ r'.2.1) (h0 : 0 < r.2.1) (h0' : 0 < r'.2.1)
    {v v' : ℝ≥0} (hwv : w ≤ v) (hwv' : w ≤ v') (a : ℝ≥0) (ε : ℝ) {v₀ T u : ℝ≥0}
    (hv₀ : v₀ ≤ w) (hT : T ≤ w)
    (hu : ((Real.arctan (((RootH29.forwardCapacity x s T (p₁, r)).toNNReal + u / a ^ 2 : ℝ≥0) :
      ℝ)).toNNReal : ℝ) ≤ runMax x s w (p₁, r))
    (hu₀ : ((Real.arctan (RootH29.forwardCapacity x s v₀ (p₁, r)).toNNReal).toNNReal : ℝ) ≤
      runMax x s w (p₁, r)) :
    stageDriverRead a ε x s v v₀ T u (p₁, r) = stageDriverRead a ε x s v' v₀ T u (p₁, r') := by
  unfold stageDriverRead
  rw [capacityDriverRead_congr_le hdrv hr hr' h0 h0' hwv hwv' hu,
    capacityDriverRead_congr_le hdrv hr hr' h0 h0' hwv hwv' hu₀,
    forwardCapacity_congr_le hdrv hT, forwardCapacity_congr_le hdrv hv₀]

/-- The lifetime of a driver record is its horizon. -/
theorem recOfDriver_life (q₀ : ℝ≥0) (W : ℝ≥0 → ℝ) :
    (StagedEntrance.Strip.recOfDriver q₀ W).2.1 = (q₀ : ℝ≥0∞) := by
  rw [recOfDriver_eq_recOf]
  change min (q₀ : ℝ≥0∞) ⊤ = _
  exact min_top_right _

/-- **Reader consistency for driver records**: a record of horizon `L` and a record of horizon `w ≤ L` whose
continuous drivers agree on `[0, w]` give the same J32 stage driver at levels reached by `w`. (Applied with the
candidate's future record, `L = T + cap`, and the next history's joined record, `w = q'`.) -/
theorem stageDriverRead_recOfDriver_congr {J J' : ℝ≥0 → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0)
    (hJ' : Continuous J') (hJ'0 : J' 0 = 0) {L : ℝ≥0} (hwL : w ≤ L) (hw0 : 0 < w)
    (hJJ : ∀ y ≤ w, J y = J' y) {v v' : ℝ≥0} (hwv : w ≤ v) (hwv' : w ≤ v') (a : ℝ≥0) (ε : ℝ)
    {v₀ T u : ℝ≥0} (hv₀ : v₀ ≤ w) (hT : T ≤ w)
    (hu : ((Real.arctan (((RootH29.forwardCapacity x s T
      (p₁, StagedEntrance.Strip.recOfDriver L J)).toNNReal + u / a ^ 2 : ℝ≥0) : ℝ)).toNNReal : ℝ) ≤
        runMax x s w (p₁, StagedEntrance.Strip.recOfDriver L J))
    (hu₀ : ((Real.arctan (RootH29.forwardCapacity x s v₀
      (p₁, StagedEntrance.Strip.recOfDriver L J)).toNNReal).toNNReal : ℝ) ≤
        runMax x s w (p₁, StagedEntrance.Strip.recOfDriver L J)) :
    stageDriverRead a ε x s v v₀ T u (p₁, StagedEntrance.Strip.recOfDriver L J) =
      stageDriverRead a ε x s v' v₀ T u (p₁, StagedEntrance.Strip.recOfDriver w J') := by
  refine stageDriverRead_congr_le (fun y hy => ?_) ?_ ?_ ?_ ?_ hwv hwv' a ε hv₀ hT hu hu₀
  · rw [rdrv_recOfDriver hJ hJ0, rdrv_recOfDriver hJ' hJ'0, min_eq_left (hy.trans hwL),
      min_eq_left hy, hJJ y hy]
  · rw [recOfDriver_life]; exact ENNReal.coe_le_coe.2 hwL
  · rw [recOfDriver_life]
  · rw [recOfDriver_life]; exact ENNReal.coe_pos.2 (hw0.trans_le hwL)
  · rw [recOfDriver_life]; exact ENNReal.coe_pos.2 hw0

end Causal

section Next

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The history record pair is retained**: the counterflow record and the joined record of a history's
program are `c.sigma r l`-measurable. For the next history `(θ, q') :: l` this is the record pair whose J32 readers
are compared, on the query window, with the candidate's future pair. -/
theorem measurable_historyPair_sigma (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    Measurable[c.sigma r l] fun ω => (cfRec c.s c.W c.ζ ω,
      RootJ31.joinedRecord (RootJ31.historyProgram c r l)
        (RootJ31.programRecords c (rootPt r.1) (RootJ31.historyProgram c r l) ω)) := by
  have hlen : (RootJ31.historyProgram c r l).length = (entryList l).length + 1 := by
    simp only [RootJ31.historyProgram, schedOf, List.length_cons, List.length_reverse]
  have hsig : c.sigma r l = stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l))
        (RootJ31.historyProgram c r l).length := by
    rw [hlen]
    rfl
  rw [hsig]
  exact (measurable_fst.comp (comap_measurable _)).prodMk
    ((RootJ31.measurable_joinedRecord _).comp (measurable_snd.comp (comap_measurable _)))

end Next

end InteractingSLE.Theorem14.GW2TipSystem.Gm
