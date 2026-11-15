/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Read
import InteractingSLE.Spec.Supplement.GW2GmTip

/-!
# J32's running-maximum reader agrees with the exact-horizon reader on the live window

Packet PROVE-GW2-GEOM2 (ruling R110).

* `forwardCapacity_nonneg`, `runMax_nonneg`, `runMax_lt`, **`monotone_runMax`**: at every record pair the
  running maximum is monotone and bounded;
* **`runMax_eq_of_clock`**: where the capacity reader is a clock (monotone and continuous on `[0, w]`), the
  running maximum is `arctan` of the reader;
* **`clockInverse_eq_of_clock`**, `capacityTipRead_eq_of_clock`: for levels up to the capacity at `w`, J32's
  inverse clock (any horizon `v ≥ w`) is I30's inverse clock with the exact horizon `w`;
* `invClock_congr_le`, `rootTipRead_congr_record`, **`capacityDriverRead_eq_of_clock`**: the same for the
  driver reader, transported from the joined record at a cap `L` to I30's reader record `recOf w (J, ⊤)`;
* **`continuousAt_capacityDriverRead_of_clock`**: J32's driver reader is continuous below the capacity
  reached at `w`, for a joined trace before contact up to `w` (from the R5 core, `GW2GmTip`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ32

open Exist Staged StagedLaw Restart RootB23 Supp8.GB6

theorem forwardCapacity_nonneg (x : ℝ) (s t : ℝ≥0) (p : RecData × RecData) :
    0 ≤ RootH29.forwardCapacity x s t p :=
  div_nonneg ENNReal.toReal_nonneg (by norm_num)

theorem runMax_term_nonneg (x : ℝ) (s t : ℝ≥0) (p : RecData × RecData) (q : ℚ) :
    0 ≤ (if ((q : ℝ)).toNNReal ≤ t then
      Real.arctan (RootH29.forwardCapacity x s ((q : ℝ)).toNNReal p) else 0) := by
  split_ifs
  · exact Real.arctan_nonneg.2 (forwardCapacity_nonneg x s _ p)
  · exact le_rfl

theorem runMax_bdd (x : ℝ) (s t : ℝ≥0) (p : RecData × RecData) :
    BddAbove (range fun q : ℚ =>
      if ((q : ℝ)).toNNReal ≤ t then
        Real.arctan (RootH29.forwardCapacity x s ((q : ℝ)).toNNReal p) else 0) := by
  refine ⟨Real.pi / 2, ?_⟩
  rintro _ ⟨q, rfl⟩
  dsimp only
  split_ifs
  · exact (Real.arctan_lt_pi_div_two _).le
  · positivity

theorem runMax_nonneg (x : ℝ) (s t : ℝ≥0) (p : RecData × RecData) : 0 ≤ runMax x s t p :=
  (runMax_term_nonneg x s t p 0).trans (le_ciSup (runMax_bdd x s t p) 0)

/-- **The running maximum is monotone in time**, at every record pair. -/
theorem monotone_runMax (x : ℝ) (s : ℝ≥0) (p : RecData × RecData) :
    Monotone fun t => runMax x s t p := by
  intro t t' htt'
  refine ciSup_mono (runMax_bdd x s t' p) fun q => ?_
  by_cases hq : ((q : ℝ)).toNNReal ≤ t
  · simp only [hq, hq.trans htt', ↓reduceIte, le_refl]
  · simp only [hq, ↓reduceIte]
    exact runMax_term_nonneg x s t' p q

/-- **Where the capacity reader is monotone and continuous, the running maximum is its `arctan`.** -/
theorem runMax_eq_of_clock {x : ℝ} {s w : ℝ≥0} {p : RecData × RecData}
    (hm : MonotoneOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 w))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 w))
    {t : ℝ≥0} (htw : t ≤ w) :
    runMax x s t p = Real.arctan (RootH29.forwardCapacity x s t p) := by
  set g := fun t => Real.arctan (RootH29.forwardCapacity x s t p) with hg
  apply le_antisymm
  · refine ciSup_le fun q => ?_
    split_ifs with hq
    · exact Real.arctan_strictMono.monotone (hm ⟨zero_le, hq.trans htw⟩ ⟨zero_le, htw⟩ hq)
    · exact Real.arctan_nonneg.2 (forwardCapacity_nonneg x s t p)
  · by_contra hlt
    push Not at hlt
    have hε : 0 < g t - runMax x s t p := sub_pos.2 hlt
    have hgc : ContinuousWithinAt g (Icc 0 t) t :=
      (Real.continuous_arctan.comp_continuousOn (hc.mono fun r hr => ⟨zero_le, hr.2.trans htw⟩))
        t ⟨zero_le, le_rfl⟩
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 hgc _ hε
    -- a rational time in `[0, t]` within `δ` of `t`
    obtain ⟨q, hqt, hqδ⟩ : ∃ q : ℚ, ((q : ℝ)).toNNReal ≤ t ∧
        dist ((q : ℝ)).toNNReal t < δ := by
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
      · exact ⟨0, by rw [← h0]; simp, by rw [← h0]; simpa using hδ⟩
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max ((t : ℝ) - δ) 0 < t from
          max_lt (by linarith) (NNReal.coe_pos.2 hpos))
        have hq0 : (0 : ℝ) ≤ q := (le_max_right _ _).trans hq1.le
        refine ⟨q, Real.toNNReal_le_iff_le_coe.2 hq2.le, ?_⟩
        rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_sub_lt_iff]
        constructor <;> linarith [le_max_left ((t : ℝ) - δ) 0]
    have hq0 := hqt
    have hd := hδc ⟨zero_le, hqt⟩ hqδ
    have hle : g ((q : ℝ)).toNNReal ≤ runMax x s t p := by
      have := le_ciSup (runMax_bdd x s t p) q
      simp only [hq0, ↓reduceIte] at this
      exact this
    rw [Real.dist_eq, abs_sub_lt_iff] at hd
    linarith [hd.2]

/-- The inverse clock with the exact horizon `w` only reads the clock on `[0, w]`. -/
theorem invClock_congr_le {a b : ℝ≥0 → ℝ} {w : ℝ≥0} (h : ∀ t ≤ w, a t = b t) (u : ℝ≥0) :
    invClock a (w : ℝ≥0∞) u = invClock b (w : ℝ≥0∞) u := by
  unfold invClock
  congr 1
  funext q
  by_cases hq : (((q : ℝ)).toNNReal : ℝ≥0∞) ≤ (w : ℝ≥0∞)
  · rw [h _ (ENNReal.coe_le_coe.1 hq)]
  · simp only [hq, false_and, and_false, ↓reduceIte]

/-- **J32's inverse clock is I30's exact-horizon inverse clock** for levels up to the capacity at `w`,
whenever the capacity reader is a clock on `[0, w]` and the horizon is `v ≥ w`. -/
theorem clockInverse_eq_of_clock {x : ℝ} {s w v : ℝ≥0} {p : RecData × RecData} (hwv : w ≤ v)
    (hm : MonotoneOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 w))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 w))
    {u : ℝ≥0} (hu : (u : ℝ) ≤ RootH29.forwardCapacity x s w p) :
    clockInverse x s v u p = RootI30.clockInverse x s w u p := by
  unfold clockInverse RootI30.clockInverse invClock
  congr 1
  funext q
  have hlev : (((Real.arctan u).toNNReal : ℝ≥0) : ℝ) = Real.arctan u :=
    Real.coe_toNNReal _ (Real.arctan_nonneg.2 u.2)
  by_cases hqw : (((q : ℝ)).toNNReal : ℝ≥0∞) ≤ (w : ℝ≥0∞)
  · have hqw' : ((q : ℝ)).toNNReal ≤ w := ENNReal.coe_le_coe.1 hqw
    have hqv : (((q : ℝ)).toNNReal : ℝ≥0∞) ≤ (v : ℝ≥0∞) := hqw.trans (ENNReal.coe_le_coe.2 hwv)
    have hiff : runMax x s ((q : ℝ)).toNNReal p < (((Real.arctan u).toNNReal : ℝ≥0) : ℝ) ↔
        RootH29.forwardCapacity x s ((q : ℝ)).toNNReal p < (u : ℝ) := by
      rw [runMax_eq_of_clock hm hc hqw', hlev]
      exact Real.arctan_strictMono.lt_iff_lt
    simp only [hqw, hqv, true_and, hiff]
  · have hfalse : ¬ runMax x s ((q : ℝ)).toNNReal p < (((Real.arctan u).toNNReal : ℝ≥0) : ℝ) := by
      rw [not_lt, hlev]
      have hwq : w ≤ ((q : ℝ)).toNNReal := (lt_of_not_ge fun h => hqw (ENNReal.coe_le_coe.2 h)).le
      calc Real.arctan u ≤ Real.arctan (RootH29.forwardCapacity x s w p) :=
            Real.arctan_strictMono.monotone hu
        _ = runMax x s w p := (runMax_eq_of_clock hm hc le_rfl).symm
        _ ≤ runMax x s ((q : ℝ)).toNNReal p := monotone_runMax x s p hwq
    simp only [hqw, hfalse, false_and, and_false, ↓reduceIte]

theorem capacityTipRead_eq_of_clock {x : ℝ} {s w v : ℝ≥0} {p : RecData × RecData}
    (hwv : w ≤ v) (hm : MonotoneOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 w))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 w))
    {u : ℝ≥0} (hu : (u : ℝ) ≤ RootH29.forwardCapacity x s w p) :
    capacityTipRead x s v u p = RootI30.capacityTipRead x s w u p := by
  rw [capacityTipRead, clockInverse_eq_of_clock hwv hm hc hu]
  rfl

/-- The centered tip reader at times up to `w` is the same for the joined record at a cap `L ≥ w` and for
I30's reader record at `w`. -/
theorem rootTipRead_congr_record {x : ℝ} {s : ℝ≥0} {p₁ : RecData} {J : ℝ≥0 → ℝ}
    (hJ : Continuous J) (hJ0 : J 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace J ⊤ γ)
    {w L t : ℝ≥0} (hwL : w ≤ L) (htw : t ≤ w) :
    RootH29.rootTipRead x s t (p₁, StagedEntrance.Strip.recOfDriver L J) =
      RootH29.rootTipRead x s t (p₁, recOf (w : ℝ≥0∞) (J, ⊤)) := by
  have he := Gm.isRegularDriver_top hJ hJ0
  have h1 : RootA22.physicalTipRead (StagedEntrance.Strip.recOfDriver L J, t) = γ t := by
    rw [Gm.recOfDriver_eq_recOf]
    exact RootA22.physicalTipRead_recOf_eq he hγ ENNReal.coe_lt_top (htw.trans hwL)
  have h2 : RootA22.physicalTipRead (recOf (w : ℝ≥0∞) (J, ⊤), t) = γ t :=
    RootA22.physicalTipRead_recOf_eq he hγ ENNReal.coe_lt_top htw
  unfold RootH29.rootTipRead
  rw [h1, h2]

/-- **J32's driver reader on the live window is I30's reader driver** for the joined trace: at capacities up
to the capacity at `w`, with the joined record at the cap `L ≥ v ≥ w`. -/
theorem capacityDriverRead_eq_of_clock {x : ℝ} {s w v L : ℝ≥0} {p₁ : RecData}
    {J : ℝ≥0 → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace J ⊤ γ)
    (hwv : w ≤ v) (hwL : w ≤ L)
    (hm : MonotoneOn (fun t => RootH29.forwardCapacity x s t
      (p₁, StagedEntrance.Strip.recOfDriver L J)) (Icc 0 w))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t
      (p₁, StagedEntrance.Strip.recOfDriver L J)) (Icc 0 w))
    {c : ℝ≥0} (hcw : (c : ℝ) ≤ RootH29.forwardCapacity x s w
      (p₁, StagedEntrance.Strip.recOfDriver L J)) :
    capacityDriverRead x s v c (p₁, StagedEntrance.Strip.recOfDriver L J) =
      RootJ31.capacityDriverRead x s w c (p₁, recOf (w : ℝ≥0∞) (J, ⊤)) := by
  -- the capacity readers agree on `[0, w]`
  have hA : ∀ t ≤ w, RootH29.forwardCapacity x s t (p₁, StagedEntrance.Strip.recOfDriver L J) =
      RootH29.forwardCapacity x s t (p₁, recOf (w : ℝ≥0∞) (J, ⊤)) := by
    intro t htw
    refine Gm.forwardCapacity_congr x s t p₁ fun y hy => ?_
    have hy0 : 0 ≤ y := hy.1
    have hyw : y.toNNReal ≤ w := Real.toNNReal_le_iff_le_coe.2 (hy.2.trans (NNReal.coe_le_coe.2 htw))
    have e1 := Gm.rdrv_recOfDriver hJ hJ0 (q₀ := L) y.toNNReal
    have e2 := Gm.rdrv_recOfDriver hJ hJ0 (q₀ := w) y.toNNReal
    rw [Real.coe_toNNReal _ hy0] at e1 e2
    rw [e1, ← Gm.recOfDriver_eq_recOf, e2, min_eq_left hyw, min_eq_left (hyw.trans hwL)]
  unfold capacityDriverRead RootJ31.capacityDriverRead
  refine traceDriverRead_congr_prefix fun u hu => ?_
  have hu' : (u : ℝ) ≤ RootH29.forwardCapacity x s w (p₁, StagedEntrance.Strip.recOfDriver L J) :=
    (NNReal.coe_le_coe.2 hu.2).trans hcw
  change capacityTipRead x s v u _ = RootI30.capacityTipRead x s w u _
  rw [capacityTipRead_eq_of_clock hwv hm hc hu', RootI30.capacityTipRead, RootI30.capacityTipRead,
    RootI30.clockInverse, RootI30.clockInverse, invClock_congr_le hA]
  have hτ : invClock (fun t => RootH29.forwardCapacity x s t (p₁, recOf (w : ℝ≥0∞) (J, ⊤)))
      (w : ℝ≥0∞) u ≤ w := by
    unfold invClock
    apply ciSup_le
    intro q
    split_ifs with hq
    · exact ENNReal.coe_le_coe.mp hq.2.1
    · exact zero_le
  exact rootTipRead_congr_record hJ hJ0 hγ hwL hτ

/-- **J32's driver reader is continuous below the capacity reached at `w`**, for a joined trace whose
record is before contact up to `w` (R5 core). -/
theorem continuousAt_capacityDriverRead_of_clock {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (ω : Ω) {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α) (hW : Continuous (W · ω))
    (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤) {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x)
    (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1) {J : ℝ≥0 → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0)
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace J ⊤ γ) {w v L : ℝ≥0} (hwv : w ≤ v) (hwL : w ≤ L)
    (hnc : ∀ t ∈ Icc 0 w, ∀ u ∈ Icc 0 s, ((x : ℂ) + γ t) * α u + 1 ≠ 0)
    (hm : MonotoneOn (fun t => RootH29.forwardCapacity x s t
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) (Icc 0 w))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) (Icc 0 w))
    {c₀ : ℝ≥0} (hc₀ : (c₀ : ℝ) < RootH29.forwardCapacity x s w
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) :
    ContinuousAt (fun c => capacityDriverRead x s v c
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) c₀ := by
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous α := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hv : (w : ℝ≥0∞) < min (firstContactTime
      (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) (J, (⊤ : ℝ≥0∞)).2 := by
    change _ < min _ ⊤
    rw [min_top_right]
    exact (Gm.lt_firstContactTime_iff_noncontact (continuous_const.add hγc) hαc w s).2 hnc
  have hAw : RootH29.forwardCapacity x s w (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J) =
      RootH29.forwardCapacity x s w (cfRec s W ζ ω, recOf (w : ℝ≥0∞) (J, ⊤)) := by
    refine Gm.forwardCapacity_congr x s w _ fun y hy => ?_
    have hy0 : 0 ≤ y := hy.1
    have hyw : y.toNNReal ≤ w := Real.toNNReal_le_iff_le_coe.2 hy.2
    have e1 := Gm.rdrv_recOfDriver hJ hJ0 (q₀ := L) y.toNNReal
    have e2 := Gm.rdrv_recOfDriver hJ hJ0 (q₀ := w) y.toNNReal
    rw [Real.coe_toNNReal _ hy0] at e1 e2
    rw [e1, ← Gm.recOfDriver_eq_recOf, e2, min_eq_left hyw, min_eq_left (hyw.trans hwL)]
  have hcont := Gm.continuousAt_capacityDriverRead W ζ ω hα hW hW0 hζ hs hx harc
    (Gm.isRegularDriver_top hJ hJ0) hγ hv (u := c₀) (by rw [← hAw]; exact hc₀)
  have hev : ∀ᶠ c : ℝ≥0 in 𝓝 c₀, ((c : ℝ≥0) : ℝ) ≤ RootH29.forwardCapacity x s w
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J) :=
    (NNReal.continuous_coe.continuousAt.eventually (gt_mem_nhds hc₀)).mono fun _ h => h.le
  refine hcont.congr ?_
  filter_upwards [hev] with c hc'
  exact (capacityDriverRead_eq_of_clock hJ hJ0 hγ hwv hwL hm hc hc').symm

end InteractingSLE.Theorem14.GW2TipSystem.RootJ32
