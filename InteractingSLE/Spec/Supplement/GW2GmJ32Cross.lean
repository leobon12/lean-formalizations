/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmCross
import InteractingSLE.Spec.Supplement.GW2GmJ32Iface

/-!
# J32's cross-program identity: the next stage driver starts at minus the passed reading

Packet PROVE-GW2-GEOM2 (ruling R111). After a passed test at `q` for the candidate `a₀` of history `l`, the next
history is `(θ, q) :: l`. Its stage driver starts (capacity `0`) at minus the reading `X_l(q)`: the sign flips
(`(-1)^{|l|+1}`), the base capacity is the root's, and the two future programs have the same joined driver on
`[0, q]`, hence the same capacity readers there.

* `invClock_eq_of_monotoneOn`: the rational inverse at a level reached by `q` only reads the clock on `[0, q]`;
* **`capacityDriverRead_I30_congr`**: I30's exact-horizon driver readers of two joined traces agree at capacities
  reached by `q`, when the drivers agree on `[0, q]`;
* `sourceDriver_eq_I30`: J32's stage driver of a live sample through I30's exact-horizon reader;
* **`ae_sourceDriver_cons_zero`**: almost surely, at a passed test `q` of `(l, a₀)` after an alive `l` and a live
  next sample `((θ, q) :: l, a)`, `Y_{(θ,q)::l, a}(0) = −X_{l, a₀}(q)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootB23

/-- The rational inverse at a level reached by `q` only reads the clock on `[0, q]`. -/
theorem invClock_eq_of_monotoneOn {a : ℝ≥0 → ℝ} {q w : ℝ≥0} (hqw : q ≤ w)
    (hm : MonotoneOn a (Icc 0 w)) {u : ℝ≥0} (hu : (u : ℝ) ≤ a q) :
    invClock a (w : ℝ≥0∞) u = invClock a (q : ℝ≥0∞) u := by
  unfold invClock
  congr 1
  funext r
  by_cases hrq : ((r : ℝ)).toNNReal ≤ q
  · have h1 : ((((r : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (w : ℝ≥0∞) :=
      ENNReal.coe_le_coe.2 (hrq.trans hqw)
    have h2 : ((((r : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (q : ℝ≥0∞) := ENNReal.coe_le_coe.2 hrq
    simp only [h1, h2, true_and]
  · have h2 : ¬ ((((r : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (q : ℝ≥0∞) := fun h =>
      hrq (ENNReal.coe_le_coe.1 h)
    by_cases h1 : ((((r : ℝ)).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (w : ℝ≥0∞)
    · have hnot : ¬ a ((r : ℝ)).toNNReal < u := by
        rw [not_lt]
        exact hu.trans (hm ⟨zero_le, hqw⟩ ⟨zero_le, ENNReal.coe_le_coe.1 h1⟩ (le_of_not_ge hrq))
      simp only [h1, h2, hnot, and_false, ↓reduceIte]
    · simp only [h1, h2, false_and, and_false, ↓reduceIte]

theorem invClock_le_horizon {a : ℝ≥0 → ℝ} {w : ℝ≥0} (u : ℝ≥0) : invClock a (w : ℝ≥0∞) u ≤ w := by
  unfold invClock
  apply ciSup_le
  intro q
  split_ifs with hq
  · exact ENNReal.coe_le_coe.mp hq.2.1
  · exact zero_le

/-- The capacity reader of a joined record only reads the joined driver on `[0, t]`. -/
theorem forwardCapacity_recOf_congr {x : ℝ} {s : ℝ≥0} {p₁ : RecData} {J J' : ℝ≥0 → ℝ}
    (hJ : Continuous J) (hJ0 : J 0 = 0) (hJ' : Continuous J') (hJ'0 : J' 0 = 0)
    {w w' t : ℝ≥0} (htw : t ≤ w) (htw' : t ≤ w') (hJJ : ∀ y ≤ t, J y = J' y) :
    RootH29.forwardCapacity x s t (p₁, recOf (w : ℝ≥0∞) (J, ⊤)) =
      RootH29.forwardCapacity x s t (p₁, recOf (w' : ℝ≥0∞) (J', ⊤)) := by
  refine forwardCapacity_congr x s t p₁ fun y hy => ?_
  have hy0 : 0 ≤ y := hy.1
  have hyt : y.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hy.2
  have e1 := rdrv_recOfDriver hJ hJ0 (q₀ := w) y.toNNReal
  have e2 := rdrv_recOfDriver hJ' hJ'0 (q₀ := w') y.toNNReal
  rw [Real.coe_toNNReal _ hy0, recOfDriver_eq_recOf] at e1 e2
  rw [e1, e2, min_eq_left (hyt.trans htw), min_eq_left (hyt.trans htw'), hJJ _ hyt]

/-- **I30's exact-horizon driver readers of two joined traces agree** at capacities reached by `q`, when the
joined drivers agree on `[0, q]` and both capacity readers are monotone on their horizons. -/
theorem capacityDriverRead_I30_congr {x : ℝ} {s : ℝ≥0} {p₁ : RecData} {J J' : ℝ≥0 → ℝ}
    (hJ : Continuous J) (hJ0 : J 0 = 0) (hJ' : Continuous J') (hJ'0 : J' 0 = 0)
    {γ γ' : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace J ⊤ γ) (hγ' : IsGeneratingTrace J' ⊤ γ')
    {q w w' : ℝ≥0} (hqw : q ≤ w) (hqw' : q ≤ w') (hJJ : ∀ t ≤ q, J t = J' t)
    (hm : MonotoneOn (fun t => RootH29.forwardCapacity x s t (p₁, recOf (w : ℝ≥0∞) (J, ⊤)))
      (Icc 0 w))
    (hm' : MonotoneOn (fun t => RootH29.forwardCapacity x s t (p₁, recOf (w' : ℝ≥0∞) (J', ⊤)))
      (Icc 0 w'))
    {c : ℝ≥0} (hc : (c : ℝ) ≤ RootH29.forwardCapacity x s q (p₁, recOf (w : ℝ≥0∞) (J, ⊤))) :
    RootJ31.capacityDriverRead x s w c (p₁, recOf (w : ℝ≥0∞) (J, ⊤)) =
      RootJ31.capacityDriverRead x s w' c (p₁, recOf (w' : ℝ≥0∞) (J', ⊤)) := by
  have hA : ∀ t ≤ q, RootH29.forwardCapacity x s t (p₁, recOf (w : ℝ≥0∞) (J, ⊤)) =
      RootH29.forwardCapacity x s t (p₁, recOf (w' : ℝ≥0∞) (J', ⊤)) := fun t ht =>
    forwardCapacity_recOf_congr hJ hJ0 hJ' hJ'0 (ht.trans hqw) (ht.trans hqw')
      fun y hy => hJJ y (hy.trans ht)
  have htr := trace_eq_of_driver_eqOn hJ hJ0 hJ' hJ'0 hγ hγ' hJJ
  unfold RootJ31.capacityDriverRead
  refine traceDriverRead_congr_prefix fun u hu => ?_
  have hu1 : (u : ℝ) ≤ RootH29.forwardCapacity x s q (p₁, recOf (w : ℝ≥0∞) (J, ⊤)) :=
    (NNReal.coe_le_coe.2 hu.2).trans hc
  have hu2 : (u : ℝ) ≤ RootH29.forwardCapacity x s q (p₁, recOf (w' : ℝ≥0∞) (J', ⊤)) := by
    rw [← hA q le_rfl]; exact hu1
  change RootH29.rootTipRead x s (invClock _ (w : ℝ≥0∞) u) _ =
    RootH29.rootTipRead x s (invClock _ (w' : ℝ≥0∞) u) _
  rw [invClock_eq_of_monotoneOn hqw hm hu1, invClock_eq_of_monotoneOn hqw' hm' hu2,
    RootJ32.invClock_congr_le hA u]
  have hτ := invClock_le_horizon (a := fun t => RootH29.forwardCapacity x s t
    (p₁, recOf (w' : ℝ≥0∞) (J', ⊤))) (w := q) u
  set τ := invClock (fun t => RootH29.forwardCapacity x s t (p₁, recOf (w' : ℝ≥0∞) (J', ⊤)))
    (q : ℝ≥0∞) u
  have he : IsRegularDriver (J, ⊤) := isRegularDriver_top hJ hJ0
  have he' : IsRegularDriver (J', ⊤) := isRegularDriver_top hJ' hJ'0
  unfold RootH29.rootTipRead
  rw [RootA22.physicalTipRead_recOf_eq he hγ ENNReal.coe_lt_top (hτ.trans hqw),
    RootA22.physicalTipRead_recOf_eq he' hγ' ENNReal.coe_lt_top (hτ.trans hqw'), htr τ hτ]

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- The history time of the next history is the query time. -/
theorem historyTime_cons (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (θ : c.Θ) (q : c.Q) :
    RootJ31.historyTime c r ((θ, q) :: l) = q := by
  unfold RootJ31.historyTime
  rw [RootJ31.historyProgram_cons, List.length_append, List.length_singleton,
    schedTime_succ_eq_getElem (by simp)]
  simp

omit [StandardBorelSpace Ω] in
/-- The root's time is at most the history time of a time-ordered history. -/
theorem rootTime_le_historyTime (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q))
    (hord : Sec5.Prop513Schedule.TimeOrdered 0 (RootJ31.historyProgram c r l)) :
    (rootEntry r.1).2 ≤ RootJ31.historyTime c r l := by
  rw [RootJ31.historyTime, schedTime_length_eq_lastTime]
  exact le_lastTime_of_mem hord (rootEntry r.1) (by simp [RootJ31.historyProgram, schedOf])

/-- **J32's cross-program identity**: almost surely, at a passed test `q` of `(l, a₀)` after an alive history
`l`, the next history's stage driver of any live candidate `a` starts at minus the reading at `q`. -/
theorem ae_sourceDriver_cons_zero (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a₀ : ℕ) (q : c.Q) (a : ℕ),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ω ∈ (RootJ32.experiment c r).data.tests l a₀ q →
      0 < (RootJ31.sourceSample c r ((RootJ31.candidateAngle c r a₀, q) :: l) a ω).1 →
      RootJ32.sourceDriver c r ((RootJ31.candidateAngle c r a₀, q) :: l) a ω 0 =
        -RootJ32.sourceX c r l a₀ ω q := by
  filter_upwards [ae_live_clock h13 c r, ae_futureJoined_trace h13 c r]
    with ω hclock hjoin l a₀ q a halive htest hlive
  set θ := RootJ31.candidateAngle c r a₀ with hθ
  set l' := (θ, q) :: l with hl'
  set x := rootPt r.1 with hx
  set k : ℝ≥0 := 2 ^ r.2 with hk
  have hk0 : 0 < k := pow_pos (by norm_num) _
  set v₀ := (rootEntry r.1).2 with hv₀
  -- the history `l` and its passed test
  obtain ⟨hTq₀, hqv₀, hlive₀, -⟩ := RootJ32.test_spec c r l a₀ q ω htest
  have hold₀ := RootJ32.oldSuccess_of_alive c r l ω halive
  have hord₀ := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive
  obtain ⟨γ₀, hγ₀, hA0₀, hm₀, hc₀, -, -⟩ := hclock l a₀ hlive₀
  obtain ⟨hgood₀, -⟩ := hjoin l a₀ hold₀
  -- the next history and its candidate
  have halive' : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l' :=
    TestEvents.aliveTests_inter_subset l a₀ q ⟨halive, htest⟩
  have hold' := RootJ32.oldSuccess_of_alive c r l' ω halive'
  have hord' := RootJ32.timeOrdered_historyProgram_of_alive c r l' ω halive'
  obtain ⟨γ, hγ, hA0, hm, hc, -, -⟩ := hclock l' a hlive
  obtain ⟨hgood', -⟩ := hjoin l' a hold'
  have hT' : RootJ31.historyTime c r l' = q := historyTime_cons c r l θ q
  obtain ⟨hJ, hJ0⟩ := continuous_futureJoined c r l' a ω
  obtain ⟨hJ₀, hJ₀0⟩ := continuous_futureJoined c r l a₀ ω
  -- the two joined drivers agree on `[0, q]`
  have hqcap₀ : (q : ℝ≥0) ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a₀ :=
    hqv₀.le.trans (add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a₀ ω))
  have hJJ : ∀ t ≤ (q : ℝ≥0), futureJoined c r l' a ω t = futureJoined c r l a₀ ω t := by
    intro t ht
    have h1 := futureJoined_eq_joinDrv_hist c r l' a ω hord' hold' hgood' t (by rw [hT']; exact ht)
    have h2 := futureJoined_eq_joinDrv_query c r l a₀ ω hord₀ hold₀ hgood₀ hTq₀ hqcap₀
      (RootJ32.next_piece_live_of_test c r l a₀ q ω htest) t ht
    rw [h1, h2, hl', RootJ31.historyProgram_cons, List.length_append, List.length_singleton]
  -- record forms
  set L' := RootJ31.historyTime c r l' + RootJ31.candidateCap c r a with hL'
  set L₀ := RootJ31.historyTime c r l + RootJ31.candidateCap c r a₀ with hL₀
  set w' := RootJ31.historyTime c r l' + RootJ31.sourceBuffer c r l' a ω with hw'
  set w₀ := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a₀ ω with hw₀
  have hw'L : w' ≤ L' := add_le_add le_rfl (RootJ31.sourceBuffer_le c r l' a ω)
  have hw₀L : w₀ ≤ L₀ := add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a₀ ω)
  have hqw' : (q : ℝ≥0) ≤ w' := by rw [hw', hT']; exact le_self_add
  have hqw₀ : (q : ℝ≥0) ≤ w₀ := hqv₀.le
  have hpe' := futurePair_eq_recOfDriver c r l' a ω
  have hpe₀ := futurePair_eq_recOfDriver c r l a₀ ω
  rw [hpe'] at hm hc hA0
  rw [hpe₀] at hm₀ hc₀ hA0₀
  -- capacity readers of the I30 records
  set P' := (cfRec c.s c.W c.ζ ω, recOf (w' : ℝ≥0∞) (futureJoined c r l' a ω, ⊤)) with hP'
  set P₀ := (cfRec c.s c.W c.ζ ω, recOf (w₀ : ℝ≥0∞) (futureJoined c r l a₀ ω, ⊤)) with hP₀
  have hAP' : ∀ t ≤ w', RootH29.forwardCapacity x c.s t (cfRec c.s c.W c.ζ ω,
      StagedEntrance.Strip.recOfDriver L' (futureJoined c r l' a ω)) =
        RootH29.forwardCapacity x c.s t P' := fun t ht => by
    rw [recOfDriver_eq_recOf]
    exact forwardCapacity_recOf_congr hJ hJ0 hJ hJ0 (ht.trans hw'L) ht fun _ _ => rfl
  have hAP₀ : ∀ t ≤ w₀, RootH29.forwardCapacity x c.s t (cfRec c.s c.W c.ζ ω,
      StagedEntrance.Strip.recOfDriver L₀ (futureJoined c r l a₀ ω)) =
        RootH29.forwardCapacity x c.s t P₀ := fun t ht => by
    rw [recOfDriver_eq_recOf]
    exact forwardCapacity_recOf_congr hJ₀ hJ₀0 hJ₀ hJ₀0 (ht.trans hw₀L) ht fun _ _ => rfl
  have hmP' : MonotoneOn (fun t => RootH29.forwardCapacity x c.s t P') (Icc 0 w') :=
    fun t ht t' ht' htt' => by
      show RootH29.forwardCapacity x c.s t P' ≤ RootH29.forwardCapacity x c.s t' P'
      rw [← hAP' t ht.2, ← hAP' t' ht'.2]; exact hm.monotoneOn ht ht' htt'
  have hmP₀ : MonotoneOn (fun t => RootH29.forwardCapacity x c.s t P₀) (Icc 0 w₀) :=
    fun t ht t' ht' htt' => by
      show RootH29.forwardCapacity x c.s t P₀ ≤ RootH29.forwardCapacity x c.s t' P₀
      rw [← hAP₀ t ht.2, ← hAP₀ t' ht'.2]; exact hm₀.monotoneOn ht ht' htt'
  -- the two capacities read at `q` and at the root time agree
  have hv₀q : v₀ ≤ (q : ℝ≥0) := (rootTime_le_historyTime c r l hord₀).trans hTq₀.le
  have hcapq : RootH29.forwardCapacity x c.s q P' = RootH29.forwardCapacity x c.s q P₀ :=
    forwardCapacity_recOf_congr hJ hJ0 hJ₀ hJ₀0 hqw' hqw₀ hJJ
  have hcapv : RootH29.forwardCapacity x c.s v₀ P' = RootH29.forwardCapacity x c.s v₀ P₀ :=
    forwardCapacity_recOf_congr hJ hJ0 hJ₀ hJ₀0 (hv₀q.trans hqw') (hv₀q.trans hqw₀)
      fun y hy => hJJ y (hy.trans hv₀q)
  have hnn : ∀ t, 0 ≤ RootH29.forwardCapacity x c.s t P' := fun t =>
    RootJ32.forwardCapacity_nonneg x c.s t P'
  have hnn₀ : ∀ t, 0 ≤ RootH29.forwardCapacity x c.s t P₀ := fun t =>
    RootJ32.forwardCapacity_nonneg x c.s t P₀
  have hvq' : RootH29.forwardCapacity x c.s v₀ P' ≤ RootH29.forwardCapacity x c.s q P' :=
    hmP' ⟨zero_le, hv₀q.trans hqw'⟩ ⟨zero_le, hqw'⟩ hv₀q
  -- the driver readers: J32 = I30 on each record, and I30 readers agree
  have hD : ∀ c' : ℝ≥0, (c' : ℝ) ≤ RootH29.forwardCapacity x c.s q P' →
      RootJ32.capacityDriverRead x c.s L' c' (RootJ31.futurePair c r l' a ω) =
        RootJ32.capacityDriverRead x c.s L₀ c' (RootJ31.futurePair c r l a₀ ω) := by
    intro c' hc'
    have hc'w' : (c' : ℝ) ≤ RootH29.forwardCapacity x c.s w' (cfRec c.s c.W c.ζ ω,
        StagedEntrance.Strip.recOfDriver L' (futureJoined c r l' a ω)) := by
      rw [hAP' w' le_rfl]; exact hc'.trans (hmP' ⟨zero_le, hqw'⟩ ⟨zero_le, le_rfl⟩ hqw')
    have hc'w₀ : (c' : ℝ) ≤ RootH29.forwardCapacity x c.s w₀ (cfRec c.s c.W c.ζ ω,
        StagedEntrance.Strip.recOfDriver L₀ (futureJoined c r l a₀ ω)) := by
      rw [hAP₀ w₀ le_rfl]
      exact (hc'.trans hcapq.le).trans (hmP₀ ⟨zero_le, hqw₀⟩ ⟨zero_le, le_rfl⟩ hqw₀)
    rw [hpe', hpe₀, RootJ32.capacityDriverRead_eq_of_clock hJ hJ0 hγ hw'L hw'L hm.monotoneOn hc hc'w',
      RootJ32.capacityDriverRead_eq_of_clock hJ₀ hJ₀0 hγ₀ hw₀L hw₀L hm₀.monotoneOn hc₀ hc'w₀]
    exact capacityDriverRead_I30_congr hJ hJ0 hJ₀ hJ₀0 hγ hγ₀ hqw' hqw₀ hJJ hmP' hmP₀ hc'
  -- assemble
  have hY : RootJ32.sourceDriver c r l' a ω 0 = ((-1) ^ l'.length) * (k : ℝ) *
      (RootJ32.capacityDriverRead x c.s L' (RootH29.forwardCapacity x c.s
          (RootJ31.historyTime c r l') (RootJ31.futurePair c r l' a ω)).toNNReal
          (RootJ31.futurePair c r l' a ω) -
        RootJ32.capacityDriverRead x c.s L' (RootH29.forwardCapacity x c.s v₀
          (RootJ31.futurePair c r l' a ω)).toNNReal (RootJ31.futurePair c r l' a ω)) := by
    change ((-1) ^ l'.length) * (k : ℝ) * (RootJ32.capacityDriverRead x c.s L'
      ((RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l')
        (RootJ31.futurePair c r l' a ω)).toNNReal + 0 / k ^ 2) (RootJ31.futurePair c r l' a ω) - _) = _
    rw [zero_div, add_zero]
  have hAT : RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l')
      (RootJ31.futurePair c r l' a ω) = RootH29.forwardCapacity x c.s q
        (RootJ31.futurePair c r l' a ω) :=
    congrArg (fun t => RootH29.forwardCapacity x c.s t (RootJ31.futurePair c r l' a ω)) hT'
  have hAq' : RootH29.forwardCapacity x c.s q (RootJ31.futurePair c r l' a ω) =
      RootH29.forwardCapacity x c.s q (RootJ31.futurePair c r l a₀ ω) := by
    rw [hpe', hpe₀, hAP' q hqw', hAP₀ q hqw₀, hcapq]
  have hAv' : RootH29.forwardCapacity x c.s v₀ (RootJ31.futurePair c r l' a ω) =
      RootH29.forwardCapacity x c.s v₀ (RootJ31.futurePair c r l a₀ ω) := by
    rw [hpe', hpe₀, hAP' v₀ (hv₀q.trans hqw'), hAP₀ v₀ (hv₀q.trans hqw₀), hcapv]
  have hle_q : (((RootH29.forwardCapacity x c.s q (RootJ31.futurePair c r l' a ω)).toNNReal : ℝ≥0) :
      ℝ) ≤ RootH29.forwardCapacity x c.s q P' := by
    rw [Real.coe_toNNReal _ (RootJ32.forwardCapacity_nonneg _ _ _ _), hpe', hAP' q hqw']
  have hle_v : (((RootH29.forwardCapacity x c.s v₀ (RootJ31.futurePair c r l' a ω)).toNNReal : ℝ≥0) :
      ℝ) ≤ RootH29.forwardCapacity x c.s q P' := by
    rw [Real.coe_toNNReal _ (RootJ32.forwardCapacity_nonneg _ _ _ _), hpe',
      hAP' v₀ (hv₀q.trans hqw')]
    exact hvq'
  -- the reading at `q` of the previous history
  have hAT0 : 0 ≤ RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l)
      (RootJ31.futurePair c r l a₀ ω) := RootJ32.forwardCapacity_nonneg _ _ _ _
  have hATq : RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l)
      (RootJ31.futurePair c r l a₀ ω) ≤ RootH29.forwardCapacity x c.s q
        (RootJ31.futurePair c r l a₀ ω) := by
    rw [hpe₀]
    exact hm₀.monotoneOn ⟨zero_le, hTq₀.le.trans hqw₀⟩ ⟨zero_le, hqw₀⟩ hTq₀.le
  have hcapX : (RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l)
      (RootJ31.futurePair c r l a₀ ω)).toNNReal + RootJ31.sourceClock c r l a₀ q ω / k ^ 2 =
      (RootH29.forwardCapacity x c.s q (RootJ31.futurePair c r l a₀ ω)).toNNReal := by
    change _ + RootJ31.capacityIncrement k x c.s (RootJ31.historyTime c r l)
      ((q : ℝ≥0) - RootJ31.historyTime c r l) (RootJ31.futurePair c r l a₀ ω) / k ^ 2 = _
    rw [RootJ31.capacityIncrement, add_tsub_cancel_of_le hTq₀.le,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 hk0.ne'), ← Real.toNNReal_add hAT0
      (sub_nonneg.2 hATq), add_sub_cancel]
  have hX : RootJ32.sourceX c r l a₀ ω q = ((-1) ^ l.length) * (k : ℝ) *
      (RootJ32.capacityDriverRead x c.s L₀ (RootH29.forwardCapacity x c.s q
          (RootJ31.futurePair c r l a₀ ω)).toNNReal (RootJ31.futurePair c r l a₀ ω) -
        RootJ32.capacityDriverRead x c.s L₀ (RootH29.forwardCapacity x c.s v₀
          (RootJ31.futurePair c r l a₀ ω)).toNNReal (RootJ31.futurePair c r l a₀ ω)) := by
    change ((-1) ^ l.length) * (k : ℝ) * (RootJ32.capacityDriverRead x c.s L₀
      ((RootH29.forwardCapacity x c.s (RootJ31.historyTime c r l)
        (RootJ31.futurePair c r l a₀ ω)).toNNReal +
          RootJ31.sourceClock c r l a₀ (((q : ℝ≥0) : ℝ)).toNNReal ω / k ^ 2)
        (RootJ31.futurePair c r l a₀ ω) - _) = _
    rw [Real.toNNReal_coe, hcapX]
  rw [hY, hAT, hD _ hle_q, hD _ hle_v, hAq', hAv', hX, hl', List.length_cons, pow_succ]
  ring

end InteractingSLE.Theorem14.GW2TipSystem.Gm
