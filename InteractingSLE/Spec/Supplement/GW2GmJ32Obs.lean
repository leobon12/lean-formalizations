/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Next
import InteractingSLE.Spec.Supplement.GW2GmJ32Causal
import InteractingSLE.Spec.Supplement.GW2GmJ32Shift
import InteractingSLE.Spec.Supplement.GW2GmJ32RegT

/-!
# Reader consistency for J32: the observed readers on the query window

Packet PROVE-GW2-GEOM2 (round 4). J32's observation at `q` reads the stage driver at the clock `U(q)` and the tip at
the increment from the root entry, both from the candidate's future pair `(cfRec, recOfDriver (T + cap) J)`. With
the next history's pair `(cfRec, recOfDriver q' J')` (`J = J'` on `[0, w]`, `ae_futureJoined_eq_nextJoined'`):

* `jointTipRead_congr`: the joint tip at `u` only reads the joint driver on `[0, u]` (lifetime `⊤`, fix F3);
* **`stageDriverRead_clock_congr`**, **`jointTipRead_clock_congr`** (deterministic): at a time `τ ≤ w` of a
  capacity clock on `[0, w]` (`T, v₀ ≤ τ`), the stage driver at `U(τ)` and the joint tip at the increment from `v₀`
  are the same for both pairs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootB23 RootJ32

/-- The dyadic left-limit reader at `u` reads the path only on `[0, u]`. -/
theorem endVal_congr {u : ℝ≥0} {f g : ℝ≥0 → ℂ} (h : ∀ r ≤ u, f r = g r) :
    Restart.endVal ((u : ℝ≥0∞), f) = Restart.endVal ((u : ℝ≥0∞), g) := by
  unfold Restart.endVal
  by_cases hu : u = 0
  · subst hu
    simp only [ENNReal.coe_zero, ↓reduceIte]
    exact h 0 le_rfl
  · have hne : ((u : ℝ≥0∞)) ≠ 0 := by exact_mod_cast hu
    simp only [hne, ↓reduceIte, ENNReal.toNNReal_coe]
    have hu0 : 0 < u := lt_of_le_of_ne zero_le (Ne.symm hu)
    congr 1
    funext n
    exact h _ (LP.dyadicBelow_lt hu0 n).le

/-- The joint tip at `u` reads the joint driver only on `[0, u]`. -/
theorem jointTipRead_congr {k : ℝ≥0} {x : ℝ} {s v v' v₀ u : ℝ≥0} {p p' : RecData × RecData}
    (h : ∀ r ≤ u, jointDriverRead k x s v v₀ p r = jointDriverRead k x s v' v₀ p' r) :
    jointTipRead k x s v v₀ u p = jointTipRead k x s v' v₀ u p' := by
  unfold jointTipRead jointTraceRead
  rw [drivingTrace_top_snd, drivingTrace_top_snd]
  exact endVal_congr fun r hr => LP.traceAt_congr fun r' hr' => h r' (hr'.trans hr)

section Clock

variable {x : ℝ} {s w : ℝ≥0} {p₁ : RecData} {J J' : ℝ≥0 → ℝ} {L L' : ℝ≥0}

/-- The capacity increment from `T` reaches the capacity at `τ`. -/
theorem level_capacityIncrement {p : RecData × RecData} {k : ℝ≥0} (hk : 0 < k) {T τ : ℝ≥0}
    (hTτ : T ≤ τ) (h0 : 0 ≤ RootH29.forwardCapacity x s T p)
    (hmono : RootH29.forwardCapacity x s T p ≤ RootH29.forwardCapacity x s τ p) :
    (((RootH29.forwardCapacity x s T p).toNNReal +
      RootJ31.capacityIncrement k x s T (τ - T) p / k ^ 2 : ℝ≥0) : ℝ) =
        RootH29.forwardCapacity x s τ p := by
  rw [RootJ31.capacityIncrement, add_tsub_cancel_of_le hTτ,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hk.ne'), ← Real.toNNReal_add h0 (sub_nonneg.2 hmono),
    add_sub_cancel, Real.coe_toNNReal _ (h0.trans hmono)]

variable (hJ : Continuous J) (hJ0 : J 0 = 0) (hJ' : Continuous J') (hJ'0 : J' 0 = 0)
  (hwL : w ≤ L) (hwL' : w ≤ L') (hw0 : 0 < w) (hJJ : ∀ y ≤ w, J y = J' y)
  (hm : MonotoneOn (fun t => RootH29.forwardCapacity x s t
    (p₁, StagedEntrance.Strip.recOfDriver L J)) (Icc 0 w))
  (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t
    (p₁, StagedEntrance.Strip.recOfDriver L J)) (Icc 0 w))
include hJ hJ0 hJ' hJ'0 hwL hwL' hw0 hJJ hm hc

omit hw0 hm hc in
theorem rdrv_recOfDriver_congr :
    ∀ y : ℝ≥0, y ≤ w → rdrv (StagedEntrance.Strip.recOfDriver L J) y =
      rdrv (StagedEntrance.Strip.recOfDriver L' J') y := by
  intro y hy
  rw [rdrv_recOfDriver hJ hJ0, rdrv_recOfDriver hJ' hJ'0, min_eq_left (hy.trans hwL),
    min_eq_left (hy.trans hwL'), hJJ y hy]

/-- **The observed stage driver is the same for both pairs** at a time `τ ≤ w` of the clock window. -/
theorem stageDriverRead_clock_congr (k : ℝ≥0) (hk : 0 < k) (ε : ℝ) {v₀ T τ : ℝ≥0}
    (hv₀ : v₀ ≤ w) (hTτ : T ≤ τ) (hτw : τ ≤ w) :
    stageDriverRead k ε x s L v₀ T
        (RootJ31.capacityIncrement k x s T (τ - T) (p₁, StagedEntrance.Strip.recOfDriver L J))
        (p₁, StagedEntrance.Strip.recOfDriver L J) =
      stageDriverRead k ε x s L' v₀ T
        (RootJ31.capacityIncrement k x s T (τ - T) (p₁, StagedEntrance.Strip.recOfDriver L' J'))
        (p₁, StagedEntrance.Strip.recOfDriver L' J') := by
  have hdrv := rdrv_recOfDriver_congr hJ hJ0 hJ' hJ'0 hwL hwL' hJJ
  have hT : T ≤ w := hTτ.trans hτw
  have hinc : RootJ31.capacityIncrement k x s T (τ - T) (p₁, StagedEntrance.Strip.recOfDriver L J) =
      RootJ31.capacityIncrement k x s T (τ - T) (p₁, StagedEntrance.Strip.recOfDriver L' J') := by
    unfold RootJ31.capacityIncrement
    rw [forwardCapacity_congr_le hdrv (by rw [add_tsub_cancel_of_le hTτ]; exact hτw),
      forwardCapacity_congr_le hdrv hT]
  rw [← hinc]
  have hA0 : ∀ t, 0 ≤ RootH29.forwardCapacity x s t (p₁, StagedEntrance.Strip.recOfDriver L J) :=
    fun t => forwardCapacity_nonneg x s t _
  refine stageDriverRead_congr_le hdrv ?_ ?_ ?_ ?_ hwL hwL' k ε hv₀ hT ?_ ?_
  · rw [recOfDriver_life]; exact ENNReal.coe_le_coe.2 hwL
  · rw [recOfDriver_life]; exact ENNReal.coe_le_coe.2 hwL'
  · rw [recOfDriver_life]; exact ENNReal.coe_pos.2 (hw0.trans_le hwL)
  · rw [recOfDriver_life]; exact ENNReal.coe_pos.2 (hw0.trans_le hwL')
  · refine level_le_runMax_of_clock hm hc hτw ?_
    rw [level_capacityIncrement hk hTτ (hA0 T)
      (hm ⟨zero_le, hT⟩ ⟨zero_le, hτw⟩ hTτ)]
  · exact level_le_runMax_of_clock hm hc hv₀ (Real.coe_toNNReal _ (hA0 v₀)).le

/-- **The observed joint tip is the same for both pairs** at a time `τ ≤ w` of the clock window, `v₀ ≤ τ`. -/
theorem jointTipRead_clock_congr (k : ℝ≥0) (hk : 0 < k) {v₀ τ : ℝ≥0} (hv₀τ : v₀ ≤ τ)
    (hτw : τ ≤ w) :
    jointTipRead k x s L v₀
        (RootJ31.capacityIncrement k x s v₀ (τ - v₀) (p₁, StagedEntrance.Strip.recOfDriver L J))
        (p₁, StagedEntrance.Strip.recOfDriver L J) =
      jointTipRead k x s L' v₀
        (RootJ31.capacityIncrement k x s v₀ (τ - v₀) (p₁, StagedEntrance.Strip.recOfDriver L' J'))
        (p₁, StagedEntrance.Strip.recOfDriver L' J') := by
  have hdrv := rdrv_recOfDriver_congr hJ hJ0 hJ' hJ'0 hwL hwL' hJJ
  have hv₀ : v₀ ≤ w := hv₀τ.trans hτw
  have hinc : RootJ31.capacityIncrement k x s v₀ (τ - v₀) (p₁, StagedEntrance.Strip.recOfDriver L J) =
      RootJ31.capacityIncrement k x s v₀ (τ - v₀)
        (p₁, StagedEntrance.Strip.recOfDriver L' J') := by
    unfold RootJ31.capacityIncrement
    rw [forwardCapacity_congr_le hdrv (by rw [add_tsub_cancel_of_le hv₀τ]; exact hτw),
      forwardCapacity_congr_le hdrv hv₀]
  rw [← hinc]
  have hA0 : ∀ t, 0 ≤ RootH29.forwardCapacity x s t (p₁, StagedEntrance.Strip.recOfDriver L J) :=
    fun t => forwardCapacity_nonneg x s t _
  refine jointTipRead_congr fun r hr => ?_
  refine stageDriverRead_congr_le hdrv ?_ ?_ ?_ ?_ hwL hwL' k 1 hv₀ hv₀ ?_ ?_
  · rw [recOfDriver_life]; exact ENNReal.coe_le_coe.2 hwL
  · rw [recOfDriver_life]; exact ENNReal.coe_le_coe.2 hwL'
  · rw [recOfDriver_life]; exact ENNReal.coe_pos.2 (hw0.trans_le hwL)
  · rw [recOfDriver_life]; exact ENNReal.coe_pos.2 (hw0.trans_le hwL')
  · refine level_le_runMax_of_clock hm hc hτw ?_
    rw [← level_capacityIncrement hk hv₀τ (hA0 v₀) (hm ⟨zero_le, hv₀⟩ ⟨zero_le, hτw⟩ hv₀τ)]
    exact NNReal.coe_le_coe.2 ((add_le_add_iff_left _).2 (div_le_div_of_nonneg_right hr zero_le))
  · exact level_le_runMax_of_clock hm hc hv₀ (Real.coe_toNNReal _ (hA0 v₀)).le

end Clock

/-! ### The next history's readers -/

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The next history's retained record pair (its counterflow record and joined record). -/
def nextPair (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (q' : c.Q) (ω : Ω) : RecData × RecData :=
  (cfRec c.s c.W c.ζ ω,
    RootJ31.joinedRecord (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l))
      (RootJ31.programRecords c (rootPt r.1)
        (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l)) ω))

/-- J32's observed driver read from the next history's pair. -/
def nextX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (q' : c.Q) (ω : Ω) (t : ℝ) : ℝ :=
  stageDriverRead (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s q' (rootEntry r.1).2
    (RootJ31.historyTime c r l)
    (RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (RootJ31.historyTime c r l)
      (t.toNNReal - RootJ31.historyTime c r l) (nextPair c r l a q' ω)) (nextPair c r l a q' ω)

/-- J32's observed tip read from the next history's pair. -/
def nextTip (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (q' : c.Q) (ω : Ω) (t : ℝ) : ℂ :=
  RootJ31.orientTip l.length (jointTipRead (2 ^ r.2) (rootPt r.1) c.s q' (rootEntry r.1).2
    (RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (rootEntry r.1).2
      ((RootJ31.historyTime c r l + (t.toNNReal - RootJ31.historyTime c r l)) - (rootEntry r.1).2)
      (nextPair c r l a q' ω)) (nextPair c r l a q' ω))

/-- The next history's pair is retained by the next history's σ-algebra. -/
theorem measurable_nextPair (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q' : c.Q) :
    Measurable[c.sigma r ((RootJ31.candidateAngle c r a, q') :: l)] (nextPair c r l a q') :=
  measurable_historyPair_sigma c r _

/-- The next readers are retained by the next history's σ-algebra. -/
theorem measurable_nextX_nextTip (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q' : c.Q) (t : ℝ) :
    Measurable[c.sigma r ((RootJ31.candidateAngle c r a, q') :: l)]
      (fun ω => (nextX c r l a q' ω t, nextTip c r l a q' ω t)) := by
  have hp := measurable_nextPair c r l a q'
  have hX : Measurable fun p : RecData × RecData =>
      stageDriverRead (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s q' (rootEntry r.1).2
        (RootJ31.historyTime c r l)
        (RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (RootJ31.historyTime c r l)
          (t.toNNReal - RootJ31.historyTime c r l) p) p :=
    measurable_stageDriverRead_random measurable_id _ _ _ _ _ _ _
      (RootJ31.measurable_capacityIncrement_random measurable_id measurable_const _ _ _ _)
  have hT : Measurable fun p : RecData × RecData =>
      RootJ31.orientTip l.length (jointTipRead (2 ^ r.2) (rootPt r.1) c.s q' (rootEntry r.1).2
        (RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (rootEntry r.1).2
          ((RootJ31.historyTime c r l + (t.toNNReal - RootJ31.historyTime c r l)) - (rootEntry r.1).2)
          p) p) :=
    (RootJ31.measurable_orientTip _).comp (measurable_jointTipRead_random measurable_id _ _ _ _ _
      (RootJ31.measurable_capacityIncrement_random measurable_id measurable_const _ _ _ _))
  exact (hX.comp hp).prodMk (hT.comp hp)

/-- The next history's record has the query time as its horizon. -/
theorem lastTime_next (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (θ : c.Θ) (q' : c.Q) :
    Sec5.Prop513Schedule.lastTime 0 (RootJ31.historyProgram c r ((θ, q') :: l)) = (q' : ℝ≥0) := by
  rw [RootJ31.historyProgram_cons, Sec5.Prop513Schedule.lastTime_eq_getLast _ _ (by simp)]
  simp only [List.getLast_append, List.isEmpty_cons, Bool.false_eq_true, ↓reduceDIte,
    List.getLast_singleton]

variable [StandardBorelSpace Ω]

/-- **Reader consistency for J32**: almost surely, on every alive history `l`, for every candidate `a` and
queries `q ≤ q'`, if the observation at `q` is gated open (`S < q < F`) then J32's observed driver and tip at `q`
equal the same readers on the next history `(θ_a, q') :: l`'s retained pair. -/
theorem ae_observed_eq_next (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q q' : c.Q),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l → q ≤ q' →
      (RootJ32.experiment c r).data.S l a ω < (q : ℝ≥0) →
      ((q : ℝ≥0) : ℝ) < (RootJ32.experiment c r).data.F l a ω →
      (RootJ32.experiment c r).data.X l a ω q = nextX c r l a q' ω q ∧
        (RootJ32.experiment c r).data.γ l a ω q = nextTip c r l a q' ω q := by
  filter_upwards [ae_live_clock h13 c r, ae_futureJoined_eq_nextJoined' h13 c r]
    with ω hclock hnext l a q q' halive hqq' hSq hqF
  have hSF : RootJ32.sourceEntry c r l a ω < RootJ31.sourceFailure c r l a ω := hSq.trans hqF
  have hlive := RootJ32.live_of_entry_lt_failure c r l a ω hSF
  obtain ⟨-, hold, hord⟩ := RootJ32.alive_spec c r l ω halive
  obtain ⟨γ, -, -, hm, hc, -, -⟩ := hclock l a hlive
  obtain ⟨hJ, hJ0⟩ := continuous_futureJoined c r l a ω
  have hpe := futurePair_eq_recOfDriver c r l a ω
  set T := RootJ31.historyTime c r l with hT
  set Fb := RootJ31.sourceBuffer c r l a ω with hFb
  set L := T + RootJ31.candidateCap c r a with hL
  set v₀ := (rootEntry r.1).2 with hv₀
  set k : ℝ≥0 := 2 ^ r.2 with hk
  have hk0 : 0 < k := pow_pos (by norm_num) _
  have hTq : T < (q : ℝ≥0) := NNReal.coe_lt_coe.mp
    ((RootJ32.sourceEntry_ge_historyTime c r l a ω).trans_lt hSq)
  have hqF : (q : ℝ≥0) < T + Fb := by
    have h := hqF
    change ((q : ℝ≥0) : ℝ) < ((T + Fb : ℝ≥0) : ℝ) at h
    exact_mod_cast h
  have hFL : T + Fb ≤ L := add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ω)
  have hv₀T : v₀ ≤ T := rootTime_le_historyTime c r l hord
  -- the two joined drivers agree on `[0, q]`
  set J' := RootJ31.joinedRead (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l))
    (RootJ31.programRecords c (rootPt r.1)
      (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l)) ω) with hJ'def
  obtain ⟨hJ', hJ'0⟩ := RootJ31.continuous_joinedRead
    (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l))
    (RootJ31.programRecords c (rootPt r.1)
      (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l)) ω)
  have hqq'' : (q : ℝ≥0) ≤ (q' : ℝ≥0) := hqq'
  have hqw : (q : ℝ≥0) ≤ T + min (RootJ31.candidateCap c r a) ((q' : ℝ≥0) - T) := by
    rw [← add_tsub_cancel_of_le hTq.le]
    refine (add_le_add_iff_left T).2 (le_min ?_ ?_)
    · exact tsub_le_iff_left.2 ((hqF.le.trans hFL))
    · exact tsub_le_tsub_right hqq'' T
  have hJJ : ∀ y ≤ (q : ℝ≥0), futureJoined c r l a ω y = J' y := fun y hy =>
    hnext l a q' hold y (hy.trans hqw)
  have hnp : nextPair c r l a q' ω =
      (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver (q' : ℝ≥0) J') := by
    show (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver (Sec5.Prop513Schedule.lastTime 0
      (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l))) J') = _
    rw [lastTime_next]
  -- the clock on `[0, q]`
  rw [hpe] at hm hc
  have hsub : Icc 0 (q : ℝ≥0) ⊆ Icc 0 (T + Fb) := Icc_subset_Icc le_rfl hqF.le
  have hm' := (hm.mono hsub).monotoneOn
  have hc' := hc.mono hsub
  have hw0 : 0 < (q : ℝ≥0) := lt_of_le_of_lt zero_le hTq
  have hqL : (q : ℝ≥0) ≤ L := hqF.le.trans hFL
  have hqq : ((q : ℝ≥0) : ℝ).toNNReal = (q : ℝ≥0) := Real.toNNReal_coe
  constructor
  · have key := stageDriverRead_clock_congr (x := rootPt r.1) (s := c.s)
      (p₁ := cfRec c.s c.W c.ζ ω) hJ hJ0 hJ' hJ'0 hqL hqq'' hw0 hJJ hm' hc' k hk0
      ((-1) ^ l.length) (hv₀T.trans hTq.le) hTq.le le_rfl
    rw [← hpe, ← hnp] at key
    change RootJ32.sourceX c r l a ω q = nextX c r l a q' ω q
    show stageDriverRead k ((-1) ^ l.length) (rootPt r.1) c.s L v₀ T
        (RootJ31.capacityIncrement k (rootPt r.1) c.s T (((q : ℝ≥0) : ℝ).toNNReal - T)
          (RootJ31.futurePair c r l a ω)) (RootJ31.futurePair c r l a ω) =
      stageDriverRead k ((-1) ^ l.length) (rootPt r.1) c.s q' v₀ T
        (RootJ31.capacityIncrement k (rootPt r.1) c.s T (((q : ℝ≥0) : ℝ).toNNReal - T)
          (nextPair c r l a q' ω)) (nextPair c r l a q' ω)
    rw [hqq]
    exact key
  · have key := jointTipRead_clock_congr (x := rootPt r.1) (s := c.s)
      (p₁ := cfRec c.s c.W c.ζ ω) hJ hJ0 hJ' hJ'0 hqL hqq'' hw0 hJJ hm' hc' k hk0
      (hv₀T.trans hTq.le) le_rfl
    rw [← hpe, ← hnp] at key
    change RootJ32.sourceTip c r l a ω q = nextTip c r l a q' ω q
    show RootJ31.orientTip l.length (jointTipRead k (rootPt r.1) c.s L v₀
        (RootJ31.capacityIncrement k (rootPt r.1) c.s v₀
          ((T + (((q : ℝ≥0) : ℝ).toNNReal - T)) - v₀) (RootJ31.futurePair c r l a ω))
        (RootJ31.futurePair c r l a ω)) =
      RootJ31.orientTip l.length (jointTipRead k (rootPt r.1) c.s q' v₀
        (RootJ31.capacityIncrement k (rootPt r.1) c.s v₀
          ((T + (((q : ℝ≥0) : ℝ).toNNReal - T)) - v₀) (nextPair c r l a q' ω))
        (nextPair c r l a q' ω))
    rw [hqq, add_tsub_cancel_of_le hTq.le, key]

/-- **J32's observation on alive histories, given a retained version of its gate** (conditional helper). If the gate
`S < q < F` agrees, almost surely on the alive histories `l`, with an event retained by the next history
`(θ_a, q') :: l`, then the observation at `q ≤ q'` agrees there with a function retained by the next history:
the gated next readers. -/
theorem exists_observation_alive_of_gate (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {q q' : c.Q} (hqq' : q ≤ q')
    {G' : Set Ω}
    (hG' : MeasurableSet[c.sigma r ((RootJ31.candidateAngle c r a, q') :: l)] G')
    (hgate : ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      (ω ∈ G' ↔ ((RootJ32.experiment c r).data.S l a ω < (q : ℝ≥0) ∧
        ((q : ℝ≥0) : ℝ) < (RootJ32.experiment c r).data.F l a ω))) :
    ∃ g : Ω → ℝ × ℂ, Measurable[c.sigma r ((RootJ31.candidateAngle c r a, q') :: l)] g ∧
      ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
        (RootJ32.experiment c r).data.observation l a q ω = g ω := by
  classical
  refine ⟨fun ω => if ω ∈ G' then (nextX c r l a q' ω q, nextTip c r l a q' ω q) else (0, 0),
    Measurable.ite hG' (measurable_nextX_nextTip c r l a q' q) measurable_const, ?_⟩
  filter_upwards [ae_observed_eq_next h13 c r, hgate] with ω hω hg halive
  have hgω := hg halive
  unfold RootK3.StageModelData.observation
  by_cases hgo : (RootJ32.experiment c r).data.S l a ω < (q : ℝ≥0) ∧
      ((q : ℝ≥0) : ℝ) < (RootJ32.experiment c r).data.F l a ω
  · rw [ite_eq_left hgo, ite_eq_left (hgω.2 hgo)]
    obtain ⟨h1, h2⟩ := hω l a q q' halive hqq' hgo.1 hgo.2
    rw [h1, h2]
  · rw [ite_eq_right hgo, ite_eq_right (fun h => hgo (hgω.1 h))]

end InteractingSLE.Theorem14.GW2TipSystem.Gm
