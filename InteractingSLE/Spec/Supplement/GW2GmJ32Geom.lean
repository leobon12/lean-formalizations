/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Data
import InteractingSLE.Spec.Supplement.GW2GmJ32Agree
import InteractingSLE.Spec.Supplement.GW2GmDrv

/-!
# J32's geometry: `reach_identification` and all of `clock_spec`

Packet PROVE-GW2-GEOM2 (ruling R110). For the successor construction `RootJ32.constructionFamily`:

* **`RootJ32.reach_identification`**: the field `reach_identification` (as for J31; J32's entry has J31's
  form, its sample has J31's lifetime);
* **`Gm.ae_clock_spec_bcd_J32`**: clauses (b), (c), (d) of `clock_spec` (J31's proof with J32's tests: the
  clock, increments and `capR` are J31's);
* `continuousAt_stageDriverRead_J32`: J32's stage driver is continuous at every capacity whose absolute value is
  below the capacity reached at the buffer (the running-maximum reader there is I30's exact-horizon reader,
  `GW2GmJ32Agree`, and the R5 core applies);
* **`Gm.ae_clock_spec_a_J32`**: clause (a) of `clock_spec`, unconditionally (J31 needed the cap window before
  contact);
* **`RootJ32.clock_spec`**: the whole field `clock_spec`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 Supp8.GB6
  Supp8.GB6.CoordB Sec5.Prop513Schedule

/-- **J32's stage driver is continuous below the buffer's capacity** (deterministic). -/
theorem continuousAt_stageDriverRead_J32 {Ω' : Type*} (W : ℝ≥0 → Ω' → ℝ)
    (ζ : Ω' → ℝ≥0∞) (ω : Ω') {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
    (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤) {s : ℝ≥0} (hs : 0 < s)
    {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1) {J : ℝ≥0 → ℝ}
    (hJ : Continuous J) (hJ0 : J 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace J ⊤ γ)
    {w L : ℝ≥0} (hwL : w ≤ L)
    (hnc : ∀ t ∈ Icc 0 w, ∀ u ∈ Icc 0 s, ((x : ℂ) + γ t) * α u + 1 ≠ 0)
    (hm : StrictMonoOn (fun t => RootH29.forwardCapacity x s t
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) (Icc 0 w))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) (Icc 0 w))
    {k : ℝ≥0} (ε : ℝ) (v₀ T : ℝ≥0) {u₀ : ℝ≥0}
    (hu₀ : (((RootH29.forwardCapacity x s T
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)).toNNReal + u₀ / k ^ 2 : ℝ≥0) : ℝ) <
        RootH29.forwardCapacity x s w (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) :
    ContinuousAt (fun u => RootJ32.stageDriverRead k ε x s L v₀ T u
        (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) u₀ := by
  have hcont := RootJ32.continuousAt_capacityDriverRead_of_clock W ζ ω hα hW hW0 hζ hs hx harc
    hJ hJ0 hγ hwL hwL hnc hm.monotoneOn hc hu₀
  have hin : ContinuousAt (fun u : ℝ≥0 => (RootH29.forwardCapacity x s T
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)).toNNReal + u / k ^ 2) u₀ :=
    (continuous_const.add (continuous_id.div_const _)).continuousAt
  exact continuousAt_const.mul ((ContinuousAt.comp (f := fun u : ℝ≥0 =>
    (RootH29.forwardCapacity x s T
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)).toNNReal + u / k ^ 2)
      hcont hin).sub continuousAt_const)

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- J32's entry, unfolded (sample-level form). -/
theorem sourceEntry_J32_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    RootJ32.sourceEntry c r l a ω = ((RootJ31.historyTime c r l +
      (open scoped Classical in
      if RootJ32.sourceSample c r l a ω ∈ RootD25.reachSet then
        invClock (fun t => (RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s
          (RootJ31.historyTime c r l) t (RootJ31.futurePair c r l a ω) : ℝ))
          (RootJ31.sourceBuffer c r l a ω : ℝ≥0∞)
          (RootD25.entryCapacity (RootJ32.sourceSample c r l a ω)).toNNReal
      else RootJ31.sourceBuffer c r l a ω) : ℝ≥0) : ℝ) := rfl

/-- **Reached J32 samples have entry before failure**, almost surely. -/
theorem ae_reach_imp_entry_lt_failure_J32 (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      RootJ32.sourceSample c r l a ω ∈ RootD25.reachSet →
        RootJ32.sourceEntry c r l a ω < RootJ31.sourceFailure c r l a ω := by
  classical
  filter_upwards [ae_live_clock h13 c r] with ω hω l a hreach
  have hz1 : 0 < (RootJ32.sourceSample c r l a ω).1 := lt_of_le_of_lt bot_le hreach
  have hz1' : 0 < (RootJ31.sourceSample c r l a ω).1 := by
    rw [← RootJ32.sourceSample_fst]; exact hz1
  obtain ⟨-, -, -, -, hcont, -, -⟩ := hω l a hz1'
  have hzF : (RootJ32.sourceSample c r l a ω).1 =
      (RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (RootJ31.historyTime c r l)
        (RootJ31.sourceBuffer c r l a ω) (RootJ31.futurePair c r l a ω) : ℝ≥0∞) := rfl
  have hF0 : 0 < RootJ31.sourceBuffer c r l a ω :=
    RootK32.sourceBuffer_pos_of_sample_life_pos c r l a ω hz1'
  have hinc : ContinuousWithinAt
      (fun t => ((RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (RootJ31.historyTime c r l)
        t (RootJ31.futurePair c r l a ω) : ℝ≥0) : ℝ))
      (Icc 0 (RootJ31.sourceBuffer c r l a ω)) (RootJ31.sourceBuffer c r l a ω) := by
    have hmaps : MapsTo (fun t : ℝ≥0 => RootJ31.historyTime c r l + t)
        (Icc 0 (RootJ31.sourceBuffer c r l a ω))
        (Icc 0 (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω)) :=
      fun t ht => ⟨zero_le, add_le_add le_rfl ht.2⟩
    have hA : ContinuousWithinAt
        (fun t : ℝ≥0 => RootH29.forwardCapacity (rootPt r.1) c.s
          (RootJ31.historyTime c r l + t) (RootJ31.futurePair c r l a ω))
        (Icc 0 (RootJ31.sourceBuffer c r l a ω)) (RootJ31.sourceBuffer c r l a ω) :=
      (hcont _ ⟨zero_le, le_rfl⟩).comp (continuous_const.add continuous_id).continuousWithinAt
        hmaps
    have h1 := hA.sub (continuousWithinAt_const
      (b := RootH29.forwardCapacity (rootPt r.1) c.s (RootJ31.historyTime c r l)
        (RootJ31.futurePair c r l a ω)))
    have hg : Continuous fun y : ℝ => ((((2 : ℝ≥0) ^ r.2) ^ 2 * y.toNNReal : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (continuous_const.mul continuous_real_toNNReal)
    exact hg.continuousAt.comp_continuousWithinAt h1
  have hfin : RootD25.entryCapacity (RootJ32.sourceSample c r l a ω) ≠ ⊤ := ne_top_of_lt hreach
  have hlev : ((RootD25.entryCapacity (RootJ32.sourceSample c r l a ω)).toNNReal : ℝ) <
      ((RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (RootJ31.historyTime c r l)
        (RootJ31.sourceBuffer c r l a ω) (RootJ31.futurePair c r l a ω) : ℝ≥0) : ℝ) := by
    have h : RootD25.entryCapacity (RootJ32.sourceSample c r l a ω) <
        (RootJ32.sourceSample c r l a ω).1 := hreach
    rw [hzF, ← ENNReal.coe_toNNReal hfin, ENNReal.coe_lt_coe] at h
    exact_mod_cast h
  have hentry := invClock_lt_of_continuousWithinAt hF0 hinc hlev
  rw [sourceEntry_J32_eq]
  simp only [hreach, ↓reduceIte]
  change _ < ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω : ℝ≥0) : ℝ)
  exact NNReal.coe_lt_coe.2 (add_lt_add_right hentry _)

/-- **The field `reach_identification`** for J32. -/
theorem reach_identification_J32 (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    (RootJ32.experiment c r).data.sample l a ⁻¹' (RootJ32.experiment c r).data.reach l a =ᵐ[c.P]
      {ω | (RootJ32.experiment c r).data.S l a ω < (RootJ32.experiment c r).data.F l a ω} := by
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [ae_reach_imp_entry_lt_failure_J32 h13 c r] with ω hω
  exact ⟨hω l a, RootJ32.entry_lt_failure_imp_reach c r l a ω⟩

/-- **Clauses (b), (c), (d) of `clock_spec` for J32.** -/
theorem ae_clock_spec_bcd_J32 (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ∀ q : c.Q, ω ∈ (RootJ32.experiment c r).data.tests l a q →
        ((RootJ32.experiment c r).clock l a q ω : ℝ≥0∞) <
            ((RootJ32.experiment c r).data.sample l a ω).1 ∧
          7 / 4 < (RootJ32.experiment c r).Y l a ω ((RootJ32.experiment c r).clock l a q ω) ∧
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω +
              (RootJ32.experiment c r).clock l a q ω ≤
            capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r
              (((RootJ32.experiment c r).data.ang a, q) :: l) ω := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hcapall : ∀ᵐ ω ∂c.P, 0 ≤ rootPt r.1 → ∀ l' : List (EntryIdx c.Θ c.Q),
      (∀ u ∈ Icc 0 c.s, rootPt r.1 * ‖c.α ω u‖ < 1) →
      SchedAdm c.b c.jumps c.Θ c.Q (κ := c.κ) (rootPt r.1) (rootEntry r.1) (entryList l') →
      Disjoint (c.α ω '' Icc 0 c.s) ((fun z : ℂ => -z⁻¹) ''
        (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (rootPt r.1)
          (schedOf (rootEntry r.1) (entryList l')) ω \ {0})) →
      schedCap c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (regW c.s c.W c.ζ)
        c.s c.Θ c.Q (rootPt r.1) (rootEntry r.1) (entryList l') ω =
      capOf (prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (regW c.s c.W c.ζ) c.s
        (rootPt r.1) (schedOf (rootEntry r.1) (entryList l')) ω) := by
    by_cases hx : 0 ≤ rootPt r.1
    · have h := ae_all_iff.2 fun l' : List (EntryIdx c.Θ c.Q) =>
        RootH29.ae_schedCap_eq_capOf_before_contact h13 c (rootPt r.1) hx (rootEntry r.1)
          (entryList l')
      filter_upwards [h] with ω hω _ l'
      exact hω l'
    · exact Eventually.of_forall fun _ h => absurd h hx
  filter_upwards [ae_live_clock h13 c r, ae_futureJoined_trace h13 c r, hcapall,
    RootCv.ae_coverEvent_spec h13 c r, c.hα, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ,
    c.hζ] with ω hclock hjoin hcap hcover hα hreg hζ halive q htest
  set x := rootPt r.1 with hxdef
  set T := RootJ31.historyTime c r l with hTdef
  set F := RootJ31.sourceBuffer c r l a ω with hFdef
  set p := RootJ31.futurePair c r l a ω with hpdef
  set A := fun t => RootH29.forwardCapacity x c.s t p with hAdef
  have hSF : RootJ32.sourceEntry c r l a ω < RootJ31.sourceFailure c r l a ω :=
    htest.1.trans htest.2.1
  have hlive : 0 < (RootJ31.sourceSample c r l a ω).1 :=
    RootJ32.live_of_entry_lt_failure c r l a ω hSF
  obtain ⟨hcov, hold, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ω hlive
  obtain ⟨hseed, -, -, -, -, harc⟩ := hcover hcov
  have hx : 0 ≤ x := RootH29.rootPt_nonneg_of_seedOK c hseed
  obtain ⟨γ, hγ, -, hmono, -, hcapA, hnc⟩ := hclock l a hlive
  obtain ⟨hgood, -⟩ := hjoin l a hold
  obtain ⟨_, _, hWc, hW0, _⟩ := hreg
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive
  -- the query time
  have hTq : T < (q : ℝ≥0) :=
    NNReal.coe_lt_coe.mp ((RootJ32.sourceEntry_ge_historyTime c r l a ω).trans_lt htest.1)
  have hqv : (q : ℝ≥0) < T + F := by
    have h := htest.2.1
    change ((q : ℝ≥0) : ℝ) < ((T + F : ℝ≥0) : ℝ) at h
    exact_mod_cast h
  have hqcap : (q : ℝ≥0) ≤ T + RootJ31.candidateCap c r a :=
    hqv.le.trans (add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ω))
  have hTmem : T ∈ Icc 0 (T + F) := ⟨zero_le, le_self_add⟩
  have hqmem : (q : ℝ≥0) ∈ Icc 0 (T + F) := ⟨zero_le, hqv.le⟩
  have hFmem : T + F ∈ Icc 0 (T + F) := ⟨zero_le, le_rfl⟩
  have hATq : A T < A q := hmono hTmem hqmem hTq
  have hAqF : A q < A (T + F) := hmono hqmem hFmem hqv
  have hTqeq : T + ((q : ℝ≥0) - T) = q := add_tsub_cancel_of_le hTq.le
  -- the clock and the sample lifetime
  have hclock_eq : (RootJ31.sourceClock c r l a q ω : ℝ) = 4 ^ r.2 * (A q - A T) := by
    change ((((2 : ℝ≥0) ^ r.2) ^ 2 *
      (RootH29.forwardCapacity x c.s (T + ((q : ℝ≥0) - T)) p -
        RootH29.forwardCapacity x c.s T p).toNNReal : ℝ≥0) : ℝ) = _
    rw [hTqeq, NNReal.coe_mul, Real.coe_toNNReal _ (sub_nonneg.2 hATq.le), NNReal.coe_pow,
      NNReal.coe_pow, NNReal.coe_ofNat, four_pow_eq]
  refine ⟨?_, ?_, ?_⟩
  · -- (b)
    change ((RootJ31.sourceClock c r l a q ω : ℝ≥0) : ℝ≥0∞) <
      ((RootJ31.capacityIncrement (2 ^ r.2) x c.s T F p : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hclock_eq]
    change _ < (((((2 : ℝ≥0) ^ r.2) ^ 2 *
      (RootH29.forwardCapacity x c.s (T + F) p - RootH29.forwardCapacity x c.s T p).toNNReal :
        ℝ≥0)) : ℝ)
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (sub_nonneg.2 (hATq.trans hAqF).le), NNReal.coe_pow,
      NNReal.coe_pow, NNReal.coe_ofNat, ← four_pow_eq]
    exact mul_lt_mul_of_pos_left (sub_lt_sub_right hAqF _) (pow_pos (by norm_num) _)
  · -- (c)
    have h := htest.2.2.2
    change RootJ32.sourceDriver c r l a ω
      (RootJ31.sourceClock c r l a (((q : ℝ≥0) : ℝ)).toNNReal ω) ∈ Ioo (7 / 4) (9 / 4) at h
    rw [Real.toNNReal_coe] at h
    exact h.1
  · -- (d)
    have hJ := continuous_futureJoined c r l a ω
    have he := isRegularDriver_top hJ.1 hJ.2
    have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ =>
      show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    have hαc : Continuous (c.α ω) := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
      show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    have hv : ((T + F : ℝ≥0) : ℝ≥0∞) < min
        (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
          ((fun u => (c.α ω u : OnePoint ℂ)) '' Icc 0 c.s))
        (futureJoined c r l a ω, (⊤ : ℝ≥0∞)).2 := by
      change _ < min _ ⊤
      rw [min_top_right]
      exact (lt_firstContactTime_iff_noncontact (continuous_const.add hγc) hαc _ _).2 hnc
    have hnc' : ∀ t ≤ T + F, ∀ t' ∈ Icc 0 t, ∀ u ∈ Icc 0 c.s,
        ((x : ℂ) + γ t') * c.α ω u + 1 ≠ 0 :=
      fun t ht t' ht' => hnc t' ⟨zero_le, ht'.2.trans ht⟩
    -- the history
    have hsetT := prefixSet_history_eq c r l a ω hord hold hgood hγ
    have hcapT : capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω = 4 ^ r.2 * A T := by
      have hsc := hcap hx l harc (RootJ32.schedAdm_of_alive c r l ω halive hseed)
        (by
          change Disjoint _ ((fun z : ℂ => -z⁻¹) ''
            (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x
              (RootJ31.historyProgram c r l) ω \ {0}))
          rw [hsetT]
          exact disjoint_of_noncontact (hnc' T hTmem.2))
      change 4 ^ r.2 * schedCap c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (regW c.s c.W c.ζ) c.s
        c.Θ c.Q x (rootEntry r.1) (entryList l) ω = _
      rw [hsc]
      change 4 ^ r.2 * capOf (prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
        (regW c.s c.W c.ζ) c.s x (RootJ31.historyProgram c r l) ω) = _
      rw [prefixImage_eq_of_prefixSet c ω hα hWc hW0 hζ hx harc he hγ hv _ hTmem.2 hsetT,
        hcapA T hTmem]
    -- the extension by the query
    have halive' : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r)
        (((RootJ32.experiment c r).data.ang a, q) :: l) :=
      TestEvents.aliveTests_inter_subset l a q ⟨halive, htest⟩
    have hqlive := RootJ32.next_piece_live_of_test c r l a q ω htest
    have hsetq := prefixSet_query_eq c r l a ω hord hold hgood hγ hTq hqcap hqlive
    have hhist' : RootJ31.historyProgram c r (((RootJ32.experiment c r).data.ang a, q) :: l) =
        RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))] :=
      RootJ31.historyProgram_cons c r l _ q
    have hcapq : capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r
        (((RootJ32.experiment c r).data.ang a, q) :: l) ω = 4 ^ r.2 * A q := by
      have hsc := hcap hx _ harc (RootJ32.schedAdm_of_alive c r _ ω halive' hseed)
        (by
          change Disjoint _ ((fun z : ℂ => -z⁻¹) ''
            (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x
              (RootJ31.historyProgram c r (((RootJ32.experiment c r).data.ang a, q) :: l)) ω \
                {0}))
          rw [hhist', hsetq]
          exact disjoint_of_noncontact (hnc' q hqmem.2))
      change 4 ^ r.2 * schedCap c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (regW c.s c.W c.ζ) c.s
        c.Θ c.Q x (rootEntry r.1) (entryList (((RootJ32.experiment c r).data.ang a, q) :: l)) ω = _
      rw [hsc]
      change 4 ^ r.2 * capOf (prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
        (regW c.s c.W c.ζ) c.s x
          (RootJ31.historyProgram c r (((RootJ32.experiment c r).data.ang a, q) :: l)) ω) = _
      rw [hhist', prefixImage_eq_of_prefixSet c ω hα hWc hW0 hζ hx harc he hγ hv _ hqmem.2 hsetq,
        hcapA q hqmem]
    change capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω +
      (RootJ31.sourceClock c r l a q ω : ℝ) ≤ _
    rw [hcapT, hcapq, hclock_eq]
    linarith


/-- **Clause (a) of `clock_spec` for J32**, almost surely at every passed test after any history. -/
theorem ae_clock_spec_a_J32 (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ∀ q : c.Q, ω ∈ (RootJ32.experiment c r).data.tests l a q →
      ContinuousAt ((RootJ32.experiment c r).Y l a ω) ((RootJ32.experiment c r).clock l a q ω) := by
  filter_upwards [ae_live_clock h13 c r, RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ]
    with ω hclock hcover hα hreg hζ q htest
  have hSF : RootJ32.sourceEntry c r l a ω < RootJ31.sourceFailure c r l a ω :=
    htest.1.trans htest.2.1
  have hlive := RootJ32.live_of_entry_lt_failure c r l a ω hSF
  obtain ⟨hcov, -, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ω hlive
  obtain ⟨hseed, hsH, -, -, -, harc⟩ := hcover hcov
  obtain ⟨_, _, hWc, hW0, _⟩ := hreg
  have hs : 0 < c.s := by
    by_contra hn
    have hs0 : c.s = 0 := le_antisymm (not_lt.mp hn) zero_le
    exact ne_zero_of_mem_H hsH (by rw [hs0]; exact hα.1)
  obtain ⟨γ, hγ, hA0, hmono, hcont, -, hnc⟩ := hclock l a hlive
  obtain ⟨hJ, hJ0⟩ := continuous_futureJoined c r l a ω
  set T := RootJ31.historyTime c r l with hTdef
  set F := RootJ31.sourceBuffer c r l a ω with hFdef
  set L := T + RootJ31.candidateCap c r a with hLdef
  have hTq : T < (q : ℝ≥0) :=
    NNReal.coe_lt_coe.mp ((RootJ32.sourceEntry_ge_historyTime c r l a ω).trans_lt htest.1)
  have hqv : (q : ℝ≥0) < T + F := by
    have h := htest.2.1
    change ((q : ℝ≥0) : ℝ) < ((T + F : ℝ≥0) : ℝ) at h
    exact_mod_cast h
  have hFL : T + F ≤ L := add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ω)
  have hpe := futurePair_eq_recOfDriver c r l a ω
  rw [hpe] at hmono hcont
  have hTmem : T ∈ Icc 0 (T + F) := ⟨zero_le, hTq.le.trans hqv.le⟩
  have hqmem : (q : ℝ≥0) ∈ Icc 0 (T + F) := ⟨zero_le, hqv.le⟩
  have hFmem : T + F ∈ Icc 0 (T + F) := ⟨zero_le, le_rfl⟩
  set p' := (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver L (futureJoined c r l a ω))
    with hp'
  have hA0' : RootH29.forwardCapacity (rootPt r.1) c.s 0 p' = 0 := by rw [← hpe]; exact hA0
  have hAT0 : 0 ≤ RootH29.forwardCapacity (rootPt r.1) c.s T p' := by
    rw [← hA0']; exact hmono.monotoneOn ⟨le_rfl, zero_le⟩ hTmem zero_le
  have hATq := hmono.monotoneOn hTmem hqmem hTq.le
  have hAqF := hmono hqmem hFmem hqv
  set k : ℝ≥0 := 2 ^ r.2 with hk
  have hk0 : 0 < k := pow_pos (by norm_num) _
  have hclockq : RootJ31.sourceClock c r l a q ω =
      RootJ31.capacityIncrement k (rootPt r.1) c.s T ((q : ℝ≥0) - T) p' := by
    rw [← hpe]; rfl
  have hcap : (RootH29.forwardCapacity (rootPt r.1) c.s T p').toNNReal +
      RootJ31.capacityIncrement k (rootPt r.1) c.s T ((q : ℝ≥0) - T) p' / k ^ 2 =
      (RootH29.forwardCapacity (rootPt r.1) c.s q p').toNNReal := by
    rw [RootJ31.capacityIncrement, add_tsub_cancel_of_le hTq.le,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 hk0.ne'), ← Real.toNNReal_add hAT0
      (sub_nonneg.2 hATq), add_sub_cancel]
  have key := continuousAt_stageDriverRead_J32 c.W c.ζ ω hα hWc hW0 hζ hs
    (RootH29.rootPt_nonneg_of_seedOK c hseed) harc hJ hJ0 hγ hFL hnc hmono hcont
    (k := k) ((-1) ^ l.length) (rootEntry r.1).2 T
    (u₀ := RootJ31.capacityIncrement k (rootPt r.1) c.s T ((q : ℝ≥0) - T) p')
    (by rw [hcap, Real.coe_toNNReal _ (hAT0.trans hATq)]; exact hAqF)
  have hD : (RootJ32.experiment c r).Y l a ω = fun u => RootJ32.stageDriverRead k
      ((-1) ^ l.length) (rootPt r.1) c.s L (rootEntry r.1).2 T u p' := by
    funext u
    change RootJ32.stageDriverRead _ _ _ _ _ _ _ u (RootJ31.futurePair c r l a ω) = _
    rw [hpe]
  have hC : (RootJ32.experiment c r).clock l a q ω =
      RootJ31.capacityIncrement k (rootPt r.1) c.s T ((q : ℝ≥0) - T) p' := hclockq
  rw [hD, hC]
  exact key

end InteractingSLE.Theorem14.GW2TipSystem.Gm

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ32

open RootC24

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem reach_identification (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    (experiment c r).data.sample l a ⁻¹' (experiment c r).data.reach l a =ᵐ[c.P]
      {ω | (experiment c r).data.S l a ω < (experiment c r).data.F l a ω} :=
  Gm.reach_identification_J32 h13 c r l a

/-- **The field `clock_spec` for J32.** -/
theorem clock_spec (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ (experiment c r).data.alive ((construction c).G r) l → ∀ q : c.Q,
      ω ∈ (experiment c r).data.tests l a q →
        ContinuousAt ((experiment c r).Y l a ω) ((experiment c r).clock l a q ω) ∧
        ((experiment c r).clock l a q ω : ℝ≥0∞) < ((experiment c r).data.sample l a ω).1 ∧
        7 / 4 < (experiment c r).Y l a ω ((experiment c r).clock l a q ω) ∧
        capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω +
            (experiment c r).clock l a q ω ≤
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r
            (((experiment c r).data.ang a, q) :: l) ω := by
  filter_upwards [Gm.ae_clock_spec_a_J32 h13 c r l a, Gm.ae_clock_spec_bcd_J32 h13 c r l a]
    with ω ha hbcd halive q htest
  exact ⟨ha q htest, hbcd halive q htest⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootJ32
