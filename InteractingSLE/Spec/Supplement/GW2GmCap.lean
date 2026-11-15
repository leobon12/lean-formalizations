/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmPrefix
import InteractingSLE.Spec.Supplement.GW2GmReach
import InteractingSLE.Spec.Supplement.GW2RootH29Capacity
import InteractingSLE.Spec.Supplement.GW2RootI30Initial

/-!
# The switched capacity increment of J31: `clock_spec` without the driver continuity

Packet PROVE-GW2-GEOM2 (step R4). The field `clock_spec` of the open geometry asks, at every passed test
`q` after an alive history `l`, for (a) continuity of the stage driver at the clock, (b) the clock before
the sample's lifetime, (c) the band crossing `7/4 < Y(clock)`, and (d) the capacity increment
`capR l + clock ≤ capR ((θ, q) :: l)`. This file proves (b), (c) and (d) for J31's construction:

* `prefixImage_eq_of_prefixSet`: a prefix set equal to a translated trace prefix before contact has, as
  prefix image, the mapped trace prefix (the multi-piece form of I30's `capR_nil_eq_reader` step);
* `disjoint_of_noncontact`, `schedAdm_of_alive`: the hypotheses of H29's capacity identification;
* **`ae_clock_spec_bcd`**: clauses (b), (c), (d) of `clock_spec`, almost surely; (d) holds with equality
  (`capR l = 4ᵏ A(T)`, `capR ((θ, q) :: l) = 4ᵏ A(q)`, `clock = 4ᵏ (A(q) - A(T))`).

Clause (a) (continuity of `RootJ31.sourceDriver` at the clock) needs the capacity-time driver reader to be
the driver of the capacity-parametrized trace (step R5); it is not proved here.
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

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The prefix image of a prefix set that is a translated trace prefix before contact** is the
mapped trace prefix (I30's `capR_nil_eq_reader` step, for any schedule). -/
theorem prefixImage_eq_of_prefixSet (c : SourceData Ω) (ω : Ω)
    (hα : IsGeneratingTrace (c.W · ω) ⊤ (c.α ω)) (hW : Continuous (c.W · ω))
    (hW0 : c.W 0 ω = 0) (hζ : c.ζ ω = ⊤) {x : ℝ} (hx : 0 ≤ x)
    (harc : ∀ u ∈ Icc 0 c.s, x * ‖c.α ω u‖ < 1)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (c.α ω u : OnePoint ℂ)) '' Icc 0 c.s)) e.2)
    (L : List (ℝ × ℝ≥0)) {t : ℝ≥0} (htv : t ≤ v)
    (hset : prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x L ω =
      (fun z => (x : ℂ) + z) '' (γ '' Icc 0 t)) :
    prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (regW c.s c.W c.ζ) c.s x L ω =
      relMap (rdrv (cfRec c.s c.W c.ζ ω)) c.s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t ∩ H) := by
  let U := rdrv (cfRec c.s c.W c.ζ ω)
  let U₀ := Ito.rpath (c.W · ω)
  have hrec := GaugeE.record_prefix_eq c.s hW0 hW.continuousOn
    (show (c.s : ℝ≥0∞) < c.ζ ω by rw [hζ]; exact ENNReal.coe_lt_top)
  have hUK : QuantumZipper.fwdHull U c.s = QuantumZipper.fwdHull U₀ c.s :=
    GaugeE.record_hull_eq c.s hW0 hW.continuousOn (by rw [hζ]; exact ENNReal.coe_lt_top)
  have hmap : relMap U c.s = relMap U₀ c.s := relMap_eq_of_eqOn c.s.coe_nonneg hrec
  have hdom : relDomain U c.s = relDomain U₀ c.s := by
    unfold relDomain Supp8.Q3Rel.invHull
    rw [hUK]
  have hreg : (fun q : ℝ => regW c.s c.W c.ζ q.toNNReal ω) = U₀ := by
    funext q
    exact regW_eq c.s hζ hW0 hW q.toNNReal
  have hsafe : MapsTo (fun q => (x : ℂ) + γ q) (Icc 0 t) (relSafe U c.s) :=
    fun q hq => RootH29.trace_mem_record_relSafe c.W c.ζ ω hα hW hW0 hζ hx harc he hγ hv
      (hq.2.trans htv)
  have hinter : (fun z => (x : ℂ) + z) '' (γ '' Icc 0 t) ∩ relDomain U c.s =
      (fun q => (x : ℂ) + γ q) '' Icc 0 t ∩ H := by
    rw [image_image]
    apply Subset.antisymm
    · exact inter_subset_inter_right _ fun _ hz => hz.1
    · rintro z ⟨⟨q, hq, rfl⟩, hzH⟩
      exact ⟨mem_image_of_mem _ hq, hzH, fun hzInv => (hsafe hq).2 (subset_closure hzInv)⟩
  rw [prefixImage, hreg, hset, ← RootY20.relDomain_eq_jointDomain, ← hdom]
  change relMap U₀ c.s '' _ = _
  rw [← hmap, hinter]

/-- A translated trace prefix that never meets the inverted counterflow prefix is disjoint from it, in
the inverted form used by H29's capacity identification. -/
theorem disjoint_of_noncontact {x : ℝ} {γ α : ℝ≥0 → ℂ} {t s : ℝ≥0}
    (h : ∀ t' ∈ Icc 0 t, ∀ u ∈ Icc 0 s, ((x : ℂ) + γ t') * α u + 1 ≠ 0) :
    Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' ((fun z => (x : ℂ) + z) '' (γ '' Icc 0 t) \ {0})) := by
  rw [Set.disjoint_left]
  rintro _ ⟨u, hu, rfl⟩ ⟨_, ⟨⟨_, ⟨t', ht', rfl⟩, rfl⟩, hz0⟩, heq⟩
  have hz : (x : ℂ) + γ t' ≠ 0 := hz0
  apply h t' ht' u hu
  rw [← heq, mul_neg, mul_inv_cancel₀ hz, neg_add_cancel]

/-- **An alive history of J31 is an admissible schedule** at a protected root. -/
theorem schedAdm_of_alive [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (RootJ31.experiment c r).data.alive ((RootJ31.construction c).G r) l)
    (hseed : RootCv.RootSeedOK c r.1) :
    SchedAdm c.b c.jumps c.Θ c.Q (κ := c.κ) (rootPt r.1) (rootEntry r.1) (entryList l) := by
  refine ⟨(RootI30.schedAdm_nil_of_seedOK c r hseed).1, ?_,
    pairwise_lt_historyProgram_of_alive c r l ω ha⟩
  intro p hp
  simp only [schedOf, entryList, List.mem_cons, List.mem_reverse, List.mem_map] at hp
  rcases hp with rfl | ⟨y, -, rfl⟩
  · exact ⟨r.1.2.1.property, r.1.2.2.property⟩
  · exact ⟨y.1.property, y.2.property⟩

theorem four_pow_eq (k : ℕ) : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

variable [StandardBorelSpace Ω]

/-- **Clauses (b), (c), (d) of `clock_spec` for J31's construction.** Almost surely, at every passed
test `q` after an alive history `l`: the clock is before the sample's lifetime, the stage driver at the
clock is above `7/4`, and the normalized capacity grows by the clock (with equality). -/
theorem ae_clock_spec_bcd (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ31.experiment c r).data.alive ((RootJ31.construction c).G r) l →
      ∀ q : c.Q, ω ∈ (RootJ31.experiment c r).data.tests l a q →
        ((RootJ31.experiment c r).clock l a q ω : ℝ≥0∞) <
            ((RootJ31.experiment c r).data.sample l a ω).1 ∧
          7 / 4 < (RootJ31.experiment c r).Y l a ω ((RootJ31.experiment c r).clock l a q ω) ∧
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω +
              (RootJ31.experiment c r).clock l a q ω ≤
            capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r
              (((RootJ31.experiment c r).data.ang a, q) :: l) ω := by
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
  have hSF : RootJ31.sourceEntry c r l a ω < RootJ31.sourceFailure c r l a ω :=
    htest.1.trans htest.2.1
  have hlive : 0 < (RootJ31.sourceSample c r l a ω).1 :=
    lt_of_le_of_lt bot_le (RootJ31.entry_lt_failure_imp_reach c r l a ω hSF)
  obtain ⟨hcov, hold, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ω hlive
  obtain ⟨hseed, -, -, -, -, harc⟩ := hcover hcov
  have hx : 0 ≤ x := RootH29.rootPt_nonneg_of_seedOK c hseed
  obtain ⟨γ, hγ, -, hmono, -, hcapA, hnc⟩ := hclock l a hlive
  obtain ⟨hgood, -⟩ := hjoin l a hold
  obtain ⟨_, _, hWc, hW0, _⟩ := hreg
  have hord := timeOrdered_historyProgram_of_alive c r l ω halive
  -- the query time
  have hTq : T < (q : ℝ≥0) :=
    NNReal.coe_lt_coe.mp ((RootJ31.sourceEntry_ge_historyTime c r l a ω).trans_lt htest.1)
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
    change RootJ31.sourceDriver c r l a ω
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
      have hsc := hcap hx l harc (schedAdm_of_alive c r l ω halive hseed)
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
    have halive' : ω ∈ (RootJ31.experiment c r).data.alive ((RootJ31.construction c).G r)
        (((RootJ31.experiment c r).data.ang a, q) :: l) :=
      TestEvents.aliveTests_inter_subset l a q ⟨halive, htest⟩
    have hqlive := RootJ31.next_piece_live_of_test c r l a q ω htest
    have hsetq := prefixSet_query_eq c r l a ω hord hold hgood hγ hTq hqcap hqlive
    have hhist' : RootJ31.historyProgram c r (((RootJ31.experiment c r).data.ang a, q) :: l) =
        RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))] :=
      RootJ31.historyProgram_cons c r l _ q
    have hcapq : capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r
        (((RootJ31.experiment c r).data.ang a, q) :: l) ω = 4 ^ r.2 * A q := by
      have hsc := hcap hx _ harc (schedAdm_of_alive c r _ ω halive' hseed)
        (by
          change Disjoint _ ((fun z : ℂ => -z⁻¹) ''
            (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h x
              (RootJ31.historyProgram c r (((RootJ31.experiment c r).data.ang a, q) :: l)) ω \
                {0}))
          rw [hhist', hsetq]
          exact disjoint_of_noncontact (hnc' q hqmem.2))
      change 4 ^ r.2 * schedCap c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (regW c.s c.W c.ζ) c.s
        c.Θ c.Q x (rootEntry r.1) (entryList (((RootJ31.experiment c r).data.ang a, q) :: l)) ω = _
      rw [hsc]
      change 4 ^ r.2 * capOf (prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
        (regW c.s c.W c.ζ) c.s x
          (RootJ31.historyProgram c r (((RootJ31.experiment c r).data.ang a, q) :: l)) ω) = _
      rw [hhist', prefixImage_eq_of_prefixSet c ω hα hWc hW0 hζ hx harc he hγ hv _ hqmem.2 hsetq,
        hcapA q hqmem]
    change capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω +
      (RootJ31.sourceClock c r l a q ω : ℝ) ≤ _
    rw [hcapT, hcapq, hclock_eq]
    linarith

end InteractingSLE.Theorem14.GW2TipSystem.Gm
