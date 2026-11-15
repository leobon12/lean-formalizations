/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmVStmt
import InteractingSLE.Spec.Supplement.GW2RootH29Sigma

/-!
# The per-root claims from the successor geometry, with measurable versions of the tests

Packet PROVE-GW2-GEOM2 (ruling R111). `GW2RootTestStatement` quantifies its alive events and tests existentially.
From the successor geometry (`ExperimentGeometryV`: observation measurable up to null sets, regularity on alive
histories) the claims are proved for **measurable versions** `T'` of the actual tests (a.e. equal to them) and the
alive events `A' = aliveTests G ang T'` built from them. Every use of exactness in SWITCH's
`Swc.testClaims_unitEvent` / `Swc.testClaims_of_nearModels_unitEvent` becomes an a.e. transfer:

* `ae_condExpKernel_congr`: a.e. equal sets have equal conditional measures, a.s.;
* `ae_mem_aliveTests_iff`: a.e. equal tests give a.e. equal alive events (countable index sets);
* `ae_exists_candidate_probability_on`: `TestCross.ae_exists_candidate_probability` with the path regularity
  required only on a retained event `R`;
* **`testClaims_unitEvent_V`**, **`testClaims_of_nearModels_unitEvent_V`**;
* **`ExperimentGeometryV.exists_testClaims`**: as `Swc.ExperimentGeometryU.exists_testClaims`, with versions.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u v

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open GW2Schedule Exist Staged StagedLaw Restart LQGMetric RootC24 RootK3

/-- A.e. equal sets have, almost surely, the same conditional measure. -/
theorem ae_condExpKernel_congr {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] (hm : m ≤ mΩ) {U V : Set Ω}
    (h : U =ᵐ[P] V) : ∀ᵐ ω ∂P, condExpKernel P m ω U = condExpKernel P m ω V := by
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae hm h] with ω hω
  exact measure_congr hω

/-- Pointwise agreement of the tests gives pointwise agreement of the alive events. -/
theorem mem_aliveTests_iff {Ω : Type*} {Θ : Set ℝ} {Q : Set ℝ≥0} {G : Set Ω} {ang : ℕ → Θ}
    {T T' : List (Θ × Q) → ℕ → Q → Set Ω} {ω : Ω}
    (h : ∀ l a q, ω ∈ T' l a q ↔ ω ∈ T l a q) :
    ∀ l, ω ∈ TestEvents.aliveTests G ang T' l ↔ ω ∈ TestEvents.aliveTests G ang T l
  | [] => Iff.rfl
  | x :: l => by
    simp only [TestEvents.aliveTests, mem_inter_iff, mem_iUnion, h, mem_aliveTests_iff h l]

/-- **The candidate crossing transfer with regularity on a retained event.** -/
theorem ae_exists_candidate_probability_on {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (h𝒢 : 𝒢 ≤ mΩ) {Q : Set ℝ≥0} (hQ : Dense Q)
    {R : Set Ω} (hR : MeasurableSet[𝒢] R) {X : ℕ → Ω → ℝ → ℝ} {γ : ℕ → Ω → ℝ → ℂ}
    {S F : ℕ → Ω → ℝ} {I : ℕ → Set ℝ} (hI : ∀ a, IsOpen (I a))
    (hreg : ∀ a, ∀ᵐ ω ∂P, ω ∈ R → S a ω < F a ω →
      0 ≤ S a ω ∧ ContinuousAt (X a ω) (S a ω) ∧ X a ω (S a ω) ∈ I a ∧
      ContinuousOn (γ a ω) (Ioo (S a ω) (F a ω)) ∧
      volume {t | t ∈ Ioo (S a ω) (F a ω) ∧ γ a ω t ∉ H} = 0)
    {ε : ℝ≥0∞}
    (hcross : ∀ᵐ ω ∂P, ω ∈ R → ∃ a,
      1 - ε < condExpKernel P 𝒢 ω {ω' | S a ω' < F a ω'}) :
    ∀ᵐ ω ∂P, ω ∈ R → ∃ a, 1 - ε <
      condExpKernel P 𝒢 ω (⋃ q : Q, TestCross.candidateTest (X a) (γ a) (S a) (F a) (I a) q) := by
  have heq : ∀ a, ∀ᵐ ω₀ ∂P, ω₀ ∈ R →
      condExpKernel P 𝒢 ω₀ (⋃ q : Q, TestCross.candidateTest (X a) (γ a) (S a) (F a) (I a) q) =
        condExpKernel P 𝒢 ω₀ {ω' | S a ω' < F a ω'} := by
    intro a
    filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (hreg a),
      KernelTower.ae_condExpKernel_compl_eq_zero h𝒢 hR] with ω₀ hω₀ hcompl hω₀R
    have hRae : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ R :=
      measure_eq_zero_iff_ae_notMem.1 ((hcompl.1 hω₀R)) |>.mono fun _ h => not_not.1 h
    refine TestCross.measure_candidate_union _ hQ (hI a) ?_
    filter_upwards [hω₀, hRae] with ω h hωR
    exact h hωR
  filter_upwards [ae_all_iff.2 heq, hcross] with ω hωeq hωcross hωR
  obtain ⟨a, ha⟩ := hωcross hωR
  exact ⟨a, (hωeq a hωR).symm ▸ ha⟩

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The per-root claims for measurable versions of the tests** (as `Swc.testClaims_unitEvent`, with the
tests replaced by versions `T'` and the alive events by `aliveTests G ang T'`; regularity on those alive events). -/
theorem testClaims_unitEvent_V (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {G : Set Ω}
    (hG : MeasurableSet[c.sigma r []] G) (ang : ℕ → c.Θ)
    (X : List (EntryIdx c.Θ c.Q) → ℕ → Ω → ℝ → ℝ)
    (γ : List (EntryIdx c.Θ c.Q) → ℕ → Ω → ℝ → ℂ)
    (S F : List (EntryIdx c.Θ c.Q) → ℕ → Ω → ℝ)
    (I : List (EntryIdx c.Θ c.Q) → ℕ → Set ℝ) (hI : ∀ l a, IsOpen (I l a))
    (T' : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Set Ω)
    (hT'm : ∀ l a (q q' : c.Q), q ≤ q' → MeasurableSet[c.sigma r ((ang a, q') :: l)] (T' l a q))
    (hT'eq : ∀ l a q, T' l a q =ᵐ[c.P] experimentTests X γ S F I l a q)
    (hreg : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ TestEvents.aliveTests G ang T' l → S l a ω < F l a ω →
      0 ≤ S l a ω ∧ ContinuousAt (X l a ω) (S l a ω) ∧ X l a ω (S l a ω) ∈ I l a ∧
      ContinuousOn (γ l a ω) (Ioo (S l a ω) (F l a ω)) ∧
      volume {t | t ∈ Ioo (S l a ω) (F l a ω) ∧ γ l a ω t ∉ H} = 0)
    (hreach : ∀ l (ε : ℝ≥0∞), 0 < ε → ∀ᵐ ω ∂c.P,
      ω ∈ TestEvents.aliveTests G ang T' l → ∃ a,
        1 - ε < condExpKernel c.P (c.sigma r l) ω {ω' | S l a ω' < F l a ω'})
    (E : List (EntryIdx c.Θ c.Q) → ℕ → Set Ω) (hE : ∀ l a, MeasurableSet (E l a))
    {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hcomp : ∀ (k : ℕ) l, l.length = 2 * k + 4 → ∀ a (C : Set Ω),
      MeasurableSet[c.sigma r l] C → C ⊆ TestEvents.aliveTests G ang T' l →
      ENNReal.ofReal p₀ * c.P C ≤ c.P (C ∩ E l a))
    (hslow : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ TestEvents.aliveTests G ang T' l →
      ω ∈ E l a → ∀ q : c.Q, ω ∈ T' l a q →
        capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω + 1 ≤
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r ((ang a, q) :: l) ω) :
    TestClaims c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P r G
      (TestEvents.aliveTests G ang T') ang T' (RootF27.unitEvent c r) p₀ := by
  have : Countable c.Q := c.hQc.to_subtype
  have hmono := rootSigma_le_cons c.hκ c.h12p c.βA c.c₀ c.h c.W c.ζ c.s r
  have hle : ∀ l, c.sigma r l ≤ mΩ := fun l => stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  have hA := TestEvents.measurableSet_aliveTests hmono hG (fun l a q => hT'm l a q q le_rfl)
  refine
    { hG := hG
      hGA := Subset.rfl
      hA := hA
      hT := hT'm
      hTA := TestEvents.aliveTests_inter_subset
      hV := RootF27.measurableSet_unitEvent c r
      hcross := ?_
      hp₀ := hp₀
      hp₀1 := hp₀1
      hnounit := ?_
      hcapU := fun l x _ _ hω => RootF27.unitEvent_capR c r l x hω }
  · intro l ε hε
    have h1 := ae_exists_candidate_probability_on (hle l) c.hQd (hA l) (hI l) (hreg l)
      (hreach l ε hε)
    have h2 : ∀ a, ∀ᵐ ω ∂c.P, condExpKernel c.P (c.sigma r l) ω (⋃ q : c.Q, T' l a q) =
        condExpKernel c.P (c.sigma r l) ω (⋃ q : c.Q, experimentTests X γ S F I l a q) :=
      fun a => ae_condExpKernel_congr (hle l) (EventuallyEqSet.countable_iUnion (hT'eq l a))
    filter_upwards [h1, ae_all_iff.2 h2] with ω hω1 hω2 hωA
    obtain ⟨a, ha⟩ := hω1 hωA
    exact ⟨a, (hω2 a).symm ▸ ha⟩
  · intro k l hl
    have hunit : ∀ a, ∀ᵐ ω ∂c.P, ω ∈ TestEvents.aliveTests G ang T' l →
        condExpKernel c.P (c.sigma r l) ω
          (⋃ q : c.Q, T' l a q \ RootF27.unitEvent c r ((ang a, q) :: l)) ≤
            ENNReal.ofReal (1 - p₀) := fun a =>
      TestKernel.ae_no_unit_le_of_comparison (hle l) (hA l) (hE l a) hp₀.le
        (hcomp k l hl a)
        (RootF27.ae_tests_mem_unitEvent c r (hle l _ (hA l)) (hE l a) l (ang a)
          (fun q => T' l a q) (fun q => hle _ _ (hT'm l a q q le_rfl)) (hslow l a))
    filter_upwards [ae_all_iff.2 hunit] with ω hω hωA a
    exact hω a hωA

/-- **The per-root claims from near-crossing models and the successor geometry's two weak fields.** As
`Swc.testClaims_of_nearModels_unitEvent`, with `hObs` up to null sets and `hReg` on alive histories; the claims
are for measurable versions of the tests. -/
theorem testClaims_of_nearModels_unitEvent_V {Ξ : Type v} [MeasurableSpace Ξ]
    (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {G : Set Ω}
    (d : StageModelData Ω c.Θ c.Q Ξ (c.sigma r))
    (hNear : RootN4.HasNearCrossingModels.{u} c.κ c.P (d.alive G)
      (fun l a ω => d.kernel l a ω (d.reach l a)))
    (hG : MeasurableSet[c.sigma r []] G)
    (hI : ∀ l a, IsOpen (d.I l a))
    (hObs : ∀ l a (q q' : c.Q), q ≤ q' → ∃ g : Ω → ℝ × ℂ,
      Measurable[c.sigma r ((d.ang a, q') :: l)] g ∧ d.observation l a q =ᵐ[c.P] g)
    (hReg : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ d.alive G l → d.S l a ω < d.F l a ω →
      0 ≤ d.S l a ω ∧ ContinuousAt (d.X l a ω) (d.S l a ω) ∧
      d.X l a ω (d.S l a ω) ∈ d.I l a ∧
      ContinuousOn (d.γ l a ω) (Ioo (d.S l a ω) (d.F l a ω)) ∧
      volume {t | t ∈ Ioo (d.S l a ω) (d.F l a ω) ∧ d.γ l a ω t ∉ H} = 0)
    (hSample : ∀ l a, Measurable (d.sample l a))
    (hReachMeas : ∀ l a, MeasurableSet (d.reach l a))
    (hSlowMeas : ∀ l a, MeasurableSet (d.slow l a))
    (hLaw : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ d.alive G l →
      (condExpKernel c.P (c.sigma r l) ω).map (d.sample l a) = d.kernel l a ω)
    (hReachIdent : ∀ l a, d.sample l a ⁻¹' d.reach l a =ᵐ[c.P]
      {ω | d.S l a ω < d.F l a ω})
    (hp₀ : 0 < d.p₀) (hp₀1 : d.p₀ ≤ 1)
    (hModelSlow : ∀ (k : ℕ) l, l.length = 2 * k + 4 → ∀ a,
      ∀ᵐ ω ∂c.P, ω ∈ d.alive G l →
        ENNReal.ofReal d.p₀ ≤ d.kernel l a ω (d.slow l a))
    (hUnit : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ d.alive G l →
      d.sample l a ω ∈ d.slow l a → ∀ q : c.Q, ω ∈ d.tests l a q →
        capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω + 1 ≤
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r ((d.ang a, q) :: l) ω) :
    ∃ (A : List (EntryIdx c.Θ c.Q) → Set Ω) (T : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Set Ω),
      TestClaims c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P r G A d.ang T
        (RootF27.unitEvent c r) d.p₀ := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hle : ∀ l, c.sigma r l ≤ mΩ := fun l => stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  -- the versions of the tests
  choose g hgm hgeq using fun l a (q : c.Q) => hObs l a q q le_rfl
  set T' : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Set Ω :=
    fun l a q => g l a q ⁻¹' (d.I l a ×ˢ H) with hT'def
  have hT'm : ∀ l a (q q' : c.Q), q ≤ q' →
      MeasurableSet[c.sigma r ((d.ang a, q') :: l)] (T' l a q) := fun l a q q' hqq' =>
    RootH29.rootSigma_next_mono c r l (d.ang a) hqq' _
      (hgm l a q ((hI l a).measurableSet.prod QuantumZipper.isOpen_H.measurableSet))
  have hT'eq : ∀ l a q, T' l a q =ᵐ[c.P] d.tests l a q := by
    intro l a q
    rw [d.tests_eq_preimage_observation l a q]
    filter_upwards [hgeq l a q] with ω hω
    change (g l a q ω ∈ d.I l a ×ˢ H) = (d.observation l a q ω ∈ d.I l a ×ˢ H)
    rw [hω]
  have hpt : ∀ᵐ ω ∂c.P, ∀ l a q, ω ∈ T' l a q ↔ ω ∈ d.tests l a q := by
    rw [ae_all_iff]; intro l; rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro q
    filter_upwards [hT'eq l a q] with ω hω
    exact Iff.of_eq hω
  have halive : ∀ᵐ ω ∂c.P, ∀ l, ω ∈ TestEvents.aliveTests G d.ang T' l ↔ ω ∈ d.alive G l := by
    filter_upwards [hpt] with ω hω
    exact mem_aliveTests_iff hω
  -- transfer every alive-quantified hypothesis
  have hModelCross := hNear.modelCross h13 c.hκ c.hκ4
  refine ⟨TestEvents.aliveTests G d.ang T', T', testClaims_unitEvent_V c r hG d.ang d.X d.γ d.S
    d.F d.I hI T' hT'm hT'eq ?_ ?_ (fun l a => d.sample l a ⁻¹' d.slow l a)
    (fun l a => hSample l a (hSlowMeas l a)) hp₀ hp₀1 ?_ ?_⟩
  · intro l a
    filter_upwards [hReg l a, halive] with ω hω hal hωA
    exact hω ((hal l).1 hωA)
  · intro l ε hε
    have heq := ae_all_iff.2 fun a =>
      ae_condExpKernel_event_eq_of_map (hle l) (hSample l a)
        (hReachMeas l a) (hLaw l a) (hReachIdent l a)
    filter_upwards [heq, hModelCross l ε hε, halive] with ω hωeq hωcross hal hωA
    have hωA' := (hal l).1 hωA
    obtain ⟨a, ha⟩ := hωcross hωA'
    exact ⟨a, (hωeq a hωA').symm ▸ ha⟩
  · intro k l hl a C hC hCA
    have hLaw' : ∀ᵐ ω ∂c.P, ω ∈ TestEvents.aliveTests G d.ang T' l →
        (condExpKernel c.P (c.sigma r l) ω).map (d.sample l a) = d.kernel l a ω := by
      filter_upwards [hLaw l a, halive] with ω h hal hωA
      exact h ((hal l).1 hωA)
    have hSlow' : ∀ᵐ ω ∂c.P, ω ∈ TestEvents.aliveTests G d.ang T' l →
        ENNReal.ofReal d.p₀ ≤ d.kernel l a ω (d.slow l a) := by
      filter_upwards [hModelSlow k l hl a, halive] with ω h hal hωA
      exact h ((hal l).1 hωA)
    exact le_measure_inter_preimage_of_map (hle l) (hSample l a)
      (hSlowMeas l a) hLaw' hSlow' hC hCA
  · intro l a
    filter_upwards [hUnit l a, halive, hpt] with ω h hal hpω hωA hE q hq
    exact h ((hal l).1 hωA) hE q ((hpω l a q).1 hq)

/-- **All per-root claims from the successor geometry** (as `Swc.ExperimentGeometryU.exists_testClaims`), for
measurable versions of the tests. -/
theorem ExperimentGeometryV.exists_testClaims {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {G : Set Ω} {e : Experiment c r}
    (hg : ExperimentGeometryV c r G e) (h13 : Theorem13Statement.{u})
    (hG : MeasurableSet[c.sigma r []] G)
    (hNear : RootN4.HasNearCrossingModels.{u} c.κ c.P (e.data.alive G)
      (fun l a ω => e.retained.kernel l a ω (e.data.reach l a)))
    (hSlow : RootS5.HasSlowComparisonModels.{u} c.κ e.driftBound
      (Icc (-Sec5.angleWeightBound c.κ) (Sec5.angleWeightBound c.κ)) c.P
      (e.data.alive G) List.length
      (fun l a ω => e.retained.kernel l a ω RootV7.slowSet)) :
    ∃ (p₀ : ℝ) (A : List (EntryIdx c.Θ c.Q) → Set Ω) (T : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Set Ω),
      TestClaims c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P r G A e.data.ang T
        (RootF27.unitEvent c r) p₀ := by
  have hJ2 : Icc (-Sec5.angleWeightBound c.κ) (Sec5.angleWeightBound c.κ) ⊆
      Ioi (-2) := by
    intro x hx
    exact (neg_lt_neg (Sec5.angleWeightBound_lt_two c.hκ)).trans_le hx.1
  obtain ⟨p₀, hp₀, hp₀1, hModelSlow⟩ := hSlow.exists_modelSlow c.hκ isCompact_Icc hJ2
  let d' : StageModelData Ω c.Θ c.Q RootV7.DriverRecord (c.sigma r) :=
    { e.retained with p₀ := p₀ }
  have hUnit := RootV7.ae_unit_of_record_clock (d := d') (fun _ _ => rfl)
    e.Y e.clock hg.record_read hg.clock_spec
  obtain ⟨A, T, hc⟩ := testClaims_of_nearModels_unitEvent_V (d := d') h13 c r hNear hG hg.band_open
    hg.observation hg.regularity e.sampleMeas hg.reach_measurable
    (fun _ _ => RootV7.measurableSet_slowSet)
    (fun _ _ => Eventually.of_forall fun _ _ => rfl)
    hg.reach_identification hp₀ hp₀1 hModelSlow hUnit
  exact ⟨p₀, A, T, hc⟩

end InteractingSLE.Theorem14.GW2TipSystem.Gm
