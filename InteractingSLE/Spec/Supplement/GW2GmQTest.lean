/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmQStmt
import InteractingSLE.Spec.Supplement.GW2SdjTop

/-!
# The per-root claims from the D2 geometry (observation on alive histories)

Packet PROVE-GW2-GEOM2 (round 5; decision D2). The consumer of `observation` builds versions `T'` of the tests;
with `observation` only on alive histories, `T'` agrees with the tests only on alive histories. Both uses survive:

* `mem_aliveTests_iff_of_alive`: tests agreeing on the alive histories give the same alive events (induction);
* **`testClaims_unitEvent_A`** (successor of `Gm.testClaims_unitEvent_V`): the conditional crossing probabilities
  of `⋃ T'` and `⋃ tests` agree at almost every alive point (the kernel there is carried by the retained alive set);
* **`testClaims_of_modelCross_unitEvent_A`** (successor of `GW2Sdj.testClaims_of_modelCross_unitEvent_V`);
* **`ExperimentGeometryA.exists_testClaims_lossy`** (successor of `GW2Sdj.ExperimentGeometryV.exists_testClaims_lossy`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u v

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open GW2Schedule Exist Staged StagedLaw Restart LQGMetric RootC24 RootK3 GW2Sdj

/-- **Tests agreeing on the alive histories give the same alive events.** -/
theorem mem_aliveTests_iff_of_alive {Ω' Θ Q : Type*} {G : Set Ω'} {ang : ℕ → Θ}
    {T T' : List (Θ × Q) → ℕ → Q → Set Ω'} {ω : Ω'}
    (h : ∀ l a q, ω ∈ TestEvents.aliveTests G ang T l → (ω ∈ T' l a q ↔ ω ∈ T l a q)) :
    ∀ l, ω ∈ TestEvents.aliveTests G ang T' l ↔ ω ∈ TestEvents.aliveTests G ang T l
  | [] => Iff.rfl
  | x :: l => by
    have ih := mem_aliveTests_iff_of_alive h l
    simp only [TestEvents.aliveTests, mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨hA, a, ha, hT⟩
      exact ⟨ih.1 hA, a, ha, (h l a x.2 (ih.1 hA)).1 hT⟩
    · rintro ⟨hA, a, ha, hT⟩
      exact ⟨ih.2 hA, a, ha, (h l a x.2 hA).2 hT⟩

section Claims

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The per-root claims for versions of the tests agreeing with them on the alive histories** (successor of
`testClaims_unitEvent_V`, decision D2; as `Swc.testClaims_unitEvent`, with the
tests replaced by versions `T'` and the alive events by `aliveTests G ang T'`; regularity on those alive events). -/
theorem testClaims_unitEvent_A (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {G : Set Ω}
    (hG : MeasurableSet[c.sigma r []] G) (ang : ℕ → c.Θ)
    (X : List (EntryIdx c.Θ c.Q) → ℕ → Ω → ℝ → ℝ)
    (γ : List (EntryIdx c.Θ c.Q) → ℕ → Ω → ℝ → ℂ)
    (S F : List (EntryIdx c.Θ c.Q) → ℕ → Ω → ℝ)
    (I : List (EntryIdx c.Θ c.Q) → ℕ → Set ℝ) (hI : ∀ l a, IsOpen (I l a))
    (T' : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Set Ω)
    (hT'm : ∀ l a (q q' : c.Q), q ≤ q' → MeasurableSet[c.sigma r ((ang a, q') :: l)] (T' l a q))
    (hT'eq : ∀ l a q, ∀ᵐ ω ∂c.P, ω ∈ TestEvents.aliveTests G ang T' l →
      (ω ∈ T' l a q ↔ ω ∈ experimentTests X γ S F I l a q))
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
    have h2 : ∀ a, ∀ᵐ ω ∂c.P, ω ∈ TestEvents.aliveTests G ang T' l →
        condExpKernel c.P (c.sigma r l) ω (⋃ q : c.Q, T' l a q) =
          condExpKernel c.P (c.sigma r l) ω (⋃ q : c.Q, experimentTests X γ S F I l a q) := by
      intro a
      have hU : (⋃ q : c.Q, T' l a q) ∩ TestEvents.aliveTests G ang T' l =ᵐ[c.P]
          (⋃ q : c.Q, experimentTests X γ S F I l a q) ∩ TestEvents.aliveTests G ang T' l := by
        filter_upwards [ae_all_iff.2 (hT'eq l a)] with ω hω
        show (ω ∈ (⋃ q : c.Q, T' l a q) ∩ TestEvents.aliveTests G ang T' l) =
          (ω ∈ (⋃ q : c.Q, experimentTests X γ S F I l a q) ∩ TestEvents.aliveTests G ang T' l)
        apply propext
        simp only [mem_inter_iff, mem_iUnion]
        constructor
        · rintro ⟨⟨q, hq⟩, hA'⟩
          exact ⟨⟨q, (hω q hA').1 hq⟩, hA'⟩
        · rintro ⟨⟨q, hq⟩, hA'⟩
          exact ⟨⟨q, (hω q hA').2 hq⟩, hA'⟩
      filter_upwards [ae_condExpKernel_congr (hle l) hU,
        KernelTower.ae_condExpKernel_compl_eq_zero (hle l) (hA l)] with ω hω hcompl hωA
      have hc := hcompl.1 hωA
      rw [← measure_inter_conull hc, hω, measure_inter_conull hc]
    filter_upwards [h1, ae_all_iff.2 h2] with ω hω1 hω2 hωA
    obtain ⟨a, ha⟩ := hω1 hωA
    exact ⟨a, (hω2 a hωA).symm ▸ ha⟩
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


/-- **The per-root claims from the model crossing clause, with the observation on alive histories** (successor of
`GW2Sdj.testClaims_of_modelCross_unitEvent_V`, decision D2). -/
theorem testClaims_of_modelCross_unitEvent_A {Ξ : Type v} [MeasurableSpace Ξ]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {G : Set Ω}
    (d : StageModelData Ω c.Θ c.Q Ξ (c.sigma r))
    (hModelCross : ∀ l (δ : ℝ≥0∞), 0 < δ → ∀ᵐ ω ∂c.P,
      ω ∈ d.alive G l → ∃ a, 1 - δ < d.kernel l a ω (d.reach l a))
    (hG : MeasurableSet[c.sigma r []] G)
    (hI : ∀ l a, IsOpen (d.I l a))
    (hObs : ∀ l a (q q' : c.Q), q ≤ q' → ∃ g : Ω → ℝ × ℂ,
      Measurable[c.sigma r ((d.ang a, q') :: l)] g ∧
      ∀ᵐ ω ∂c.P, ω ∈ d.alive G l → d.observation l a q ω = g ω)
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
  choose g hgm hgeq using fun l a (q : c.Q) => hObs l a q q le_rfl
  set T' : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Set Ω :=
    fun l a q => g l a q ⁻¹' (d.I l a ×ˢ H) with hT'def
  have hT'm : ∀ l a (q q' : c.Q), q ≤ q' →
      MeasurableSet[c.sigma r ((d.ang a, q') :: l)] (T' l a q) := fun l a q q' hqq' =>
    RootH29.rootSigma_next_mono c r l (d.ang a) hqq' _
      (hgm l a q ((hI l a).measurableSet.prod QuantumZipper.isOpen_H.measurableSet))
  have hT'eq : ∀ l a q, ∀ᵐ ω ∂c.P, ω ∈ d.alive G l → (ω ∈ T' l a q ↔ ω ∈ d.tests l a q) := by
    intro l a q
    filter_upwards [hgeq l a q] with ω hω hωA
    rw [d.tests_eq_preimage_observation l a q]
    change (g l a q ω ∈ d.I l a ×ˢ H) ↔ (d.observation l a q ω ∈ d.I l a ×ˢ H)
    rw [hω hωA]
  have hpt : ∀ᵐ ω ∂c.P, ∀ l a q, ω ∈ d.alive G l → (ω ∈ T' l a q ↔ ω ∈ d.tests l a q) := by
    rw [ae_all_iff]; intro l; rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro q
    exact hT'eq l a q
  have halive : ∀ᵐ ω ∂c.P, ∀ l, ω ∈ TestEvents.aliveTests G d.ang T' l ↔ ω ∈ d.alive G l := by
    filter_upwards [hpt] with ω hω
    exact mem_aliveTests_iff_of_alive hω
  have hT'eqA : ∀ l a q, ∀ᵐ ω ∂c.P, ω ∈ TestEvents.aliveTests G d.ang T' l →
      (ω ∈ T' l a q ↔ ω ∈ d.tests l a q) := by
    intro l a q
    filter_upwards [hT'eq l a q, halive] with ω hω hal hωA
    exact hω ((hal l).1 hωA)
  refine ⟨TestEvents.aliveTests G d.ang T', T', testClaims_unitEvent_A c r hG d.ang d.X d.γ d.S
    d.F d.I hI T' hT'm hT'eqA ?_ ?_ (fun l a => d.sample l a ⁻¹' d.slow l a)
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
    exact h ((hal l).1 hωA) hE q ((hpω l a q ((hal l).1 hωA)).1 hq)

/-- **All per-root claims from the D2 geometry and the LOSSY near models** (successor of
`GW2Sdj.ExperimentGeometryV.exists_testClaims_lossy`). -/
theorem ExperimentGeometryA.exists_testClaims_lossy {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {G : Set Ω} {e : Experiment c r}
    (hg : ExperimentGeometryA c r G e) (h13 : Theorem13Statement.{u})
    (hG : MeasurableSet[c.sigma r []] G)
    (hNear : GW2Sdi.HasNearCrossingModelsLossy.{u} c.κ c.P (e.data.alive G)
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
  obtain ⟨A, T, hc⟩ := testClaims_of_modelCross_unitEvent_A (d := d') c r
    (hNear.modelCross h13 c.hκ c.hκ4) hG hg.band_open
    hg.observation hg.regularity e.sampleMeas hg.reach_measurable
    (fun _ _ => RootV7.measurableSet_slowSet)
    (fun _ _ => Eventually.of_forall fun _ _ => rfl)
    hg.reach_identification hp₀ hp₀1 hModelSlow hUnit
  exact ⟨p₀, A, T, hc⟩

end Claims

end InteractingSLE.Theorem14.GW2TipSystem.Gm
