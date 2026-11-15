/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootF27Unit
import InteractingSLE.Spec.Supplement.GW2RootC24Assembly

/-!
# GW2's root tests with observable unit events

Packet PROVE-GW2-SWITCH. The C24 assembly (`RootC24.ExperimentGeometry.exists_testClaims`) reaches
`TestClaims` with the literal unit events `TestEvents.capacityUnit capR`. Their measurability in the
retained sigma algebra is the only use of the field `RootC24.ExperimentGeometry.capacity`. That
field asks for Borel measurability, at EVERY sample, of the attached/preconnected event and of the
filling of the canonical prefix images (including samples where the canonical traces do not exist).

`GW2RootTestStatement` quantifies the unit events existentially. Here they are ROOT2's observable
unit events `RootF27.unitEvent c r` (measurable in `c.sigma r l`; pointwise capacity increment;
every measurable almost-sure unit certificate is preserved). This removes the capacity-measurability
requirement from the claims chain:

* `testClaims_unitEvent`: `testClaims_of_crossing_and_comparison` with these events and no capacity
  measurability premise;
* `testClaims_of_nearModels_unitEvent`: `RootN4.testClaims_of_nearModels` (via `IsStageModel.testClaims`)
  with these events and without its `hCap` premise.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u v

namespace InteractingSLE.Theorem14.GW2TipSystem.Swc

open GW2Schedule Exist Staged StagedLaw Restart LQGMetric RootC24 RootK3

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The per-candidate claims with observable unit events.** As
`GW2TipSystem.testClaims_of_crossing_and_comparison`, for the original source data, with the unit
events `RootF27.unitEvent c r` and without any capacity measurability premise. -/
theorem testClaims_unitEvent (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {G : Set Ω}
    (hG : MeasurableSet[c.sigma r []] G) (ang : ℕ → c.Θ)
    (X : List (EntryIdx c.Θ c.Q) → ℕ → Ω → ℝ → ℝ)
    (γ : List (EntryIdx c.Θ c.Q) → ℕ → Ω → ℝ → ℂ)
    (S F : List (EntryIdx c.Θ c.Q) → ℕ → Ω → ℝ)
    (I : List (EntryIdx c.Θ c.Q) → ℕ → Set ℝ) (hI : ∀ l a, IsOpen (I l a))
    (hT : ∀ l a (q q' : c.Q), q ≤ q' →
      MeasurableSet[c.sigma r ((ang a, q') :: l)] (experimentTests X γ S F I l a q))
    (hreg : ∀ l a, ∀ᵐ ω ∂c.P, S l a ω < F l a ω →
      0 ≤ S l a ω ∧ ContinuousAt (X l a ω) (S l a ω) ∧ X l a ω (S l a ω) ∈ I l a ∧
      ContinuousOn (γ l a ω) (Ioo (S l a ω) (F l a ω)) ∧
      volume {t | t ∈ Ioo (S l a ω) (F l a ω) ∧ γ l a ω t ∉ H} = 0)
    (hreach : ∀ l (ε : ℝ≥0∞), 0 < ε → ∀ᵐ ω ∂c.P,
      ω ∈ TestEvents.aliveTests G ang (experimentTests X γ S F I) l → ∃ a,
        1 - ε < condExpKernel c.P (c.sigma r l) ω {ω' | S l a ω' < F l a ω'})
    (E : List (EntryIdx c.Θ c.Q) → ℕ → Set Ω) (hE : ∀ l a, MeasurableSet (E l a))
    {p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hcomp : ∀ (k : ℕ) l, l.length = 2 * k + 4 → ∀ a (C : Set Ω),
      MeasurableSet[c.sigma r l] C →
      C ⊆ TestEvents.aliveTests G ang (experimentTests X γ S F I) l →
      ENNReal.ofReal p₀ * c.P C ≤ c.P (C ∩ E l a))
    (hslow : ∀ l a, ∀ᵐ ω ∂c.P,
      ω ∈ TestEvents.aliveTests G ang (experimentTests X γ S F I) l →
      ω ∈ E l a → ∀ q : c.Q, ω ∈ experimentTests X γ S F I l a q →
        capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω + 1 ≤
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r ((ang a, q) :: l) ω) :
    TestClaims c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P r G
      (TestEvents.aliveTests G ang (experimentTests X γ S F I)) ang
      (experimentTests X γ S F I) (RootF27.unitEvent c r) p₀ := by
  have hmono := rootSigma_le_cons c.hκ c.h12p c.βA c.c₀ c.h c.W c.ζ c.s r
  have hle : ∀ l, c.sigma r l ≤ mΩ := fun l => stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  have hA := TestEvents.measurableSet_aliveTests hmono hG (fun l a q => hT l a q q le_rfl)
  refine
    { hG := hG
      hGA := Subset.rfl
      hA := hA
      hT := hT
      hTA := TestEvents.aliveTests_inter_subset
      hV := RootF27.measurableSet_unitEvent c r
      hcross := ?_
      hp₀ := hp₀
      hp₀1 := hp₀1
      hnounit := ?_
      hcapU := fun l x _ _ hω => RootF27.unitEvent_capR c r l x hω }
  · intro l ε hε
    exact TestCross.ae_exists_candidate_probability (hle l) c.hQd (hI l) (hreg l)
      (hreach l ε hε)
  · intro k l hl
    have hunit : ∀ a, ∀ᵐ ω ∂c.P,
        ω ∈ TestEvents.aliveTests G ang (experimentTests X γ S F I) l →
        condExpKernel c.P (c.sigma r l) ω
          (⋃ q : c.Q, experimentTests X γ S F I l a q \
            RootF27.unitEvent c r ((ang a, q) :: l)) ≤ ENNReal.ofReal (1 - p₀) := fun a =>
      TestKernel.ae_no_unit_le_of_comparison (hle l) (hA l) (hE l a) hp₀.le
        (hcomp k l hl a)
        (RootF27.ae_tests_mem_unitEvent c r (hle l _ (hA l)) (hE l a) l (ang a)
          (fun q => experimentTests X γ S F I l a q)
          (fun q => hle _ _ (hT l a q q le_rfl)) (hslow l a))
    filter_upwards [ae_all_iff.2 hunit] with ω hω hωA a
    exact hω a hωA

/-- **The per-root claims from near-crossing models, with observable unit events.** As
`RootN4.testClaims_of_nearModels`, for the original source data, with the unit events
`RootF27.unitEvent c r` and without its capacity measurability premise `hCap`. -/
theorem testClaims_of_nearModels_unitEvent {Ξ : Type v} [MeasurableSpace Ξ]
    (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {G : Set Ω}
    (d : StageModelData Ω c.Θ c.Q Ξ (c.sigma r))
    (hNear : RootN4.HasNearCrossingModels.{u} c.κ c.P (d.alive G)
      (fun l a ω => d.kernel l a ω (d.reach l a)))
    (hG : MeasurableSet[c.sigma r []] G)
    (hI : ∀ l a, IsOpen (d.I l a))
    (hObs : ∀ l a (q q' : c.Q), q ≤ q' →
      Measurable[c.sigma r ((d.ang a, q') :: l)] (d.observation l a q))
    (hReg : ∀ l a, ∀ᵐ ω ∂c.P, d.S l a ω < d.F l a ω →
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
    TestClaims c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P r G
      (d.alive G) d.ang d.tests (RootF27.unitEvent c r) d.p₀ := by
  have hle : ∀ l, c.sigma r l ≤ mΩ := fun l => stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  have hModelCross := hNear.modelCross h13 c.hκ c.hκ4
  refine testClaims_unitEvent c r hG d.ang d.X d.γ d.S d.F d.I hI ?_ hReg ?_
    (fun l a => d.sample l a ⁻¹' d.slow l a)
    (fun l a => hSample l a (hSlowMeas l a)) hp₀ hp₀1 ?_ hUnit
  · intro l a q q' hqq'
    change MeasurableSet[c.sigma r ((d.ang a, q') :: l)] (d.tests l a q)
    rw [d.tests_eq_preimage_observation l a q]
    exact hObs l a q q' hqq'
      ((hI l a).measurableSet.prod QuantumZipper.isOpen_H.measurableSet)
  · intro l ε hε
    have heq := ae_all_iff.2 fun a =>
      ae_condExpKernel_event_eq_of_map (hle l) (hSample l a)
        (hReachMeas l a) (hLaw l a) (hReachIdent l a)
    filter_upwards [heq, hModelCross l ε hε] with ω hωeq hωcross hωA
    obtain ⟨a, ha⟩ := hωcross hωA
    exact ⟨a, (hωeq a hωA).symm ▸ ha⟩
  · intro k l hl a C hC hCA
    exact le_measure_inter_preimage_of_map (hle l) (hSample l a)
      (hSlowMeas l a) (hLaw l a) (hModelSlow k l hl a) hC hCA

end InteractingSLE.Theorem14.GW2TipSystem.Swc
