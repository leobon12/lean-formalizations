/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootI30Cover
import InteractingSLE.Spec.Restart.ClockInv

/-!
# Low-arc inverse-clock and capacity-time tip readers

Packet PROVE-T14-GW2ROOT2. Reuse the rational-supremum clock inverse.
Both readers are Borel at a random relative capacity. On the actual
cover they invert the physical clock, recover every attained tip, and
are continuous through the attained endpoints.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootI30

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart RootC24

/-- Physical time read at a relative capacity, capped at the recorded horizon. -/
def clockInverse (x : ℝ) (s v u : ℝ≥0) (p : RecData × RecData) : ℝ≥0 :=
  invClock (fun t => RootH29.forwardCapacity x s t p) (v : ℝ≥0∞) u

/-- The centered low-arc tip in relative capacity time. -/
def capacityTipRead (x : ℝ) (s v u : ℝ≥0) (p : RecData × RecData) : ℂ :=
  RootH29.rootTipRead x s (clockInverse x s v u p) p

theorem measurable_clockInverse_random {Ω : Type*} [MeasurableSpace Ω]
    (x : ℝ) (s v : ℝ≥0) {p : Ω → RecData × RecData} (hp : Measurable p)
    {u : Ω → ℝ≥0} (hu : Measurable u) :
    Measurable fun ω => clockInverse x s v (u ω) (p ω) := by
  classical
  unfold clockInverse invClock
  refine Measurable.iSup fun q : ℚ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    (measurableSet_lt (RootH29.measurable_forwardCapacity_random x s hp measurable_const)
      (NNReal.continuous_coe.measurable.comp hu)))

theorem measurable_capacityTipRead_random {Ω : Type*} [MeasurableSpace Ω]
    (x : ℝ) (s v : ℝ≥0) {p : Ω → RecData × RecData} (hp : Measurable p)
    {u : Ω → ℝ≥0} (hu : Measurable u) :
    Measurable fun ω => capacityTipRead x s v (u ω) (p ω) :=
  RootH29.measurable_rootTipRead_random x s hp (measurable_clockInverse_random x s v hp hu)

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The actual cover supplies the existing clock predicate outright. -/
theorem ae_cover_isClockOn (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      IsClockOn (fun t => RootH29.forwardCapacity (rootPt r.1) c.s t
        (RootCv.rootRecs c r.1 ω)) ((rootEntry r.1).2 : ℝ≥0∞) := by
  filter_upwards [ae_cover_clock h13 c r] with ω hω hcover
  obtain ⟨h0, hm, hc, _⟩ := hω hcover
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ((rootEntry r.1).2 : ℝ≥0∞)} =
      Icc 0 (rootEntry r.1).2 := by
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  exact ⟨h0, hset ▸ hm, hset ▸ hc, fun h => (ENNReal.coe_ne_top h).elim⟩

/-- On COVER's event the Borel inverse attains every retained capacity. -/
theorem ae_cover_inverse_spec (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      let p := RootCv.rootRecs c r.1 ω
      ∀ u : ℝ≥0, (u : ℝ) ≤ RootH29.forwardCapacity (rootPt r.1) c.s (rootEntry r.1).2 p →
        clockInverse (rootPt r.1) c.s (rootEntry r.1).2 u p ≤ (rootEntry r.1).2 ∧
        RootH29.forwardCapacity (rootPt r.1) c.s
          (clockInverse (rootPt r.1) c.s (rootEntry r.1).2 u p) p = u := by
  filter_upwards [ae_cover_isClockOn h13 c r] with ω hω hcover
  intro p u hu
  have ha := hω hcover
  have hu' : (u : ℝ≥0∞) ≤ capLife
      (fun t => RootH29.forwardCapacity (rootPt r.1) c.s t p)
        ((rootEntry r.1).2 : ℝ≥0∞) := by
    rw [capLife, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe,
      ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hu
  have hh := ha.invClock_spec hu'
  exact ⟨ENNReal.coe_le_coe.mp hh.1, hh.2⟩

/-- The relative-capacity tip recovers every attained physical tip and
is continuous through the entire closed attained interval on the cover. -/
theorem ae_cover_capacityTip (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      let p := RootCv.rootRecs c r.1 ω
      let v := (rootEntry r.1).2
      let a := fun t => RootH29.forwardCapacity (rootPt r.1) c.s t p
      ContinuousOn (fun u => capacityTipRead (rootPt r.1) c.s v u p)
        {u : ℝ≥0 | (u : ℝ) ≤ a v} ∧
      capacityTipRead (rootPt r.1) c.s v 0 p = 0 ∧
      ∀ t ≤ v, capacityTipRead (rootPt r.1) c.s v (a t).toNNReal p =
        RootH29.rootTipRead (rootPt r.1) c.s t p := by
  filter_upwards [ae_cover_isClockOn h13 c r, RootH29.ae_cover_rootTip_regular h13 c r]
    with ω hclock htip hcover
  intro p v a
  have ha := hclock hcover
  obtain ⟨hc, h0, _⟩ := htip hcover
  have hsub : {u : ℝ≥0 | (u : ℝ) ≤ a v} ⊆ {u | (u : ℝ≥0∞) ≤ capLife a (v : ℝ≥0∞)} := by
    intro u hu
    change (u : ℝ≥0∞) ≤ capLife a (v : ℝ≥0∞)
    rw [capLife, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe,
      ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hu
  have hcontinuous := hc.comp (ha.continuousOn_invClock.mono hsub) (fun u hu =>
    ⟨zero_le, ENNReal.coe_le_coe.mp (ha.invClock_spec (hsub hu)).1⟩)
  refine ⟨hcontinuous, ?_, ?_⟩
  · have hz := ha.invClock_apply (r := 0) (bot_le : (0 : ℝ≥0∞) ≤ (v : ℝ≥0∞))
    rw [ha.zero, Real.toNNReal_zero] at hz
    change RootH29.rootTipRead (rootPt r.1) c.s (invClock a (v : ℝ≥0∞) 0) p = 0
    rw [hz]
    exact h0
  · intro t ht
    change RootH29.rootTipRead (rootPt r.1) c.s
      (invClock a (v : ℝ≥0∞) (a t).toNNReal) p = _
    rw [ha.invClock_apply (ENNReal.coe_le_coe.mpr ht)]

omit [StandardBorelSpace Ω] in
/-- Random relative-capacity tips are observable in the literal root stage. -/
theorem measurable_initial_capacityTip_random (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) {u : Ω → ℝ≥0} (hu : Measurable[c.sigma r []] u) :
    Measurable[c.sigma r []] fun ω => capacityTipRead (rootPt r.1) c.s (rootEntry r.1).2
      (u ω) (RootCv.rootRecs c r.1 ω) :=
  @measurable_capacityTipRead_random Ω (c.sigma r []) (rootPt r.1) c.s (rootEntry r.1).2
    _ (RootCv.measurable_rootRecs c r) u hu

end InteractingSLE.Theorem14.GW2TipSystem.RootI30
