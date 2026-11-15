/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR12History
import InteractingSLE.Spec.Supplement.GW2RootI30Inverse

/-!
# Dense physical caps exhaust the actual normalized initial capacity

The low-arc clock now comes from the source at every COVER root. The
original dense set Q supplies positive caps below the recorded horizon
whose actual normalized capacities exceed any earlier capacity query.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR12

open GW2TipSystem GW2TipSystem.RootC24 GW2Schedule GW2Tip Exist Staged StagedLaw

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The actual initial clock in the root test's normalized capacity units. -/
def normalizedRootClock (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (ω : Ω) (t : ℝ≥0) : ℝ≥0 :=
  4 ^ r.2 * (RootH29.forwardCapacity (rootPt r.1) c.s t (RootCv.rootRecs c r.1 ω)).toNNReal

omit [StandardBorelSpace Ω] in
/-- Nonnegative totalization does not change this actual capacity reader. -/
theorem coe_normalizedRootClock (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (ω : Ω) (t : ℝ≥0) :
    (normalizedRootClock c r ω t : ℝ) =
      4 ^ r.2 * RootH29.forwardCapacity (rootPt r.1) c.s t (RootCv.rootRecs c r.1 ω) := by
  simp only [normalizedRootClock, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat,
    Real.coe_toNNReal _ (RootH29.forwardCapacity_nonneg _ _ _ _)]

omit [StandardBorelSpace Ω] in
/-- The normalized clock is known at every retained history, even at a
random history-measurable physical time. -/
theorem measurable_normalizedRootClock_random (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    {t : Ω → ℝ≥0} (ht : Measurable[c.sigma r l] t) :
    Measurable[c.sigma r l] fun ω => normalizedRootClock c r ω (t ω) :=
  measurable_const.mul
    ((@RootH29.measurable_forwardCapacity_random Ω (c.sigma r l) (rootPt r.1) c.s
      _ (measurable_rootRecs_history c r l) _ ht).real_toNNReal)

/-- COVER supplies the normalized strict continuous clock and the exact
literal initial capacity endpoint, at every admissible low-arc root. -/
theorem ae_cover_normalizedRootClock (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      let v := (rootEntry r.1).2
      normalizedRootClock c r ω 0 = 0 ∧
      StrictMonoOn (normalizedRootClock c r ω) (Icc 0 v) ∧
      ContinuousOn (normalizedRootClock c r ω) (Icc 0 v) ∧
      (normalizedRootClock c r ω v : ℝ) =
        capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω := by
  filter_upwards [RootI30.ae_cover_clock h13 c r] with ω hc hω
  obtain ⟨h0, hm, hcont, _, hcap, _⟩ := hc hω
  dsimp only at h0 hm hcont hcap ⊢
  have hm' : StrictMonoOn (fun t =>
      (RootH29.forwardCapacity (rootPt r.1) c.s t (RootCv.rootRecs c r.1 ω)).toNNReal)
      (Icc 0 (rootEntry r.1).2) := by
    intro t ht u hu htu
    apply NNReal.coe_lt_coe.mp
    rw [Real.coe_toNNReal _ (RootH29.forwardCapacity_nonneg _ _ _ _),
      Real.coe_toNNReal _ (RootH29.forwardCapacity_nonneg _ _ _ _)]
    exact hm ht hu htu
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [normalizedRootClock, h0, Real.toNNReal_zero, mul_zero]
  · intro t ht u hu htu
    exact mul_lt_mul_of_pos_left (hm' ht hu htu) (by positivity)
  · exact continuousOn_const.mul (continuous_real_toNNReal.comp_continuousOn hcont)
  · exact (coe_normalizedRootClock c r ω _).trans hcap.symm

/-- Original-Q caps strictly inside the protected root prefix have
positive normalized capacity strictly below the literal initial endpoint. -/
theorem ae_cover_capacityBuffer_bounds (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      ∀ b : c.Q, (b : ℝ≥0) < (rootEntry r.1).2 →
        0 < normalizedRootClock c r ω b ∧
          (normalizedRootClock c r ω b : ℝ) <
            capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω := by
  filter_upwards [ae_cover_normalizedRootClock h13 c r] with ω hc hω
  obtain ⟨h0, hm, _, hcap⟩ := hc hω
  intro b hb
  have hpos := hm ⟨zero_le, zero_le⟩ ⟨zero_le, hb.le⟩ (c.hQpos b b.property)
  rw [h0] at hpos
  refine ⟨hpos, ?_⟩
  rw [← hcap]
  exact NNReal.coe_lt_coe.mpr (hm ⟨zero_le, hb.le⟩ ⟨zero_le, le_rfl⟩ hb)

/-- Every capacity query strictly below the initial literal capacity lies
below a positive original-Q cap before the physical root horizon. -/
theorem ae_cover_exists_capacityBuffer (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r → ∀ u : ℝ≥0,
      (u : ℝ) < capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω →
      ∃ b : c.Q, 0 < (b : ℝ≥0) ∧ (b : ℝ≥0) < (rootEntry r.1).2 ∧
        u < normalizedRootClock c r ω b := by
  filter_upwards [ae_cover_normalizedRootClock h13 c r] with ω hc hω
  obtain ⟨h0, hm, hcont, hcap⟩ := hc hω
  intro u hu
  have huv : u < normalizedRootClock c r ω (rootEntry r.1).2 := by
    apply NNReal.coe_lt_coe.mp
    rwa [hcap]
  obtain ⟨y, huy, hyv⟩ := exists_between huv
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc
    (zero_le : (0 : ℝ≥0) ≤ (rootEntry r.1).2) hcont
    (show y ∈ Icc (normalizedRootClock c r ω 0)
      (normalizedRootClock c r ω (rootEntry r.1).2) from
        ⟨by rw [h0]; exact zero_le, hyv.le⟩)
  have htv : t < (rootEntry r.1).2 := lt_of_le_of_ne ht.2 (by
    intro he
    rw [he] at heq
    exact hyv.ne heq.symm)
  obtain ⟨b, hb, hbQ⟩ := c.hQd.inter_open_nonempty
    (Ioo t (rootEntry r.1).2) isOpen_Ioo (nonempty_Ioo.mpr htv)
  refine ⟨⟨b, hbQ⟩, (zero_le.trans_lt hb.1), hb.2, ?_⟩
  exact huy.trans (heq ▸ hm ht ⟨zero_le, hb.2.le⟩ hb.1)

end InteractingSLE.Theorem14.GW2JDetR12
