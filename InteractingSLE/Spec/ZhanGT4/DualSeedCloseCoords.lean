/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseNoise

/-!
# Actual image coordinates from the inverse capacity clock

Packet PROVE-ZHAN-GT4-A22. Define the centered image driver and every
image force using the inverse of the actual quadratic clock. Extend them
constantly after the image horizon. Their coordinate identities are proved,
including at zero; they are not additional image-noise hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*}

/-- Inverting a strictly increasing full clock recovers the original time. -/
theorem seed_invClockT_clock_eq {C : Ω → ℝ≥0 → ℝ} {c : ℝ}
    (hCc : ∀ ω, Continuous (C ω)) (hCs : ∀ ω, StrictMono (C ω))
    (hC0 : ∀ ω, C ω 0 = 0) (hc : 0 < c) (hlb : ∀ ω r, c * r ≤ C ω r)
    (ω : Ω) (r : ℝ≥0) : invClockT C (C ω r).toNNReal ω = r := by
  have h0 : 0 ≤ C ω r := by rw [← hC0 ω]; exact (hCs ω).monotone (zero_le (a := r))
  apply (hCs ω).injective
  simpa only [Real.coe_toNNReal _ h0] using
    (invClock_eq_coe hCc hC0 hc hlb (C ω r).toNNReal ω).2.1

/-- Own time corresponding to capacity time, clamped at the own horizon. -/
def seedCapacityTime {n : ℕ} (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (u : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  min (invClockT (seedQuadClock (seedCapacityCoeff d S)) u ω) (S ω)

/-- The actual centered capacity driver, continued constantly after its horizon. -/
def seedCapacityDriver {n : ℕ} (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (u : ℝ≥0) (ω : Ω) : ℝ :=
  (d ω).A 0 (seedCapacityTime d S u ω) - (d ω).A 0 0

/-- Every actual image force, including the other tip, in capacity time. -/
def seedCapacityForce {n : ℕ} (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (i : Fin (n + 1)) (u : ℝ≥0) (ω : Ω) : ℝ :=
  (d ω).imageForce (seedCapacityTime d S u ω) i - (d ω).A 0 0

/-- The actual stopped capacity horizon. -/
def seedCapacityHorizon {n : ℕ} (d : Ω → SeedData n) (S : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  ((d ω).a (S ω)).toNNReal

variable {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ}
  {c : ℝ}
  (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
  (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
  (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω))
  (hc : 0 < c) (hlb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r)

include hown hCc hCs hc hlb

/-- The inverse-clock definition gives the required coordinate relation
on the full closed own-time interval. -/
theorem seedCapacityTime_at_capacity (ω : Ω) {r : ℝ≥0} (hr : r ≤ S ω) :
    seedCapacityTime d S ((d ω).a r).toNNReal ω = r := by
  rw [← seedCapacityCoeff_clock_eq hown ω hr]
  unfold seedCapacityTime
  rw [seed_invClockT_clock_eq hCc hCs (seedQuadClock_zero _) hc hlb, min_eq_left hr]

/-- The driver relation used by the D10 substitution is automatic. -/
theorem seedCapacityDriver_at_capacity (ω : Ω) {r : ℝ≥0} (hr : r ≤ S ω) :
    seedCapacityDriver d S ((d ω).a r).toNNReal ω = (d ω).A 0 r - (d ω).A 0 0 := by
  rw [seedCapacityDriver, seedCapacityTime_at_capacity hown hCc hCs hc hlb ω hr]

/-- The force relations used by capacity substitution are automatic. -/
theorem seedCapacityForce_at_capacity (ω : Ω) (i : Fin (n + 1)) {r : ℝ≥0} (hr : r ≤ S ω) :
    seedCapacityForce d S i ((d ω).a r).toNNReal ω = (d ω).imageForce r i - (d ω).A 0 0 := by
  rw [seedCapacityForce, seedCapacityTime_at_capacity hown hCc hCs hc hlb ω hr]

/-- Every capacity time before the image horizon comes from an own time
before the own horizon; no interval in capacity time is omitted. -/
theorem seedCapacityTime_spec (ω : Ω) {u : ℝ≥0} (hu : u ≤ seedCapacityHorizon d S ω) :
    seedCapacityTime d S u ω ≤ S ω ∧
      (d ω).a (seedCapacityTime d S u ω) = u := by
  let C := seedQuadClock (seedCapacityCoeff d S)
  have hval := (invClock_eq_coe hCc (seedQuadClock_zero _) hc hlb u ω).2.1
  have hCS : C ω (S ω) = (d ω).a (S ω) := seedCapacityCoeff_clock_eq hown ω le_rfl
  have hCS0 : 0 ≤ C ω (S ω) := by
    rw [← seedQuadClock_zero (seedCapacityCoeff d S) ω]
    exact (hCs ω).monotone zero_le
  have hu' : (u : ℝ) ≤ C ω (S ω) := by
    have hh : (u : ℝ) ≤ (seedCapacityHorizon d S ω : ℝ) := hu
    simpa only [seedCapacityHorizon, ← hCS, Real.coe_toNNReal _ hCS0] using hh
  have hτ : invClockT C u ω ≤ S ω := (hCs ω).le_iff_le.1 (hval.trans_le hu')
  have ht : seedCapacityTime d S u ω = invClockT C u ω := min_eq_left hτ
  refine ⟨by rw [ht]; exact hτ, ?_⟩
  rw [ht, ← seedCapacityCoeff_clock_eq hown ω hτ]
  exact hval

/-- The actual capacity driver starts at zero. -/
theorem seedCapacityDriver_zero (ω : Ω) : seedCapacityDriver d S 0 ω = 0 := by
  have hh := seedCapacityDriver_at_capacity hown hCc hCs hc hlb ω (zero_le (a := S ω))
  simpa only [NNReal.coe_zero, (hown ω).a0, Real.toNNReal_zero, sub_self] using hh

/-- The initial capacity force positions are the actual centered image marks. -/
theorem seedCapacityForce_zero (ω : Ω) (i : Fin (n + 1)) :
    seedCapacityForce d S i 0 ω = (d ω).imageForce 0 i - (d ω).A 0 0 := by
  have hh := seedCapacityForce_at_capacity hown hCc hCs hc hlb ω i (zero_le (a := S ω))
  simpa only [NNReal.coe_zero, (hown ω).a0, Real.toNNReal_zero] using hh

omit hCc hCs hc hlb in
/-- A positive own horizon has positive image capacity. -/
theorem seedCapacityHorizon_pos (ω : Ω) : 0 < seedCapacityHorizon d S ω := by
  apply Real.toNNReal_pos.2
  rw [← (hown ω).a0]
  exact (hown ω).mono ⟨le_rfl, (hown ω).pos.le⟩ ⟨(S ω).coe_nonneg, le_rfl⟩ (hown ω).pos

omit hown in
/-- The clamped inverse time is continuous on every path. -/
theorem continuous_seedCapacityTime (ω : Ω) : Continuous (seedCapacityTime d S · ω) :=
  (continuous_invClockT hCc hCs (seedQuadClock_zero _) hc hlb ω).min continuous_const

/-- The actual driver is continuous, including at its horizon and entrance. -/
theorem continuous_seedCapacityDriver (ω : Ω) : Continuous (seedCapacityDriver d S · ω) := by
  refine Continuous.sub ?_ continuous_const
  apply (hown ω).continuousOn_frzA 0 |>.comp_continuous
    (continuous_subtype_val.comp (continuous_seedCapacityTime hCc hCs hc hlb ω))
  intro u
  exact ⟨(seedCapacityTime d S u ω).coe_nonneg, min_le_right _ _⟩

omit hown in
/-- Continuous own-time image forces give continuous capacity forces. -/
theorem continuous_seedCapacityForce
    (hV : ∀ ω i, ContinuousOn (fun t => (d ω).imageForce t i) (Icc 0 (S ω)))
    (ω : Ω) (i : Fin (n + 1)) : Continuous (seedCapacityForce d S i · ω) := by
  refine Continuous.sub ?_ continuous_const
  apply (hV ω i).comp_continuous
    (continuous_subtype_val.comp (continuous_seedCapacityTime hCc hCs hc hlb ω))
  intro u
  exact ⟨(seedCapacityTime d S u ω).coe_nonneg, min_le_right _ _⟩

end InteractingSLE.ZhanGT4
