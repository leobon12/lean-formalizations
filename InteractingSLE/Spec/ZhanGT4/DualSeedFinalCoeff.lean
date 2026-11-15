/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalClock
import InteractingSLE.Spec.ZhanGT4.DualSeedImagePredictable
import InteractingSLE.Spec.ZhanGT4.DualD10Frozen

/-!
# The protected mapped-noise coefficient

Packet PROVE-ZHAN-GT4-A22. Continue the actual own-map derivative by one
after the stopping horizon. The construction is predictable, bounded,
nondegenerate, and its quadratic clock is exactly the capacity clock
before the horizon. Its chosen value at time zero has no effect on that
integral.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The mapped-noise coefficient with an independent Brownian continuation
in the original time variable after the own-time horizon. -/
def seedCapacityCoeff {n : ℕ} (d : Ω → SeedData n) (S : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  1 + positiveStopped (fun t ω => (d ω).A 1 t - 1) S u ω

/-- Before the horizon at positive times it is the actual mapped coefficient. -/
theorem seedCapacityCoeff_eq {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    {u : ℝ≥0} {ω : Ω} (hu : 0 < u) (hS : u ≤ S ω) :
    seedCapacityCoeff d S u ω = (d ω).A 1 u := by
  simp only [seedCapacityCoeff, positiveStopped, hu, hS, and_self, ite_true]
  ring

/-- Protected derivative bounds give the global bound for the continued coefficient. -/
theorem abs_seedCapacityCoeff_le {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {C : ℝ}
    (hb : ∀ ω u, 0 < u → u ≤ S ω → |(d ω).A 1 u| ≤ C) (u : ℝ≥0) (ω : Ω) :
    |seedCapacityCoeff d S u ω| ≤ max C 1 := by
  by_cases hh : 0 < u ∧ u ≤ S ω
  · rw [seedCapacityCoeff_eq hh.1 hh.2]
    exact (hb ω u hh.1 hh.2).trans (le_max_left _ _)
  · simp only [seedCapacityCoeff, positiveStopped, ite_eq_right hh, add_zero, abs_one]
    exact le_max_right _ _

/-- Protected derivative clearance also gives uniform nondegeneracy. -/
theorem seedCapacityCoeff_sq_ge {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {a₀ : ℝ}
    (ha : 0 < a₀) (hb : ∀ ω u, 0 < u → u ≤ S ω → a₀ ≤ (d ω).A 1 u)
    (u : ℝ≥0) (ω : Ω) : min (a₀ ^ 2) 1 ≤ seedCapacityCoeff d S u ω ^ 2 := by
  by_cases hh : 0 < u ∧ u ≤ S ω
  · rw [seedCapacityCoeff_eq hh.1 hh.2]
    exact (min_le_left _ _).trans (pow_le_pow_left₀ ha.le (hb ω u hh.1 hh.2) 2)
  · simp only [seedCapacityCoeff, positiveStopped, ite_eq_right hh, add_zero, one_pow]
    exact min_le_right _ _

/-- Alive-coordinate measurability and positive-time continuity construct
an actual predictable coefficient, including its post-horizon continuation. -/
theorem seedCapacityCoeff_predictable {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (𝓕 : Filtration ℝ≥0 mΩ)
    (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).A 1 u - 1))
    (hc : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (S ω))) :
    IsStronglyPredictable 𝓕 (seedCapacityCoeff d S) := by
  have hcont : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u - 1) (Ioc 0 (S ω)) :=
    fun ω => (hc ω).sub continuousOn_const
  have hp := isStronglyPredictable_positiveStopped 𝓕 hm hcont
  apply StronglyAdapted.isStronglyPredictable_of_leftContinuous
  · intro u
    exact stronglyMeasurable_const.add (hp.stronglyAdapted u)
  · intro ω u
    exact continuousWithinAt_const.add (continuousWithinAt_positiveStopped hcont ω u)

/-- The coefficient has exactly the left continuity required by the
project's Riemann integral construction. -/
theorem seedCapacityCoeff_riemannRegular {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (Q : Measure Ω)
    (hc : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (S ω))) :
    Girsanov.IsRiemannRegular Q (seedCapacityCoeff d S) := by
  have hh := isRiemannRegular_positiveStopped Q
    (X := fun u ω => (d ω).A 1 u - 1) (fun ω => (hc ω).sub continuousOn_const)
  exact hh.mono fun ω hω => hω.mono fun _ hu => continuousWithinAt_const.add hu

/-- No separate capacity-clock identity is required before the stopping
horizon: the own-map Loewner equation supplies it. -/
theorem seedCapacityCoeff_clock_eq {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    {A : Ω → Set ℂ}
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (ω : Ω) {t : ℝ≥0} (ht : t ≤ S ω) :
    seedQuadClock (seedCapacityCoeff d S) ω t = (d ω).a t := by
  rw [← (hown ω).integral_frzA_one_sq ⟨t.coe_nonneg, show (t : ℝ) ≤ S ω from ht⟩]
  apply intervalIntegral.integral_congr_Ioo_of_le t.coe_nonneg
  intro u hu
  have hu0 : 0 < u.toNNReal := Real.toNNReal_pos.2 hu.1
  have huS : u.toNNReal ≤ S ω := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]
    exact hu.2.le.trans ht
  dsimp only
  rw [seedCapacityCoeff_eq hu0 huS]
  change (d ω).A 1 u.toNNReal ^ 2 = (d ω).A 1 u ^ 2
  rw [Real.coe_toNNReal _ hu.1.le]

end InteractingSLE.ZhanGT4
