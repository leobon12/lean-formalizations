/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalWald

/-!
# Nondegenerate capacity clocks

Packet PROVE-ZHAN-GT4-A22. The protected derivative bounds give a bounded
nondegenerate clock coefficient, continued by one after the own-time
horizon. Its quadratic integral has all the inverse-clock properties
needed for the landed Lévy time-change theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {w : ℝ≥0 → Ω → ℝ}

/-- The own-time quadratic clock of the mapped noise. -/
def seedQuadClock (w : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) : ℝ := quadInt w t ω

/-- A bounded progressive coefficient has a progressive bounded square. -/
theorem seed_square_progressive (hw : IsStronglyProgressive 𝓕 w) :
    IsStronglyProgressive 𝓕 (fun u ω => w u ω ^ 2) := fun u => (hw u).pow 2

/-- The square bound used for pathwise clock integrability. -/
theorem seed_square_bound {C : ℝ} (hb : ∀ u ω, |w u ω| ≤ C) (u : ℝ≥0) (ω : Ω) :
    |w u ω ^ 2| ≤ C ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb u ω) 2

/-- The quadratic clock is continuous on every path. -/
theorem continuous_seedQuadClock (hw : IsStronglyProgressive 𝓕 w)
    {C : ℝ} (hb : ∀ u ω, |w u ω| ≤ C) (ω : Ω) : Continuous (seedQuadClock w ω) :=
  continuous_drift (seed_square_progressive hw) (seed_square_bound hb) ω

/-- The quadratic clock is adapted in the original filtration. -/
theorem measurable_seedQuadClock (hw : IsStronglyProgressive 𝓕 w) (u : ℝ≥0) :
    Measurable[𝓕 u] (fun ω => seedQuadClock w ω u) :=
  (stronglyMeasurable_integral_comp hw (measurable_id.pow_const 2) u).measurable

/-- A pointwise lower bound for the squared coefficient gives a quantitative
lower bound for every clock increment. -/
theorem seedQuadClock_sub_ge (hw : IsStronglyProgressive 𝓕 w)
    {C c : ℝ} (hb : ∀ u ω, |w u ω| ≤ C) (hlb : ∀ u ω, c ≤ w u ω ^ 2)
    (ω : Ω) {a b : ℝ≥0} (hab : a ≤ b) :
    c * ((b : ℝ) - a) ≤ seedQuadClock w ω b - seedQuadClock w ω a := by
  have hi := intervalIntegrable_time (seed_square_progressive hw) (seed_square_bound hb) ω
  have he : seedQuadClock w ω b - seedQuadClock w ω a =
      ∫ u in (a : ℝ)..b, w u.toNNReal ω ^ 2 := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a b)
    dsimp only [seedQuadClock, quadInt]
    linarith only [hh]
  rw [he]
  have hh := intervalIntegral.integral_mono_on (show (a : ℝ) ≤ b from hab)
    (intervalIntegrable_const (c := c)) (hi a b) (fun u _ => hlb u.toNNReal ω)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh

/-- Nondegeneracy makes the quadratic clock strictly increasing. -/
theorem strictMono_seedQuadClock (hw : IsStronglyProgressive 𝓕 w)
    {C c : ℝ} (hb : ∀ u ω, |w u ω| ≤ C) (hc : 0 < c)
    (hlb : ∀ u ω, c ≤ w u ω ^ 2) (ω : Ω) : StrictMono (seedQuadClock w ω) := by
  intro a b hab
  have hh := seedQuadClock_sub_ge hw hb hlb ω hab.le
  have hp : 0 < c * ((b : ℝ) - a) := mul_pos hc (sub_pos.2 hab)
  linarith

/-- The clock starts at zero. -/
theorem seedQuadClock_zero (w : ℝ≥0 → Ω → ℝ) (ω : Ω) : seedQuadClock w ω 0 = 0 := by
  simp only [seedQuadClock, quadInt, NNReal.coe_zero, intervalIntegral.integral_same]

/-- The inverse-clock stopping times are deterministically bounded. -/
theorem seedQuadClock_ge (hw : IsStronglyProgressive 𝓕 w)
    {C c : ℝ} (hb : ∀ u ω, |w u ω| ≤ C) (hlb : ∀ u ω, c ≤ w u ω ^ 2)
    (ω : Ω) (t : ℝ≥0) : c * t ≤ seedQuadClock w ω t := by
  simpa only [seedQuadClock_zero, NNReal.coe_zero, sub_zero] using
    seedQuadClock_sub_ge hw hb hlb ω (zero_le (a := t))

end InteractingSLE.ZhanGT4
