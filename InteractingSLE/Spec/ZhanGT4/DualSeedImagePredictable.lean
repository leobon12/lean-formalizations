/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImageRegularity
import InteractingSLE.Spec.Sec2.GirsanovCut
import BrownianMotion.StochasticIntegral.Predictable

/-!
# The predictable seeded noise coordinate

Packet PROVE-ZHAN-GT4-A22. Kill the noise after its stopping horizon and
choose value zero at the entrance. Positive-time continuity makes this
process left-continuous; no entrance limit or natural-filtration assumption
is needed for predictability.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A process restricted to positive times up to a pathwise horizon. -/
def positiveStopped (X : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if 0 < t ∧ t ≤ S ω then X t ω else 0

/-- Killing at the right endpoint preserves left continuity, including
when the original process has no chosen continuous entrance value. -/
theorem continuousWithinAt_positiveStopped {X : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
    (hc : ∀ ω, ContinuousOn (X · ω) (Ioc 0 (S ω))) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (positiveStopped X S · ω) (Iio t) t := by
  by_cases ht : 0 < t
  · by_cases htS : t ≤ S ω
    · have hJ : Ioc 0 (S ω) ∈ 𝓝[Iio t] t := by
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht), self_mem_nhdsWithin] with u hu hut
        exact ⟨hu, hut.le.trans htS⟩
      have hct := ((hc ω) t ⟨ht, htS⟩).mono_of_mem_nhdsWithin hJ
      apply hct.congr_of_eventuallyEq
      · filter_upwards [hJ] with u hu
        simp [positiveStopped, hu.1, hu.2]
      · simp [positiveStopped, ht, htS]
    · have hgt : S ω < t := lt_of_not_ge htS
      apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hgt)] with u hu
        simp [positiveStopped, not_le_of_gt (show S ω < u from hu)]
      · simp [positiveStopped, htS]
  · have he : t = 0 := le_antisymm (le_of_not_gt ht) (zero_le (a := t))
    subst t
    rw [show Iio (0 : ℝ≥0) = ∅ by ext u; simp]
    exact continuousWithinAt_of_notMem_closure (by simp)

/-- Alive-event measurability and positive-time continuity produce an
actual predictable process in the given filtration. -/
theorem isStronglyPredictable_positiveStopped (𝓕 : Filtration ℝ≥0 mΩ)
    {X : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
    (hm : ∀ t, Measurable[𝓕 t] ({ω | t ≤ S ω}.indicator (X t)))
    (hc : ∀ ω, ContinuousOn (X · ω) (Ioc 0 (S ω))) :
    IsStronglyPredictable 𝓕 (positiveStopped X S) := by
  apply StronglyAdapted.isStronglyPredictable_of_leftContinuous
  · intro t
    by_cases ht : 0 < t
    · convert (hm t).stronglyMeasurable using 1
      funext ω
      by_cases hs : t ≤ S ω <;> simp [positiveStopped, ht, hs]
    · have he : positiveStopped X S t = fun _ => 0 := by
        funext ω
        simp [positiveStopped, ht]
      rw [he]
      exact stronglyMeasurable_const
  · exact continuousWithinAt_positiveStopped hc

/-- The stopped process has precisely the time regularity required by the
project's general-filtration Girsanov theorem. -/
theorem isRiemannRegular_positiveStopped (P : Measure Ω)
    {X : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
    (hc : ∀ ω, ContinuousOn (X · ω) (Ioc 0 (S ω))) :
    Girsanov.IsRiemannRegular P (positiveStopped X S) :=
  ae_of_all _ fun ω => ae_of_all _ fun u =>
    continuousWithinAt_Iio_iff_Iic.1 (continuousWithinAt_positiveStopped hc ω u.toNNReal)

/-- The actual negative logarithmic noise used in the seeded change of measure. -/
def seedNoise {n : ℕ} (κ : ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  positiveStopped (fun t ω => -Real.sqrt κ * (d ω).ellX t ((d ω).W t)) S

/-- This construction satisfies the earlier noise-coordinate predicate exactly. -/
theorem seedNoise_coordinate {n : ℕ} (κ : ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0) :
    SeedNoiseCoordinate κ d S (seedNoise κ d S) := by
  constructor
  · intro ω u hu huS
    simp [seedNoise, positiveStopped, hu, huS]
  · intro ω u hu
    simp [seedNoise, positiveStopped, not_le_of_gt hu]

/-- A uniform positive-time bound is preserved by the predictable construction. -/
theorem abs_seedNoise_le {n : ℕ} {κ K : ℝ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hK : 0 ≤ K) (hb : ∀ ω t, t ∈ Ioc (0 : ℝ≥0) (S ω) →
      |(d ω).ellX t ((d ω).W t)| ≤ K) (t : ℝ≥0) (ω : Ω) :
    |seedNoise κ d S t ω| ≤ Real.sqrt κ * K := by
  unfold seedNoise positiveStopped
  split_ifs with ht
  · rw [abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hb ω t ht) (Real.sqrt_nonneg _)
  · rw [abs_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) hK

/-- The seeded noise is predictable and Riemann regular in the original
filtration once its actual alive values are measurable. -/
theorem seedNoise_predictable_regular {n : ℕ} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    {κ : ℝ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hm : ∀ t, Measurable[𝓕 t]
      ({ω | t ≤ S ω}.indicator fun ω => (d ω).ellX t ((d ω).W t)))
    (hc : ∀ ω, ContinuousOn (fun t : ℝ≥0 => (d ω).ellX t ((d ω).W t)) (Ioc 0 (S ω))) :
    IsStronglyPredictable 𝓕 (seedNoise κ d S) ∧ Girsanov.IsRiemannRegular P (seedNoise κ d S) := by
  have hm' : ∀ t, Measurable[𝓕 t] ({ω | t ≤ S ω}.indicator
      fun ω => -Real.sqrt κ * (d ω).ellX t ((d ω).W t)) := by
    intro t
    convert (hm t).const_mul (-Real.sqrt κ) using 1
    funext ω
    by_cases hs : t ≤ S ω <;> simp [hs]
  have hc' : ∀ ω, ContinuousOn
      (fun t : ℝ≥0 => -Real.sqrt κ * (d ω).ellX t ((d ω).W t)) (Ioc 0 (S ω)) :=
    fun ω => continuousOn_const.mul (hc ω)
  exact ⟨isStronglyPredictable_positiveStopped 𝓕 hm' hc', isRiemannRegular_positiveStopped P hc'⟩

end InteractingSLE.ZhanGT4
