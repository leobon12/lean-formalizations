/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalAdapted

/-!
# D10 entrance limit for the actual mapped driver

Packet PROVE-ZHAN-GT4-A22. Adjacent interval integrals identify the
compensated positive-time increment exactly; the bounded stochastic
integral entrance limit removes the restart, then the Brownian
continuation gives the stable own-time D10 statement.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open Girsanov
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The compensated actual coordinates give the exact increment, also
when the horizon precedes the restart time. -/
theorem seedStoppedMappedNoise_sub {n : ℕ} (κ : ℝ) (d : Ω → SeedData n)
    (T : Ω → ℝ≥0) (hi : ∀ ω, IntervalIntegrable (d ω).d10Rate volume 0 (T ω))
    {ε t : ℝ≥0} (hεt : ε ≤ t) (ω : Ω) :
    seedStoppedMappedNoise κ d T t ω - seedStoppedMappedNoise κ d T ε ω =
      ((d ω).A 0 (min t (T ω)) - (d ω).A 0 (min ε (T ω)) -
        (∫ u in (min ε (T ω) : ℝ≥0)..(min t (T ω) : ℝ≥0), (d ω).d10Rate u)) / Real.sqrt κ := by
  have hle : (min ε (T ω) : ℝ≥0) ≤ min t (T ω) := min_le_min_right _ hεt
  have hsub (u v : ℝ≥0) (huv : u ≤ v) (hv : v ≤ T ω) :
      uIcc (u : ℝ) (v : ℝ) ⊆ uIcc (0 : ℝ) (T ω) := by
    rw [uIcc_of_le (NNReal.coe_le_coe.2 huv), uIcc_of_le (T ω).coe_nonneg]
    exact Icc_subset_Icc u.coe_nonneg (NNReal.coe_le_coe.2 hv)
  have hi0 := (hi ω).mono_set (hsub 0 _ bot_le (min_le_right ε (T ω)))
  have hi1 := (hi ω).mono_set (hsub _ _ hle (min_le_right t (T ω)))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  simp only [NNReal.coe_zero] at hadd
  unfold seedStoppedMappedNoise
  rw [← hadd]
  ring

/-- Positive-time actual map calculus, entrance integrability and the
uniform first-derivative bound yield the stable global stochastic D10.
The positive-time premise is discharged by gap-band exhaustion, rather
than an assumed identity for the final compensated mapped noise. -/
theorem seedOwnD10Integral_of_positive_map_calculus
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ} {d : Ω → SeedData n} {κ : ℝ}
    (hκ : 0 < κ) {B : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0} {A : Ω → Set ℂ}
    (hB : IsFilteredPreBrownian B 𝓕 P) (hBc : ∀ ω, Continuous (B · ω))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (T ω) (d ω).a (d ω).W')
    (hi : ∀ ω, IntervalIntegrable (d ω).d10Rate volume 0 (T ω))
    (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (d ω).A 1 u))
    (hc : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (T ω)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u ω, 0 < u → u ≤ T ω → |(d ω).A 1 u| ≤ C)
    (hpos : ∀ ε t : ℝ≥0, 0 < ε → ε ≤ t →
      (fun ω => (d ω).A 0 (min t (T ω)) - (d ω).A 0 (min ε (T ω)) -
        (∫ u in (min ε (T ω) : ℝ≥0)..(min t (T ω) : ℝ≥0), (d ω).d10Rate u)) =ᵐ[P]
      fun ω => stochIntegral P 𝓕 B (positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T) t ω -
        stochIntegral P 𝓕 B (positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T) ε ω) :
    SeedOwnD10Integral P 𝓕 B κ d T := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let w := positiveStopped (fun u ω => (d ω).A 1 u) T
  have hp := isStronglyPredictable_positiveStopped 𝓕 hm hc
  have hr : IsRiemannRegular P w := isRiemannRegular_positiveStopped P hc
  have hbw : ∀ u ω, |w u ω| ≤ C := by
    intro u ω
    unfold w positiveStopped
    split_ifs with hu
    · exact hb u ω hu.1 hu.2
    · simpa only [abs_zero] using hC
  have hmul : (fun u ω => Real.sqrt κ * w u ω) =
      positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T := by
    funext u ω
    unfold w positiveStopped
    split_ifs <;> simp only [mul_zero]
  have hε (ε t : ℝ≥0) (he : 0 < ε) (het : ε ≤ t) :
      (fun ω => seedStoppedMappedNoise κ d T t ω - seedStoppedMappedNoise κ d T ε ω) =ᵐ[P]
      fun ω => stochIntegral P 𝓕 B w t ω - stochIntegral P 𝓕 B w ε ω := by
    have hit := seed_stochIntegral_const_mul hB hp.stronglyAdapted hbw hr (Real.sqrt κ) t
    have hie := seed_stochIntegral_const_mul hB hp.stronglyAdapted hbw hr (Real.sqrt κ) ε
    rw [hmul] at hit hie
    filter_upwards [hpos ε t he het, hit, hie] with ω hω ht' he'
    rw [seedStoppedMappedNoise_sub κ d T hi het ω, hω, ht', he']
    field_simp [ne_of_gt (Real.sqrt_pos.2 hκ)]
    rfl
  have hX := fun ω => (continuous_seedStoppedMappedNoise (κ := κ) hown hi ω).continuousAt (x := 0)
  have hI (t : ℝ≥0) := seed_integral_from_positive_times hB hp.stronglyAdapted hbw hr hX hε t
  apply seedOwnD10Integral_of_stopped_map_integral hB hBc hT hm hc hC hb
  intro t
  simpa only [seedStoppedMappedNoise_zero, sub_zero] using hI t

end InteractingSLE.ZhanGT4
