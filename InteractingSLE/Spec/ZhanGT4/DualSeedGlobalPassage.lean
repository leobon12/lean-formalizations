/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalFields

/-!
# The entrance limit and the spliced own-time D10 identity

Packet PROVE-ZHAN-GT4-A22. Bounded integral coefficients give the entrance
limit in probability. Continuity of the actual compensated mapped driver
identifies that limit, and the checked stopping-indicator integral then
supplies the Brownian continuation after the horizon.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B w X : ℝ≥0 → Ω → ℝ}

/-- A continuous entrance and bounded coefficient extend positive-time
integral identities to time zero for the actual chosen integral. -/
theorem seed_integral_from_positive_times (hB : IsFilteredPreBrownian B 𝓕 P)
    (hw : StronglyAdapted 𝓕 w) {C : ℝ} (hb : ∀ u ω, |w u ω| ≤ C)
    (hr : IsRiemannRegular P w) (hX : ∀ ω, ContinuousAt (X · ω) 0)
    (hpos : ∀ ε t : ℝ≥0, 0 < ε → ε ≤ t →
      (fun ω => X t ω - X ε ω) =ᵐ[P]
        fun ω => stochIntegral P 𝓕 B w t ω - stochIntegral P 𝓕 B w ε ω) (t : ℝ≥0) :
    (fun ω => X t ω - X 0 ω) =ᵐ[P] stochIntegral P 𝓕 B w t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  by_cases ht : t = 0
  · subst t
    filter_upwards [seedStochIntegral_zero_ae hB hw hb hr] with ω hω
    simp only [sub_self, hω]
  have htp : 0 < t := lt_of_le_of_ne (zero_le (a := t)) (Ne.symm ht)
  let ε : ℕ → ℝ≥0 := fun k => t / (k + 1)
  have hεp : ∀ k, 0 < ε k := fun k => div_pos htp (by positivity)
  have hεt : ∀ k, ε k ≤ t := fun k => div_le_self (zero_le (a := t))
    (le_add_of_nonneg_left (zero_le (a := (k : ℝ≥0))))
  have hε : Tendsto ε atTop (𝓝 0) := by
    have he := (tendsto_const_div_atTop_nhds_zero_nat (t : ℝ)).comp (tendsto_add_atTop_nat 1)
    apply NNReal.tendsto_coe.1
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, ε, NNReal.coe_div,
      NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_zero] using he
  obtain ⟨a, ha, hI⟩ :=
    (tendstoInMeasure_seedStochIntegral_zero hB hw hb hr hε).exists_seq_tendsto_ae
  have hids := ae_all_iff.2 (fun k => hpos (ε (a k)) t (hεp _) (hεt _))
  filter_upwards [hI, hids] with ω hi hω
  have hεa := hε.comp ha.tendsto_atTop
  have hleft := (tendsto_const_nhds (x := X t ω)).sub ((hX ω).tendsto.comp hεa)
  have hright := (tendsto_const_nhds (x := stochIntegral P 𝓕 B w t ω)).sub hi
  have hh := tendsto_nhds_unique hleft (hright.congr fun k => (hω k).symm)
  simpa only [sub_zero] using hh

/-- The actual compensated mapped driver before its Brownian continuation. -/
def seedStoppedMappedNoise {n : ℕ} (κ : ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ((d ω).A 0 (min t (S ω)) - (d ω).A 0 0 -
    (∫ u in (0 : ℝ)..(min t (S ω) : ℝ≥0), (d ω).d10Rate u)) / Real.sqrt κ

/-- Its chosen origin is zero, including a zero horizon. -/
theorem seedStoppedMappedNoise_zero {n : ℕ} (κ : ℝ) (d : Ω → SeedData n)
    (S : Ω → ℝ≥0) (ω : Ω) : seedStoppedMappedNoise κ d S 0 ω = 0 := by
  simp only [seedStoppedMappedNoise, zero_min, NNReal.coe_zero, min_eq_left (S ω).coe_nonneg,
    sub_self, intervalIntegral.integral_same, zero_div]

/-- Actual map continuity and entrance-integrable D10 give continuity
of the compensated driver, including at the seed entrance. -/
theorem continuous_seedStoppedMappedNoise {n : ℕ} {κ : ℝ} {d : Ω → SeedData n}
    {S : Ω → ℝ≥0} {A : Ω → Set ℂ}
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hi : ∀ ω, IntervalIntegrable (d ω).d10Rate volume 0 (S ω)) (ω : Ω) :
    Continuous (seedStoppedMappedNoise κ d S · ω) := by
  have hcI (ω : Ω) : ContinuousOn
      (fun t => ∫ u in (0 : ℝ)..t, (d ω).d10Rate u) (Icc 0 (S ω : ℝ)) := by
    simpa only [uIcc_of_le (S ω).coe_nonneg] using
      intervalIntegral.continuousOn_primitive_interval' (hi ω) left_mem_uIcc
  exact (((continuous_stopped_of_continuousOn (fun ω => (hown ω).continuousOn_frzA 0) ω).sub
    continuous_const).sub (continuous_stopped_of_continuousOn hcI ω)).div_const _

/-- Once the actual stopped map integral is identified, the Brownian
continuation gives exactly the stable `SeedOwnD10Integral` statement. -/
theorem seedOwnD10Integral_of_stopped_map_integral {n : ℕ} {κ : ℝ} {d : Ω → SeedData n}
    {S : Ω → ℝ≥0} (hB : IsFilteredPreBrownian B 𝓕 P) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ S ω}.indicator fun ω => (d ω).A 1 u))
    (hc : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (S ω)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u ω, 0 < u → u ≤ S ω → |(d ω).A 1 u| ≤ C)
    (hI : ∀ t, seedStoppedMappedNoise κ d S t =ᵐ[P]
      stochIntegral P 𝓕 B (positiveStopped (fun u ω => (d ω).A 1 u) S) t) :
    SeedOwnD10Integral P 𝓕 B κ d S := by
  have hp := isStronglyPredictable_positiveStopped 𝓕 hm hc
  have hbm : ∀ u ω, |positiveStopped (fun u ω => (d ω).A 1 u) S u ω| ≤ C := by
    intro u ω
    unfold positiveStopped
    split_ifs with hu
    · exact hb u ω hu.1 hu.2
    · simpa only [abs_zero] using hC
  have hrm := isRiemannRegular_positiveStopped P hc
  have hp1 := isStronglyPredictable_positiveStopped 𝓕
    (X := fun _ _ => (1 : ℝ)) (S := S)
    (fun u => measurable_const.indicator
      (by simpa only [WithTop.coe_le_coe] using hS.measurableSet_ge u))
    (fun _ => continuousOn_const)
  have hb1 : ∀ u ω, |positiveStopped (fun _ _ => 1) S u ω| ≤ 1 := by
    intro u ω
    unfold positiveStopped
    split_ifs <;> norm_num
  have hr1 := isRiemannRegular_positiveStopped P (X := fun _ _ => (1 : ℝ))
    (S := S) (fun _ => continuousOn_const)
  obtain ⟨ha, hba, hra⟩ := seed_one_sub_facts hp1.stronglyAdapted hb1 hr1
  intro t
  have hsum := seed_stochIntegral_add hB hp.stronglyAdapted ha hbm hba hrm hra t
  rw [← seedCapacityCoeff_split] at hsum
  filter_upwards [hI t, hsum, seed_stochIntegral_after_horizon hB hBc hS t] with ω hi hs ha'
  change seedStoppedMappedNoise κ d S t ω + (B t ω - B (min t (S ω)) ω) = _
  rw [hi, hs, ha']

end InteractingSLE.ZhanGT4
