/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalStop
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalCapacity

/-!
# Brownian continuation after the seeded own-time horizon

Packet PROVE-ZHAN-GT4-A22. Identify the chosen integral of the stopped
unit coefficient, remove its two endpoint conventions, and splice the
mapped integral with the Brownian increment after the horizon.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}

/-- The positive-time closed stopping indicator has the same chosen integral. -/
theorem seed_stochIntegral_positive_one (hB : IsFilteredPreBrownian B 𝓕 P)
    (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    stochIntegral P 𝓕 B (positiveStopped (fun _ _ => 1) S) t =ᵐ[P]
      fun ω => B (min t (S ω)) ω - B 0 ω := by
  obtain ⟨hm, hb, hr⟩ := seed_stop_one_facts P hS
  have hp := isStronglyPredictable_positiveStopped 𝓕
    (X := fun _ _ => (1 : ℝ)) (S := S)
    (fun u => measurable_const.indicator
      (by simpa only [WithTop.coe_le_coe] using hS.measurableSet_ge u))
    (fun _ => continuousOn_const)
  have hbp : ∀ u ω, |positiveStopped (fun _ _ => 1) S u ω| ≤ 1 := by
    intro u ω
    unfold positiveStopped
    split_ifs <;> norm_num
  have hrp := isRiemannRegular_positiveStopped P (X := fun _ _ => (1 : ℝ))
    (S := S) (fun _ => continuousOn_const)
  have he : seedFin2Endpoint (fun _ => 0) (cutRate S (fun _ _ => 1)) =
      seedFin2Endpoint S (positiveStopped (fun _ _ => 1) S) := by
    funext u ω
    by_cases h0 : u = 0
    · subst u
      simp only [seedFin2Endpoint, positiveStopped, lt_self_iff_false,
        false_and, ite_false, ite_self, ite_true]
    · have hup : 0 < u := lt_of_le_of_ne (zero_le (a := u)) (Ne.symm h0)
      by_cases hs : u = S ω
      · rw [seedFin2Endpoint, seedFin2Endpoint, ite_eq_right h0, ite_eq_left hs]
        simp only [cutRate, hs, lt_self_iff_false, ite_false]
      · simp only [seedFin2Endpoint, h0, hs, ite_false, positiveStopped, hup, true_and]
        by_cases hlt : u < S ω
        · simp only [cutRate, hlt, hlt.le, ite_true]
        · have hn : ¬u ≤ S ω := fun hu => hlt (lt_of_le_of_ne hu hs)
          simp only [cutRate, hlt, hn, ite_false]
  have hi0 := seed_stochIntegral_endpoint hB hBc (isStoppingTime_const 𝓕 0) hm
    zero_le_one hb hr t
  have hiS := seed_stochIntegral_endpoint hB hBc hS hp.stronglyAdapted zero_le_one hbp hrp t
  rw [he] at hi0
  filter_upwards [hi0, hiS, seed_stochIntegral_stop_one hB hBc hS t] with ω h0 hS' hst
  exact hS'.symm.trans (h0.trans hst)

/-- Subtracting a bounded adapted coefficient from one preserves all integral inputs. -/
theorem seed_one_sub_facts {w : ℝ≥0 → Ω → ℝ} (hw : StronglyAdapted 𝓕 w)
    {C : ℝ} (hb : ∀ u ω, |w u ω| ≤ C) (hr : IsRiemannRegular P w) :
    StronglyAdapted 𝓕 (fun u ω => 1 - w u ω) ∧
      (∀ u ω, |1 - w u ω| ≤ 1 + C) ∧ IsRiemannRegular P (fun u ω => 1 - w u ω) := by
  refine ⟨fun u => stronglyMeasurable_const.sub (hw u), fun u ω => ?_, ?_⟩
  · exact (abs_sub _ _).trans (by simpa only [abs_one] using add_le_add le_rfl (hb u ω))
  · filter_upwards [hr] with ω hω
    exact hω.mono fun _ hu => continuousWithinAt_const.sub hu

/-- The integral of the complementary positive stopping indicator is the
actual Brownian continuation after the horizon. -/
theorem seed_stochIntegral_after_horizon (hB : IsFilteredPreBrownian B 𝓕 P)
    (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    stochIntegral P 𝓕 B (fun u ω => 1 - positiveStopped (fun _ _ => 1) S u ω) t =ᵐ[P]
      fun ω => B t ω - B (min t (S ω)) ω := by
  have hp := isStronglyPredictable_positiveStopped 𝓕
    (X := fun _ _ => (1 : ℝ)) (S := S)
    (fun u => measurable_const.indicator
      (by simpa only [WithTop.coe_le_coe] using hS.measurableSet_ge u))
    (fun _ => continuousOn_const)
  have hb : ∀ u ω, |positiveStopped (fun _ _ => 1) S u ω| ≤ 1 := by
    intro u ω
    unfold positiveStopped
    split_ifs <;> norm_num
  have hr := isRiemannRegular_positiveStopped P (X := fun _ _ => (1 : ℝ))
    (S := S) (fun _ => continuousOn_const)
  obtain ⟨ha, hba, hra⟩ := seed_one_sub_facts hp.stronglyAdapted hb hr
  have hs := seed_stochIntegral_add hB hp.stronglyAdapted ha hb hba hr hra t
  have he : (fun u ω => positiveStopped (fun _ _ => 1) S u ω +
      (1 - positiveStopped (fun _ _ => 1) S u ω)) = (fun _ _ => (1 : ℝ)) := by
    funext u ω
    ring
  rw [he] at hs
  filter_upwards [hs, seed_stochIntegral_one hB t, seed_stochIntegral_positive_one hB hBc hS t]
    with ω hsum hone hstop
  linarith only [hsum, hone, hstop]

/-- The capacity coefficient is the stopped map derivative plus the
complementary stopped unit coefficient, including both endpoint conventions. -/
theorem seedCapacityCoeff_split {n : ℕ} (d : Ω → SeedData n) (S : Ω → ℝ≥0) :
    seedCapacityCoeff d S = fun u ω => positiveStopped (fun u ω => (d ω).A 1 u) S u ω +
      (1 - positiveStopped (fun _ _ => 1) S u ω) := by
  funext u ω
  unfold seedCapacityCoeff positiveStopped
  split_ifs <;> ring

end InteractingSLE.ZhanGT4
