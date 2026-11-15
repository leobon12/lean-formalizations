/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow20Admission
import InteractingSLE.Spec.Sec5.Aux61GWindow20Refine

/-! # Landing admission in the simultaneous capture quantifiers

The good time and real endpoint may be chosen after the sample. These
are the quantifiers of `completed_cover_of_admission`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow20
open Aux61SlitW Aux61GWindow17 Aux61GWindow19 Aux61Cpt LawUnique
universe u

/-- The actual record passes a rational landing test simultaneously for
every representative of the original good time and every actual endpoint. -/
theorem ae_landing_admission (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ, S.windowEvent p →
    ∀ t : GoodTime S, t.1 = S.t → ∀ y : ℝ,
      Tendsto (timePath S t p) (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)) →
      ∃ L : LandParam, |y - L.1.1| < L.1.2.1 ∧ timeRecord S t p ∈ landRecords S t L := by
  have hall : ∀ᵐ p ∂S.μ, ∀ t : GoodTime S, t.1 = S.t → S.windowEvent p → ∀ y : ℝ,
      Tendsto (timePath S t p) (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)) →
      ∃ L : LandParam, |y - L.1.1| < L.1.2.1 ∧ timeRecord S t p ∈ landRecords S t L := by
    refine ae_all_iff.2 fun t => ?_
    by_cases ht : t.1 = S.t
    · filter_upwards [ae_landing_admission_at_time S t ht] with p hp _ hw y hy
      exact hp hw y hy
    · exact ae_of_all _ fun _ h => (ht h).elim
  filter_upwards [hall] with p hp hw t ht y hy
  exact hp t ht hw y hy

/-- Admission with an arbitrarily small rational landing interval,
in the exact sample/time/endpoint quantifiers of the capture input. -/
theorem ae_landing_admission_small (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ, S.windowEvent p →
    ∀ t : GoodTime S, t.1 = S.t → ∀ y : ℝ,
      Tendsto (timePath S t p) (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)) →
      ∀ η : ℝ, 0 < η → ∃ L : LandParam,
        |y - L.1.1| < L.1.2.1 ∧ |(L.1.1 : ℝ) - y| + L.1.2.1 < η ∧
          timeRecord S t p ∈ landRecords S t L := by
  filter_upwards [ae_landing_admission S] with p hp hw t ht y hy η hη
  obtain ⟨L, hyL, hr⟩ := hp hw t ht y hy
  exact exists_landRecords_refinement S t hr hyL hη

/-- Admission with a positive gap between the seed and landing parts.
The seed test may subsequently be chosen with radius below this gap. -/
theorem ae_landing_admission_separated (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ, S.windowEvent p →
    ∀ t : GoodTime S, t.1 = S.t → ∀ y : ℝ, y ≠ 0 →
      Tendsto (timePath S t p) (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)) →
      ∃ ε : ℝ, 0 < ε ∧ ∃ L : LandParam, |y - L.1.1| < L.1.2.1 ∧
        timeRecord S t p ∈ landRecords S t L ∧
        (ε ≤ (L.1.1 : ℝ) - L.1.2.1 ∨ (L.1.1 : ℝ) + L.1.2.1 ≤ -ε) := by
  filter_upwards [ae_landing_admission S] with p hp hw t ht y hy0 hy
  obtain ⟨L, hyL, hr⟩ := hp hw t ht y hy
  exact exists_separated_landRecords S t hr hyL hy0

end InteractingSLE.Sec5.Aux61GWindow20
