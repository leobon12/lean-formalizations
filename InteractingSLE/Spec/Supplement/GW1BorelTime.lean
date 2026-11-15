/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1BorelTrace

/-!
# Countable tests for continuous retargeting clocks

Continuation of PROVE-GW1-DET. Strict increase and coverage of the source
interval can both be tested at nonnegative rational times.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.Theorem14.GW1Borel

/-- A real path code regularized as a nonnegative continuous clock. -/
def clock (f : Code) (t : ℝ≥0) : ℝ≥0 := (driver f t).toNNReal

theorem continuous_clock (f : Code) : Continuous (clock f) :=
  continuous_real_toNNReal.comp (continuous_driver f)

theorem clock_zero (f : Code) : clock f 0 = 0 := by
  simp only [clock, driver_zero, Real.toNNReal_zero]

theorem measurable_clock (t : ℝ≥0) : Measurable (fun f : Code => clock f t) :=
  measurable_real_toNNReal.comp (measurable_driver t)

/-- Continuity upgrades the rational strict-order test to strict increase. -/
theorem strictMono_iff_rat {ℓ : ℝ≥0 → ℝ≥0} (hc : Continuous ℓ) :
    StrictMono ℓ ↔ ∀ a b : ℚ≥0, a < b → ℓ a < ℓ b := by
  constructor
  · intro h a b hab
    exact h (by exact_mod_cast hab)
  · intro h
    have hm : Monotone ℓ := by
      intro s t hst
      rcases hst.eq_or_lt with rfl | hst
      · exact le_rfl
      have hev : ∀ᶠ n in atTop,
          (Sec7.Coding.apxQ s n : ℝ≥0) < (Sec7.Coding.apxQ t n : ℝ≥0) :=
        (Sec7.Coding.tendsto_apxQ s).eventually_lt (Sec7.Coding.tendsto_apxQ t) hst
      exact le_of_tendsto_of_tendsto ((hc.tendsto s).comp (Sec7.Coding.tendsto_apxQ s))
        ((hc.tendsto t).comp (Sec7.Coding.tendsto_apxQ t))
        (hev.mono fun n hn => (h _ _ (by exact_mod_cast hn)).le)
    intro s t hst
    obtain ⟨a, hsa, hat⟩ := Sec7.Coding.exists_nnrat_btwn hst
    obtain ⟨b, hab, hbt⟩ := Sec7.Coding.exists_nnrat_btwn hat
    exact (hm hsa.le).trans_lt ((h a b (by exact_mod_cast hab)).trans_le (hm hbt.le))

theorem measurableSet_strictMono_clock : MeasurableSet {f : Code | StrictMono (clock f)} := by
  simp_rw [strictMono_iff_rat (continuous_clock _)]
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun a : ℚ≥0 => MeasurableSet.iInter fun b : ℚ≥0 =>
    MeasurableSet.iInter fun _ : a < b => measurableSet_lt (measurable_clock a) (measurable_clock b)

/-- Integer-time upper bounds and their supremum characterize the range of a
continuous strictly increasing clock starting at zero. -/
theorem range_clock_iff {ℓ : ℝ≥0 → ℝ≥0} (hc : Continuous ℓ) (hm : StrictMono ℓ)
    (h0 : ℓ 0 = 0) (T : ℝ≥0∞) :
    range ℓ = {t : ℝ≥0 | (t : ℝ≥0∞) < T} ↔
      (∀ n : ℕ, (ℓ n : ℝ≥0∞) < T) ∧ (⨆ n : ℕ, (ℓ n : ℝ≥0∞)) = T := by
  constructor
  · intro hr
    have hbound (t : ℝ≥0) : (ℓ t : ℝ≥0∞) < T := by
      have h := mem_range_self (f := ℓ) t
      rwa [hr] at h
    refine ⟨fun n => hbound n, le_antisymm (iSup_le fun n => (hbound n).le) ?_⟩
    apply ENNReal.le_of_forall_nnreal_lt
    intro s hs
    obtain ⟨r, hr'⟩ := (show s ∈ range ℓ by rw [hr]; exact hs)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    have hn' : r < (n : ℝ≥0) := by exact_mod_cast hn
    exact (ENNReal.coe_le_coe.2 (hr' ▸ (hm hn').le)).trans (le_iSup (fun n : ℕ => (ℓ n : ℝ≥0∞)) n)
  · rintro ⟨hb, hsup⟩
    ext s
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨n, hn⟩ := exists_nat_gt r
      have hn' : r < (n : ℝ≥0) := by exact_mod_cast hn
      exact (ENNReal.coe_lt_coe.2 (hm hn')).trans (hb n)
    · intro hs
      change (s : ℝ≥0∞) < T at hs
      rw [← hsup, lt_iSup_iff] at hs
      obtain ⟨n, hn⟩ := hs
      have hsn : s ≤ ℓ n := (ENNReal.coe_lt_coe.1 hn).le
      have himg := hc.continuousOn.image_Icc_of_monotoneOn (show (0 : ℝ≥0) ≤ n from zero_le)
        (hm.monotone.monotoneOn _)
      rw [h0] at himg
      exact image_subset_range ℓ _ (himg ▸ (show s ∈ Icc 0 (ℓ n) from ⟨zero_le, hsn⟩))

theorem measurableSet_clock_range :
    MeasurableSet {p : Code × ℝ≥0∞ | StrictMono (clock p.1) ∧
      range (clock p.1) = {t : ℝ≥0 | (t : ℝ≥0∞) < p.2}} := by
  have hc (n : ℕ) : Measurable (fun p : Code × ℝ≥0∞ => (clock p.1 n : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp ((measurable_clock n).comp measurable_fst)
  have hbound : MeasurableSet {p : Code × ℝ≥0∞ | ∀ n : ℕ, (clock p.1 n : ℝ≥0∞) < p.2} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun n => measurableSet_lt (hc n) measurable_snd
  have hsup : MeasurableSet {p : Code × ℝ≥0∞ | (⨆ n : ℕ, (clock p.1 n : ℝ≥0∞)) = p.2} :=
    measurableSet_eq_fun (.iSup hc) measurable_snd
  convert (measurableSet_strictMono_clock.preimage measurable_fst).inter (hbound.inter hsup) using 1
  ext p
  exact and_congr_right fun hm => range_clock_iff (continuous_clock p.1) hm (clock_zero p.1) p.2

end InteractingSLE.Theorem14.GW1Borel
