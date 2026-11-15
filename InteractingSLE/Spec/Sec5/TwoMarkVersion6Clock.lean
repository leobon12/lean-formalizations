/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkVersion6Announce
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianTime

/-!
# Announcing the image horizon from clock stopping times

A running maximum enforces monotonicity even on exceptional paths. The exact
remaining filtration input is that each clock image of an original stop is a
stopping time. No Brownian time-change claim is made here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Version6

open Zhan.Retarget

/-- Running maxima of the clock images of a sequence of original times. -/
def clockAnnounce {Ω : Type*} (a : ℝ) (W V : ℝ≥0 → Ω → ℝ) (A : ℕ → Ω → ℝ≥0) :
    ℕ → Ω → ℝ≥0
  | 0, ω => (clk (rate a (W · ω) (V · ω)) (A 0 ω)).toNNReal
  | n + 1, ω => max (clockAnnounce a W V A n ω)
      (clk (rate a (W · ω) (V · ω)) (A (n + 1) ω)).toNNReal

variable {Ω : Type*} {a : ℝ} {W V : ℝ≥0 → Ω → ℝ} {A : ℕ → Ω → ℝ≥0}

/-- The running maxima are nondecreasing on every path. -/
theorem monotone_clockAnnounce (ω : Ω) : Monotone (clockAnnounce a W V A · ω) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

/-- On a separated path, the running maximum equals the current clock image. -/
theorem clockAnnounce_eq_clock {ω : Ω} {T : ℝ≥0∞} (ha : 0 < a)
    (hsep : SepUpTo (W · ω) (V · ω) T) (hAm : Monotone (A · ω))
    (hA : ∀ n, (A n ω : ℝ≥0∞) < T) (n : ℕ) :
    clockAnnounce a W V A n ω = (clk (rate a (W · ω) (V · ω)) (A n ω)).toNNReal := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [clockAnnounce, ih, max_eq_right]
    apply Real.toNNReal_mono
    have hr := (hsep.isSep_of_lt (hA (n + 1))).isRate ha
    exact (hr.clk_le_clk ⟨(A n ω).coe_nonneg, by exact_mod_cast hAm (Nat.le_succ n)⟩
      ⟨(A (n + 1) ω).coe_nonneg, le_rfl⟩).2 (by exact_mod_cast hAm (Nat.le_succ n))

/-- Finite running maxima preserve the named clock stopping-time input. -/
theorem isStoppingTime_clockAnnounce [mΩ : MeasurableSpace Ω] {𝓘 : Filtration ℝ≥0 mΩ}
    (hclock : ∀ n, IsStoppingTime 𝓘 fun ω =>
      ((clk (rate a (W · ω) (V · ω)) (A n ω)).toNNReal : WithTop ℝ≥0)) (n : ℕ) :
    IsStoppingTime 𝓘 fun ω => (clockAnnounce a W V A n ω : WithTop ℝ≥0) := by
  induction n with
  | zero => exact hclock 0
  | succ n ih =>
    intro t
    simpa only [clockAnnounce, WithTop.coe_le_coe, max_le_iff, Set.ofPred_and] using
      (ih t).inter (hclock (n + 1) t)

/-- Clock images announce the image horizon once their stopping-time property is supplied. -/
theorem isAnnouncingSeq_clockAnnounce [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 𝓘 : Filtration ℝ≥0 mΩ} {e τ : Ω → ℝ≥0∞} (ha : 0 < a)
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A)
    (hsep : ∀ᵐ ω ∂P, SepUpTo (W · ω) (V · ω) (e ω))
    (hτ : ∀ᵐ ω ∂P, τ ω = newHorizon a (W · ω) (V · ω) (e ω))
    (hclock : ∀ n, IsStoppingTime 𝓘 fun ω =>
      ((clk (rate a (W · ω) (V · ω)) (A n ω)).toNNReal : WithTop ℝ≥0)) :
    Coupling.IsAnnouncingSeq 𝓘 P τ (clockAnnounce a W V A) := by
  have hbefore : ∀ᵐ ω ∂P, ∀ n, (A n ω : ℝ≥0∞) < e ω := ae_all_iff.2 hA.2.2.1
  apply isAnnouncingSeq_congr_horizon (τ := τ) (he := Filter.EventuallyEq.symm hτ)
  refine ⟨isStoppingTime_clockAnnounce hclock, monotone_clockAnnounce, ?_, ?_⟩
  · intro n
    filter_upwards [hsep, hbefore] with ω hs hb
    rw [clockAnnounce_eq_clock ha hs (hA.2.1 ω) hb n]
    exact (clk_lt_newHorizon' hs ha (hb n)).2
  · filter_upwards [hsep, hbefore, hA.2.2.2] with ω hs hb hcof u hu
    obtain ⟨s, hse, hus⟩ := exists_lt_clk_of_lt_newHorizon hu
    obtain ⟨n, hn⟩ := hcof s hse
    refine ⟨n, ?_⟩
    rw [clockAnnounce_eq_clock ha hs (hA.2.1 ω) hb n]
    have hr := (hs.isSep_of_lt (hb n)).isRate ha
    have hle := (hr.clk_le_clk ⟨s.coe_nonneg, by exact_mod_cast hn⟩
      ⟨(A n ω).coe_nonneg, le_rfl⟩).2 (by exact_mod_cast hn)
    exact (Real.le_toNNReal_iff_coe_le (clk_lt_newHorizon' hs ha (hb n)).1).2 (hus.le.trans hle)

end InteractingSLE.Sec5.TwoMark.Version6
