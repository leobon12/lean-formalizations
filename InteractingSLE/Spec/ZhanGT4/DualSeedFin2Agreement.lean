/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Endpoint
import InteractingSLE.Spec.ZhanGT4.DualSeedEndLog

/-!
# Actual coefficient agreement at a seed-band exit

Packet PROVE-ZHAN-GT4-A22. Compute the pulled restarted coefficient in
the original coordinates. On a good band event its localized version is
exactly the deterministic cut of the strict endpoint noise.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*}

/-- Exact original-time value of the restarted first derivative. -/
theorem seed_restart_coef_eq (ℓx : Ω → ℝ → ℝ → ℝ) (σ : ℝ)
    (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) (S : Ω → ℝ≥0) (ω : Ω)
    (hεS : ε ≤ S ω) (u : ℝ≥0) :
    seedEndCoef ε (Ito.stopCoef (seedRestartDeriv 1 ℓx σ B D ε)
      (shiftBM B ε) (fun ω => S ω - ε)) u ω =
      if ε ≤ u ∧ u < S ω then σ * ℓx ω u (driftDriver σ B D ω u) else 0 := by
  by_cases hu : ε ≤ u
  · have hs : u - ε < S ω - ε ↔ u < S ω := by
      constructor
      · intro h
        simpa only [tsub_add_cancel_of_le hu, tsub_add_cancel_of_le hεS] using add_lt_add_left h ε
      · intro h
        apply (add_lt_add_iff_left ε).1
        simpa only [add_tsub_cancel_of_le hu, add_tsub_cancel_of_le hεS] using h
    simp only [seedEndCoef, hu, ite_true, Ito.stopCoef, hs, true_and]
    by_cases hut : u < S ω
    · simp only [hut, ite_true, seedRestartDeriv, pow_one]
      change σ * seedRestartLog ℓx σ B D ε ((u - ε : ℝ≥0) : ℝ)
        ω (shiftBM B ε (u - ε) ω) = _
      rw [seedRestartLog_at_driver]
      simp only [← NNReal.coe_add, add_tsub_cancel_of_le hu]
    · simp only [hut, ite_false]
  · simp only [seedEndCoef, hu, ite_false, false_and]

/-- Actual event-localized coefficients agree on every original time
once the band exit equals the target horizon. -/
theorem seed_band_coef_agreement {ℓx : Ω → ℝ → ℝ → ℝ} {σ : ℝ}
    {B D : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0} {S T : Ω → ℝ≥0} {E : Set Ω}
    {ω : Ω} (hω : ω ∈ E) (hε : 0 < ε) (hεS : ε ≤ S ω) (hST : S ω = T ω) (u : ℝ≥0) :
    seedEndCoef ε (Ito.stopCoef (seedRestartDeriv 1 (onEv E ℓx) σ B D ε)
      (shiftBM B ε) (fun ω => onEvS E ε S ω - ε)) u ω =
    seedEndWindow ε (seedFin2Endpoint T
      (positiveStopped (fun u ω => σ * ℓx ω u (driftDriver σ B D ω u)) T)) u ω := by
  have hs : ε ≤ onEvS E ε S ω := by rw [onEvS_of_mem hω]; exact hεS
  rw [seed_restart_coef_eq _ _ _ _ _ _ _ hs, onEvS_of_mem hω, onEv_of_mem hω, hST]
  unfold seedEndWindow seedFin2Endpoint positiveStopped
  by_cases hu : ε ≤ u
  · have hu0 : 0 < u := hε.trans_le hu
    rcases lt_trichotomy u (T ω) with hlt | he | hgt
    · simp only [hu, hu0, hlt, hlt.le, hlt.ne, and_self, ite_true, ite_false]
    · subst u
      simp only [hu, lt_self_iff_false, and_false, ite_false, ite_true]
    · simp only [hu, hu0, not_lt_of_ge hgt.le, not_le_of_gt hgt, hgt.ne',
        and_false, ite_false, ite_true]
  · simp only [hu, false_and, ite_false]

end InteractingSLE.ZhanGT4
