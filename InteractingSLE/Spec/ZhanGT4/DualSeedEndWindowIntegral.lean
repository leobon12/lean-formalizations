/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndWindow

/-!
# Original-clock integral increments are cut integrals

Packet PROVE-ZHAN-GT4-A22. Prove the deterministic interval-cut identity
for the project's actual chosen stochastic integral from its Riemann
limits and the single crossing-cell error.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B c : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0}

/-- Cutting at a deterministic time preserves adaptedness. -/
theorem seedEndWindow_adapted (hc : StronglyAdapted 𝓕 c) :
    StronglyAdapted 𝓕 (seedEndWindow ε c) := by
  intro u
  by_cases hu : ε ≤ u
  · have he : seedEndWindow ε c u = c u := by funext ω; exact ite_eq_left hu
    rw [he]
    exact hc u
  · have he : seedEndWindow ε c u = fun _ => 0 := by funext ω; exact ite_eq_right hu
    rw [he]
    exact stronglyMeasurable_const

/-- The deterministic cut adds only one possible time discontinuity. -/
theorem seedEndWindow_isRiemannRegular (hc : IsRiemannRegular P c) :
    IsRiemannRegular P (seedEndWindow ε c) := by
  filter_upwards [hc] with ω hω
  filter_upwards [hω, ae_ne_real ε] with r hr hne
  rcases le_or_gt r 0 with h0 | h0
  · have he : Iic r.toNNReal = {r.toNNReal} := by
      simp only [Real.toNNReal_of_nonpos h0]
      ext u
      simp only [mem_Iic, nonpos_iff_eq_zero, mem_singleton_iff]
    rw [he]
    exact continuousWithinAt_singleton
  · have hu : (r.toNNReal : ℝ) = r := Real.coe_toNNReal _ h0.le
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt' : r.toNNReal < ε := by exact_mod_cast hu.trans_lt hlt
      have hz : ∀ v ∈ Iic r.toNNReal, seedEndWindow ε c v ω = 0 := fun v hv =>
        ite_eq_right (not_le_of_gt ((mem_Iic.1 hv).trans_lt hlt'))
      exact (continuousWithinAt_const (b := (0 : ℝ))).congr hz (hz _ (mem_Iic.2 le_rfl))
    · have hgt' : ε < r.toNNReal := by exact_mod_cast hgt.trans_eq hu.symm
      apply hr.congr_of_eventuallyEq
      · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hgt')] with v hv
        exact ite_eq_left (mem_Ioi.1 hv).le
      · exact ite_eq_left hgt'.le

/-- The chosen stochastic integral of the cut coefficient is the actual
integral increment. The proof identifies limits, not versions by choice. -/
theorem seed_stochIntegral_window (hB : IsFilteredPreBrownian B 𝓕 P)
    (hBc : ∀ ω, Continuous (B · ω)) (hc : StronglyAdapted 𝓕 c)
    {C : ℝ} (hb : ∀ u ω, |c u ω| ≤ C) (hr : IsRiemannRegular P c)
    {t : ℝ≥0} (hεt : ε ≤ t) :
    stochIntegral P 𝓕 B (seedEndWindow ε c) t =ᵐ[P]
      fun ω => stochIntegral P 𝓕 B c t ω - stochIntegral P 𝓕 B c ε ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hbw (u : ℝ≥0) (ω : Ω) : |seedEndWindow ε c u ω| ≤ |C| := by
    unfold seedEndWindow
    split_ifs
    · exact (hb _ _).trans (le_abs_self C)
    · simpa only [abs_zero] using abs_nonneg C
  obtain ⟨a, ha, hIt⟩ := (tendstoInMeasure_riemannSum hB hc hb hr t).exists_seq_tendsto_ae
  obtain ⟨b, hbt, hIe⟩ :=
    ((tendstoInMeasure_riemannSum hB hc hb hr ε).comp ha.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨d, hd, hIw⟩ := ((tendstoInMeasure_riemannSum hB (seedEndWindow_adapted hc) hbw
    (seedEndWindow_isRiemannRegular hr) t).comp
      (ha.tendsto_atTop.comp hbt.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hIt, hIe, hIw] with ω hit hie hiw
  have hl := ((hit.comp (hbt.tendsto_atTop.comp hd.tendsto_atTop)).sub
    (hie.comp hd.tendsto_atTop)).sub hiw
  have hz := (tendsto_seedEndWindow_error hb hBc hεt ω).comp
    (ha.tendsto_atTop.comp (hbt.tendsto_atTop.comp hd.tendsto_atTop))
  have he := tendsto_nhds_unique hl hz
  linarith only [he]

end InteractingSLE.ZhanGT4
