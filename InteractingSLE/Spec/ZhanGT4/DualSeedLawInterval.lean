/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLawIto

/-!
# Positive-time interval form of the random-field Itô engine

Packet PROVE-ZHAN-GT4-A22. Only errors between `ε` and `t` are required.
This avoids imposing a Taylor bound at the singular seed entrance.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B X c₁ c₂ : ℝ≥0 → Ω → ℝ}

/-- The stochastic-integral increment is identified from the Taylor
errors on that interval only. No time-zero error bound is assumed. -/
theorem seed_stochIntegral_sub_eq_of_dyadicDefect (hB : IsFilteredPreBrownian B 𝓕 P)
    (h₁ : StronglyAdapted 𝓕 c₁) {C₁ : ℝ} (hb₁ : ∀ u ω, |c₁ u ω| ≤ C₁)
    (hr₁ : IsRiemannRegular P c₁) (h₂ : StronglyAdapted 𝓕 c₂)
    {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (hb₂ : ∀ u ω, |c₂ u ω| ≤ C₂)
    {ε t : ℝ≥0} (hεt : ε ≤ t)
    (hd : TendstoInMeasure P (fun n ω => seedDyadicDefect X c₁ c₂ B n t ω -
      seedDyadicDefect X c₁ c₂ B n ε ω) atTop (fun _ => (0 : ℝ))) :
    (fun ω => X t ω - X ε ω) =ᵐ[P]
      fun ω => stochIntegral P 𝓕 B c₁ t ω - stochIntegral P 𝓕 B c₁ ε ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨a, ha, hIt⟩ := (tendstoInMeasure_riemannSum hB h₁ hb₁ hr₁ t).exists_seq_tendsto_ae
  obtain ⟨b, hb, hIe⟩ :=
    ((tendstoInMeasure_riemannSum hB h₁ hb₁ hr₁ ε).comp ha.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨c, hc, hQt⟩ := ((tendstoInMeasure_seedQuadraticError hB h₂ hC₂ hb₂ t).comp
    (ha.tendsto_atTop.comp hb.tendsto_atTop)).exists_seq_tendsto_ae
  obtain ⟨d, hd', hQe⟩ := ((tendstoInMeasure_seedQuadraticError hB h₂ hC₂ hb₂ ε).comp
    (ha.tendsto_atTop.comp (hb.tendsto_atTop.comp hc.tendsto_atTop))).exists_seq_tendsto_ae
  obtain ⟨e, he, hD⟩ := (hd.comp (ha.tendsto_atTop.comp (hb.tendsto_atTop.comp
    (hc.tendsto_atTop.comp hd'.tendsto_atTop)))).exists_seq_tendsto_ae
  filter_upwards [hIt, hIe, hQt, hQe, hD] with ω hit hie hqt hqe hδ
  have hit' := hit.comp (hb.tendsto_atTop.comp (hc.tendsto_atTop.comp
    (hd'.tendsto_atTop.comp he.tendsto_atTop)))
  have hie' := hie.comp (hc.tendsto_atTop.comp (hd'.tendsto_atTop.comp he.tendsto_atTop))
  have hqt' := hqt.comp (hd'.tendsto_atTop.comp he.tendsto_atTop)
  have hqe' := hqe.comp he.tendsto_atTop
  have hl := ((hit'.sub hie').add ((hqt'.sub hqe').div_const 2)).add hδ
  simp only [sub_self, zero_div, add_zero] at hl
  have hnat : Tendsto (fun k => (a (b (c (d (e k)))) : ℝ≥0)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (ha.tendsto_atTop.comp (hb.tendsto_atTop.comp
      (hc.tendsto_atTop.comp (hd'.tendsto_atTop.comp he.tendsto_atTop))))
  have heq : ∀ᶠ k in atTop,
      (riemannSum B c₁ (a (b (c (d (e k))))) t ω - riemannSum B c₁ (a (b (c (d (e k))))) ε ω) +
        (seedQuadraticError B c₂ (a (b (c (d (e k))))) t ω -
          seedQuadraticError B c₂ (a (b (c (d (e k))))) ε ω) / 2 +
        (seedDyadicDefect X c₁ c₂ B (a (b (c (d (e k))))) t ω -
          seedDyadicDefect X c₁ c₂ B (a (b (c (d (e k))))) ε ω) = X t ω - X ε ω := by
    filter_upwards [hnat.eventually (eventually_ge_atTop t)] with k hk
    rw [seedDyadicDefect_eq _ _ _ _ _ hk, seedDyadicDefect_eq _ _ _ _ _ (hεt.trans hk)]
    ring
  have hh : Tendsto (fun _ : ℕ => X t ω - X ε ω) atTop
      (𝓝 (stochIntegral P 𝓕 B c₁ t ω - stochIntegral P 𝓕 B c₁ ε ω)) := (tendsto_congr' heq).1 hl
  exact tendsto_nhds_unique tendsto_const_nhds hh

end InteractingSLE.ZhanGT4
