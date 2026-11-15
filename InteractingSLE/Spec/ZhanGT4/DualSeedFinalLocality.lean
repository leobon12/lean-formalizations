/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalLocal

/-!
# Pathwise locality of the chosen stochastic integral

Packet PROVE-ZHAN-GT4-A22. Equality on an entire path prefix implies
almost sure equality of the chosen integrals on that event. The event
need not belong to the initial sigma algebra. Consequently the existing
eventual equality of band exits removes integral localization directly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B w v : ℝ≥0 → Ω → ℝ}

/-- Locality on a path prefix, proved from the actual Riemann sums. -/
theorem seed_stochIntegral_eq_of_pathAgreement
    (hB : IsFilteredPreBrownian B 𝓕 P) (hw : StronglyAdapted 𝓕 w) (hv : StronglyAdapted 𝓕 v)
    {Cw Cv : ℝ} (hbw : ∀ u ω, |w u ω| ≤ Cw) (hbv : ∀ u ω, |v u ω| ≤ Cv)
    (hrw : IsRiemannRegular P w) (hrv : IsRiemannRegular P v) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, (∀ u ≤ t, w u ω = v u ω) →
      stochIntegral P 𝓕 B w t ω = stochIntegral P 𝓕 B v t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨ns, hns, hI⟩ := (tendstoInMeasure_riemannSum hB hw hbw hrw t).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hJ⟩ :=
    ((tendstoInMeasure_riemannSum hB hv hbv hrv t).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hI, hJ] with ω hIω hJω heq
  have he (n : ℕ) : riemannSum B w n t ω = riemannSum B v n t ω := by
    rw [seed_riemannSum_clamped, seed_riemannSum_clamped]
    apply Finset.sum_congr rfl
    intro k _
    rw [heq _ (min_le_right _ _)]
  have hh := hIω.comp hms.tendsto_atTop
  simp only [Function.comp_def, he] at hh
  exact tendsto_nhds_unique hh hJω

/-- Removing bands uses only their eventual equality on each path; the
bounds for individual bands may depend on the band index. -/
theorem seed_stochIntegral_sub_eq_of_eventual_band
    (hB : IsFilteredPreBrownian B 𝓕 P) (hw : StronglyAdapted 𝓕 w)
    {Cw : ℝ} (hbw : ∀ u ω, |w u ω| ≤ Cw) (hrw : IsRiemannRegular P w)
    {wk : ℕ → ℝ≥0 → Ω → ℝ} (hmk : ∀ k, StronglyAdapted 𝓕 (wk k))
    {Ck : ℕ → ℝ} (hbk : ∀ k u ω, |wk k u ω| ≤ Ck k)
    (hrk : ∀ k, IsRiemannRegular P (wk k))
    {ε t : ℝ≥0} (hεt : ε ≤ t) {fk : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hIto : ∀ k, fk k =ᵐ[P] fun ω => stochIntegral P 𝓕 B (wk k) t ω -
      stochIntegral P 𝓕 B (wk k) ε ω)
    (hstage : ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      (∀ u ≤ t, wk k u ω = w u ω) ∧ fk k ω = f ω) :
    f =ᵐ[P] fun ω => stochIntegral P 𝓕 B w t ω - stochIntegral P 𝓕 B w ε ω := by
  have ht : ∀ᵐ ω ∂P, ∀ k, (∀ u ≤ t, wk k u ω = w u ω) →
      stochIntegral P 𝓕 B (wk k) t ω = stochIntegral P 𝓕 B w t ω :=
    ae_all_iff.2 fun k => seed_stochIntegral_eq_of_pathAgreement hB (hmk k) hw (hbk k) hbw (hrk k) hrw t
  have he : ∀ᵐ ω ∂P, ∀ k, (∀ u ≤ ε, wk k u ω = w u ω) →
      stochIntegral P 𝓕 B (wk k) ε ω = stochIntegral P 𝓕 B w ε ω :=
    ae_all_iff.2 fun k => seed_stochIntegral_eq_of_pathAgreement hB (hmk k) hw (hbk k) hbw (hrk k) hrw ε
  filter_upwards [ht, he, ae_all_iff.2 hIto, hstage] with ω ht he hi hs
  obtain ⟨k, hk, hfk⟩ := hs.exists
  rw [← hfk, hi k, ht k hk, he k (fun u hu => hk u (hu.trans hεt))]

end InteractingSLE.ZhanGT4
