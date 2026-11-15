/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndWindowIntegral
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalLocality

/-!
# Removing restarted bands in the original stochastic integral

Packet PROVE-ZHAN-GT4-A22. Actual regular band fields give the integral
identity on each band. Eventual pathwise agreement removes the band, and
the checked deterministic cut identity returns the original integral
increment. There is no assumed bandwise Itô identity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov LP.LP4HB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B w : ℝ≥0 → Ω → ℝ} {ε t : ℝ≥0}
  {τ : ℕ → Ω → ℝ≥0} {ρ K : ℕ → ℝ}
  {Φ Φ₁ Φ₂ Φ₃ Ψ : ℕ → ℝ → Ω → ℝ → ℝ} {f : Ω → ℝ}

/-- Original-clock band removal from the actual local fields. The stage
assumption is literal agreement of the band coordinates and integrands
on each path, as supplied by eventual equality of the gap-band exits. -/
theorem seed_original_integral_of_band_family
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hw : StronglyAdapted 𝓕 w) {Cw : ℝ} (hbw : ∀ u ω, |w u ω| ≤ Cw)
    (hrw : IsRiemannRegular P w) (hεt : ε ≤ t)
    (hband : ∀ k, SeedRegularBand (shiftBM B ε) (τ k) (Φ k) (Φ₁ k) (Φ₂ k) (Φ₃ k) (Ψ k) (ρ k) (K k))
    (hX : ∀ k u, Measurable (Ito.fieldStopped (Φ k) (Φ₂ k) (Ψ k) (shiftBM B ε) (τ k) 0 u))
    (h₁ : ∀ k, StronglyAdapted (shiftFiltration 𝓕 ε) (Ito.stopCoef (Φ₁ k) (shiftBM B ε) (τ k)))
    (h₂ : ∀ k, StronglyAdapted (shiftFiltration 𝓕 ε) (Ito.stopCoef (Φ₂ k) (shiftBM B ε) (τ k)))
    (hr : ∀ k, IsRiemannRegular P (Ito.stopCoef (Φ₁ k) (shiftBM B ε) (τ k)))
    (hstage : ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      (∀ u ≤ t, seedEndCoef ε (Ito.stopCoef (Φ₁ k) (shiftBM B ε) (τ k)) u ω =
        seedEndWindow ε w u ω) ∧
      (seedEndProcess ε (Ito.fieldStopped (Φ k) (Φ₂ k) (Ψ k) (shiftBM B ε) (τ k) 0) t ω -
        seedEndProcess ε (Ito.fieldStopped (Φ k) (Φ₂ k) (Ψ k) (shiftBM B ε) (τ k) 0) 0 ω = f ω)) :
    f =ᵐ[P] fun ω => stochIntegral P 𝓕 B w t ω - stochIntegral P 𝓕 B w ε ω := by
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  have hpre := isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hwin := seedEndWindow_adapted (ε := ε) hw
  have hreg := seedEndWindow_isRiemannRegular (ε := ε) hrw
  have hbwin (u : ℝ≥0) (ω : Ω) : |seedEndWindow ε w u ω| ≤ |Cw| := by
    unfold seedEndWindow
    split_ifs
    · exact (hbw _ _).trans (le_abs_self _)
    · simpa only [abs_zero] using abs_nonneg Cw
  have hh := seed_stochIntegral_sub_eq_of_eventual_band hpre hwin hbwin hreg
    (wk := fun k => seedEndCoef ε (Ito.stopCoef (Φ₁ k) (shiftBM B ε) (τ k)))
    (fun k => seedEndCoef_adapted (h₁ k))
    (fun k => abs_seedEndCoef_le (hband k).bound_nonneg
      (fun u ω => ((hband k).coef_bound ω u).1) ε)
    (fun k => seedEndCoef_isRiemannRegular (hr k)) (ε := 0) (t := t) bot_le
    (fun k => (hband k).original_stochIntegral hB hBc (hX k) (h₁ k) (h₂ k) (hr k) t) hstage
  filter_upwards [hh, seedStochIntegral_zero_ae hpre hwin hbwin hreg,
    seed_stochIntegral_window hpre hBc hw hbw hrw hεt] with ω hi h0 hw'
  rw [h0, sub_zero, hw'] at hi
  exact hi

end InteractingSLE.ZhanGT4
