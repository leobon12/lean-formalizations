/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualTimeChangeBM
import InteractingSLE.Spec.Sec2.GirsanovDensity

/-!
# The exponential martingales for the capacity time change

Packet PROVE-ZHAN-GT4-A22. The Doléans theorem supplies every real
exponential test required by the landed Lévy characterization. Thus an
own-time integral identity, rather than an assumed capacity Brownian
motion or an assumed family of exponential martingales, suffices.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B w Y : ℝ≥0 → Ω → ℝ}

/-- The chosen Riemann integral is homogeneous almost surely. -/
theorem seed_stochIntegral_const_mul [IsProbabilityMeasure P]
    (hB : IsFilteredPreBrownian B 𝓕 P) (hw : StronglyAdapted 𝓕 w)
    {C : ℝ} (hb : ∀ u ω, |w u ω| ≤ C) (hr : IsRiemannRegular P w)
    (c : ℝ) (t : ℝ≥0) :
    stochIntegral P 𝓕 B (fun u ω => c * w u ω) t =ᵐ[P]
      fun ω => c * stochIntegral P 𝓕 B w t ω := by
  have hm : StronglyAdapted 𝓕 (fun u ω => c * w u ω) := fun u => (hw u).const_mul c
  have hbc (u : ℝ≥0) (ω : Ω) : |c * w u ω| ≤ |c| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb u ω) (abs_nonneg c)
  have hrc : IsRiemannRegular P (fun u ω => c * w u ω) :=
    hr.mono fun ω hω => hω.mono fun _ hu => hu.const_mul c
  obtain ⟨ns, hns, hI⟩ := (tendstoInMeasure_riemannSum hB hw hb hr t).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hJ⟩ :=
    ((tendstoInMeasure_riemannSum hB hm hbc hrc t).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hI, hJ] with ω hIω hJω
  have he (n : ℕ) : riemannSum B (fun u ω => c * w u ω) n t ω = c * riemannSum B w n t ω := by
    simp only [riemannSum, ← Finset.mul_sum, mul_assoc]
  simp only [Function.comp_def, he] at hJω
  exact tendsto_nhds_unique hJω ((hIω.comp hms.tendsto_atTop).const_mul c)

/-- Homogeneity of the quadratic clock is an exact pathwise identity. -/
theorem seed_quadInt_const_mul (w : ℝ≥0 → Ω → ℝ) (c : ℝ) (t : ℝ≥0) (ω : Ω) :
    quadInt (fun u ω => c * w u ω) t ω = c ^ 2 * quadInt w t ω := by
  simp only [quadInt, mul_pow, intervalIntegral.integral_const_mul]

/-- A bounded predictable integral has the entire exponential-martingale
family needed for the capacity Brownian construction. -/
theorem seed_martingale_wald_of_integral (hB : IsFilteredPreBrownian B 𝓕 P)
    (hw : IsStronglyProgressive 𝓕 w) {C : ℝ} (hb : ∀ u ω, |w u ω| ≤ C)
    (hr : IsRiemannRegular P w) (hYm : ∀ u, Measurable[𝓕 u] (Y u))
    (hYI : ∀ u, Y u =ᵐ[P] stochIntegral P 𝓕 B w u) (ν : ℝ) :
    Martingale (fun t ω => Real.exp (ν * Y t ω - ν ^ 2 * quadInt w t ω / 2)) 𝓕 P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let wν : ℝ≥0 → Ω → ℝ := fun u ω => -ν * w u ω
  have hp : IsStronglyProgressive 𝓕 wν := fun u => (hw u).const_mul (-ν)
  have hbn (u : ℝ≥0) (ω : Ω) : |wν u ω| ≤ |ν| * C := by
    simpa only [wν, abs_mul, abs_neg] using
      mul_le_mul_of_nonneg_left (hb u ω) (abs_nonneg ν)
  have hrn : IsRiemannRegular P wν :=
    hr.mono fun ω hω => hω.mono fun _ hu => hu.const_mul (-ν)
  have : IsFilteredPreBrownian B 𝓕 P := hB
  apply (martingale_doleansDensity (B := B) hp hbn hrn).congr
    (fun t => (((hYm t).const_mul ν).sub
      ((stronglyMeasurable_integral_comp hw (measurable_id.pow_const 2) t).measurable.const_mul
        (ν ^ 2) |>.div_const 2)).exp.stronglyMeasurable)
  intro t
  filter_upwards [seed_stochIntegral_const_mul hB hw.stronglyAdapted hb hr (-ν) t, hYI t] with ω hI hY
  change Real.exp (-stochIntegral P 𝓕 B wν t ω - quadInt wν t ω / 2) =
    Real.exp (ν * Y t ω - ν ^ 2 * quadInt w t ω / 2)
  dsimp only [wν]
  rw [hI, seed_quadInt_const_mul, hY]
  congr 1
  ring

end InteractingSLE.ZhanGT4
