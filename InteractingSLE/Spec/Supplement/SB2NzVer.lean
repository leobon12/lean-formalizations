/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzPos

/-!
# Versions of maps frozen under the regular conditional laws

Packet PROVE-SB2-LCMEAN, round 16 (D32: the root record). A measurable map `f` which, under the regular conditional
law given `𝒢` at almost every sample `ω₁`, is almost surely the constant `f ω₁` ("frozen") has a `𝒢`-measurable
version: its kernel integral (real coordinates), kernel lower integral (`ℝ≥0∞`), or kernel probability (`Bool`).
For records (`Exist.StagedLaw.RecData`), coordinate by coordinate:

* `exists_version_of_frozen_real`, `exists_version_of_frozen_ennreal`, `exists_version_of_frozen_bool`;
* **`exists_version_of_frozen_rec`**.

All statements are standard (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nz

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

theorem exists_version_of_frozen_real {f : Ω → ℝ} (hf : Measurable f)
    (hfr : ∀ᵐ ω₁ ∂μ, ∀ᵐ ω ∂(condExpKernel μ 𝒢 ω₁), f ω = f ω₁) :
    ∃ g : Ω → ℝ, Measurable[𝒢] g ∧ f =ᵐ[μ] g := by
  refine ⟨fun ω₁ => ∫ ω, f ω ∂(condExpKernel μ 𝒢 ω₁),
    (hf.stronglyMeasurable.integral_condExpKernel).measurable, ?_⟩
  filter_upwards [hfr] with ω₁ h
  rw [integral_congr_ae h, integral_const]
  simp

theorem exists_version_of_frozen_ennreal {f : Ω → ℝ≥0∞} (hf : Measurable f)
    (hfr : ∀ᵐ ω₁ ∂μ, ∀ᵐ ω ∂(condExpKernel μ 𝒢 ω₁), f ω = f ω₁) :
    ∃ g : Ω → ℝ≥0∞, Measurable[𝒢] g ∧ f =ᵐ[μ] g := by
  refine ⟨fun ω₁ => ∫⁻ ω, f ω ∂(condExpKernel μ 𝒢 ω₁), hf.lintegral_kernel, ?_⟩
  filter_upwards [hfr] with ω₁ h
  rw [lintegral_congr_ae h, lintegral_const, measure_univ, mul_one]

theorem exists_version_of_frozen_bool {f : Ω → Bool} (hf : Measurable f)
    (hfr : ∀ᵐ ω₁ ∂μ, ∀ᵐ ω ∂(condExpKernel μ 𝒢 ω₁), f ω = f ω₁) :
    ∃ g : Ω → Bool, Measurable[𝒢] g ∧ f =ᵐ[μ] g := by
  classical
  set S : Set Ω := f ⁻¹' {true} with hS
  have hSm : MeasurableSet S := hf (measurableSet_singleton true)
  refine ⟨fun ω₁ => decide (condExpKernel μ 𝒢 ω₁ S = 1), ?_, ?_⟩
  · have hm : Measurable[𝒢] fun ω₁ => condExpKernel μ 𝒢 ω₁ S := (condExpKernel μ 𝒢).measurable_coe hSm
    have hd : Measurable fun x : ℝ≥0∞ => decide (x = 1) := by
      refine measurable_to_countable' fun b => ?_
      cases b
      · have e : (fun x : ℝ≥0∞ => decide (x = 1)) ⁻¹' {false} = {1}ᶜ := by ext x; simp
        rw [e]
        exact (measurableSet_singleton 1).compl
      · have e : (fun x : ℝ≥0∞ => decide (x = 1)) ⁻¹' {true} = {1} := by ext x; simp
        rw [e]
        exact measurableSet_singleton 1
    exact hd.comp hm
  · filter_upwards [hfr] with ω₁ h
    by_cases hb : f ω₁ = true
    · have h1 : condExpKernel μ 𝒢 ω₁ S = 1 := by
        rw [← measure_univ (μ := condExpKernel μ 𝒢 ω₁)]
        refine measure_congr ?_
        filter_upwards [h] with ω hω
        simp only [hS, mem_preimage, mem_singleton_iff, hω, hb, mem_univ]
      simp [h1, hb]
    · have h0 : condExpKernel μ 𝒢 ω₁ S = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [h] with ω hω
        simp only [hS, mem_preimage, mem_singleton_iff, hω]
        exact hb
      simp only [Bool.not_eq_true] at hb
      simp [h0, hb]

/-- **A frozen record has a version measurable for `𝒢`.** -/
theorem exists_version_of_frozen_rec {f : Ω → Exist.StagedLaw.RecData} (hf : Measurable f)
    (hfr : ∀ᵐ ω₁ ∂μ, ∀ᵐ ω ∂(condExpKernel μ 𝒢 ω₁), f ω = f ω₁) :
    ∃ g : Ω → Exist.StagedLaw.RecData, Measurable[𝒢] g ∧ f =ᵐ[μ] g := by
  have hq : ∀ q : ℚ, ∃ g : Ω → ℝ, Measurable[𝒢] g ∧ (fun ω => (f ω).1 q) =ᵐ[μ] g := fun q =>
    exists_version_of_frozen_real ((measurable_pi_apply q).comp (measurable_fst.comp hf))
      (by filter_upwards [hfr] with ω₁ h; filter_upwards [h] with ω hω; rw [hω])
  choose gq hgq hgqe using hq
  obtain ⟨gl, hgl, hgle⟩ := exists_version_of_frozen_ennreal (𝒢 := 𝒢) (μ := μ)
    (f := fun ω => (f ω).2.1) (measurable_fst.comp (measurable_snd.comp hf))
    (by filter_upwards [hfr] with ω₁ h; filter_upwards [h] with ω hω; rw [hω])
  obtain ⟨gb, hgb, hgbe⟩ := exists_version_of_frozen_bool (𝒢 := 𝒢) (μ := μ)
    (f := fun ω => (f ω).2.2) (measurable_snd.comp (measurable_snd.comp hf))
    (by filter_upwards [hfr] with ω₁ h; filter_upwards [h] with ω hω; rw [hω])
  refine ⟨fun ω => (fun q => gq q ω, gl ω, gb ω), ?_, ?_⟩
  · let _ : MeasurableSpace Ω := 𝒢
    exact (measurable_pi_iff.2 hgq).prodMk (hgl.prodMk hgb)
  · filter_upwards [ae_all_iff.2 hgqe, hgle, hgbe] with ω h1 h2 h3
    exact Prod.ext (funext fun q => h1 q) (Prod.ext h2 h3)

end InteractingSLE.Theorem14.SB.Nz
