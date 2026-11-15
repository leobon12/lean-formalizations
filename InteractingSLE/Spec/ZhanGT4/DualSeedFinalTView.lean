/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImageAmalgam
import InteractingSLE.Spec.ZhanGT4.DualSeedLawCoupling
import InteractingSLE.Spec.ZhanGT4.DualSeedDrift

/-!
# Normalization in the amalgamated t-view

Packet PROVE-ZHAN-GT4-A22. The remaining geometric input is stated as
the normalized t-view field with its actual amalgamated drift. Its unit
row mass is proved from the existing random-field martingale theorem;
no normalization integral is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}

/-- Exact geometric/calculus input still needed for the normalized t-view.
The force rate uses the single amalgamated charge, not separate coincident
force gaps or an ordinary protected-mark hypothesis on a source seed. -/
structure SeedNormalizedTView {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ)
    (𝓕₂ : Filtration ℝ≥0 m₂) (B₂ D₂ : ℝ≥0 → Ω₂ → ℝ)
    (V₂ : Ω₂ → ℝ → ℝ) (S₂ : Ω₂ → ℝ≥0)
    (M : Ω₁ × Ω₂ → ℝ≥0∞) (a₂ : Ω₂ → ℝ≥0∞) where
  radius : Ω₁ → ℝ
  bound : Ω₁ → ℝ
  logField : Ω₁ → Ω₂ → ℝ → ℝ → ℝ
  logX : Ω₁ → Ω₂ → ℝ → ℝ → ℝ
  logXX : Ω₁ → Ω₂ → ℝ → ℝ → ℝ
  logXXX : Ω₁ → Ω₂ → ℝ → ℝ → ℝ
  logT : Ω₁ → Ω₂ → ℝ → ℝ → ℝ
  radius_pos : ∀ ω₁, 0 < radius ω₁
  field : ∀ ω₁, IsDriftLogField 𝓕₂ (Real.sqrt (16 / κ)) (radius ω₁) (bound ω₁) B₂ D₂
    (fun ω t => mirrorSourceCharge κ rr / (driftDriver (Real.sqrt (16 / κ)) B₂ D₂ ω t - V₂ ω t))
    0 S₂ (logField ω₁) (logX ω₁) (logXX ω₁) (logXXX ω₁) (logT ω₁)
  initial : ∀ ω₁ ω₂, logField ω₁ ω₂ 0 (driftDriver (Real.sqrt (16 / κ)) B₂ D₂ ω₂ 0) = 0
  factorization : ∀ ω₁ ω₂, M (ω₁, ω₂) * a₂ ω₂ =
    ENNReal.ofReal (Real.exp (logField ω₁ ω₂ (S₂ ω₂)
      (driftDriver (Real.sqrt (16 / κ)) B₂ D₂ ω₂ (S₂ ω₂))))

/-- The normalized t-view field proves the row identity required by the
seeded coupling, including the actual source density factor. -/
theorem SeedNormalizedTView.row_mass {n : ℕ} {κ : ℝ} {rr : Fin n → ℝ}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂] {𝓕₂ : Filtration ℝ≥0 m₂}
    {B₂ D₂ : ℝ≥0 → Ω₂ → ℝ} {V₂ : Ω₂ → ℝ → ℝ} {S₂ : Ω₂ → ℝ≥0}
    {M : Ω₁ × Ω₂ → ℝ≥0∞} {a₂ : Ω₂ → ℝ≥0∞}
    (h : SeedNormalizedTView κ rr 𝓕₂ B₂ D₂ V₂ S₂ M a₂)
    (hB : IsFilteredBrownianReal 𝓕₂ B₂ P₂) (hBc : ∀ ω, Continuous (B₂ · ω))
    (hS : IsStoppingTime 𝓕₂ fun ω => (S₂ ω : WithTop ℝ≥0))
    {U : ℝ≥0} (hSU : ∀ ω, S₂ ω ≤ U) (hm : Measurable M) (ha : Measurable a₂)
    (ω₁ : Ω₁) : ∫⁻ ω₂, M (ω₁, ω₂) * a₂ ω₂ ∂P₂ = 1 := by
  let Z : Ω₂ → ℝ := fun ω => Real.exp (h.logField ω₁ ω (S₂ ω)
    (driftDriver (Real.sqrt (16 / κ)) B₂ D₂ ω (S₂ ω)))
  have hmeas : Measurable Z := by
    have hh : Measurable (fun ω => (M (ω₁, ω) * a₂ ω).toReal) :=
      ((hm.comp (measurable_const.prodMk measurable_id)).mul ha).ennreal_toReal
    have he : (fun ω => (M (ω₁, ω) * a₂ ω).toReal) = Z := by
      funext ω
      rw [h.factorization]
      exact ENNReal.toReal_ofReal (Real.exp_pos _).le
    rwa [he] at hh
  have hbound (ω : Ω₂) : ‖Z ω‖ ≤ Real.exp (h.bound ω₁) := by
    have hm : ((S₂ ω : ℝ), driftDriver (Real.sqrt (16 / κ)) B₂ D₂ ω (S₂ ω)) ∈
        driftTube (Real.sqrt (16 / κ)) B₂ D₂ 0 (S₂ ω) (4 * h.radius ω₁) ω := by
      exact ⟨⟨(S₂ ω).coe_nonneg, le_rfl⟩, by
        simp only [sub_self, abs_zero]
        exact mul_pos (by norm_num) (h.radius_pos ω₁)⟩
    have hh := ((h.field ω₁).bound ω _ hm).1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans hh)
  have hi : Integrable Z P₂ := (integrable_const (Real.exp (h.bound ω₁))).mono'
    hmeas.aestronglyMeasurable (Eventually.of_forall hbound)
  have he := (h.field ω₁).integral_mul_stopped_sub_eq_zero hB hBc (Real.sqrt_nonneg _)
    (h.radius_pos ω₁) hS (s := 0) (t := U) le_rfl (zero_le (a := U))
    (ξ := fun _ => 1) measurable_const (fun _ => by simp)
  have he' : (∫ ω, Z ω - 1 ∂P₂) = 0 := by
    convert he using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      simp only [NNReal.coe_zero, min_eq_right (show (S₂ ω : ℝ) ≤ U from hSU ω),
        min_eq_left (S₂ ω).coe_nonneg, h.initial,
        Real.exp_zero, one_mul, Z]
  rw [integral_sub hi (integrable_const _)] at he'
  simp only [integral_const, probReal_univ, one_smul] at he'
  have hmass : ∫ ω, Z ω ∂P₂ = 1 := by linarith only [he']
  simp_rw [h.factorization]
  change (∫⁻ ω, ENNReal.ofReal (Z ω) ∂P₂) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ω => (Real.exp_pos _).le),
    hmass, ENNReal.ofReal_one]

end InteractingSLE.ZhanGT4
