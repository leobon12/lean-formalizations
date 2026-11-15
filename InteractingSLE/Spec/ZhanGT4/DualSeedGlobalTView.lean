/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalD10
import MathFin.Probability.Martingales.MartingaleSetIntegral

/-!
# Stopped-prefix calculus for the named normalized opposite view

Packet PROVE-ZHAN-GT4-A22. Conditional on the precise existing geometric
interface, prove the entire bounded continuous density martingale. This
provides optional sampling, beyond its previously proved terminal mass.
It does not assert existence of the opposite-view geometric fields.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4
variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}

/-- The stopped density determined by the normalized t-view fields. -/
def SeedNormalizedTView.process {n : ℕ} {κ : ℝ} {rr : Fin n → ℝ}
    {𝓕₂ : Filtration ℝ≥0 m₂} {B₂ D₂ : ℝ≥0 → Ω₂ → ℝ}
    {V₂ : Ω₂ → ℝ → ℝ} {S₂ : Ω₂ → ℝ≥0} {M : Ω₁ × Ω₂ → ℝ≥0∞} {a₂ : Ω₂ → ℝ≥0∞}
    (h : SeedNormalizedTView κ rr 𝓕₂ B₂ D₂ V₂ S₂ M a₂) (ω₁ : Ω₁) (t : ℝ≥0) (ω₂ : Ω₂) : ℝ :=
  Real.exp (h.logField ω₁ ω₂ (min t (S₂ ω₂))
    (driftDriver (Real.sqrt (16 / κ)) B₂ D₂ ω₂ (min t (S₂ ω₂))))

/-- The normalized t-view gives a bounded continuous martingale in the
actual second filtration. No optional-sampling identity is a premise. -/
theorem SeedNormalizedTView.process_facts {n : ℕ} {κ : ℝ} {rr : Fin n → ℝ}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂] {𝓕₂ : Filtration ℝ≥0 m₂}
    {B₂ D₂ : ℝ≥0 → Ω₂ → ℝ} {V₂ : Ω₂ → ℝ → ℝ} {S₂ : Ω₂ → ℝ≥0}
    {M : Ω₁ × Ω₂ → ℝ≥0∞} {a₂ : Ω₂ → ℝ≥0∞}
    (h : SeedNormalizedTView κ rr 𝓕₂ B₂ D₂ V₂ S₂ M a₂)
    (hB : IsFilteredBrownianReal 𝓕₂ B₂ P₂) (hBc : ∀ ω, Continuous (B₂ · ω))
    (hS : IsStoppingTime 𝓕₂ fun ω => (S₂ ω : WithTop ℝ≥0)) (ω₁ : Ω₁) :
    Martingale (h.process ω₁) 𝓕₂ P₂ ∧
      (∀ ω, Continuous (h.process ω₁ · ω)) ∧
      (∀ t ω, |h.process ω₁ t ω| ≤ Real.exp (h.bound ω₁)) := by
  have hpath (ω : Ω₂) : ContinuousOn
      (fun u : ℝ => h.logField ω₁ ω u (driftDriver (Real.sqrt (16 / κ)) B₂ D₂ ω u))
      (Icc 0 (S₂ ω)) := by
    have hmap : MapsTo
        (fun u : ℝ => (u, driftDriver (Real.sqrt (16 / κ)) B₂ D₂ ω u))
        (Icc 0 (S₂ ω : ℝ))
        (driftTube (Real.sqrt (16 / κ)) B₂ D₂ 0 (S₂ ω) (4 * h.radius ω₁) ω) := by
      intro u hu
      refine ⟨hu, ?_⟩
      simp only [sub_self, abs_zero]
      exact mul_pos (by norm_num) (h.radius_pos ω₁)
    exact ((h.field ω₁).cont ω).comp
      (continuousOn_id.prodMk ((h.field ω₁).continuousOn_driftDriver hBc ω)) hmap
  have hm (t : ℝ≥0) : Measurable[𝓕₂ t] (h.process ω₁ t) :=
    (measurable_stopped_of_indicator hS
      (fun u => (h.field ω₁).meas0 u bot_le) hpath t).exp
  have hc (ω : Ω₂) : Continuous (h.process ω₁ · ω) :=
    Real.continuous_exp.comp (continuous_stopped_of_continuousOn hpath ω)
  have hb (t : ℝ≥0) (ω : Ω₂) : |h.process ω₁ t ω| ≤ Real.exp (h.bound ω₁) := by
    have hh := ((h.field ω₁).bound ω
      ((min (t : ℝ) (S₂ ω : ℝ)),
        driftDriver (Real.sqrt (16 / κ)) B₂ D₂ ω (min (t : ℝ) (S₂ ω : ℝ)))
      ⟨⟨le_min t.coe_nonneg (S₂ ω).coe_nonneg, min_le_right _ _⟩, by
        simp only [sub_self, abs_zero]
        exact mul_pos (by norm_num) (h.radius_pos ω₁)⟩).1
    rw [process, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans hh)
  have hi (t : ℝ≥0) : Integrable (h.process ω₁ t) P₂ :=
    (integrable_const (Real.exp (h.bound ω₁))).mono' ((hm t).mono (𝓕₂.le t) le_rfl).aestronglyMeasurable
      (ae_of_all P₂ fun ω => by simpa only [Real.norm_eq_abs] using hb t ω)
  refine ⟨martingale_iff_setIntegral_eq.2 ⟨fun t => (hm t).stronglyMeasurable, hi, ?_⟩, hc, hb⟩
  intro s t hst A hA
  have hξ : ∀ ω, |A.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ A <;> simp [indicator, hω]
  have he := (h.field ω₁).integral_mul_stopped_sub_eq_zero hB hBc (Real.sqrt_nonneg _)
    (h.radius_pos ω₁) hS (s := s) (t := t) bot_le hst (measurable_const.indicator hA) hξ
  have he' : (∫ ω in A, h.process ω₁ t ω - h.process ω₁ s ω ∂P₂) = 0 := by
    rw [← integral_indicator (𝓕₂.le s _ hA)]
    convert he using 1
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [indicator, hω, process]
  rw [integral_sub (hi t).integrableOn (hi s).integrableOn] at he'
  exact (sub_eq_zero.1 he').symm

/-- Second-coordinate optional sampling for the actual density of the
named normalized t-view, on every capped stopping-prefix event. -/
theorem SeedNormalizedTView.prefix_integral {n : ℕ} {κ : ℝ} {rr : Fin n → ℝ}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂] {𝓕₂ : Filtration ℝ≥0 m₂}
    {B₂ D₂ : ℝ≥0 → Ω₂ → ℝ} {V₂ : Ω₂ → ℝ → ℝ} {S₂ : Ω₂ → ℝ≥0}
    {M : Ω₁ × Ω₂ → ℝ≥0∞} {a₂ : Ω₂ → ℝ≥0∞}
    (h : SeedNormalizedTView κ rr 𝓕₂ B₂ D₂ V₂ S₂ M a₂)
    (hB : IsFilteredBrownianReal 𝓕₂ B₂ P₂) (hBc : ∀ ω, Continuous (B₂ · ω))
    (hS : IsStoppingTime 𝓕₂ fun ω => (S₂ ω : WithTop ℝ≥0))
    {U : ℝ≥0} (hSU : ∀ ω, S₂ ω ≤ U) {τ : Ω₂ → ℝ≥0}
    (hτ : IsStoppingTime 𝓕₂ fun ω => (τ ω : WithTop ℝ≥0)) (hτU : ∀ ω, τ ω ≤ U)
    {A : Set Ω₂} (hA : MeasurableSet[hτ.measurableSpace] A) (ω₁ : Ω₁) :
    (∫ ω in A, (M (ω₁, ω) * a₂ ω).toReal ∂P₂) =
      ∫ ω in A, h.process ω₁ (τ ω) ω ∂P₂ := by
  obtain ⟨hM, hc, -⟩ := h.process_facts hB hBc hS ω₁
  have he := setIntegral_stoppedValue_eq_of_rightContinuous hM
    (fun ω u => (hc ω).continuousWithinAt) hτ (isStoppingTime_const 𝓕₂ U)
    (fun ω => WithTop.coe_le_coe.2 (hτU ω)) (T := U) (fun _ => le_rfl) hA
  simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe] at he
  have hterm (ω : Ω₂) : h.process ω₁ U ω = (M (ω₁, ω) * a₂ ω).toReal := by
    rw [h.factorization, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    simp only [process, min_eq_right (NNReal.coe_le_coe.2 (hSU ω))]
  simpa only [hterm] using he.symm

end InteractingSLE.ZhanGT4
