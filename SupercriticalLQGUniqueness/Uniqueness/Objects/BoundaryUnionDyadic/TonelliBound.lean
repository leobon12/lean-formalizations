import Mathlib.MeasureTheory.Integral.Prod




 





set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic

theorem lintegral_indicator_sections_le
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (μ : Measure Ω) [SFinite μ] (ν : Measure Θ) [SFinite ν]
    (E : Set (Ω × Θ)) (hE : MeasurableSet E) (B : ℝ≥0∞)
    (hsection : ∀ θ, μ {ω | (ω, θ) ∈ E} ≤ B) :
    (∫⁻ ω, ∫⁻ θ, E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, θ) ∂ν ∂μ) ≤
      ν Set.univ * B := by
  have hf : Measurable (fun p : Ω × Θ => E.indicator (fun _ => (1 : ℝ≥0∞)) p) :=
    measurable_const.indicator hE
  rw [lintegral_lintegral_swap hf.aemeasurable]
  calc
    (∫⁻ θ, ∫⁻ ω, E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, θ) ∂μ ∂ν)
        ≤ ∫⁻ _ : Θ, B ∂ν := by
          apply lintegral_mono
          intro θ
          have hθ : MeasurableSet {ω : Ω | (ω, θ) ∈ E} :=
            hE.preimage (measurable_id.prodMk measurable_const)
          have hind : (fun ω : Ω => E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, θ)) =
              {ω : Ω | (ω, θ) ∈ E}.indicator (fun _ => 1) := by
            funext ω
            rfl
          change (∫⁻ ω, E.indicator (fun _ => (1 : ℝ≥0∞)) (ω, θ) ∂μ) ≤ B
          rw [hind]
          have hone : (fun _ : Ω => (1 : ℝ≥0∞)) = (1 : Ω → ℝ≥0∞) := by
            funext ω
            rfl
          have heq : (∫⁻ ω, {ω : Ω | (ω, θ) ∈ E}.indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂μ) = μ {ω | (ω, θ) ∈ E} := by
            rw [hone]
            exact lintegral_indicator_one (μ := μ) hθ
          exact heq.le.trans (hsection θ)
    _ = ν Set.univ * B := by rw [lintegral_const]; exact mul_comm _ _

end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic
