import SupercriticalLQGUniqueness.B2.Polylog.P4Scale

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem measure_le_of_stationary_heat_version
    {μ : Measure DistC} (T : DistC → DistC)
    (hT : AEMeasurable T μ) (hlaw : μ.map T = μ)
    (δ : ℝ) (Y X : DistC → C(ℂ, ℝ))
    (hY : ∀ᵐ g ∂μ, ∀ u, Y g u = heatMollify δ (T g) u)
    (hX : ∀ᵐ g ∂μ, ∀ u, X g u = heatMollify δ g u)
    (Ψ : C(ℂ, ℝ) → Prop) :
    μ {g | Ψ (Y g)} ≤ μ {g | Ψ (X g)} := by
  set B : Set DistC :=
    {g' | ∃ φ : C(ℂ, ℝ), (∀ u, φ u = heatMollify δ g' u) ∧ Ψ φ}
  calc
    μ {g | Ψ (Y g)} ≤ μ (T ⁻¹' B) := by
      refine measure_mono_ae ?_
      filter_upwards [hY] with g hg hΨ
      exact ⟨Y g, hg, hΨ⟩
    _ ≤ (μ.map T) B := Measure.le_map_apply hT B
    _ = μ B := by rw [hlaw]
    _ ≤ μ {g | Ψ (X g)} := by
      refine measure_mono_ae ?_
      filter_upwards [hX] with g hg hB
      obtain ⟨φ, hφ, hΨ⟩ := hB
      have hEq : φ = X g := by
        ext u
        rw [hφ u, hg u]
      simpa only [hEq] using hΨ

 

theorem measure_le_of_pushed_heat_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : AEMeasurable h P)
    (μ : Measure DistC) (hlaw : P.map h = μ)
    (δ : ℝ) (Y : Ω → C(ℂ, ℝ)) (X : DistC → C(ℂ, ℝ))
    (hY : ∀ᵐ ω ∂P, ∀ u, Y ω u = heatMollify δ (h ω) u)
    (hX : ∀ᵐ g ∂μ, ∀ u, X g u = heatMollify δ g u)
    (Ψ : C(ℂ, ℝ) → Prop) :
    P {ω | Ψ (Y ω)} ≤ μ {g | Ψ (X g)} := by
  set B : Set DistC :=
    {g | ∃ φ : C(ℂ, ℝ), (∀ u, φ u = heatMollify δ g u) ∧ Ψ φ}
  calc
    P {ω | Ψ (Y ω)} ≤ P (h ⁻¹' B) := by
      refine measure_mono_ae ?_
      filter_upwards [hY] with ω hω hΨ
      exact ⟨Y ω, hω, hΨ⟩
    _ ≤ (P.map h) B := Measure.le_map_apply hh B
    _ = μ B := by rw [hlaw]
    _ ≤ μ {g | Ψ (X g)} := by
      refine measure_mono_ae ?_
      filter_upwards [hX] with g hg hB
      obtain ⟨φ, hφ, hΨ⟩ := hB
      have hEq : φ = X g := by
        ext u
        rw [hφ u, hg u]
      simpa only [hEq] using hΨ

end SupercriticalLQGUniqueness.B2.DG20Lim
