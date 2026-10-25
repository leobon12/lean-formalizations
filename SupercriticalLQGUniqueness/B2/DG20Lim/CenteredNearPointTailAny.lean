import SupercriticalLQGUniqueness.B2.DG20Lim.CenteredNearPointTail
import SupercriticalLQGUniqueness.B2.DG20Lim.StationaryHeatEventLaw

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_small_centered_point_upper_tail_any_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (θ η : ℝ) (hθ : 0 < θ) (hη : 0 < η) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
      ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
        (∀ ε, IsHeatSmoothing P h ε (X ε)) →
      ∀ (r : Ioo (0 : ℝ) 1), (r : ℝ) ≤ r₀ →
      ∀ (δ : Ioo (0 : ℝ) 1),
        let e : Ioi (0 : ℝ) :=
          ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property.1 δ.property.1⟩
        P {ω | ENNReal.ofReal θ <
          edist ((normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).pt 0)
            ((normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).pt (r : ℂ))} ≤
          ENNReal.ofReal η := by
  obtain ⟨μ, hμp, hμ⟩ :=
    Uniqueness.Positivity.Witnesses.exists_canonical_normalized_law
  letI : IsProbabilityMeasure μ := hμp
  have hXex : ∀ e : Ioi (0 : ℝ),
      ∃ X : DistC → C(ℂ, ℝ), IsHeatSmoothing μ id e X := by
    intro e
    obtain ⟨X, -, hX⟩ := exists_heatVersion hμ e e.property
    exact ⟨X, hX⟩
  choose X0 hX0 using hXex
  obtain ⟨r₀, hr₀, hcanon⟩ :=
    exists_small_centered_point_upper_tail_of_inputs
      hS4 hPos ξ Q hQ m hm μ hμ X0 hX0 θ η hθ hη
  refine ⟨r₀, hr₀, ?_⟩
  intro Ω _ P _ h hh X hX r hrr₀ δ
  let e : Ioi (0 : ℝ) :=
    ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property.1 δ.property.1⟩
  let Ψ : C(ℂ, ℝ) → Prop := fun φ =>
    ENNReal.ofReal θ <
      edist ((normalizedContLFPP (ξ : ℝ) (m e) φ).pt 0)
        ((normalizedContLFPP (ξ : ℝ) (m e) φ).pt (r : ℂ))
  have hlaw : P.map h = μ := by
    have hh' := map_eq_of_candidate_normalized hh hμ
    rwa [Measure.map_id] at hh'
  have hY : ∀ᵐ ω ∂P, ∀ u,
      X e ω u = heatMollify (e : ℝ) (h ω) u :=
    B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh e (X e) (hX e)
  have hXv : ∀ᵐ g ∂μ, ∀ u,
      X0 e g u = heatMollify (e : ℝ) g u :=
    B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify μ id hμ e (X0 e) (hX0 e)
  change P {ω | Ψ (X e ω)} ≤ ENNReal.ofReal η
  exact (measure_le_of_pushed_heat_version P h
    hh.1.measurable.aemeasurable μ hlaw (e : ℝ)
    (X e) (X0 e) hY hXv Ψ).trans (by
      simpa only [Ψ, e] using hcanon r hrr₀ δ)

end SupercriticalLQGUniqueness.B2.DG20Lim
