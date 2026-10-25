import SupercriticalLQGUniqueness.B2.DG20Lim.TranslatedGoodAnnulusRatio

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem exists_uniform_good_annulus_ratio_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (η : ℝ) (hη : 0 < η) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
      ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
        (∀ e, IsHeatSmoothing P h e (X e)) →
      ∀ z : ℂ, ∀ r : Ioi (0 : ℝ), ∀ δ : Ioo (0 : ℝ) 1,
        (δ : ℝ) < δ₀ →
        let e : Ioi (0 : ℝ) :=
          ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property δ.property.1⟩
        let D : Ω → ContMetric :=
          fun ω => normalizedContLFPP (ξ : ℝ) (m e) (X e ω)
        let T : ℂ ≃ₜ ℂ := B2.Polylog.dilateHomeo r.property
        let U : ℂ ≃ₜ ℂ := Homeomorph.addRight z
        P {ω | ENNReal.ofReal C *
          LQGMetric.Blueprint.setDist (D ω)
            (U '' (T '' unitInnerCircle.toSet))
            (U '' (T '' unitOuterCircle.toSet)) <
          (D ω).aroundDist
            (U '' (T '' unitRatAnnulus.toSet))
            (U '' (T '' unitInnerCircle.toSet))
            (U '' (T '' unitOuterCircle.toSet))} ≤
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
  obtain ⟨C, δ₀, hC, hδ₀, hcanon⟩ :=
    exists_uniform_translated_scaled_good_ratio_tail_of_inputs
      hS4 hPerc ξ Q hQ m hm μ hμ X0 hX0 η hη
  refine ⟨C, δ₀, hC, hδ₀, ?_⟩
  intro Ω _ P _ h hh X hX z r δ hδ
  let e : Ioi (0 : ℝ) :=
    ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property δ.property.1⟩
  let T : ℂ ≃ₜ ℂ := B2.Polylog.dilateHomeo r.property
  let U : ℂ ≃ₜ ℂ := Homeomorph.addRight z
  let Ψ : C(ℂ, ℝ) → Prop := fun φ =>
    ENNReal.ofReal C *
      LQGMetric.Blueprint.setDist
        (normalizedContLFPP (ξ : ℝ) (m e) φ)
        (U '' (T '' unitInnerCircle.toSet))
        (U '' (T '' unitOuterCircle.toSet)) <
      (normalizedContLFPP (ξ : ℝ) (m e) φ).aroundDist
        (U '' (T '' unitRatAnnulus.toSet))
        (U '' (T '' unitInnerCircle.toSet))
        (U '' (T '' unitOuterCircle.toSet))
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
    (X e) (X0 e) hY hXv Ψ).trans
      (hcanon z r δ hδ)

end SupercriticalLQGUniqueness.B2.DG20Lim
