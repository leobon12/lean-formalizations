import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPPAffine
import SupercriticalLQGUniqueness.B2.DG20Lim.UnitGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.Polylog.P4Prob

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_centered_scaled_good_annulus_ratio_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (X : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing μ id ε (X ε))
    (η : ℝ) (hη : 0 < η) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
      ∀ r : Ioi (0 : ℝ), ∀ δ : Ioo (0 : ℝ) 1, (δ : ℝ) < δ₀ →
        let e : Ioi (0 : ℝ) :=
          ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property δ.property.1⟩
        let D : DistC → ContMetric :=
          fun g => normalizedContLFPP (ξ : ℝ) (m e) (X e g)
        let T : ℂ ≃ₜ ℂ := B2.Polylog.dilateHomeo r.property
        μ {g | ENNReal.ofReal C *
          LQGMetric.Blueprint.setDist (D g)
            (T '' unitInnerCircle.toSet) (T '' unitOuterCircle.toSet) <
          (D g).aroundDist (T '' unitRatAnnulus.toSet)
            (T '' unitInnerCircle.toSet) (T '' unitOuterCircle.toSet)} ≤
          ENNReal.ofReal η := by
  obtain ⟨C, δ₀, hC, hδ₀, hunit⟩ :=
    exists_unit_good_annulus_ratio_tail_of_inputs
      hS4 hPerc ξ Q hQ m hm μ id hμ X hX η hη
  refine ⟨C, δ₀, hC, hδ₀, ?_⟩
  intro r δ hδ
  let d : Ioi (0 : ℝ) := ⟨(δ : ℝ), δ.property.1⟩
  let e : Ioi (0 : ℝ) :=
    ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property δ.property.1⟩
  let T : ℂ ≃ₜ ℂ := B2.Polylog.dilateHomeo r.property
  let cr : DistC → ℝ :=
    fun g => circleAvg (affineComp r 0 g) 1 0
  let Y : DistC → C(ℂ, ℝ) :=
    fun g => B2.Polylog.unitField (X e g) r (cr g)
  let Ψ : C(ℂ, ℝ) → Prop := fun φ =>
    ENNReal.ofReal C *
      LQGMetric.Blueprint.setDist
        (normalizedContLFPP (ξ : ℝ) (m d) φ)
        unitInnerCircle.toSet unitOuterCircle.toSet <
      (normalizedContLFPP (ξ : ℝ) (m d) φ).aroundDist
        unitRatAnnulus.toSet unitInnerCircle.toSet unitOuterCircle.toSet
  have hYv : ∀ᵐ g ∂μ, ∀ u,
      Y g u = heatMollify (δ : ℝ) (B2.Polylog.gScale r g) u := by
    filter_upwards [B2.Polylog.ae_heatMollify_gScale hμ e r (X e) (hX e)] with g hg u
    have he : ((e : ℝ) / (r : ℝ)) = (δ : ℝ) := by
      dsimp [e]
      field_simp [(Set.mem_Ioi.mp r.property).ne']
    rw [← he]
    exact (hg u).symm
  have hXv : ∀ᵐ g ∂μ, ∀ u, X d g u = heatMollify (δ : ℝ) g u :=
    B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify μ id hμ d (X d) (hX d)
  have hsc := B2.Polylog.isWholePlaneGFF_gScale hμ.1 r.property
  have hlaw : μ.map (B2.Polylog.gScale r) = μ := by
    have hh := B2.Polylog.map_gScale hμ r.property
    rwa [Measure.map_id] at hh
  have hscale : ∀ g : DistC, Ψ (Y g) ↔
      ENNReal.ofReal C *
        LQGMetric.Blueprint.setDist
          (normalizedContLFPP (ξ : ℝ) (m e) (X e g))
          (T '' unitInnerCircle.toSet) (T '' unitOuterCircle.toSet) <
        (normalizedContLFPP (ξ : ℝ) (m e) (X e g)).aroundDist
          (T '' unitRatAnnulus.toSet)
          (T '' unitInnerCircle.toSet) (T '' unitOuterCircle.toSet) := by
    intro g
    have hφ : ∀ u, Y g u =
        X e g ((0 : ℂ) + (r : ℂ) * u) + -(cr g) := by
      intro u
      simp only [Y, B2.Polylog.unitField_apply, zero_add]
    have hT : ∀ u, T u = (0 : ℂ) + (r : ℂ) * u := by
      intro u
      have hh : T u = (r : ℝ) • u :=
        B2.Polylog.dilateHomeo_apply r.property u
      rw [hh, Complex.real_smul]
      simp
    exact normalizedContLFPP_good_iff_affine
      (ξ : ℝ) (m e) (m d)
      (by exact_mod_cast r.property.ne')
      (-(cr g)) hφ T hT
      unitRatAnnulus.toSet unitInnerCircle.toSet unitOuterCircle.toSet
      (ENNReal.ofReal C)
  change μ {g | ENNReal.ofReal C *
      LQGMetric.Blueprint.setDist
        (normalizedContLFPP (ξ : ℝ) (m e) (X e g))
        (T '' unitInnerCircle.toSet) (T '' unitOuterCircle.toSet) <
      (normalizedContLFPP (ξ : ℝ) (m e) (X e g)).aroundDist
        (T '' unitRatAnnulus.toSet)
        (T '' unitInnerCircle.toSet) (T '' unitOuterCircle.toSet)} ≤
    ENNReal.ofReal η
  calc
    μ {g | ENNReal.ofReal C *
        LQGMetric.Blueprint.setDist
          (normalizedContLFPP (ξ : ℝ) (m e) (X e g))
          (T '' unitInnerCircle.toSet) (T '' unitOuterCircle.toSet) <
        (normalizedContLFPP (ξ : ℝ) (m e) (X e g)).aroundDist
          (T '' unitRatAnnulus.toSet)
          (T '' unitInnerCircle.toSet) (T '' unitOuterCircle.toSet)}
        = μ {g | Ψ (Y g)} := by
          congr 1
          ext g
          exact (hscale g).symm
    _ ≤ μ {g | Ψ (X d g)} :=
      B2.Polylog.measure_le_of_scaled_version
        hsc.measurable.aemeasurable hlaw (δ : ℝ)
        Y (X d) hYv hXv Ψ
    _ ≤ ENNReal.ofReal η := by
      simpa only [Ψ, d, finiteCircleCoords, finiteAroundCoords,
        unitRatAnnulus] using hunit δ hδ

end SupercriticalLQGUniqueness.B2.DG20Lim
