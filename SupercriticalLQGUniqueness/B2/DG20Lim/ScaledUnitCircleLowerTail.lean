import SupercriticalLQGUniqueness.B2.DG20Lim.CanonicalCircleLowerTail
import SupercriticalLQGUniqueness.B2.Polylog.P4Prob

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_scaled_unit_circle_lower_tail_of_perc
    (hPerc : B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (X : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing μ id ε (X ε))
    (η : ℝ) (hη : 0 < η) :
    ∃ T ε₀ : ℝ, 0 < T ∧ 0 < ε₀ ∧
      ∀ (r : Ioi (0 : ℝ)) (δ : Ioo (0 : ℝ) 1),
        (δ : ℝ) < ε₀ →
        let e : Ioi (0 : ℝ) :=
          ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property δ.property.1⟩
        let d : Ioi (0 : ℝ) := ⟨(δ : ℝ), δ.property.1⟩
        let cr : DistC → ℝ := fun g => circleAvg (affineComp r 0 g) 1 0
        let Y : DistC → C(ℂ, ℝ) :=
          fun g => B2.Polylog.unitField (X e g) r (cr g)
        μ {g | finiteCircleCoords
          (normalizedContLFPP (ξ : ℝ) (m d) (Y g))
          (unitInnerCircle, unitOuterCircle) < ENNReal.ofReal T⁻¹} ≤
          ENNReal.ofReal η := by
  obtain ⟨T, ε₀, hT, hε₀, hunit⟩ :=
    exists_unit_circle_lower_tail_uniform_of_perc hPerc ξ m hm η hη
  refine ⟨T, ε₀, hT, hε₀, ?_⟩
  intro r δ hδ
  let d : Ioi (0 : ℝ) := ⟨(δ : ℝ), δ.property.1⟩
  let e : Ioi (0 : ℝ) :=
    ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property δ.property.1⟩
  let cr : DistC → ℝ := fun g => circleAvg (affineComp r 0 g) 1 0
  let Y : DistC → C(ℂ, ℝ) :=
    fun g => B2.Polylog.unitField (X e g) r (cr g)
  let Ψ : C(ℂ, ℝ) → Prop := fun φ =>
    finiteCircleCoords (normalizedContLFPP (ξ : ℝ) (m d) φ)
      (unitInnerCircle, unitOuterCircle) < ENNReal.ofReal T⁻¹
  have hYv : ∀ᵐ g ∂μ, ∀ u,
      Y g u = heatMollify (δ : ℝ) (B2.Polylog.gScale r g) u := by
    filter_upwards [B2.Polylog.ae_heatMollify_gScale hμ e r (X e) (hX e)] with g hg u
    have he : ((e : ℝ) / (r : ℝ)) = (δ : ℝ) := by
      dsimp [e]
      field_simp [(Set.mem_Ioi.mp r.property).ne']
    rw [← he]
    exact (hg u).symm
  have hXv : ∀ᵐ g ∂μ, ∀ u,
      X d g u = heatMollify (δ : ℝ) g u :=
    B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify μ id hμ d (X d) (hX d)
  have hsc := B2.Polylog.isWholePlaneGFF_gScale hμ.1 r.property
  have hlaw : μ.map (B2.Polylog.gScale r) = μ := by
    have hh := B2.Polylog.map_gScale hμ r.property
    rwa [Measure.map_id] at hh
  change μ {g | Ψ (Y g)} ≤ ENNReal.ofReal η
  exact (B2.Polylog.measure_le_of_scaled_version
    hsc.measurable.aemeasurable hlaw (δ : ℝ)
    Y (X d) hYv hXv Ψ).trans (by
      simpa only [Ψ, d] using hunit μ id hμ X hX δ hδ)

end SupercriticalLQGUniqueness.B2.DG20Lim
