import SupercriticalLQGUniqueness.B2.DG20Lim.TranslatedNearPointTail
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteZeroCirclePoint

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_small_finite_point_coord_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (Z : RatCircle) (hZ : Z.radius = 0)
    (θ η : ℝ) (hθ : 0 < θ) (hη : 0 < η) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ (r : Ioo (0 : ℝ) 1), (r : ℝ) ≤ r₀ →
      ∀ (δ : Ioo (0 : ℝ) 1),
      ∀ (W : RatCircle), W.radius = 0 → W.center = Z.center + (r : ℂ) →
        let e : Ioi (0 : ℝ) :=
          ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property.1 δ.property.1⟩
        let D : Ω → ContMetric := fun ω =>
          normalizedContLFPP (ξ : ℝ) (m e) (X e ω)
        let hD := aemeasurable_normalizedContLFPP_heat_version P h hh
          e (m e) (ξ : ℝ) (X e) (hX e)
        P {ω | ENNReal.ofReal θ <
          (measurableRatCoordsVersion D hD ω).1 (Z, W)} ≤
          ENNReal.ofReal η := by
  obtain ⟨r₀, hr₀, htail⟩ :=
    exists_small_translated_point_upper_tail_of_inputs
      hS4 hPos ξ Q hQ m hm P h hh X hX Z.center θ η hθ hη
  refine ⟨r₀, hr₀, ?_⟩
  intro r hrr₀ δ W hW hWcenter
  let e : Ioi (0 : ℝ) :=
    ⟨(r : ℝ) * (δ : ℝ), mul_pos r.property.1 δ.property.1⟩
  let D : Ω → ContMetric := fun ω =>
    normalizedContLFPP (ξ : ℝ) (m e) (X e ω)
  let hD := aemeasurable_normalizedContLFPP_heat_version P h hh
    e (m e) (ξ : ℝ) (X e) (hX e)
  have hEq := ae_eq_measurableRatCoordsVersion D hD
  have hsub :
      P {ω | ENNReal.ofReal θ <
        (measurableRatCoordsVersion D hD ω).1 (Z, W)} ≤
      P {ω | ENNReal.ofReal θ <
        edist ((D ω).pt Z.center) ((D ω).pt (Z.center + (r : ℂ)))} := by
    apply measure_mono_ae
    filter_upwards [hEq] with ω hω hbad
    have hc := congrArg (fun q : RatCoords => q.1 (Z, W)) hω
    rw [← hc] at hbad
    simpa only [finiteRatCoords, Prod.fst,
      finiteCircleCoords_zero_zero (D ω) Z W hZ hW, hWcenter] using hbad
  change P {ω | ENNReal.ofReal θ <
    (measurableRatCoordsVersion D hD ω).1 (Z, W)} ≤
    ENNReal.ofReal η
  exact hsub.trans (by simpa only [D, e] using htail r hrr₀ δ)

end SupercriticalLQGUniqueness.B2.DG20Lim
