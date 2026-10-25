import SupercriticalLQGUniqueness.B2.DG20Lim.LargeCircleLowerTailAny
import SupercriticalLQGUniqueness.B2.DG20Lim.CenteredCircleScale
import SupercriticalLQGUniqueness.B2.DG20Lim.FinitePointCoordTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_large_finite_circle_coord_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ e, IsLFPPNormalizer ξ e (m e))
    (T η : ℝ) (hT : 0 < T) (hη : 0 < η) :
    ∃ R₀ ε₀ : ℝ, 1 < R₀ ∧ 0 < ε₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC)
        (hh : IsNormalizedWholePlaneGFF h P)
        (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
        (hX : ∀ e, IsHeatSmoothing P h e (X e))
        (r : ℚ) (hr : 1 < r) (e : Ioo (0 : ℝ) 1),
        R₀ ≤ (r : ℝ) → (e : ℝ) < ε₀ →
        let Z := centeredInnerCircle 0 0 r (lt_trans zero_lt_one hr)
        let W := centeredOuterCircle 0 0 r (lt_trans zero_lt_one hr)
        let d : Ioi (0 : ℝ) := ⟨(e : ℝ), e.property.1⟩
        let D : Ω → ContMetric := fun ω =>
          normalizedContLFPP (ξ : ℝ) (m d) (X d ω)
        let hD := aemeasurable_normalizedContLFPP_heat_version P h hh
          d (m d) (ξ : ℝ) (X d) (hX d)
        P {ω | (measurableRatCoordsVersion D hD ω).1 (Z, W) <
          ENNReal.ofReal T} ≤ ENNReal.ofReal η := by
  obtain ⟨R₀, ε₀, hR₀, hε₀, htail⟩ :=
    exists_large_circle_lower_tail_any_of_inputs
      hS4 hPerc hPos ξ Q hQ m hm T η hT hη
  refine ⟨R₀, ε₀, hR₀, hε₀, ?_⟩
  intro Ω _ P _ h hh X hX r hr e hrR he
  let hr0 : 0 < r := lt_trans zero_lt_one hr
  let Z := centeredInnerCircle 0 0 r hr0
  let W := centeredOuterCircle 0 0 r hr0
  let d : Ioi (0 : ℝ) := ⟨(e : ℝ), e.property.1⟩
  let D : Ω → ContMetric := fun ω =>
    normalizedContLFPP (ξ : ℝ) (m d) (X d ω)
  let hD := aemeasurable_normalizedContLFPP_heat_version P h hh
    d (m d) (ξ : ℝ) (X d) (hX d)
  let rr : Ioi (1 : ℝ) :=
    ⟨(r : ℝ), Set.mem_Ioi.mpr (by exact_mod_cast hr)⟩
  have hI : (B2.Polylog.dilateHomeo
      (lt_trans one_pos rr.property)) '' unitInnerCircle.toSet = Z.toSet := by
    simpa only [rr, Z] using centeredInnerCircle_zero_scale r hr0
  have hO : (B2.Polylog.dilateHomeo
      (lt_trans one_pos rr.property)) '' unitOuterCircle.toSet = W.toSet := by
    simpa only [rr, W] using centeredOuterCircle_zero_scale r hr0
  have hEq := ae_eq_measurableRatCoordsVersion D hD
  have hsub :
      P {ω | (measurableRatCoordsVersion D hD ω).1 (Z, W) <
        ENNReal.ofReal T} ≤
      P {ω | LQGMetric.Blueprint.setDist (D ω) Z.toSet W.toSet <
        ENNReal.ofReal T} := by
    apply measure_mono_ae
    filter_upwards [hEq] with ω hω hw
    have hc := congrArg (fun q : RatCoords => q.1 (Z, W)) hω
    rw [← hc] at hw
    simpa only [finiteRatCoords, Prod.fst, finiteCircleCoords] using hw
  change P {ω | (measurableRatCoordsVersion D hD ω).1 (Z, W) <
    ENNReal.ofReal T} ≤ ENNReal.ofReal η
  exact hsub.trans (by
    simpa only [D, d, hI, hO] using
      htail P h hh X hX rr e hrR he)

end SupercriticalLQGUniqueness.B2.DG20Lim
