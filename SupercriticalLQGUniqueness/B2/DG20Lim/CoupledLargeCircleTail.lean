import SupercriticalLQGUniqueness.B2.DG20Lim.LargeFiniteCircleCoordTail
import SupercriticalLQGUniqueness.B2.DG20Lim.CircleCoordLimitProbability

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_large_coupled_circle_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ e, IsLFPPNormalizer ξ e (m e))
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hYm : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (aemeasurable_normalizedContLFPP_heat_version P h hh
          (ε n) (m (ε n)) (ξ : ℝ) (X (ε n)) (hX (ε n))) ω)))
    (hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)))
    (T η : ℝ) (hT : 0 < T) (hη : 0 < η) :
    ∃ R₀ : ℝ, 1 < R₀ ∧
      ∀ (r : ℚ) (hr : 1 < r), R₀ ≤ (r : ℝ) →
        P' {ω | (Ylim ω).2.1
          (centeredInnerCircle 0 0 r (lt_trans zero_lt_one hr),
            centeredOuterCircle 0 0 r (lt_trans zero_lt_one hr)) <
          ENNReal.ofReal T} ≤ ENNReal.ofReal η := by
  obtain ⟨R₀, ε₀, hR₀, hε₀, htail⟩ :=
    exists_large_finite_circle_coord_tail_of_inputs
      hS4 hPerc hPos ξ Q hQ m hm T η hT hη
  let V : ℕ → Ω → (CoordJ → ℝ) × RatCoords := fun n ω =>
    (pairJ ⊤ (h ω), measurableRatCoordsVersion
      (fun ω => normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω))
      (aemeasurable_normalizedContLFPP_heat_version P h hh
        (ε n) (m (ε n)) (ξ : ℝ) (X (ε n)) (hX (ε n))) ω)
  have hVm : ∀ n, Measurable (V n) := by
    intro n
    exact ((measurable_pairJ ⊤).comp hh.1.measurable).prodMk
      (measurable_measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (aemeasurable_normalizedContLFPP_heat_version P h hh
          (ε n) (m (ε n)) (ξ : ℝ) (X (ε n)) (hX (ε n))))
  refine ⟨R₀, hR₀, ?_⟩
  intro r hr hrR
  let Z := centeredInnerCircle 0 0 r (lt_trans zero_lt_one hr)
  let W := centeredOuterCircle 0 0 r (lt_trans zero_lt_one hr)
  have hev : ∀ᶠ n in atTop, (ε n : ℝ) < min 1 ε₀ :=
    hε.eventually (Iio_mem_nhds (lt_min zero_lt_one hε₀))
  have hfinite : ∀ᶠ n in atTop,
      P {ω | (V n ω).2.1 (Z, W) < ENNReal.ofReal T} ≤
        ENNReal.ofReal η := by
    filter_upwards [hev] with n hn
    let e : Ioo (0 : ℝ) 1 :=
      ⟨(ε n : ℝ), (ε n).property, hn.trans_le (min_le_left _ _)⟩
    have he : (⟨(e : ℝ), e.property.1⟩ : Ioi (0 : ℝ)) = ε n := by
      apply Subtype.ext
      rfl
    have ht := htail P h hh X hX r hr e hrR
      (hn.trans_le (min_le_right _ _))
    simpa only [V, he, Z, W] using ht
  exact circle_coord_limit_lower_probability P P' V Y Ylim
    hVm hYm (by simpa only [V] using hLaw) hConv Z W
    (ENNReal.ofReal T) (ENNReal.ofReal η) hfinite

end SupercriticalLQGUniqueness.B2.DG20Lim
