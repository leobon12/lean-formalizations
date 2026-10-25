import SupercriticalLQGUniqueness.B2.DG20Lim.FinitePointCoordTail
import SupercriticalLQGUniqueness.B2.DG20Lim.PointCoordLimitProbability

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_small_coupled_point_coord_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPos : B2.Iface.DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
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
    (Z : RatCircle) (hZ : Z.radius = 0)
    (θ η : ℝ) (hθ : 0 < θ) (hη : 0 < η) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ (r : Ioo (0 : ℝ) 1), (r : ℝ) ≤ r₀ →
      ∀ (W : RatCircle), W.radius = 0 → W.center = Z.center + (r : ℂ) →
        P' {ω | ENNReal.ofReal θ < (Ylim ω).2.1 (Z, W)} ≤
          ENNReal.ofReal η := by
  obtain ⟨r₀, hr₀, htail⟩ :=
    exists_small_finite_point_coord_tail_of_inputs
      hS4 hPos ξ Q hQ m hm P h hh X hX Z hZ θ η hθ hη
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
  refine ⟨r₀, hr₀, ?_⟩
  intro r hrr₀ W hW hWcenter
  have hev : ∀ᶠ n in atTop, (ε n : ℝ) < (r : ℝ) :=
    hε.eventually (Iio_mem_nhds r.property.1)
  have hfinite : ∀ᶠ n in atTop,
      P {ω | ENNReal.ofReal θ < (V n ω).2.1 (Z, W)} ≤
        ENNReal.ofReal η := by
    filter_upwards [hev] with n hn
    let δ : Ioo (0 : ℝ) 1 :=
      ⟨(ε n : ℝ) / (r : ℝ), div_pos (ε n).property r.property.1,
        (div_lt_one r.property.1).mpr hn⟩
    have he : (⟨(r : ℝ) * (δ : ℝ),
        mul_pos r.property.1 δ.property.1⟩ : Ioi (0 : ℝ)) = ε n := by
      apply Subtype.ext
      dsimp [δ]
      field_simp [r.property.1.ne']
    have ht := htail r hrr₀ δ W hW hWcenter
    simpa only [V, he] using ht
  exact point_coord_limit_upper_probability P P' V Y Ylim
    hVm hYm (by simpa only [V] using hLaw) hConv Z W
    (ENNReal.ofReal θ) (ENNReal.ofReal η) hfinite

end SupercriticalLQGUniqueness.B2.DG20Lim
