import SupercriticalLQGUniqueness.B2.DG20Lim.CircleCoordPositive
import SupercriticalLQGUniqueness.B2.DG20Lim.Section51FiniteBounds

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_all_positive_circle_coords_of_section51
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {Ω : Type} {Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hYm : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ)
          (m (ε (φ n))) (X (ε (φ n)) ω))
        (aemeasurable_normalizedContLFPP_heat_version P h hh
          (ε (φ n)) (m (ε (φ n))) (ξ : ℝ)
          (X (ε (φ n))) (hX (ε (φ n)))) ω)))
    (hConv : ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) :
    ∀ᵐ ω ∂P', ∀ O Pcircle : RatCircle,
      Disjoint O.toSet Pcircle.toSet →
        0 < (Ylim ω).2.1 (O, Pcircle) := by
  exact ae_all_positive_circle_coords_of_joint_law hPerc ξ m hm
    ε hε φ hφ P P' h hh X hX Y Ylim hYm
    (fun n => aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε (φ n)) (m (ε (φ n))) (ξ : ℝ)
      (X (ε (φ n))) (hX (ε (φ n))))
    hLaw (Filter.Eventually.of_forall hConv)

end SupercriticalLQGUniqueness.B2.DG20Lim
