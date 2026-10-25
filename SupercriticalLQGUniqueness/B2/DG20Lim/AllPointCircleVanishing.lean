import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledPointCircleVanishing

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_all_coupled_point_circle_vanishing_of_inputs
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
    (hRData : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2) :
    ∀ᵐ ω ∂P', ∀ Z : RatCircle, Z.radius = 0 →
      ∀ O : ℕ → RatCircle,
        (∀ᶠ n in atTop, (O n).Surrounds Z.center) →
        Tendsto (fun n => ((O n).radius : ℝ)) atTop (𝓝 0) →
        Tendsto (fun n => (Ylim ω).2.1 (Z, O n)) atTop (𝓝 0) := by
  apply ae_all_iff.mpr
  intro Z
  by_cases hZ : Z.radius = 0
  · have hV := ae_coupled_point_circle_vanishing_of_inputs
      hS4 hPos ξ Q hQ m hm P P' h hh X hX ε hε Y Ylim
      hYm hLaw hConv hRData Z hZ
    filter_upwards [hV] with ω hω _ O hO hr
    obtain ⟨R, hAcross, -, hvan⟩ := hω
    simpa only [hAcross] using hvan O hO hr
  · exact ae_of_all _ (fun ω h => (hZ h).elim)

end SupercriticalLQGUniqueness.B2.DG20Lim
