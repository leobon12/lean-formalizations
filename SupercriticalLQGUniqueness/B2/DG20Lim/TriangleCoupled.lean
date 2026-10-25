import SupercriticalLQGUniqueness.B2.DG20Lim.GoodCircleCoupled
import SupercriticalLQGUniqueness.B2.DG20Lim.NestedGoodTriangle

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_triangle_on_coupled_limit_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
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
    (hRData : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2) :
    ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      ∀ x y z : ℂ,
        R.DfromR x z ≤ R.DfromR x y + R.DfromR y z := by
  obtain ⟨C, hC, hGood⟩ :=
    exists_nested_good_circles_on_coupled_limit_of_inputs
      hS4 hPerc ξ Q hQ m hm P P' h hh X hX ε hε
      Y Ylim hYm hLaw hConv hRData
  let C' : ℝ≥0∞ := ENNReal.ofReal 2 *
    (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) * ENNReal.ofReal 2
  have hC' : C' ≠ ∞ := by
    dsimp [C']
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top <;> exact ENNReal.ofReal_ne_top
        · exact ENNReal.ofReal_ne_top
    · exact ENNReal.ofReal_ne_top
  filter_upwards [hGood] with ω hω
  obtain ⟨R, hAcross, hAround, hNested⟩ := hω
  refine ⟨R, hAcross, hAround, ?_⟩
  exact R.triangle_of_nested_good_annuli C' hC' hNested

end SupercriticalLQGUniqueness.B2.DG20Lim
