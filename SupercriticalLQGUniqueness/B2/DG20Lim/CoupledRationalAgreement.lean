import SupercriticalLQGUniqueness.B2.DG20Lim.AllPointCircleVanishing
import SupercriticalLQGUniqueness.B2.DG20Lim.EqualCenterPointCoord
import SupercriticalLQGUniqueness.B2.DG20Lim.RationalAgreementGood
import SupercriticalLQGUniqueness.B2.DG20Lim.GoodCircleCoupled

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_rational_agreement_on_coupled_limit_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
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
    ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 ∧
      ∀ Z W : RatCircle, Z.radius = 0 → W.radius = 0 →
        R.across Z W = R.DfromR Z.center W.center := by
  obtain ⟨C, hC, hGood⟩ :=
    exists_nested_good_circles_on_coupled_limit_of_inputs
      hS4 hPerc ξ Q hQ m hm P P' h hh X hX ε hε
      Y Ylim hYm hLaw hConv hRData
  have hV := ae_all_coupled_point_circle_vanishing_of_inputs
    hS4 hPos ξ Q hQ m hm P P' h hh X hX ε hε
    Y Ylim hYm hLaw hConv hRData
  let D : ℕ → Ω → ContMetric := fun n ω =>
    normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω)
  have hD : ∀ n, AEMeasurable (D n) P := by
    intro n
    exact aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε n) (m (ε n)) (ξ : ℝ) (X (ε n)) (hX (ε n))
  have hZero := ae_equal_center_point_coord_zero_of_joint_law
    P P' h hh.1.measurable D hD Y Ylim hYm
    (by simpa only [D] using hLaw) hConv
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
  filter_upwards [hGood, hV, hZero] with ω hG hVω hZω
  obtain ⟨R, hAcross, hAround, hNested⟩ := hG
  refine ⟨R, hAcross, hAround, ?_⟩
  intro Z W hZ hW
  by_cases hZW : Z.center = W.center
  · have hzero : R.across Z W = 0 := by
      rw [hAcross]
      exact hZω Z W hZ hW hZW
    rw [hzero, hZW, R.DfromR_self]
  · apply R.across_zero_eq_DfromR_of_nested_good
      C' hC' Z W hZ hW hZW hNested
    · intro O hO hr
      simpa only [hAcross] using hVω Z hZ O hO hr
    · intro O hO hr
      simpa only [hAcross] using hVω W hW O hO hr

end SupercriticalLQGUniqueness.B2.DG20Lim
