import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledLargeAnnuliAE

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_large_annuli_on_coupled_limit_of_inputs
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
    (hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) :
    ∀ᵐ ω ∂P', ∀ N : ℕ,
      ∃ r : {r : ℚ // 1 < r}, (N : ℝ) < (r : ℚ) ∧
        ENNReal.ofReal ((N : ℝ) + 1) ≤ (Ylim ω).2.1
          (centeredInnerCircle 0 0 r.1 (lt_trans zero_lt_one r.property),
            centeredOuterCircle 0 0 r.1 (lt_trans zero_lt_one r.property)) := by
  apply ae_arbitrarily_large_centered_annuli_of_tail P' Ylim
  intro T η hT hη
  exact exists_large_coupled_circle_tail_of_inputs hS4 hPerc hPos
    ξ Q hQ m hm P P' h hh X hX ε hε Y Ylim
    hYm hLaw hConv T η hT hη

end SupercriticalLQGUniqueness.B2.DG20Lim
