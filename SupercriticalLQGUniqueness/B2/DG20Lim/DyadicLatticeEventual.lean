import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicLatticeBorelCantelli

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_eventual_dyadic_lattice_good_on_coupled_limit_of_inputs
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
    (hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᵐ ω ∂P', ∀ R : ℕ, ∀ᶠ K in atTop,
        ∀ v ∈ dyadicLatticeBox R K,
          ¬ ω ∈ coupledSiteBad Ylim
            (ENNReal.ofReal 2 *
              (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) *
              ENNReal.ofReal 2) K v := by
  obtain ⟨c, C, hc, hC, hbad⟩ :=
    exists_dyadic_lattice_bad_bound_on_coupled_limit_of_inputs
      hS4 hPerc ξ Q hQ m hm P P' h hh X hX ε hε Y Ylim hYm hLaw hConv 120
      (by norm_num)
  refine ⟨C, hC, ?_⟩
  let C' : ℝ≥0∞ := ENNReal.ofReal 2 *
    (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) * ENNReal.ofReal 2
  have hR (R : ℕ) :
      ∀ᵐ ω ∂P', ∀ᶠ K in atTop,
        ∀ v ∈ dyadicLatticeBox R K,
          ¬ ω ∈ coupledSiteBad Ylim C' K v := by
    let E : ℕ → Set Ω' := fun K =>
      {ω | ∃ v ∈ dyadicLatticeBox R K, ω ∈ coupledSiteBad Ylim C' K v}
    have hb : ∀ K, 12 ≤ K →
        P' (E K) ≤ ((dyadicLatticeBox R K).card : ℝ≥0∞) *
          ENNReal.ofReal (c * Real.exp (-(120 : ℝ) *
            (sparseDyadicIndices K).card)) := by
      intro K hK
      exact hbad R K hK
    filter_upwards [ae_eventually_not_dyadic_bad_of_bound P' E R c hc.le hb] with ω hω
    filter_upwards [hω] with K hK
    intro v hv hsite
    exact hK ⟨v, hv, hsite⟩
  simpa only [C'] using (ae_all_iff.mpr hR)

end SupercriticalLQGUniqueness.B2.DG20Lim
