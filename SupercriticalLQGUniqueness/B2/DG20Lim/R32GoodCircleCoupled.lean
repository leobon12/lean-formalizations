import SupercriticalLQGUniqueness.B2.DG20Lim.R32GoodAnnulusNested

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_nested_good_circles_on_coupled_limit_of_inputsR32
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
    ∃ C : ℝ, 0 < C ∧
      ∀ᵐ ω ∂P', ∃ R : RData,
        R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
        R.around = (Ylim ω).2.2 ∧
        ∀ z : ℂ, ∃ B : ℕ → RatAnnulus,
          (∀ n, ∃ (x y r : ℚ) (hr : 0 < r), B n = centeredRatAnnulusR32 x y r hr) ∧
          (∀ n, (B n).inner.Surrounds z ∧
            R.around (B n) ≤
              (ENNReal.ofReal 2 *
                (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) *
                ENNReal.ofReal 2) *
                R.across (B n).inner (B n).outer) ∧
          (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
          Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hGood⟩ :=
    exists_eventual_dyadic_lattice_good_on_coupled_limit_of_inputsR32
      hS4 hPerc ξ Q hQ m hm P P' h hh X hX ε hε Y Ylim hYm hLaw hConv
  refine ⟨C, hC, ?_⟩
  let C' : ℝ≥0∞ := ENNReal.ofReal 2 *
    (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) * ENNReal.ofReal 2
  have hRG := ae_eventually_good_lattice_rdata_of_coord_goodR32
    P' Ylim C' hRData hGood
  filter_upwards [hRG] with ω hω
  obtain ⟨R, hA, hB, hsite⟩ := hω
  refine ⟨R, hA, hB, ?_⟩
  intro z
  exact R.exists_nested_good_annulus_sequenceR32 C' hsite z

end SupercriticalLQGUniqueness.B2.DG20Lim
