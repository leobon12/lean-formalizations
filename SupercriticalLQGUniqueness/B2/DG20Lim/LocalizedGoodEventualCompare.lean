import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodHeatCompare

 


set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_eventually_localized_lfpp_compare_on_buffer
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (x y r : ℚ) :
    ∀ᵐ ω ∂P,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z w : ℂ,
        lfppLocOn ξ ε hε (h ω) (bufferedCenteredAnnulus x y r) z w ≤
          ENNReal.ofReal 2 *
            lfppDOn ξ (heatMollify ε (h ω)) (bufferedCenteredAnnulus x y r) z w ∧
        lfppDOn ξ (heatMollify ε (h ω)) (bufferedCenteredAnnulus x y r) z w ≤
          ENNReal.ofReal 2 *
            lfppLocOn ξ ε hε (h ω) (bufferedCenteredAnnulus x y r) z w := by
  filter_upwards [B2.DG20Pt.dg20_gff_localized_approx hh
    (isBounded_bufferedCenteredAnnulus x y r) ξ] with ω hω
  exact hω.2.2 2 (by norm_num)

theorem ae_eventually_localized_lfpp_compare_on_buffer_sequence
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (x y r : ℚ)
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ z w : ℂ,
        lfppLocOn ξ (ε n : ℝ) (ε n).property (h ω)
            (bufferedCenteredAnnulus x y r) z w ≤
          ENNReal.ofReal 2 *
            lfppDOn ξ (heatMollify (ε n : ℝ) (h ω))
              (bufferedCenteredAnnulus x y r) z w ∧
        lfppDOn ξ (heatMollify (ε n : ℝ) (h ω))
            (bufferedCenteredAnnulus x y r) z w ≤
          ENNReal.ofReal 2 *
            lfppLocOn ξ (ε n : ℝ) (ε n).property (h ω)
              (bufferedCenteredAnnulus x y r) z w := by
  have hε' : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hε, Eventually.of_forall fun n => (ε n).property⟩
  filter_upwards [ae_eventually_localized_lfpp_compare_on_buffer hh ξ x y r] with ω hω
  exact hε'.eventually hω |>.mono fun n hn => hn (ε n).property

end SupercriticalLQGUniqueness.B2.DG20Lim
