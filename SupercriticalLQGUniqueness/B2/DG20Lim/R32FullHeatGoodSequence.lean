import SupercriticalLQGUniqueness.B2.DG20Lim.GoodAnnulusNormalize
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalGoodSequence

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_full_heat_good_ratio_eventually_for_sequence_of_inputsR32
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ e, IsLFPPNormalizer ξ e (m e))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ e, IsHeatSmoothing P h e (X e))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y r : ℚ, ∀ hr : 0 < r,
        ∀ᶠ n in atTop,
          P {ω | ENNReal.ofReal C *
            setDist (lfppContMetric (ξ : ℝ) (X (ε n) ω) (X (ε n) ω).continuous)
              (centeredInnerCircleR32 x y r hr).toSet
              (centeredOuterCircleR32 x y r hr).toSet <
            (lfppContMetric (ξ : ℝ) (X (ε n) ω)
              (X (ε n) ω).continuous).aroundDist
              (centeredRatAnnulusR32 x y r hr).toSet
              (centeredInnerCircleR32 x y r hr).toSet
              (centeredOuterCircleR32 x y r hr).toSet} ≤
            ENNReal.ofReal η := by
  obtain ⟨C, hC, hb⟩ :=
    exists_rational_good_ratio_eventually_for_sequence_of_inputsR32
      hS4 hPerc ξ Q hQ m hm P h hh X hX ε hε η hη
  refine ⟨C, hC, ?_⟩
  intro x y r hr
  filter_upwards [hb x y r hr] with n hn
  convert hn using 1
  congr 1
  ext ω
  exact (lfpp_bad_ratio_iff_normalized (ξ : ℝ) (m (ε n))
    (X (ε n) ω) (centeredRatAnnulusR32 x y r hr).toSet
    (centeredInnerCircleR32 x y r hr).toSet
    (centeredOuterCircleR32 x y r hr).toSet (ENNReal.ofReal C)).symm

end SupercriticalLQGUniqueness.B2.DG20Lim
