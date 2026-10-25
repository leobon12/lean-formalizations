import SupercriticalLQGUniqueness.B2.DG20Lim.GoodAnnulusLimitProbability

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_rational_good_ratio_eventually_for_sequence_of_inputs
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
            finiteCircleCoords
              (normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω))
              (centeredInnerCircle x y r hr,
                centeredOuterCircle x y r hr) <
            finiteAroundCoords
              (normalizedContLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω))
              (centeredRatAnnulus x y r hr)} ≤ ENNReal.ofReal η := by
  obtain ⟨C, δ₀, hC, hδ₀, hgood⟩ :=
    exists_rational_good_annulus_ratio_tail_of_inputs
      hS4 hPerc ξ Q hQ m hm η hη
  refine ⟨C, hC, ?_⟩
  intro x y r hr
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hthreshold : (0 : ℝ) < min ((r : ℝ) * δ₀) (r : ℝ) :=
    lt_min (mul_pos hrR hδ₀) hrR
  have hev : ∀ᶠ n in atTop,
      (ε n : ℝ) < min ((r : ℝ) * δ₀) (r : ℝ) :=
    hε.eventually (isOpen_Iio.mem_nhds hthreshold)
  filter_upwards [hev] with n hn
  have hnδ : (ε n : ℝ) / (r : ℝ) < δ₀ :=
    (div_lt_iff₀ hrR).mpr (by
      simpa only [mul_comm] using
        (lt_of_lt_of_le hn (min_le_left _ _)))
  have hn1 : (ε n : ℝ) / (r : ℝ) < 1 :=
    (div_lt_one hrR).mpr (lt_of_lt_of_le hn (min_le_right _ _))
  let δ : Ioo (0 : ℝ) 1 :=
    ⟨(ε n : ℝ) / (r : ℝ),
      ⟨div_pos (ε n).property hrR, hn1⟩⟩
  have he : (⟨(r : ℝ) * (δ : ℝ),
        mul_pos hrR δ.property.1⟩ : Ioi (0 : ℝ)) = ε n := by
    apply Subtype.ext
    dsimp [δ]
    exact mul_div_cancel₀ _ hrR.ne'
  have hb := hgood P h hh X hX x y r hr δ hnδ
  simpa only [he] using hb

end SupercriticalLQGUniqueness.B2.DG20Lim
