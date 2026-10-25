import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteGoodEventMeasurable

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem measurable_local_lfpp_metric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (e : Ioi (0 : ℝ)) :
    Measurable (fun ω => lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (e : ℝ) e.property (h ω))
      (LQGMetric.DFGPS.L217.locMollifyC (e : ℝ) e.property (h ω)).continuous) := by
  have hM : Measurable (fun φ : C(ℂ, ℝ) =>
      lfppContMetric ξ φ φ.continuous) := by
    convert (measurable_normalizedContLFPP ξ
      (⟨1, by norm_num⟩ : Ioi (0 : ℝ))) using 1
    funext φ
    exact (normalizedContLFPP_one ξ φ).symm
  exact hM.comp ((LQGMetric.DFGPS.L217.measurable_locMollifyC
    (e : ℝ) e.property).comp hh.1.measurable)

theorem exists_localized_good_ratio_eventually_for_sequence_of_inputs
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
          P {ω | (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) *
            finiteCircleCoords
              (lfppContMetric (ξ : ℝ)
                (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω))
                (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω)).continuous)
              (centeredInnerCircle x y r hr, centeredOuterCircle x y r hr) <
            finiteAroundCoords
              (lfppContMetric (ξ : ℝ)
                (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω))
                (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω)).continuous)
              (centeredRatAnnulus x y r hr)} ≤
            ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := by
  have hη2 : 0 < η / 2 := by linarith
  obtain ⟨C, hC, hbound⟩ :=
    exists_full_heat_good_ratio_eventually_for_sequence_of_inputs
      hS4 hPerc ξ Q hQ m hm P h hh X hX ε hε (η / 2) hη2
  refine ⟨C, hC, ?_⟩
  intro x y r hr
  let A : RatAnnulus := centeredRatAnnulus x y r hr
  let Dloc : ℕ → Ω → ContMetric := fun n ω => lfppContMetric (ξ : ℝ)
    (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω))
    (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω)).continuous
  let Dfull : ℕ → Ω → ContMetric := fun n ω =>
    lfppContMetric (ξ : ℝ) (X (ε n) ω) (X (ε n) ω).continuous
  let Aloc : ℕ → Set Ω := fun n => {ω | (ENNReal.ofReal 2 *
    ENNReal.ofReal C * ENNReal.ofReal 2) * finiteCircleCoords (Dloc n ω)
      (A.inner, A.outer) < finiteAroundCoords (Dloc n ω) A}
  let Bfull : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal C *
    finiteCircleCoords (Dfull n ω) (A.inner, A.outer) <
    finiteAroundCoords (Dfull n ω) A}
  have hi : A.inner = centeredInnerCircle x y r hr := rfl
  have ho : A.outer = centeredOuterCircle x y r hr := rfl
  have hAm : ∀ n, NullMeasurableSet (Aloc n) P := by
    intro n
    exact nullMeasurableSet_finite_bad_ratio (Dloc n)
      (measurable_local_lfpp_metric hh (ξ : ℝ) (ε n)).aemeasurable A _
  have hBm : ∀ n, NullMeasurableSet (Bfull n) P := by
    intro n
    exact nullMeasurableSet_finite_bad_ratio (Dfull n)
      (aemeasurable_full_heat_lfpp_metric P h hh (ξ : ℝ) (ε n)
        (X (ε n)) (hX (ε n))) A _
  have himp : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ Aloc n → ω ∈ Bfull n := by
    filter_upwards [ae_eventually_localized_good_of_full_good h hh X hX
      (ξ : ℝ) ε hε x y r hr] with ω hω
    filter_upwards [hω] with n hn
    intro ha
    by_contra hb
    have hgood : (Dfull n ω).aroundDist A.toSet A.inner.toSet A.outer.toSet ≤
        ENNReal.ofReal C * setDist (Dfull n ω) A.inner.toSet A.outer.toSet :=
      le_of_not_gt hb
    have hloc := hn (ENNReal.ofReal C) hgood
    exact not_le_of_gt ha hloc
  have hb : ∀ᶠ n in atTop, P (Bfull n) ≤ ENNReal.ofReal (η / 2) := by
    simpa only [Bfull, Dfull, finiteCircleCoords, finiteAroundCoords, hi, ho, A] using
      hbound x y r hr
  have hresult := eventually_measure_le_of_ae_eventually_imp_null
    hAm hBm himp (ENNReal.ofReal_pos.mpr hη2) hb
  simpa only [Aloc, Dloc, hi, ho, A] using hresult

end SupercriticalLQGUniqueness.B2.DG20Lim
