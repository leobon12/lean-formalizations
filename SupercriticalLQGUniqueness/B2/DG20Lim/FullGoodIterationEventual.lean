import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteGoodEvents
import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodIterationEventual

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_eventual_full_good_iteration64_of_inputs
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
    (a : ℝ) (ha : 0 < a) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (η : ℝ), 0 < η →
      ∀ (x y r₀ : ℚ) (hr₀ : 0 < r₀)
        (S : Finset ℕ) (hS : S.Nonempty),
        ∀ᶠ n in atTop,
          P (allGoodFail (fun n i =>
            fullHeatGoodEvent (X (ε n)) (ξ : ℝ) x y
              (ratRad64 r₀ i) (ratRad64_pos hr₀ i)
              (ENNReal.ofReal 2 *
                (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) *
                ENNReal.ofReal 2)) S n) ≤
            ENNReal.ofReal (c * Real.exp (-a * S.card)) + ENNReal.ofReal η := by
  obtain ⟨p, c, C, hp0, hp1, hc0, hC, hbound⟩ :=
    exists_eventual_localized_good_iteration64_of_inputs
      hS4 hPerc ξ Q hQ m hm P h hh X hX ε hε a ha
  refine ⟨c, C, hc0, hC, ?_⟩
  intro η hη x y r₀ hr₀ S hS
  let C' : ℝ≥0∞ := ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2
  let A : ℕ → ℕ → Set Ω := fun n i =>
    localizedGoodEvent h (ξ : ℝ) (ε n) x y
      (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C'
  let B : ℕ → ℕ → Set Ω := fun n i =>
    fullHeatGoodEvent (X (ε n)) (ξ : ℝ) x y
      (ratRad64 r₀ i) (ratRad64_pos hr₀ i)
      (ENNReal.ofReal 2 * C' * ENNReal.ofReal 2)
  have hA : ∀ n i, i ∈ S → NullMeasurableSet (A n i) P := by
    intro n i hi
    exact nullMeasurableSet_localizedGoodEvent h hh (ξ : ℝ) (ε n)
      x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C'
  have hB : ∀ n i, i ∈ S → NullMeasurableSet (B n i) P := by
    intro n i hi
    exact nullMeasurableSet_fullHeatGoodEvent P h hh X hX (ξ : ℝ) (ε n)
      x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i)
      (ENNReal.ofReal 2 * C' * ENNReal.ofReal 2)
  have himp : ∀ i ∈ S, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∈ A n i → ω ∈ B n i := by
    intro i hi
    filter_upwards [ae_eventually_full_good_of_local_good h hh X hX
      (ξ : ℝ) ε hε x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i)]
      with ω hω
    filter_upwards [hω] with n hn
    intro hgood
    have hg : (lfppContMetric (ξ : ℝ)
        (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω))
        (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω)).continuous).aroundDist
          (centeredRatAnnulus x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i)).toSet
          (centeredInnerCircle x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i)).toSet
          (centeredOuterCircle x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i)).toSet ≤
        C' * setDist (lfppContMetric (ξ : ℝ)
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε n : ℝ) (ε n).property (h ω)).continuous)
          (centeredInnerCircle x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i)).toSet
          (centeredOuterCircle x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i)).toSet := by
      simpa only [A, localizedGoodEvent, mem_setOf_eq, finiteAroundCoords,
        finiteCircleCoords, centeredRatAnnulus] using hgood
    have hf := hn C' hg
    simpa only [B, fullHeatGoodEvent, mem_setOf_eq, finiteAroundCoords,
      finiteCircleCoords, centeredRatAnnulus] using hf
  have hb : ∀ᶠ n in atTop, P (allGoodFail A S n) ≤
      ENNReal.ofReal (c * Real.exp (-a * S.card)) := by
    simpa only [A, C', allGoodFail] using hbound x y r₀ hr₀ S hS
  have hres := eventually_measure_allGoodFail_le_of_ae_eventual_good_imp
    A B S hA hB himp (ENNReal.ofReal_pos.mpr hη) hb
  simpa only [B, C'] using hres

end SupercriticalLQGUniqueness.B2.DG20Lim
