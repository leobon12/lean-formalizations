import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodMarginal

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_eventual_localized_good_iteration64_of_inputsR32
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
    ∃ p c C : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ (x y r₀ : ℚ) (hr₀ : 0 < r₀)
        (S : Finset ℕ) (hS : S.Nonempty),
        ∀ᶠ n in atTop,
          P {ω | ∀ i ∈ S,
            ω ∉ localizedGoodEventR32 h (ξ : ℝ) (ε n) x y
              (ratRad64 r₀ i) (ratRad64_pos hr₀ i)
              (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2)} ≤
            ENNReal.ofReal (c * Real.exp (-a * S.card)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hiter⟩ := localized_good_iteration64R32 a ha
  let η : ℝ := (1 - p) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hpe : p + η ≤ 1 := by dsimp [η]; linarith
  obtain ⟨C, hC, hbound⟩ :=
    exists_localized_good_ratio_eventually_for_sequence_of_inputsR32
      hS4 hPerc ξ Q hQ m hm P h hh X hX ε hε η hη
  refine ⟨p, c, C, hp0, hp1, hc0, hC, ?_⟩
  intro x y r₀ hr₀ S hS
  let C' : ℝ≥0∞ := ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2
  have hηeq : ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) =
      ENNReal.ofReal η := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hgood : ∀ᶠ n in atTop, ∀ i ∈ S,
      ENNReal.ofReal p ≤ P (localizedGoodEventR32 h (ξ : ℝ) (ε n) x y
        (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C') := by
    apply (Filter.eventually_all_finset S).2
    intro i hi
    have hb := hbound x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i)
    filter_upwards [hb] with n hn
    apply measure_localizedGoodEvent_ge_of_bad_leR32 P h hh (ξ : ℝ) (ε n)
      x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C' p η hp0.le hη.le hpe
    simpa only [C', hηeq] using hn
  have hεsqrt : Tendsto (fun n => Real.sqrt (ε n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hε
  have hscale : ∀ᶠ n in atTop, ∀ i ∈ S,
      Real.sqrt (ε n : ℝ) < (ratRad64 r₀ i : ℝ) / 4 := by
    apply (Filter.eventually_all_finset S).2
    intro i hi
    have hrad : 0 < (ratRad64 r₀ i : ℝ) / 4 :=
      div_pos (Rat.cast_pos.mpr (ratRad64_pos hr₀ i)) (by norm_num)
    exact hεsqrt.eventually (eventually_lt_nhds hrad)
  filter_upwards [hgood, hscale] with n hgn hsn
  exact hiter P h hh (ξ : ℝ) (ε n) x y r₀ hr₀ S hS C' hsn hgn

end SupercriticalLQGUniqueness.B2.DG20Lim
