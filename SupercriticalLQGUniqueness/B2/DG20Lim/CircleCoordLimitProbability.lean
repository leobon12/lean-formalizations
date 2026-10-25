import SupercriticalLQGUniqueness.B2.DG20Lim.OpenEventLimitProbability
import SupercriticalLQGUniqueness.B2.DG20Lim.RationalUpper

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem circle_coord_limit_lower_probability
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P']
    (V : ℕ → Ω → (CoordJ → ℝ) × RatCoords)
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hVm : ∀ n, Measurable (V n))
    (hYm : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (V n))
    (hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)))
    (Z Q : RatCircle) (δ b : ℝ≥0∞)
    (hFinite : ∀ᶠ n in atTop,
      P {ω | (V n ω).2.1 (Z, Q) < δ} ≤ b) :
    P' {ω | (Ylim ω).2.1 (Z, Q) < δ} ≤ b := by
  let E : Set ((CoordJ → ℝ) × RatCoords) :=
    {v | v.2.1 (Z, Q) < δ}
  have hOpen : IsOpen E := by
    have hc : Continuous fun v : (CoordJ → ℝ) × RatCoords => v.2.1 (Z, Q) :=
      (continuous_apply (Z, Q)).comp (continuous_fst.comp continuous_snd)
    exact isOpen_lt hc continuous_const
  have hCoupled : ∀ᶠ n in atTop,
      P' {ω | (Y n ω).2.1 (Z, Q) < δ} ≤ b := by
    filter_upwards [hFinite] with n hn
    calc
      P' {ω | (Y n ω).2.1 (Z, Q) < δ} = (P'.map (Y n)) E := by
        exact (Measure.map_apply (hYm n) hOpen.measurableSet).symm
      _ = (P.map (V n)) E := by rw [hLaw n]
      _ = P {ω | (V n ω).2.1 (Z, Q) < δ} :=
        Measure.map_apply (hVm n) hOpen.measurableSet
      _ ≤ b := hn
  exact open_event_limit_probability_le P' Y Ylim E hOpen hConv b
    (by simpa only [E, mem_ofPred_eq] using hCoupled)

end SupercriticalLQGUniqueness.B2.DG20Lim
