import SupercriticalLQGUniqueness.B2.DG20Lim.OpenEventLimitProbability
import SupercriticalLQGUniqueness.B2.DG20Lim.RationalUpper

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem point_coord_limit_upper_probability
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
      P {ω | δ < (V n ω).2.1 (Z, Q)} ≤ b) :
    P' {ω | δ < (Ylim ω).2.1 (Z, Q)} ≤ b := by
  let E : Set ((CoordJ → ℝ) × RatCoords) :=
    {v | δ < v.2.1 (Z, Q)}
  have hOpen : IsOpen E := by
    have hc : Continuous fun v : (CoordJ → ℝ) × RatCoords => v.2.1 (Z, Q) :=
      (continuous_apply (Z, Q)).comp (continuous_fst.comp continuous_snd)
    exact isOpen_lt continuous_const hc
  have hCoupled : ∀ᶠ n in atTop,
      P' {ω | δ < (Y n ω).2.1 (Z, Q)} ≤ b := by
    filter_upwards [hFinite] with n hn
    calc
      P' {ω | δ < (Y n ω).2.1 (Z, Q)} = (P'.map (Y n)) E := by
        exact (Measure.map_apply (hYm n) hOpen.measurableSet).symm
      _ = (P.map (V n)) E := by rw [hLaw n]
      _ = P {ω | δ < (V n ω).2.1 (Z, Q)} :=
        Measure.map_apply (hVm n) hOpen.measurableSet
      _ ≤ b := hn
  exact open_event_limit_probability_le P' Y Ylim E hOpen hConv b
    (by simpa only [E, mem_ofPred_eq] using hCoupled)

end SupercriticalLQGUniqueness.B2.DG20Lim
