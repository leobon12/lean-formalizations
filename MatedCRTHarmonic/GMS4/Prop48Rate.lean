import MatedCRTHarmonic.GMS4.Prop48SecondMoment
import MatedCRTHarmonic.GMS4.Prop48NearMeasure

/-!
# A common exponent for Proposition 4.8

The spatial near contribution has exponent `2q-10ζ` in [18] (4.34); the
far contribution has exponent `ζ` in (4.37). Both parameters are chosen from
`γ` before the test radius `ρ`, so their minimum is a radius-independent
positive exponent.
-/

set_option autoImplicit false
noncomputable section

namespace MatedCRTHarmonic.GMS4

/-- The common Proposition 4.8 exponent, selected before `ρ`. -/
def prop48RateAlpha (q ζ : ℝ) : ℝ := min (2 * q - 10 * ζ) ζ

theorem prop48RateAlpha_pos {q ζ : ℝ}
    (hq : 0 < q) (hζ : 0 < ζ) (hζq : ζ < q / 100) :
    0 < prop48RateAlpha q ζ := by
  unfold prop48RateAlpha
  apply lt_min
  · linarith
  · exact hζ

/-- Both source rates are dominated by the common rate at scales `ε<1`. -/
theorem prop48_near_far_rates_le_common {q ζ ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ε ^ (2 * q - 10 * ζ) ≤ ε ^ prop48RateAlpha q ζ ∧
      ε ^ ζ ≤ ε ^ prop48RateAlpha q ζ := by
  constructor
  · exact Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (min_le_left _ _)
  · exact Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (min_le_right _ _)

end MatedCRTHarmonic.GMS4

