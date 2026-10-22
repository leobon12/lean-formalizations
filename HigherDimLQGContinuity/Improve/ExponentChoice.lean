import HigherDimLQGContinuity.Improve.GainMesh
import HigherDimLQGContinuity.Improve.LinearDenom

/-!
# One fixed exponent for all final small parameters
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

def q11FinalExponent (K0 C4 γ U0 cε c4 Rcap Rtrial T : ℝ) : ℝ :=
  20 + K0 + C4 + γ +
    max 0 (-Real.log (1 / (16 * U0))) +
    max 0 (-Real.log cε) +
    max 0 (-Real.log (1 / 100)) +
    max 0 (-Real.log c4) +
    max 0 (-Real.log ((1 / Rcap) / 7)) +
    max 0 (-Real.log (1 / Rtrial)) +
    max 0 (-Real.log T)

/-- Every threshold required by gain, error, rounding, site drift, primary
cap drift, and trial drift is below the single exponent. -/
theorem q11_final_exponent_bounds {K0 C4 γ U0 cε c4 Rcap Rtrial T : ℝ}
    (hK0 : 0 ≤ K0) (hC4 : 0 ≤ C4) (hγ : 0 ≤ γ) :
    let B := q11FinalExponent K0 C4 γ U0 cε c4 Rcap Rtrial T
    1 ≤ B ∧
      K0 + 1 + max 0 (-Real.log (1 / (16 * U0))) ≤ B ∧
      K0 + 1 + max 0 (-Real.log cε) ≤ B ∧
      3 + max 0 (-Real.log (1 / 100)) ≤ B ∧
      C4 + max 0 (-Real.log c4) ≤ B ∧
      2 + max 0 (-Real.log ((1 / Rcap) / 7)) ≤ B ∧
      1 + max 0 (-Real.log (1 / Rtrial)) ≤ B ∧
      γ + max 0 (-Real.log T) ≤ B := by
  have h1 : 0 ≤ max 0 (-Real.log (1 / (16 * U0))) := le_max_left _ _
  have h2 : 0 ≤ max 0 (-Real.log cε) := le_max_left _ _
  have h3 : 0 ≤ max 0 (-Real.log (1 / 100)) := le_max_left _ _
  have h4 : 0 ≤ max 0 (-Real.log c4) := le_max_left _ _
  have h5 : 0 ≤ max 0 (-Real.log ((1 / Rcap) / 7)) := le_max_left _ _
  have h6 : 0 ≤ max 0 (-Real.log (1 / Rtrial)) := le_max_left _ _
  have h7 : 0 ≤ max 0 (-Real.log T) := le_max_left _ _
  dsimp [q11FinalExponent]
  constructor
  · linarith only [hK0, hC4, hγ, h1, h2, h3, h4, h5, h6, h7]
  constructor
  · linarith only [hK0, hC4, hγ, h1, h2, h3, h4, h5, h6, h7]
  constructor
  · linarith only [hK0, hC4, hγ, h1, h2, h3, h4, h5, h6, h7]
  constructor
  · linarith only [hK0, hC4, hγ, h1, h2, h3, h4, h5, h6, h7]
  constructor
  · linarith only [hK0, hC4, hγ, h1, h2, h3, h4, h5, h6, h7]
  constructor
  · linarith only [hK0, hC4, hγ, h1, h2, h3, h4, h5, h6, h7]
  constructor
  · linarith only [hK0, hC4, hγ, h1, h2, h3, h4, h5, h6, h7]
  · linarith only [hK0, hC4, hγ, h1, h2, h3, h4, h5, h6, h7]

end HigherDimLQGContinuity
