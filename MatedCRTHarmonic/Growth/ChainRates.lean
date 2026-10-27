import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib
import Mathlib.MeasureTheory.OuterMeasure.Basic
import MatedCRTHarmonic.Growth.Rates

/-!
# Almost-sure chain-length bounds

The finite-union estimate and the elementary symmetric bound give summable probabilities for long
chains. This module applies the first Borel–Cantelli lemma to the linear and polynomial regimes.
-/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal

namespace MatedCRTHarmonic.Growth

/-- A real summable majorant for event probabilities gives almost-sure eventual avoidance. -/
theorem ae_eventually_notMem_of_real_summable_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Set Ω) (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hs : Summable u)
    (hbound : ∀ n, μ (E n) ≤ ENNReal.ofReal (u n)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ E n := by
  have hsum : (∑' n, μ (E n)) ≤ ENNReal.ofReal (∑' n, u n) := by
    calc
      _ ≤ ∑' n, ENNReal.ofReal (u n) := ENNReal.tsum_le_tsum hbound
      _ = ENNReal.ofReal (∑' n, u n) :=
        (ENNReal.ofReal_tsum_of_nonneg hu hs).symm
  have hne : (∑' n, μ (E n)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
  exact ae_eventually_notMem_of_summable_events μ E hne

/-- The integer part of `c*n`, used as the Borel–Cantelli threshold. -/
noncomputable def linearChainThreshold (c : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (c * (n : ℝ))

/-- The integer part of `n^(1-ζ)`, used as the polynomial Borel–Cantelli threshold. -/
noncomputable def polynomialChainThreshold (ζ : ℝ) (n : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) ^ (1 - ζ))

end MatedCRTHarmonic.Growth
