import HigherDimLFPP.Assembly.Reductions
import HigherDimLFPP.Upper.LocalMean
import HigherDimLFPP.Lower.Lemma53

/-!
# Provider of the frozen `theorem11`

Theorem 1.1 of the source, for every dimension `d ≥ 2`, with no hypotheses beyond the definitions of the
objects (ruling H1). `theorem11_of_inputs` (`Assembly/Reductions.lean`) derives the frozen statement from:
* the variational part (§2);
* the existence of the exponent (DGZ Prop. 1.1 and App. A.1);
* the existence-free upper and lower comparisons (§§4–5).

The two inputs it leaves open are discharged here:
* `Upper.goodRecordMeanBound_all` — the good-record mean bound, from Lemma 4.3 (`Upper/LocalMean.lean`);
* `Lower.lemma53Holds_holds` — Lemma 5.3, with Lemma 5.2 (`Lower/Lemma53.lean`).

It is the `implementation.module` of the anchor `HigherDimLFPP/Frozen/MainTheorem.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- Implementation of the frozen `theorem11` (Theorem 1.1 for every `d ≥ 2`). -/
theorem theorem11_impl : ∀ d : ℕ, 2 ≤ d →
    (∀ n : ℕ, A n d ≠ ⊥ ∧ A n d ≠ ⊤) ∧
    (∀ n r : ℕ, A (n + r) d ≤ A n d + A r d) ∧
    Tendsto (fun n : ℕ => (A n d).toReal / ((n : ℝ) * Real.log 2)) atTop (𝓝 (kappa d)) ∧
    0 < kappa d ∧
    ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      (∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, ∃ lam : ℝ, IsLFPPExponent H P ζ lam) ∧
      ∀ lam : ℝ → ℝ, (∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, IsLFPPExponent H P ζ (lam ζ)) →
        Tendsto (fun ζ => lam ζ / ζ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (kappa d)) :=
  theorem11_of_inputs Upper.goodRecordMeanBound_all Lower.lemma53Holds_holds

end HigherDimLFPP
