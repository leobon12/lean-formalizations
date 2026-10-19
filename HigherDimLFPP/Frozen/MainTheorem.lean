-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPP.Frozen.Kappa
import HigherDimLFPP.Frozen.IsLFPPKernel
import HigherDimLFPP.Frozen.IsBandVersion
import HigherDimLFPP.Frozen.IsLFPPExponent
import HigherDimLFPP.Assembly.Main

/-!
# Frozen theorem: `theorem11`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, Theorem 1.1 with (1.3) and (1.7), in every dimension `d ≥ 2`, with no hypotheses
(ruling H1): the existence of `λ_d` (source ref. [2, Prop. 1.1]) and the positivity of `κ_d` are
conclusions.  Field model: ruling H10.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- **Theorem 1.1.** For every `d ≥ 2`: `(A_{n,d})` is finite and subadditive; `A_{n,d}/(n log 2) → κ_d`
(`κ_d` is the infimum, by definition); `0 < κ_d`; and for every admissible kernel, white noise `W`
and continuous versions `H ε` of `H_{ε,1}`, the LFPP exponent `λ_d(ζ)` exists for all small `ζ > 0`
and `λ_d(ζ)/ζ^{4/3} → κ_d` as `ζ ↓ 0`. -/
theorem theorem11 : ∀ d : ℕ, 2 ≤ d →
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
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPP.theorem11_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPP
-- FROZEN_ANCHOR_SUFFIX_END
