import QuantumZipper.Proofs.Zipper.BMHolderGaussChain
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# BM-HOLDER-GAUSS (moments): even moments of the dyadic Brownian increment maximum

For a (pre-)Brownian motion `B'` let `gM B' = sup_{n, k < 2^n} |B'((k+1)/2^n) − B'(k/2^n)| / ρ^n`
with `ρ = 2^{-1/3}` (`bmRho`). Then for `j ≥ 4`

`E[gM^{2j}] ≤ j! c^{-j} (1 − ρ)^{-1} · E_γ[e^{c N²}]`   (`lintegral_gM_pow`),

where `c > 0` comes from Fernique's theorem for the standard Gaussian `γ = N(0,1)`
(`gauss_exp_sq_fin`, mathlib's `exists_integrable_exp_sq`; X. Fernique, *Intégrabilité des
vecteurs gaussiens*, C. R. Acad. Sci. Paris 270 (1970) 1698–1699). The bound is the union bound
over the `2^n` increments of level `n`, each `N(0, 2^{-n})` (mathlib `IsPreBrownianReal.hasLaw_sub`),
with `(c x²)^j / j! ≤ e^{c x²}`; the level sum `Σ_n 2^n ρ^{jn} ≤ Σ_n ρ^n` converges for `j ≥ 4`.
This is the moment form of the Kolmogorov–Čentsov union bound (Revuz–Yor, 3rd ed., Ch. I,
proof of Thm (2.1)); the explicit Gaussian constants are an own elementary step.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Nat

namespace QuantumZipper
namespace RegUnif

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Dyadic increment of level `n`, index `k`. -/
def gInc (B' : ℝ≥0 → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  B' (((k : ℝ) + 1) / 2 ^ n).toNNReal ω - B' ((k : ℝ) / 2 ^ n).toNNReal ω

/-- Normalized dyadic increment. -/
def gY (B' : ℝ≥0 → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (|gInc B' n k ω| / bmRho ^ n)

/-- Maximal normalized dyadic increment. -/
def gM (B' : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ k : Fin (2 ^ n), gY B' n k ω

theorem measurable_gY {B' : ℝ≥0 → Ω → ℝ} (hB'm : ∀ t, Measurable (B' t)) (n k : ℕ) :
    Measurable (gY B' n k) :=
  ENNReal.measurable_ofReal.comp
    ((continuous_abs.measurable.comp ((hB'm _).sub (hB'm _))).div_const _)

theorem measurable_gM {B' : ℝ≥0 → Ω → ℝ} (hB'm : ∀ t, Measurable (B' t)) :
    Measurable (gM B') :=
  Measurable.iSup fun n => Measurable.iSup fun k => measurable_gY hB'm n k

end RegUnif
end QuantumZipper
