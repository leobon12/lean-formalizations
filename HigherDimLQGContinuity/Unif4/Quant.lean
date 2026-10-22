import HigherDimLQGContinuity.UnifBase.ExpRate
import HigherDimLQGMetric.DGZ.AcrossAroundTools

/-!
# Uniform quantile bounds in the shapes of the fixed-`ξ` DGZ port (packet U1)

Blueprint Part D, `d:prop-uexp` ((D.1)), restated in the three shapes in which the fixed-`ξ` proofs of
`HigherDimLQGMetric.DGZ` consume `IsDGZExponent` (NA3 §4.1: "`IsDGZExponent` → `UExpRate`"):

* `exists_aQ_le_unif` (port of `DGZ.exists_aQ_le`): `a^ξ_N(q) ≤ A 2^{-(1-ϕ(ξ)-ε)N}` for every `N`;
* `exists_le_aQ_unif` (port of `DGZ.exists_le_aQ`): `c 2^{-(1-ϕ(ξ)+ε)N} ≤ a^ξ_N(q)` for every `N`;
* `log_aQ_ge_unif` (the exponent step of `DGZ.lemma36_lower`): `log a^ξ_N(p) ≥ -(1-ϕ(ξ)+ϑ) N log 2` for `N ≥ N₀`;

with `ϕ(ξ) = ξ Q(ξ)`, constants depending only on `(d, κ, b, q, ε)` resp. `(d, κ, b, p, ϑ)`, uniformly in
`ξ ∈ (0, b]` and in the dyadic realization (any universe: the quantiles do not depend on the realization,
`DGZ.aQ_eq_of_isDyadicRealization`, and U0's bounds hold in a reference realization).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP (Rd WN IsLFPPKernel IsWhiteNoise IsBandVersion)

variable {d : ℕ}

/-- **`ϕ(ξ) = ξ Q(ξ)` is bounded on `(0, b]`** (PAR's `one_sub_sqrt_mul_le_phiXi`, `phiXi_le_one_add_sqrt_mul`;
`L_ϕ = √(2d)`, ruling N8): `1 - √(2d) b ≤ ξ Q(ξ) ≤ 1 + √(2d) b` for `0 < ξ ≤ b`, `d ≥ 2`. -/
theorem u1_phi_bounds (hd : 2 ≤ d) {b ξ : ℝ} (hξ : 0 < ξ) (hξb : ξ ≤ b) :
    1 - √(2 * d) * b ≤ ξ * distExp d ξ ∧ ξ * distExp d ξ ≤ 1 + √(2 * d) * b := by
  have h1 := one_sub_sqrt_mul_le_phiXi hd hξ.le
  have h2 := phiXi_le_one_add_sqrt_mul hd hξ.le
  rw [phiXi_of_pos hξ] at h1 h2
  have h3 : √(2 * d) * ξ ≤ √(2 * d) * b := mul_le_mul_of_nonneg_left hξb (Real.sqrt_nonneg _)
  exact ⟨by linarith, by linarith⟩

/-- **Uniform upper bound on the quantiles** (port of `DGZ.exists_aQ_le`, from U0's `uExp_aQ_bounds`): for `d ≥ 2`,
`b > 0`, `q ∈ (0, 1)` and `ε > 0` there is `A > 0` with `a^ξ_N(q) ≤ A 2^{-(1-ξQ(ξ)-ε)N}` for every `ξ ∈ (0, b]`,
every dyadic realization and every `N`. -/
theorem exists_aQ_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b : ℝ} (hb : 0 < b)
    {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ A > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ b → ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ N : ℕ,
        aQ P H ξ N q ≤ A * (2 : ℝ) ^ (-(1 - ξ * distExp d ξ - ε) * N) := by
  obtain ⟨C, hC, h⟩ := uExp_aQ_bounds hd hκ hb hε hq0 hq1
  obtain ⟨W₀, hW₀⟩ := HigherDimLFPP.exists_isWhiteNoise d
  obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization hκ hW₀
  refine ⟨C, hC, fun ξ hξ hξb Ω _ P W H hH N => ?_⟩
  rw [aQ_eq_of_isDyadicRealization hH hH₀, neg_mul]
  exact (h ξ hξ hξb _ _ _ _ hH₀ N).2

/-- **Uniform lower bound on the quantiles** (port of `DGZ.exists_le_aQ`, from U0's `uExp_aQ_bounds`): for `d ≥ 2`,
`b > 0`, `q ∈ (0, 1)` and `ε > 0` there is `c > 0` with `c 2^{-(1-ξQ(ξ)+ε)N} ≤ a^ξ_N(q)` for every `ξ ∈ (0, b]`,
every dyadic realization and every `N`. -/
theorem exists_le_aQ_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b : ℝ} (hb : 0 < b)
    {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ b → ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ N : ℕ,
        c * (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + ε) * N) ≤ aQ P H ξ N q := by
  obtain ⟨C, hC, h⟩ := uExp_aQ_bounds hd hκ hb hε hq0 hq1
  obtain ⟨W₀, hW₀⟩ := HigherDimLFPP.exists_isWhiteNoise d
  obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization hκ hW₀
  refine ⟨C⁻¹, inv_pos.2 hC, fun ξ hξ hξb Ω _ P W H hH N => ?_⟩
  rw [aQ_eq_of_isDyadicRealization hH hH₀, neg_mul]
  exact (h ξ hξ hξb _ _ _ _ hH₀ N).1

/-- **Uniform eventual lower bound on `log a_N`** (the exponent step of `DGZ.lemma36_lower`, from U0's
`uExpRate_rate`): for `d ≥ 2`, `ϑ > 0` and `p ∈ (0, 1)` there is `N₀ ≥ 1` with
`-(1 - ξQ(ξ) + ϑ) N log 2 ≤ log a^ξ_N(p)` for every `ξ ∈ (0, b]`, every dyadic realization and every `N ≥ N₀`. -/
theorem log_aQ_ge_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (b : ℝ) {ϑ : ℝ}
    (hϑ : 0 < ϑ) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ b → ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ N : ℕ, N₀ ≤ N →
        -(1 - ξ * distExp d ξ + ϑ) * N * Real.log 2 ≤ Real.log (aQ P H ξ N p) := by
  obtain ⟨N₀, hN₀1, hrate⟩ := uExpRate_rate hd hκ b hϑ hp0 hp1
  obtain ⟨W₀, hW₀⟩ := HigherDimLFPP.exists_isWhiteNoise d
  obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization hκ hW₀
  refine ⟨N₀, hN₀1, fun ξ hξ hξb Ω _ P W H hH N hN => ?_⟩
  rw [aQ_eq_of_isDyadicRealization hH hH₀]
  have h := (abs_le.1 (hrate ξ hξ hξb _ _ _ _ hH₀ N hN)).1
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans hN₀1 hN
    exact_mod_cast this
  have hL : (0 : ℝ) < N * Real.log 2 := mul_pos hNpos (Real.log_pos one_lt_two)
  have h2 : (ξ * distExp d ξ - 1 - ϑ) ≤ Real.log (aQ (LQGDimension.ExistAsm.stdP) H₀ ξ N p) /
      (N * Real.log 2) := by linarith
  rw [le_div_iff₀ hL] at h2
  linarith

/-- **Uniform eventual upper bound on `log a_N`** (from U0's `uExpRate_rate`): for `d ≥ 2`, `ϑ > 0` and `p ∈ (0, 1)`
there is `N₀ ≥ 1` with `log a^ξ_N(p) ≤ -(1 - ξQ(ξ) - ϑ) N log 2` for every `ξ ∈ (0, b]`, every dyadic realization
and every `N ≥ N₀`. -/
theorem log_aQ_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (b : ℝ) {ϑ : ℝ}
    (hϑ : 0 < ϑ) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ b → ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ N : ℕ, N₀ ≤ N →
        Real.log (aQ P H ξ N p) ≤ -(1 - ξ * distExp d ξ - ϑ) * N * Real.log 2 := by
  obtain ⟨N₀, hN₀1, hrate⟩ := uExpRate_rate hd hκ b hϑ hp0 hp1
  obtain ⟨W₀, hW₀⟩ := HigherDimLFPP.exists_isWhiteNoise d
  obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization hκ hW₀
  refine ⟨N₀, hN₀1, fun ξ hξ hξb Ω _ P W H hH N hN => ?_⟩
  rw [aQ_eq_of_isDyadicRealization hH hH₀]
  have h := (abs_le.1 (hrate ξ hξ hξb _ _ _ _ hH₀ N hN)).2
  have hNpos : (0 : ℝ) < N := by
    have : 1 ≤ N := le_trans hN₀1 hN
    exact_mod_cast this
  have hL : (0 : ℝ) < N * Real.log 2 := mul_pos hNpos (Real.log_pos one_lt_two)
  have h2 : Real.log (aQ (LQGDimension.ExistAsm.stdP) H₀ ξ N p) / (N * Real.log 2) ≤
      ξ * distExp d ξ - 1 + ϑ := by linarith
  rw [div_le_iff₀ hL] at h2
  linarith

end HigherDimLQGContinuity
