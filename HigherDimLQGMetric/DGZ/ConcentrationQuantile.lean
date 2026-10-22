import HigherDimLQGMetric.DGZ.Concentration
import HigherDimLFPP.Exist.Quantile

/-!
# Means, one-sided tails and quantiles of log-Lipschitz functionals (packet L3b2, MA7 D-4.6)

Source: planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-4.6 (last
sentence: "With HA5-D3, `|log a^{(p)}(Φ(X)) - E log Φ(X)| ≤ C_p ξ √(log(b/a))`") and its uses in
D-4.7s ("the lower `3/4`-quantile is `≤ …`, so `E log selfDiam_n ≤ …`"), D-3.6L
("`P[D ≥ t] ≥ 0.4/J`, so `E log D ≥ log t - C(J)√n`") and D-4.8 (2).

Everything follows from the two-sided Gaussian tail of
`measure_abs_sub_integral_ge_le_of_isSupLipschitzOn` (`Concentration.lean`):

* abstract tail lemmas: `lt_add_of_lt_measure_le_of_tail`, `sub_lt_of_lt_measure_ge_of_tail` (if
  `{Y ≤ s}` has probability larger than the tail bound at `u`, then the centre `m` satisfies
  `m < s + u`; symmetrically), and their forms with HA5's `quantileConst`;
* for sup-Lipschitz functionals `F` of a band version `X` of `H_{a,b}`:
  `integral_lt_add_of_lt_measure_le`, `sub_lt_integral_of_lt_measure_ge` (any `u ≥ 0`), the
  `quantileConst` forms `integral_lt_add_of_le_measure_le`, `sub_lt_integral_of_le_measure_ge`, and
  the quantile bound `abs_lowerQuantile_sub_integral_le_of_isSupLipschitzOn` (HA5 D3);
* for positive `Φ` with `log Φ` `|ξ|`-Lipschitz: `integral_log_lt_log_add_of_le_measure_le`,
  `log_sub_lt_integral_log_of_le_measure_ge` (mean of `log Φ(X)` against a level `T` reached with
  probability `≥ p`), the one-sided tails `measure_lt_le_of_integral_log_add_le` (upper) and
  `measure_lt_le_of_log_add_le_integral` (lower), and
  `abs_log_lowerQuantile_sub_integral_le_of_logLipschitz`
  (`|log q_p(Φ(X)) - E log Φ(X)| ≤ quantileConst p · |ξ| √(log(b/a))`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Conc

/-! ### Centres of variables with a two-sided Gaussian tail -/

section Tail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `t ↦ 2 exp(-t²/(2c))` is antitone on `[0, ∞)` for `c ≥ 0`. -/
theorem two_mul_exp_neg_sq_div_le {c u t : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) (hut : u ≤ t) :
    2 * Real.exp (-t ^ 2 / (2 * c)) ≤ 2 * Real.exp (-u ^ 2 / (2 * c)) := by
  have h1 : u ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hu hut 2
  have h2 : -t ^ 2 / (2 * c) ≤ -u ^ 2 / (2 * c) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by norm_num)

/-- **The centre lies below a level reached with large probability**: if
`P[|Y - m| ≥ t] ≤ 2 exp(-t²/(2c))` for all `t ≥ 0` and `P[Y ≤ s] > 2 exp(-u²/(2c))` for some
`u ≥ 0`, then `m < s + u`. -/
theorem lt_add_of_lt_measure_le_of_tail {Y : Ω → ℝ} {m c : ℝ} (hc : 0 ≤ c)
    (htail : ∀ t : ℝ, 0 ≤ t →
      P {ω | t ≤ |Y ω - m|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * c))))
    {s u : ℝ} (hu : 0 ≤ u)
    (h : ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * c))) < P {ω | Y ω ≤ s}) : m < s + u := by
  by_contra hge
  have hge' : s + u ≤ m := not_lt.1 hge
  have ht : u ≤ m - s := by linarith
  have hsub : {ω | Y ω ≤ s} ⊆ {ω | m - s ≤ |Y ω - m|} := fun ω hω => by
    have hω' : Y ω ≤ s := hω
    show m - s ≤ |Y ω - m|
    rw [abs_sub_comm]
    exact (by linarith : m - s ≤ m - Y ω).trans (le_abs_self _)
  have h1 := (measure_mono hsub).trans (htail (m - s) (hu.trans ht))
  have h2 := ENNReal.ofReal_le_ofReal (two_mul_exp_neg_sq_div_le hc hu ht)
  exact absurd (h1.trans h2) (not_le.2 h)

/-- **The centre lies above a level exceeded with large probability**: if
`P[|Y - m| ≥ t] ≤ 2 exp(-t²/(2c))` for all `t ≥ 0` and `P[Y ≥ s] > 2 exp(-u²/(2c))` for some
`u ≥ 0`, then `s - u < m`. -/
theorem sub_lt_of_lt_measure_ge_of_tail {Y : Ω → ℝ} {m c : ℝ} (hc : 0 ≤ c)
    (htail : ∀ t : ℝ, 0 ≤ t →
      P {ω | t ≤ |Y ω - m|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * c))))
    {s u : ℝ} (hu : 0 ≤ u)
    (h : ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * c))) < P {ω | s ≤ Y ω}) : s - u < m := by
  by_contra hge
  have hge' : m ≤ s - u := not_lt.1 hge
  have ht : u ≤ s - m := by linarith
  have hsub : {ω | s ≤ Y ω} ⊆ {ω | s - m ≤ |Y ω - m|} := fun ω hω => by
    have hω' : s ≤ Y ω := hω
    show s - m ≤ |Y ω - m|
    exact (by linarith : s - m ≤ Y ω - m).trans (le_abs_self _)
  have h1 := (measure_mono hsub).trans (htail (s - m) (hu.trans ht))
  have h2 := ENNReal.ofReal_le_ofReal (two_mul_exp_neg_sq_div_le hc hu ht)
  exact absurd (h1.trans h2) (not_le.2 h)

/-- `ofReal (2 exp(-(σ c_p)²/(2σ²))) < ofReal p` for `σ > 0`, `p ∈ (0, 1)` (HA5's constant). -/
theorem ofReal_two_mul_exp_neg_quantileConst_lt {σ p : ℝ} (hσ : 0 < σ) (hp0 : 0 < p)
    (hp1 : p < 1) :
    ENNReal.ofReal (2 * Real.exp (-(σ * quantileConst p) ^ 2 / (2 * σ ^ 2))) <
      ENNReal.ofReal p := by
  rw [two_mul_exp_neg_quantileConst hσ hp0 hp1, ENNReal.ofReal_lt_ofReal_iff hp0]
  have := min_le_left p (1 - p)
  linarith

/-- `quantileConst` form of `lt_add_of_lt_measure_le_of_tail`: if `P[Y ≤ s] ≥ p ∈ (0, 1)`, then
`m < s + σ · quantileConst p`. -/
theorem lt_add_of_le_measure_le_of_tail {Y : Ω → ℝ} {m σ : ℝ} (hσ : 0 < σ)
    (htail : ∀ t : ℝ, 0 ≤ t →
      P {ω | t ≤ |Y ω - m|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ ^ 2))))
    {s p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h : ENNReal.ofReal p ≤ P {ω | Y ω ≤ s}) :
    m < s + σ * quantileConst p :=
  lt_add_of_lt_measure_le_of_tail (sq_nonneg σ) htail
    (mul_nonneg hσ.le (quantileConst_nonneg p))
    ((ofReal_two_mul_exp_neg_quantileConst_lt hσ hp0 hp1).trans_le h)

/-- `quantileConst` form of `sub_lt_of_lt_measure_ge_of_tail`: if `P[Y ≥ s] ≥ p ∈ (0, 1)`, then
`s - σ · quantileConst p < m`. -/
theorem sub_lt_of_le_measure_ge_of_tail {Y : Ω → ℝ} {m σ : ℝ} (hσ : 0 < σ)
    (htail : ∀ t : ℝ, 0 ≤ t →
      P {ω | t ≤ |Y ω - m|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ ^ 2))))
    {s p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (h : ENNReal.ofReal p ≤ P {ω | s ≤ Y ω}) :
    s - σ * quantileConst p < m :=
  sub_lt_of_lt_measure_ge_of_tail (sq_nonneg σ) htail
    (mul_nonneg hσ.le (quantileConst_nonneg p))
    ((ofReal_two_mul_exp_neg_quantileConst_lt hσ hp0 hp1).trans_le h)

end Tail

/-! ### Sup-Lipschitz functionals of band fields -/

section Band

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
  {κ : Rd d → ℝ} {a b : ℝ} {X : Rd d → Ω → ℝ} {K : Set (Rd d)} {L : ℝ}
  {F : (Rd d → ℝ) → ℝ}

/-- The tail of `measure_abs_sub_integral_ge_le_of_isSupLipschitzOn` with `σ = L √(log(b/a))`. -/
theorem tail_sq_of_isSupLipschitzOn (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ha : 0 < a)
    (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (hK : IsCompact K)
    (hF : IsSupLipschitzOn K L F) (t : ℝ) (ht : 0 ≤ t) :
    P {ω | t ≤ |(F fun z => X z ω) - ∫ ω', F (fun z => X z ω') ∂P|} ≤
      ENNReal.ofReal
        (2 * Real.exp (-t ^ 2 / (2 * (L * √(Real.log (b / a))) ^ 2))) := by
  have hv0 : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).2 hab)
  have e : 2 * (L * √(Real.log (b / a))) ^ 2 = 2 * L ^ 2 * Real.log (b / a) := by
    rw [mul_pow, Real.sq_sqrt hv0, mul_assoc]
  rw [e]
  exact measure_abs_sub_integral_ge_le_of_isSupLipschitzOn hκ hW ha hab hX hK hF ht

/-- **Mean below a level** (MA7 D-4.6): if `P[F(X) ≤ s] > 2 exp(-u²/(2 L² log(b/a)))` for some
`u ≥ 0`, then `E F(X) < s + u`. -/
theorem integral_lt_add_of_lt_measure_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (hK : IsCompact K)
    (hF : IsSupLipschitzOn K L F) {s u : ℝ} (hu : 0 ≤ u)
    (h : ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * (L * √(Real.log (b / a))) ^ 2))) <
      P {ω | (F fun z => X z ω) ≤ s}) :
    ∫ ω, F (fun z => X z ω) ∂P < s + u :=
  lt_add_of_lt_measure_le_of_tail (sq_nonneg _)
    (tail_sq_of_isSupLipschitzOn hκ hW ha hab hX hK hF) hu h

/-- **Mean above a level** (MA7 D-4.6): if `P[F(X) ≥ s] > 2 exp(-u²/(2 L² log(b/a)))` for some
`u ≥ 0`, then `s - u < E F(X)`. -/
theorem sub_lt_integral_of_lt_measure_ge (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (hK : IsCompact K)
    (hF : IsSupLipschitzOn K L F) {s u : ℝ} (hu : 0 ≤ u)
    (h : ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * (L * √(Real.log (b / a))) ^ 2))) <
      P {ω | s ≤ F fun z => X z ω}) :
    s - u < ∫ ω, F (fun z => X z ω) ∂P :=
  sub_lt_of_lt_measure_ge_of_tail (sq_nonneg _)
    (tail_sq_of_isSupLipschitzOn hκ hW ha hab hX hK hF) hu h

/-- `L √(log(b/a)) > 0` for `L > 0`, `0 < a < b`. -/
theorem mul_sqrt_log_pos (ha : 0 < a) (hab : a < b) (hL : 0 < L) :
    0 < L * √(Real.log (b / a)) :=
  mul_pos hL (Real.sqrt_pos.2 (Real.log_pos ((one_lt_div ha).2 hab)))

/-- **Mean below a level reached with probability `≥ p`** (MA7 D-4.6 with HA5 D3): for
`0 < a < b`, `L > 0` and `p ∈ (0, 1)`, if `P[F(X) ≤ s] ≥ p` then
`E F(X) < s + L √(log(b/a)) · quantileConst p`. -/
theorem integral_lt_add_of_le_measure_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a < b) (hX : IsBandVersion P W κ a b X) (hK : IsCompact K)
    (hF : IsSupLipschitzOn K L F) (hL : 0 < L) {s p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h : ENNReal.ofReal p ≤ P {ω | (F fun z => X z ω) ≤ s}) :
    ∫ ω, F (fun z => X z ω) ∂P < s + L * √(Real.log (b / a)) * quantileConst p :=
  lt_add_of_le_measure_le_of_tail (mul_sqrt_log_pos ha hab hL)
    (tail_sq_of_isSupLipschitzOn hκ hW ha hab.le hX hK hF) hp0 hp1 h

/-- **Mean above a level exceeded with probability `≥ p`** (MA7 D-4.6 with HA5 D3): for
`0 < a < b`, `L > 0` and `p ∈ (0, 1)`, if `P[F(X) ≥ s] ≥ p` then
`s - L √(log(b/a)) · quantileConst p < E F(X)`. -/
theorem sub_lt_integral_of_le_measure_ge (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a < b) (hX : IsBandVersion P W κ a b X) (hK : IsCompact K)
    (hF : IsSupLipschitzOn K L F) (hL : 0 < L) {s p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (h : ENNReal.ofReal p ≤ P {ω | s ≤ F fun z => X z ω}) :
    s - L * √(Real.log (b / a)) * quantileConst p < ∫ ω, F (fun z => X z ω) ∂P :=
  sub_lt_of_le_measure_ge_of_tail (mul_sqrt_log_pos ha hab hL)
    (tail_sq_of_isSupLipschitzOn hκ hW ha hab.le hX hK hF) hp0 hp1 h

/-- **Quantiles of sup-Lipschitz functionals** (MA7 D-4.6 with HA5 D3): for `0 < a < b`, `L > 0`
and `p ∈ (0, 1)`, `|q_p(F(X)) - E F(X)| ≤ L √(log(b/a)) · quantileConst p`. -/
theorem abs_lowerQuantile_sub_integral_le_of_isSupLipschitzOn (hκ : IsLFPPKernel κ)
    (hW : IsWhiteNoise P W) (ha : 0 < a) (hab : a < b) (hX : IsBandVersion P W κ a b X)
    (hK : IsCompact K) (hF : IsSupLipschitzOn K L F) (hL : 0 < L) {p : ℝ≥0∞} (hp0 : 0 < p)
    (hp1 : p < 1) :
    |LQGMetric.lowerQuantile (P.map fun ω => F fun z => X z ω) p -
        ∫ ω, F (fun z => X z ω) ∂P| ≤
      L * √(Real.log (b / a)) * quantileConst p.toReal := by
  have := hW.isProbabilityMeasure
  exact abs_lowerQuantile_sub_le_of_tail (measurable_of_isSupLipschitzOn hX hK hF).aemeasurable
    (mul_sqrt_log_pos ha hab hL) (tail_sq_of_isSupLipschitzOn hκ hW ha hab.le hX hK hF) hp0 hp1

/-! ### Positive functionals with a log-Lipschitz logarithm -/

variable {ξ : ℝ} {Φ : (Rd d → ℝ) → ℝ}

/-- `log Φ(X)` for `Φ > 0` on continuous fields: the events `{Φ(X) ≤ T}` and
`{log Φ(X) ≤ log T}` agree for `T > 0`. -/
theorem setOf_le_eq_setOf_log_le (hX : IsBandVersion P W κ a b X)
    (hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < Φ φ) {T : ℝ} (hT : 0 < T) :
    {ω | (Φ fun z => X z ω) ≤ T} = {ω | Real.log (Φ fun z => X z ω) ≤ Real.log T} := by
  ext ω
  exact (Real.log_le_log_iff (hpos _ (hX.continuous ω)) hT).symm

/-- The events `{T ≤ Φ(X)}` and `{log T ≤ log Φ(X)}` agree for `T > 0`. -/
theorem setOf_ge_eq_setOf_log_ge (hX : IsBandVersion P W κ a b X)
    (hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < Φ φ) {T : ℝ} (hT : 0 < T) :
    {ω | T ≤ Φ fun z => X z ω} = {ω | Real.log T ≤ Real.log (Φ fun z => X z ω)} := by
  ext ω
  exact (Real.log_le_log_iff hT (hpos _ (hX.continuous ω))).symm

/-- **Mean of `log Φ(X)` below a level** (MA7 D-4.6 with HA5 D3; used in D-4.7s): for `0 < a < b`,
`ξ ≠ 0`, `Φ > 0` with `log Φ` `|ξ|`-Lipschitz for the sup norm on the compact `K`, `T > 0` and
`p ∈ (0, 1)`: if `P[Φ(X) ≤ T] ≥ p` then `E log Φ(X) < log T + |ξ| √(log(b/a)) · quantileConst p`. -/
theorem integral_log_lt_log_add_of_le_measure_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a < b) (hX : IsBandVersion P W κ a b X) (hK : IsCompact K)
    (hξ : ξ ≠ 0)
    (hΦ : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → |Real.log (Φ φ) - Real.log (Φ ψ)| ≤ |ξ| * M)
    (hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < Φ φ) {T p : ℝ} (hT : 0 < T) (hp0 : 0 < p)
    (hp1 : p < 1) (h : ENNReal.ofReal p ≤ P {ω | (Φ fun z => X z ω) ≤ T}) :
    ∫ ω, Real.log (Φ fun z => X z ω) ∂P <
      Real.log T + |ξ| * √(Real.log (b / a)) * quantileConst p := by
  rw [setOf_le_eq_setOf_log_le hX hpos hT] at h
  exact integral_lt_add_of_le_measure_le (F := fun φ => Real.log (Φ φ)) hκ hW ha hab hX hK hΦ
    (abs_pos.2 hξ) hp0 hp1 h

/-- **Mean of `log Φ(X)` above a level** (MA7 D-4.6 with HA5 D3; used in D-3.6L and D-4.8): for
`0 < a < b`, `ξ ≠ 0`, `Φ > 0` with `log Φ` `|ξ|`-Lipschitz for the sup norm on the compact `K`,
`T > 0` and `p ∈ (0, 1)`: if `P[Φ(X) ≥ T] ≥ p` then
`log T - |ξ| √(log(b/a)) · quantileConst p < E log Φ(X)`. -/
theorem log_sub_lt_integral_log_of_le_measure_ge (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a < b) (hX : IsBandVersion P W κ a b X) (hK : IsCompact K)
    (hξ : ξ ≠ 0)
    (hΦ : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → |Real.log (Φ φ) - Real.log (Φ ψ)| ≤ |ξ| * M)
    (hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < Φ φ) {T p : ℝ} (hT : 0 < T) (hp0 : 0 < p)
    (hp1 : p < 1) (h : ENNReal.ofReal p ≤ P {ω | T ≤ Φ fun z => X z ω}) :
    Real.log T - |ξ| * √(Real.log (b / a)) * quantileConst p <
      ∫ ω, Real.log (Φ fun z => X z ω) ∂P := by
  rw [setOf_ge_eq_setOf_log_ge hX hpos hT] at h
  exact sub_lt_integral_of_le_measure_ge (F := fun φ => Real.log (Φ φ)) hκ hW ha hab hX hK hΦ
    (abs_pos.2 hξ) hp0 hp1 h

/-- **Upper one-sided tail of `Φ(X)`** (MA7 D-4.6; the last step of D-4.7s): for `0 < a ≤ b`,
`Φ` with `log Φ` `|ξ|`-Lipschitz on the compact `K`, `T > 0` and `t ≥ 0` with
`E log Φ(X) + t ≤ log T`: `P[Φ(X) > T] ≤ 2 exp(-t²/(2 ξ² log(b/a)))`. -/
theorem measure_lt_le_of_integral_log_add_le (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (hK : IsCompact K)
    (hΦ : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → |Real.log (Φ φ) - Real.log (Φ ψ)| ≤ |ξ| * M)
    {T t : ℝ} (hT : 0 < T) (ht : 0 ≤ t)
    (hle : ∫ ω, Real.log (Φ fun z => X z ω) ∂P + t ≤ Real.log T) :
    P {ω | T < Φ fun z => X z ω} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) := by
  refine (measure_mono fun ω hω => ?_).trans
    (measure_abs_log_sub_ge_le_of_logLipschitz hκ hW ha hab hX hK ξ hΦ ht)
  have hω' : T < Φ fun z => X z ω := hω
  have hlog : Real.log T < Real.log (Φ fun z => X z ω) := Real.log_lt_log hT hω'
  show t ≤ |Real.log (Φ fun z => X z ω) - ∫ ω', Real.log (Φ fun z => X z ω') ∂P|
  exact (by linarith : t ≤ Real.log (Φ fun z => X z ω) -
    ∫ ω', Real.log (Φ fun z => X z ω') ∂P).trans (le_abs_self _)

/-- **Lower one-sided tail of `Φ(X)`** (MA7 D-4.6; the last steps of D-3.6L and D-4.8): for
`0 < a ≤ b`, `Φ > 0` with `log Φ` `|ξ|`-Lipschitz on the compact `K`, `T > 0` and `t ≥ 0` with
`log T + t ≤ E log Φ(X)`: `P[Φ(X) < T] ≤ 2 exp(-t²/(2 ξ² log(b/a)))`. -/
theorem measure_lt_le_of_log_add_le_integral (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (hK : IsCompact K)
    (hΦ : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → |Real.log (Φ φ) - Real.log (Φ ψ)| ≤ |ξ| * M)
    (hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < Φ φ) {T t : ℝ} (ht : 0 ≤ t)
    (hle : Real.log T + t ≤ ∫ ω, Real.log (Φ fun z => X z ω) ∂P) :
    P {ω | (Φ fun z => X z ω) < T} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ξ ^ 2 * Real.log (b / a)))) := by
  refine (measure_mono fun ω hω => ?_).trans
    (measure_abs_log_sub_ge_le_of_logLipschitz hκ hW ha hab hX hK ξ hΦ ht)
  have hω' : (Φ fun z => X z ω) < T := hω
  have hlog : Real.log (Φ fun z => X z ω) < Real.log T :=
    Real.log_lt_log (hpos _ (hX.continuous ω)) hω'
  show t ≤ |Real.log (Φ fun z => X z ω) - ∫ ω', Real.log (Φ fun z => X z ω') ∂P|
  rw [abs_sub_comm]
  exact (by linarith : t ≤ ∫ ω', Real.log (Φ fun z => X z ω') ∂P -
    Real.log (Φ fun z => X z ω)).trans (le_abs_self _)

/-- `Φ(X)` is measurable for positive `Φ` with a log-Lipschitz logarithm. -/
theorem measurable_of_logLipschitz_of_pos (hX : IsBandVersion P W κ a b X) (hK : IsCompact K)
    (hΦ : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → |Real.log (Φ φ) - Real.log (Φ ψ)| ≤ |ξ| * M)
    (hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < Φ φ) :
    Measurable fun ω => Φ fun z => X z ω := by
  have e : (fun ω => Φ fun z => X z ω) = fun ω => Real.exp (Real.log (Φ fun z => X z ω)) :=
    funext fun ω => (Real.exp_log (hpos _ (hX.continuous ω))).symm
  rw [e]
  exact (measurable_log_of_logLipschitz hX hK ξ hΦ).exp

/-- **MA7 D-4.6, quantile form** ("with HA5-D3"): for `0 < a < b`, `ξ ≠ 0`, `Φ > 0` with `log Φ`
`|ξ|`-Lipschitz for the sup norm on the compact `K`, and `p ∈ (0, 1)`,
`|log q_p(Φ(X)) - E log Φ(X)| ≤ quantileConst p · |ξ| √(log(b/a))`. -/
theorem abs_log_lowerQuantile_sub_integral_le_of_logLipschitz (hκ : IsLFPPKernel κ)
    (hW : IsWhiteNoise P W) (ha : 0 < a) (hab : a < b) (hX : IsBandVersion P W κ a b X)
    (hK : IsCompact K) (hξ : ξ ≠ 0)
    (hΦ : ∀ φ ψ : Rd d → ℝ, Continuous φ → Continuous ψ → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ K, |φ z - ψ z| ≤ M) → |Real.log (Φ φ) - Real.log (Φ ψ)| ≤ |ξ| * M)
    (hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < Φ φ) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    |Real.log (LQGMetric.lowerQuantile (P.map fun ω => Φ fun z => X z ω) p) -
        ∫ ω, Real.log (Φ fun z => X z ω) ∂P| ≤
      quantileConst p.toReal * |ξ| * √(Real.log (b / a)) := by
  have := hW.isProbabilityMeasure
  rw [log_lowerQuantile_map_eq (measurable_of_logLipschitz_of_pos hX hK hΦ hpos).aemeasurable
    (ae_of_all _ fun ω => hpos _ (hX.continuous ω)) hp0 hp1]
  have h := abs_lowerQuantile_sub_integral_le_of_isSupLipschitzOn (F := fun φ => Real.log (Φ φ))
    hκ hW ha hab hX hK hΦ (abs_pos.2 hξ) hp0 hp1
  calc _ ≤ |ξ| * √(Real.log (b / a)) * quantileConst p.toReal := h
    _ = quantileConst p.toReal * |ξ| * √(Real.log (b / a)) := by ring

end Band

end HigherDimLQGMetric.DGZ
