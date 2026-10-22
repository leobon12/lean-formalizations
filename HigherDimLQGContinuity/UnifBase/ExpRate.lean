import HigherDimLQGContinuity.UnifBase.ExpMean

/-!
# The uniform exponent rate `UExpRate` (packet U0)

Blueprint Part D, `d:prop-uexp` ((D.1); [C] (A.6); NA3 R2(f), §2.15 row 6). For `d ≥ 2`, an admissible kernel `κ`,
`b, ϑ > 0` and `p ∈ (0, 1)` there are `N = N(d, κ, b, ϑ, p) ≥ 1` and `C = C(d, κ, b, ϑ, p)` such that for every
`ξ ∈ (0, b]` and every dyadic realization:

`|log a^ξ_n(p)/(n log 2) - (ϕ(ξ) - 1)| ≤ ϑ` for `n ≥ N` (`uExpRate_rate`), and
`C⁻¹ 2^{-(1-ϕ(ξ)+ϑ)n} ≤ a^ξ_n(p) ≤ C 2^{-(1-ϕ(ξ)-ϑ)n}` for every `n ≥ 0` (`uExp_aQ_bounds`),

with `ϕ(ξ) = ξ Q(ξ)`; together they are the interface `UExpRate d κ` (`uExpRate`, the producer of I4).

Proof. In one reference realization (the quantiles do not depend on the realization,
`DGZ.aQ_eq_of_isDyadicRealization`) the mean exponents `f_n` are equi-Lipschitz (`expMean_lipschitz`) and converge
pointwise to `ϕ - 1` (`tendsto_expMean`); `ϕ` is `√(2d)`-Lipschitz (PAR's `phiXi_lipschitz`, ruling N8). A finite net
upgrades this to uniform convergence on `(0, b]` (`u0_exists_uniform_of_lipschitz`), and the quantile comparison
`|log a^ξ_n(p)/(n log 2) - f_n(ξ)| ≤ q(p) b/√(n log 2)` gives the rate (`n ≥ N` with `N ≥ 1`, so the junk `0/0` at
`n = 0` is never used). For `n < N`: `e^{-|ξ|An} ≤ a^ξ_n(p) ≤ e^{|ξ|An}` for `1 ≤ n` (`exists_crude_lowerQuantile_bounds`)
and `e^{-ξ} ≤ a^ξ_0(p) ≤ e^{ξ}` (the level-`0` field vanishes a.s., `DGZ.ae_forall_eq_zero_of_isBandVersion_self`);
with `|ϕ(ξ) - 1| ≤ √(2d) ξ` the powers of `2` are absorbed into `C = e^{B} 2^{√(2d) b N}`, `B = bAN + b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd WN IsLFPPKernel IsWhiteNoise IsBandVersion lfppDistance)

variable {d : ℕ}

/-! ### The finite net (NA3 R2(f)) -/

/-- **Equi-Lipschitz functions converging pointwise on `(0, ∞)` to a Lipschitz limit converge uniformly on `(0, b]`**
(the finite net of `d:prop-uexp`): grid points `(i + 1)δ`, `i < ⌈b/δ⌉`, with `δ = ε/(4(L + 1))`. -/
theorem u0_exists_uniform_of_lipschitz {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ n x y, |f n x - f n y| ≤ L * |x - y|) (hg : ∀ x y, |g x - g y| ≤ L * |x - y|)
    (hlim : ∀ x, 0 < x → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, 0 < x → x ≤ b → |f n x - g x| ≤ ε := by
  set δ : ℝ := ε / (4 * (L + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hLδ : L * δ ≤ ε / 4 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set K : ℕ := ⌈b / δ⌉₊ with hK
  have hev : ∀ᶠ n in atTop, ∀ i ∈ Finset.range K,
      |f n (((i : ℝ) + 1) * δ) - g (((i : ℝ) + 1) * δ)| < ε / 2 := by
    rw [Filter.eventually_all_finset]
    intro i _
    have hx : 0 < ((i : ℝ) + 1) * δ := by positivity
    filter_upwards [Metric.tendsto_nhds.1 (hlim _ hx) (ε / 2) (by positivity)] with n hn
    rwa [Real.dist_eq] at hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun n hn x hx hxb => ?_⟩
  have hxδ : 0 < x / δ := div_pos hx hδ0
  set j : ℕ := ⌈x / δ⌉₊ with hj
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hxδ).ne'
  have hjK : j ≤ K := Nat.ceil_mono (div_le_div_of_nonneg_right hxb hδ0.le)
  have hxle : x ≤ j * δ := by
    have := Nat.le_ceil (x / δ)
    rwa [div_le_iff₀ hδ0] at this
  have hjlt : (j : ℝ) * δ < x + δ := by
    have := Nat.ceil_lt_add_one hxδ.le
    have h2 : (j : ℝ) < x / δ + 1 := this
    calc (j : ℝ) * δ < (x / δ + 1) * δ := mul_lt_mul_of_pos_right h2 hδ0
      _ = x + δ := by field_simp
  have hi : j - 1 ∈ Finset.range K := Finset.mem_range.2 (by omega)
  have hcast : (((j - 1 : ℕ) : ℝ) + 1) = j := by
    rw [Nat.cast_sub hj1, Nat.cast_one]
    ring
  have h1 := hN n hn (j - 1) hi
  rw [hcast] at h1
  have hdist : |x - j * δ| ≤ δ := by
    rw [abs_le]
    constructor <;> linarith
  have h2 : |f n x - f n (j * δ)| ≤ L * δ :=
    (hf n x (j * δ)).trans (mul_le_mul_of_nonneg_left hdist hL)
  have h3 : |g (j * δ) - g x| ≤ L * δ := by
    have := hg (j * δ) x
    rw [abs_sub_comm (j * δ : ℝ) x] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdist hL)
  calc |f n x - g x| ≤ |f n x - f n (j * δ)| + |f n (j * δ) - g x| := abs_sub_le _ _ _
    _ ≤ |f n x - f n (j * δ)| + (|f n (j * δ) - g (j * δ)| + |g (j * δ) - g x|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
    _ ≤ ε := by linarith

/-! ### The rate -/

/-- **(D.1), first part** (`d:prop-uexp`): for `d ≥ 2`, `ϑ > 0` and `p ∈ (0, 1)` there is `N ≥ 1` with
`|log a^ξ_n(p)/(n log 2) - (ξQ(ξ) - 1)| ≤ ϑ` for all `ξ ∈ (0, b]`, all dyadic realizations and all `n ≥ N`. -/
theorem uExpRate_rate (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (b : ℝ) {ϑ : ℝ}
    (hϑ : 0 < ϑ) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ b →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
          |Real.log (DGZ.aQ P H ξ n p) / (n * Real.log 2) - (ξ * distExp d ξ - 1)| ≤ ϑ := by
  have hd0 : 0 < d := by omega
  -- the reference realization
  obtain ⟨W₀, hW₀⟩ := HigherDimLFPP.exists_isWhiteNoise d
  obtain ⟨H₀, hH₀⟩ := DGZ.exists_isDyadicRealization hκ hW₀
  -- uniform convergence of the mean exponents on `(0, b]`
  obtain ⟨Lf, hLf0, hLf⟩ := expMean_lipschitz hd0 hκ
  have hs0 : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
  have hf : ∀ (n : ℕ) (x y : ℝ), |expMean LQGDimension.ExistAsm.stdP H₀ x n -
      expMean LQGDimension.ExistAsm.stdP H₀ y n| ≤ (Lf + Real.sqrt (2 * d)) * |x - y| :=
    fun n x y => (hLf hH₀ n x y).trans
      (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  have hg : ∀ x y : ℝ, |(phiXi d x - 1) - (phiXi d y - 1)| ≤ (Lf + Real.sqrt (2 * d)) * |x - y| := by
    intro x y
    rw [sub_sub_sub_cancel_right]
    exact (phiXi_lipschitz hd x y).trans
      (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  obtain ⟨N₀, hN₀⟩ := u0_exists_uniform_of_lipschitz (by positivity) hf hg
    (fun x hx => tendsto_expMean hd hκ hH₀ hx.le) b (ε := ϑ / 2) (by positivity)
  -- the quantile error term
  set q : ℝ := HigherDimLFPP.Conc.quantileConst p.toReal with hq
  have hq0 : 0 ≤ q := HigherDimLFPP.Conc.quantileConst_nonneg _
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    ((u0_tendsto_const_div_sqrt (q * |b|)).eventually (Iic_mem_nhds (by positivity : (0 : ℝ) < ϑ / 2)))
  refine ⟨max (max N₀ N₁) 1, le_max_right _ _, ?_⟩
  intro ξ hξ hξb Ω _ P W H hH n hn
  have hn0 : N₀ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn1 : N₁ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : 1 ≤ n := (le_max_right _ _).trans hn
  rw [DGZ.aQ_eq_of_isDyadicRealization hH hH₀ ξ n p]
  have h1 := abs_log_aQ_div_sub_expMean_le hd0 hκ hH₀ hξ hn2 hp0 hp1
  have h2 := hN₀ n hn0 ξ hξ hξb
  rw [phiXi_of_pos hξ] at h2
  have h3 : q * |b| / √((n : ℝ) * Real.log 2) ≤ ϑ / 2 := hN₁ n hn1
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn2
  have hsq : 0 < √((n : ℝ) * Real.log 2) := Real.sqrt_pos.2 (by positivity)
  have h4 : q * ξ / √((n : ℝ) * Real.log 2) ≤ q * |b| / √((n : ℝ) * Real.log 2) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hξb.trans (le_abs_self b)) hq0) hsq.le
  calc |Real.log (DGZ.aQ LQGDimension.ExistAsm.stdP H₀ ξ n p) / (n * Real.log 2) -
        (ξ * distExp d ξ - 1)|
      ≤ |Real.log (DGZ.aQ LQGDimension.ExistAsm.stdP H₀ ξ n p) / (n * Real.log 2) -
          expMean LQGDimension.ExistAsm.stdP H₀ ξ n| +
        |expMean LQGDimension.ExistAsm.stdP H₀ ξ n - (ξ * distExp d ξ - 1)| := abs_sub_le _ _ _
    _ ≤ ϑ := by linarith

/-! ### The two-sided bound at every depth -/

/-- **(D.1), second part** (`d:prop-uexp`): for `d ≥ 2`, `b, ϑ > 0` and `p ∈ (0, 1)` there is `C > 0` with
`C⁻¹ 2^{-(1-ξQ(ξ)+ϑ)n} ≤ a^ξ_n(p) ≤ C 2^{-(1-ξQ(ξ)-ϑ)n}` for all `ξ ∈ (0, b]`, all dyadic realizations and **every**
`n ≥ 0` (the second conjunct of `UExpRate`). -/
theorem uExp_aQ_bounds (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b ϑ : ℝ} (hb : 0 < b)
    (hϑ : 0 < ϑ) {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ b →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ,
          C⁻¹ * (2 : ℝ) ^ (-((1 - ξ * distExp d ξ + ϑ) * n)) ≤ DGZ.aQ P H ξ n p ∧
            DGZ.aQ P H ξ n p ≤ C * (2 : ℝ) ^ (-((1 - ξ * distExp d ξ - ϑ) * n)) := by
  have hd0 : 0 < d := by omega
  have : NeZero d := ⟨hd0.ne'⟩
  obtain ⟨N, hN1, hrate⟩ := uExpRate_rate hd hκ b hϑ hp0 hp1
  obtain ⟨A, hA0, hA⟩ := HigherDimLFPP.exists_crude_lowerQuantile_bounds hκ hp0 hp1
  set s : ℝ := Real.sqrt (2 * d) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set B : ℝ := b * A * N + b with hB
  have hB0 : b ≤ B := by
    have : 0 ≤ b * A * N := by positivity
    linarith
  set C : ℝ := Real.exp B * (2 : ℝ) ^ (s * b * N) with hC
  have hC1 : 1 ≤ C := one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by linarith))
    (Real.one_le_rpow (by norm_num) (by positivity))
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨C, by linarith, ?_⟩
  intro ξ hξ hξb Ω _ P W H hH n
  have hP := hH.whiteNoise.isProbabilityMeasure
  -- `|ϕ(ξ) - 1| ≤ √(2d) ξ ≤ √(2d) b`
  have hφ : |ξ * distExp d ξ - 1| ≤ s * b := by
    have h := phiXi_lipschitz hd ξ 0
    rw [phiXi_of_pos hξ, phiXi_zero, sub_zero, abs_of_pos hξ] at h
    exact h.trans (mul_le_mul_of_nonneg_left hξb hs0)
  obtain ⟨hφlo, hφhi⟩ := abs_le.1 hφ
  have hapos : 0 < DGZ.aQ P H ξ n p := DGZ.tight_aQ_pos hd0 hH ξ n hp0 hp1
  have hpow0 : ∀ y : ℝ, 0 ≤ (2 : ℝ) ^ y := fun y => Real.rpow_nonneg (by norm_num) y
  rcases le_or_gt N n with hNn | hnN
  · -- large depth: from the rate
    have h := hrate ξ hξ hξb Ω P W H hH n hNn
    have hn1 : 1 ≤ n := hN1.trans hNn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hx : (0 : ℝ) < n * Real.log 2 := by positivity
    obtain ⟨hlo, hhi⟩ := abs_le.1 h
    have hlo' : (ξ * distExp d ξ - 1 - ϑ) * (n * Real.log 2) ≤ Real.log (DGZ.aQ P H ξ n p) :=
      (le_div_iff₀ hx).1 (by linarith)
    have hhi' : Real.log (DGZ.aQ P H ξ n p) ≤ (ξ * distExp d ξ - 1 + ϑ) * (n * Real.log 2) :=
      (div_le_iff₀ hx).1 (by linarith)
    constructor
    · calc C⁻¹ * (2 : ℝ) ^ (-((1 - ξ * distExp d ξ + ϑ) * n))
          ≤ (2 : ℝ) ^ (-((1 - ξ * distExp d ξ + ϑ) * n)) :=
            mul_le_of_le_one_left (hpow0 _) (inv_le_one_of_one_le₀ hC1)
        _ = Real.exp ((ξ * distExp d ξ - 1 - ϑ) * (n * Real.log 2)) := by
            rw [Real.rpow_def_of_pos two_pos]
            congr 1
            ring
        _ ≤ Real.exp (Real.log (DGZ.aQ P H ξ n p)) := Real.exp_le_exp.2 hlo'
        _ = DGZ.aQ P H ξ n p := Real.exp_log hapos
    · calc DGZ.aQ P H ξ n p = Real.exp (Real.log (DGZ.aQ P H ξ n p)) := (Real.exp_log hapos).symm
        _ ≤ Real.exp ((ξ * distExp d ξ - 1 + ϑ) * (n * Real.log 2)) := Real.exp_le_exp.2 hhi'
        _ = (2 : ℝ) ^ (-((1 - ξ * distExp d ξ - ϑ) * n)) := by
            rw [Real.rpow_def_of_pos two_pos]
            congr 1
            ring
        _ ≤ C * (2 : ℝ) ^ (-((1 - ξ * distExp d ξ - ϑ) * n)) :=
            le_mul_of_one_le_left (hpow0 _) hC1
  · -- small depth: crude bounds `e^{-B} ≤ a ≤ e^{B}`
    have hsmall : Real.exp (-B) ≤ DGZ.aQ P H ξ n p ∧ DGZ.aQ P H ξ n p ≤ Real.exp B := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · -- level `0`: the field vanishes almost surely
        have hband0 : IsBandVersion P W κ 1 1 (H 0) := (hH.band 0).congr_band (pow_zero _) rfl
        have h0 := DGZ.ae_forall_eq_zero_of_isBandVersion_self hκ hH.whiteNoise one_pos hband0
        have hbad : P {ω | lfppDistance d ξ (fun z => H 0 z ω) < Real.exp (-(|ξ| * 1)) ∨
            Real.exp (|ξ| * 1) < lfppDistance d ξ (fun z => H 0 z ω)} ≤ 0 := by
          refine le_of_eq (measure_mono_null
            ((HigherDimLFPP.Crude.bad_subset hd0 hband0.continuous ξ 1).trans ?_) (ae_iff.1 h0))
          rintro ω ⟨z, -, hz⟩ hall
          rw [hall z, abs_zero] at hz
          exact absurd hz (by norm_num)
        obtain ⟨h1, h2⟩ := HigherDimLFPP.Crude.lowerQuantile_mem_Icc_of_measure_le
          ((hH.band 0).measurable_lfppDistance ξ).aemeasurable hp0 hp1 hp0 zero_le hbad
        rw [abs_of_pos hξ, mul_one] at h1 h2
        exact ⟨(Real.exp_le_exp.2 (by linarith)).trans h1, h2.trans (Real.exp_le_exp.2 (by linarith))⟩
      · -- levels `1 ≤ n < N`: `e^{-|ξ| A n} ≤ a ≤ e^{|ξ| A n}`
        obtain ⟨h1, h2⟩ := hA ξ hH.whiteNoise hn ((hH.band n).congr_band (inv_pow 2 n) rfl)
        have hle : |ξ| * A * n ≤ B := by
          rw [abs_of_pos hξ]
          have h1' : ξ * A * n ≤ b * A * n :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hξb hA0.le) (Nat.cast_nonneg n)
          have h2' : b * A * n ≤ b * A * N :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast hnN.le) (by positivity)
          linarith
        exact ⟨(Real.exp_le_exp.2 (by linarith)).trans h1, h2.trans (Real.exp_le_exp.2 hle)⟩
    obtain ⟨hlo, hhi⟩ := hsmall
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
    have hsb : 0 ≤ s * b := by positivity
    constructor
    · -- `-(1 - ϕ + ϑ) n ≤ (ϕ - 1) n ≤ √(2d) b N`
      have hexp : -((1 - ξ * distExp d ξ + ϑ) * n) ≤ s * b * N := by
        have h1 : -((1 - ξ * distExp d ξ + ϑ) * n) ≤ s * b * n := by
          have : (ξ * distExp d ξ - 1 - ϑ) * n ≤ s * b * n :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
          linarith
        exact h1.trans (mul_le_mul_of_nonneg_left hnN' hsb)
      calc C⁻¹ * (2 : ℝ) ^ (-((1 - ξ * distExp d ξ + ϑ) * n))
          ≤ C⁻¹ * (2 : ℝ) ^ (s * b * N) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
              (inv_nonneg.2 (by linarith))
        _ = Real.exp (-B) := by
            rw [hC, mul_inv, mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos two_pos _).ne',
              mul_one, Real.exp_neg]
        _ ≤ DGZ.aQ P H ξ n p := hlo
    · -- `(1 - ϕ - ϑ) n ≤ √(2d) b N`
      have hexp : 0 ≤ s * b * N + -((1 - ξ * distExp d ξ - ϑ) * n) := by
        have h1 : (1 - ξ * distExp d ξ - ϑ) * n ≤ s * b * n :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
        have h2 : s * b * n ≤ s * b * N := mul_le_mul_of_nonneg_left hnN' hsb
        linarith
      calc DGZ.aQ P H ξ n p ≤ Real.exp B := hhi
        _ ≤ Real.exp B * (2 : ℝ) ^ (s * b * N + -((1 - ξ * distExp d ξ - ϑ) * n)) :=
            le_mul_of_one_le_right (Real.exp_pos B).le (Real.one_le_rpow (by norm_num) hexp)
        _ = C * (2 : ℝ) ^ (-((1 - ξ * distExp d ξ - ϑ) * n)) := by
            rw [hC, Real.rpow_add two_pos]
            exact (mul_assoc _ _ _).symm

/-! ### The interface -/

/-- **U-EXP** (`d:prop-uexp`, (D.1); the producer of the interface `UExpRate`, I4): for `d ≥ 2` and an admissible
kernel, `log a^ξ_n(p)/(n log 2) → ϕ(ξ) - 1` uniformly in `ξ ∈ (0, b]` and in the dyadic realization, with the
two-sided bound at every depth. -/
theorem uExpRate (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) : UExpRate d κ := by
  intro b ϑ hb hϑ p hp0 hp1
  obtain ⟨N, -, hN⟩ := uExpRate_rate hd hκ b hϑ hp0 hp1
  obtain ⟨C, hC, hCb⟩ := uExp_aQ_bounds hd hκ hb hϑ hp0 hp1
  exact ⟨N, C, hC, fun ξ hξ hξb Ω _ P W H hH =>
    ⟨hN ξ hξ hξb Ω P W H hH, hCb ξ hξ hξb Ω P W H hH⟩⟩

end HigherDimLQGContinuity
