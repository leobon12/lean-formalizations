import HigherDimLQGContinuity.Unif4.Quant
import HigherDimLQGMetric.DGZ.Lemma36Dyadic

/-!
# Uniform lower half of DGZ Lemma 3.6 (packet U1)

Blueprint Part D, `d:lem-u36` (NA3 §4.1; [8]-bp `r2:lem:36L`). Port of `HigherDimLQGMetric.DGZ.lemma36_lower` and
`DGZ.lemma36_lower_of_dgzHyp` (`DGZ/Lemma36.lean`, `DGZ/Lemma36Dyadic.lean`, MA7 D-3.6L).

**Statement** (`lemma36_lower_unif`). Let `d ≥ 2`, `κ` admissible, `b, δ > 0`. There is `C = C(d, κ, b, δ) > 0` such
that for every `ξ ∈ (0, b]` (no subcriticality is needed), every dyadic realization, all `x, y ∈ B̄₂(0)` with
`|x - y|_∞ ≥ 1/2` and all `n`: `P*[D_n(x, y; B₃(0)) < 2^{-(1-ξQ(ξ)+δ)n}] ≤ C e^{-n/C}`.

**Proof** (`[8]-bp r2:lem:36L` verbatim; the two changes of `d:lem-u36`):
* the chain argument `DGZ.prob_chain_ge` is deterministic in `ξ` up to the factor `e^{-|ξ| M}`, reused;
* the exponent step `log λ_{n+m} ≥ -(1 - ξQ + δ/4)(n + m) log 2` for `n + m ≥ N₀` takes `N₀` from U-EXP
  (`log_aQ_ge_unif`);
* the threshold `n₁` uses the uniform bound `c₀ = b M + |log J| + (δ/4 + √(2d) b) m log 2` of the constant
  `K₀ = |ξ| M + log J + (δ/4 - ξQ) m log 2` (from `1 - √(2d) b ≤ ξQ(ξ)`, `u1_phi_bounds`) and `c₁ = b q₀ √(log 2)`;
* the concentration rate is `c = δ² log 2/(8 b²) ≤ δ² log 2/(8 ξ²)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-- **Uniform DGZ Lemma 3.6, lower half** (`d:lem-u36`; port of `DGZ.lemma36_lower_of_dgzHyp`): for `d ≥ 2`, `κ`
admissible and `b, δ > 0` there is `C > 0` (depending only on `d, κ, b, δ`) such that for every `ξ ∈ (0, b]`, every
dyadic realization, all `x, y ∈ B̄₂(0)` with `|x - y|_∞ ≥ 1/2` and all `n`,
`P*[D_n(x, y; B₃(0)) < 2^{-(1-ξQ(ξ)+δ)n}] ≤ C e^{-n/C}`. -/
theorem lemma36_lower_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b : ℝ} (hb : 0 < b)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ b → ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ x y : Rd d, x ∈ cbox 0 2 → y ∈ cbox 0 2 → (∃ i, (1 : ℝ) / 2 ≤ |x i - y i|) →
        ∀ n : ℕ, P {ω | lfppDistOn ξ (fun z => H n z ω) (obox 0 3) x y <
          (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + δ) * n)} ≤
            ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  have hd0 : 0 < d := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow : ∀ k : ℕ, (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := fun k => by positivity
  -- the scale `m` and the chain length `J = 2·2^m`
  set m : ℕ := d + 4 with hmdef
  have hm : 9 * √(d : ℝ) < 2 ^ m := nine_mul_sqrt_lt_two_pow d
  set J : ℝ := 2 * 2 ^ m with hJ
  have hJ1 : 1 ≤ J := by
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    linarith
  -- the supremum of `h_m` on `B̄₂(0)`: `P[sup |h_m| > M] ≤ 1/10`
  obtain ⟨CG, hCG0, hCG⟩ := exists_sup_cbox_gaussian_tail hκ (R := 2) (by norm_num)
  set v : ℝ := Real.log (1 / (2 : ℝ)⁻¹ ^ m) with hv
  have hvpos : 0 < v := by
    rw [hv, log_one_div_inv_two_pow]
    have : (0 : ℝ) < m := by rw [hmdef]; positivity
    positivity
  set u₀ : ℝ := √(2 * v * Real.log 20) with hu₀
  set M : ℝ := √(2 * d) * v + CG * √v + CG + u₀ with hMdef
  have hM0 : 0 ≤ M := by positivity
  have htail : 2 * Real.exp (-u₀ ^ 2 / (2 * v)) = 1 / 10 := by
    have h20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
    rw [hu₀, Real.sq_sqrt (by positivity),
      show -(2 * v * Real.log 20) / (2 * v) = -Real.log 20 by field_simp, Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  -- the probability level `p = 2/(5J)` and its quantile constant
  set p : ℝ := 2 / (5 * J) with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p < 1 := by
    rw [hp, div_lt_one (by positivity)]
    linarith
  set q₀ : ℝ := Conc.quantileConst p with hq₀def
  have hq₀ : 0 ≤ q₀ := Real.sqrt_nonneg _
  -- the uniform exponent step (U-EXP): `log λ_N ≥ -(1 - ξQ + δ/4) N log 2` for `N ≥ N₀`
  have hhalf0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hhalf1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  obtain ⟨N₀, -, hlogN⟩ := log_aQ_ge_unif hd hκ b (ϑ := δ / 4) (by positivity) hhalf0 hhalf1
  -- the uniform constants of the final bound
  set c₀ : ℝ := b * M + |Real.log J| + (δ / 4 + √(2 * d) * b) * m * Real.log 2 with hc₀
  set c₁' : ℝ := b * q₀ * √(Real.log 2) with hc₁'def
  have hc₁' : 0 ≤ c₁' := by positivity
  have hc₀0 : 0 ≤ c₀ := by positivity
  set n₁ : ℕ := ⌈(4 * (c₀ + c₁') / (δ * Real.log 2)) ^ 2⌉₊ with hn₁
  set c : ℝ := δ ^ 2 * Real.log 2 / (8 * b ^ 2) with hcdef
  have hc : 0 < c := by positivity
  obtain ⟨C, hC0, hCsmall, hCbig⟩ := exists_const_exp_bound hc (max (max N₀ n₁) 1)
  refine ⟨C, hC0, ?_⟩
  intro ξ hξ hξb Ω _ P W H hHR x y hx hy hxy n
  have hW := hHR.whiteNoise
  have hH := hHR.band
  have := hW.isProbabilityMeasure
  set Q : ℝ := distExp d ξ with hQ
  -- small `n`
  by_cases hn : n < max (max N₀ n₁) 1
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 (hCsmall n hn))
  push Not at hn
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hnn₁ : n₁ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  -- the realization's median `λ_{n+m}`
  set lam := LQGMetric.lowerQuantile
    (P.map fun ω => lfppDistance d ξ fun z => H (n + m) z ω) 2⁻¹ with hlam
  have hlampos : 0 < lam := Conc.lowerQuantile_map_pos
    ((hH (n + m)).measurable_comp (measurable_lfppDistance_continuousMap ξ)).aemeasurable
    (ae_of_all _ fun ω => lfppDistance_pos hd0 ((hH (n + m)).continuous ω))
    (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  have hloglam : -(1 - ξ * Q + δ / 4) * ((n : ℝ) + m) * Real.log 2 ≤ Real.log lam := by
    have h := hlogN ξ hξ hξb Ω P W H hHR (n + m) (by omega)
    push_cast at h
    exact h
  -- a version of `h_m` and the probability lower bound of the chain argument
  obtain ⟨G, hG⟩ := exists_isBandVersion hκ hW (hpow m) 1
  have hGM : P {ω | ∃ z ∈ cbox (0 : Rd d) 2, M < |G z ω|} ≤ ENNReal.ofReal (1 / 10) := by
    have h := hCG hW (hpow m) (pow_le_one₀ (by norm_num) (by norm_num)) hG 0
      (Real.sqrt_nonneg (2 * v * Real.log 20))
    rw [mul_one, ← hv, ← hu₀, ← hMdef, htail] at h
    exact h
  have hxy' := half_le_norm_sub_of_exists hxy
  have hge := prob_chain_ge hd hκ hW ξ hm hG hGM (hH n) (hH (n + m)) hx hy hxy'
  set t : ℝ := (2 : ℝ) ^ m * Real.exp (-(|ξ| * M)) * lam / (2 * 2 ^ m) with htdef
  have ht : 0 < t := by positivity
  -- concentration (D-4.6): `E log D_n(x, y; B₃) > log t - |ξ| √(n log 2) q₀`
  have hab : (2 : ℝ)⁻¹ ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hx3 : x ∈ obox (0 : Rd d) 3 := cbox_subset_obox (by norm_num) hx
  have hy3 : y ∈ obox (0 : Rd d) 3 := cbox_subset_obox (by norm_num) hy
  have hΦ := isSupLipschitzOn_log_lfppDistOn ξ hx3 y (HigherDimLFPP.DGZ.obox_subset_cbox 0 3)
  have hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < lfppDistOn ξ φ (obox 0 3) x y := fun φ hφ =>
    lfppDistOn_pos hφ (ne_of_exists_half_le hxy)
      (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 3) hx3 hy3)
  have hconc := log_sub_lt_integral_log_of_le_measure_ge
    (Φ := fun φ => lfppDistOn ξ φ (obox 0 3) x y)
    hκ hW (hpow n) hab (hH n) (isCompact_cbox 0 3) hξ.ne' hΦ hpos ht hp0 hp1 hge
  -- the threshold `T' = 2^{-(1-ξQ+δ)n}` and the margin `u`
  set T' : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n) with hT'
  set u : ℝ := Real.log t - |ξ| * √(Real.log (1 / (2 : ℝ)⁻¹ ^ n)) * q₀ - Real.log T' with hudef
  have hlogT' : Real.log T' = -(1 - ξ * Q + δ) * n * Real.log 2 := Real.log_rpow two_pos _
  have hlogt : Real.log t = m * Real.log 2 - |ξ| * M + Real.log lam - Real.log J := by
    rw [htdef, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) hlampos.ne', Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_pow, Real.log_exp, hJ]
    ring
  have hsqrt : √(Real.log (1 / (2 : ℝ)⁻¹ ^ n)) = √(n : ℝ) * √(Real.log 2) := by
    rw [log_one_div_inv_two_pow, Real.sqrt_mul (Nat.cast_nonneg n)]
  set c₁ : ℝ := |ξ| * q₀ * √(Real.log 2) with hc₁def
  have hc₁le : c₁ ≤ c₁' := by
    rw [hc₁def, hc₁'def, abs_of_pos hξ]
    have h0 : 0 ≤ q₀ * √(Real.log 2) := by positivity
    have := mul_le_mul_of_nonneg_right hξb h0
    linarith
  have hu_eq : u = m * Real.log 2 - |ξ| * M + Real.log lam - Real.log J - c₁ * √(n : ℝ) +
      (1 - ξ * Q + δ) * n * Real.log 2 := by
    rw [hudef, hlogt, hlogT', hsqrt, hc₁def]
    ring
  -- the constant `K₀` is bounded by the uniform `c₀`
  set K₀ : ℝ := |ξ| * M + Real.log J + (δ / 4 - ξ * Q) * m * Real.log 2 with hK₀
  have hK : K₀ ≤ c₀ := by
    have hphi := (u1_phi_bounds hd hξ hξb).1
    have h1 : |ξ| * M ≤ b * M := by
      rw [abs_of_pos hξ]
      exact mul_le_mul_of_nonneg_right hξb hM0
    have h2 : Real.log J ≤ |Real.log J| := le_abs_self _
    have h3 : (δ / 4 - ξ * Q) * m * Real.log 2 ≤ (δ / 4 + √(2 * d) * b) * m * Real.log 2 := by
      have hml : (0 : ℝ) ≤ m * Real.log 2 := by positivity
      have h4 : δ / 4 - ξ * Q ≤ δ / 4 + √(2 * d) * b := by
        have : 0 ≤ √(2 * d) * b := by positivity
        linarith
      have := mul_le_mul_of_nonneg_right h4 hml
      linarith
    rw [hK₀, hc₀]
    linarith
  -- `c₀ + c₁ √n ≤ (δ/4) n log 2` for `n ≥ n₁`
  have hsqrtn1 : 1 ≤ √(n : ℝ) := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  have hsqrtn : 4 * (c₀ + c₁') / (δ * Real.log 2) ≤ √(n : ℝ) := by
    have h1 : (4 * (c₀ + c₁') / (δ * Real.log 2)) ^ 2 ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hnn₁)
    calc 4 * (c₀ + c₁') / (δ * Real.log 2) = √((4 * (c₀ + c₁') / (δ * Real.log 2)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt h1
  have hkey : c₀ + c₁ * √(n : ℝ) ≤ δ / 4 * n * Real.log 2 := by
    have h2 : c₀ + c₁' ≤ δ / 4 * Real.log 2 * √(n : ℝ) := by
      rw [div_le_iff₀ (by positivity)] at hsqrtn
      linarith
    have hnsq : (n : ℝ) = √(n : ℝ) * √(n : ℝ) := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    have hc1n : c₁ * √(n : ℝ) ≤ c₁' * √(n : ℝ) :=
      mul_le_mul_of_nonneg_right hc₁le (Real.sqrt_nonneg _)
    calc c₀ + c₁ * √(n : ℝ) ≤ c₀ * √(n : ℝ) + c₁' * √(n : ℝ) :=
          add_le_add (le_mul_of_one_le_right hc₀0 hsqrtn1) hc1n
      _ = (c₀ + c₁') * √(n : ℝ) := by ring
      _ ≤ (δ / 4 * Real.log 2 * √(n : ℝ)) * √(n : ℝ) :=
          mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
      _ = δ / 4 * (√(n : ℝ) * √(n : ℝ)) * Real.log 2 := by ring
      _ = δ / 4 * n * Real.log 2 := by rw [← hnsq]
  -- `u ≥ (δ/2) n log 2`
  have hu : δ / 2 * n * Real.log 2 ≤ u := by
    have hdecomp : u - δ / 2 * n * Real.log 2 =
        (Real.log lam + (1 - ξ * Q + δ / 4) * ((n : ℝ) + m) * Real.log 2) +
          (δ / 4 * n * Real.log 2 - (c₀ + c₁ * √(n : ℝ))) + (c₀ - K₀) := by
      rw [hu_eq, hK₀]
      ring
    have h1 : 0 ≤ Real.log lam + (1 - ξ * Q + δ / 4) * ((n : ℝ) + m) * Real.log 2 := by
      have := hloglam
      linarith
    linarith
  have hu0 : 0 ≤ u := le_trans (by positivity) hu
  have hle : Real.log T' + u ≤
      ∫ ω, Real.log (lfppDistOn ξ (fun z => H n z ω) (obox 0 3) x y) ∂P := by
    rw [hudef]
    linarith
  -- the tail bound
  have htail2 := measure_lt_le_of_log_add_le_integral
    (Φ := fun φ => lfppDistOn ξ φ (obox 0 3) x y) hκ hW (hpow n) hab.le (hH n)
    (isCompact_cbox 0 3) hΦ hpos hu0 hle
  rw [log_one_div_inv_two_pow] at htail2
  have hexp : -u ^ 2 / (2 * ξ ^ 2 * (n * Real.log 2)) ≤ -(c * n) := by
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have h1 : (δ / 2 * n * Real.log 2) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hu 2
    have hξ2 : ξ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hξ.le hξb 2
    have h2 : c * n * (2 * ξ ^ 2 * (n * Real.log 2)) =
        (δ / 2 * n * Real.log 2) ^ 2 * (ξ ^ 2 / b ^ 2) := by
      rw [hcdef]
      field_simp
      ring
    have h3 : ξ ^ 2 / b ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hξ2
    have h4 : 0 ≤ (δ / 2 * n * Real.log 2) ^ 2 := sq_nonneg _
    calc c * n * (2 * ξ ^ 2 * (n * Real.log 2))
        = (δ / 2 * n * Real.log 2) ^ 2 * (ξ ^ 2 / b ^ 2) := h2
      _ ≤ (δ / 2 * n * Real.log 2) ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 h4
      _ = (δ / 2 * n * Real.log 2) ^ 2 := mul_one _
      _ ≤ u ^ 2 := h1
  exact htail2.trans (ENNReal.ofReal_le_ofReal
    ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (by norm_num)).trans (hCbig n)))

end HigherDimLQGContinuity
