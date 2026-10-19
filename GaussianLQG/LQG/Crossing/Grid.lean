import GaussianLQG.LQG.FirstOrder
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Grid residuals (blueprint Lemma `lem:grid-residual`)

For `S : Setup`, `s, t ∈ [0, 1]` let `r(s, t) = |is - (1 + it)| = √(1 + (s - t)²)` and
`𝓡(s, t) = (log D^γ(is, 1 + it) - b_γ - ξ_γ Q_γ log r(s, t)) / ξ_γ - H(s, t)` (`Setup.residual`).
Let `m(γ) = ⌈3 log₂(1/ξ_γ)⌉` (`Setup.gridLevel`) and `S_m = {k 2^{-m} : 0 ≤ k ≤ 2^m}`, so that
`2^{-m(γ)} ≤ ξ³` and `#S_{m(γ)}² ≤ 16 ξ^{-6}`.

* `Setup.exists_residual_tail`: Proposition `prop:first-order` with `K` the unit square, `δ = 1`
  and `p = 150`, plus Chebyshev: `P[|𝓡(s,t)| ≥ ε] ≤ (C/ε)^{150} ξ^{150/24}` uniformly in
  `s, t ∈ [0, 1]`.
* `Setup.tendsto_measure_exists_gridResidual`: `P[max_{S_m²} |𝓡| ≥ ε] → 0`, by the union bound
  `16 ξ^{-6} (C/ε)^{150} ξ^{150/24} = 16 (C/ε)^{150} ξ^{1/4}`.
* `Setup.gridResidual` (blueprint Lemma `lem:grid-residual`): `max_{S_{m(γ)}²} |𝓡| → 0` in
  probability (`Setup.gridResidualMax`).

Generic helpers: the union bound over a square grid (`Crossing.measure_exists_grid_le`) and the
limit `x^{-n} e^{-c x^{-b}} → 0` as `x ↓ 0` (`Crossing.tendsto_inv_pow_mul_exp_neg_div_rpow`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric

namespace Crossing

/-! ## Generic helpers -/

/-- The closed unit square `[0, 1]²` of blueprint §1.1, as a subset of `ℂ`. -/
abbrev unitSquare : Set ℂ := Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1

theorem isCompact_unitSquare : IsCompact unitSquare := isCompact_Icc.reProdIm isCompact_Icc

theorem sI_mem_unitSquare {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : (s : ℂ) * Complex.I ∈ unitSquare := by
  rw [Complex.mem_reProdIm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, mul_one, sub_zero, Complex.mul_im, add_zero]
  exact ⟨⟨le_rfl, zero_le_one⟩, hs⟩

theorem one_add_tI_mem_unitSquare {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 + (t : ℂ) * Complex.I ∈ unitSquare := by
  rw [Complex.mem_reProdIm]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
    Complex.one_im, Complex.mul_im, zero_add]
  exact ⟨⟨zero_le_one, le_rfl⟩, ht⟩

/-- `is - (1 + it) = -1 + i(s - t)`. -/
theorem sI_sub_one_add_tI (s t : ℝ) :
    (s : ℂ) * Complex.I - (1 + (t : ℂ) * Complex.I) = -1 + ((s - t : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring

/-- `|is - (1 + it)|² = 1 + (s - t)²`. -/
theorem norm_sI_sub_one_add_tI_sq (s t : ℝ) :
    ‖(s : ℂ) * Complex.I - (1 + (t : ℂ) * Complex.I)‖ ^ 2 = 1 + (s - t) ^ 2 := by
  rw [sI_sub_one_add_tI, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
    Complex.add_im, Complex.neg_im, Complex.one_im, neg_zero, Complex.mul_im, zero_add]
  ring

/-- The union bound over a square grid: if each of the events `{P k l}`, `k, l ≤ n`, has measure
at most `B`, their union has measure at most `(n + 1)² B`. -/
theorem measure_exists_grid_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (n : ℕ)
    (P : ℕ → ℕ → α → Prop) {B : ℝ≥0∞} (h : ∀ k ≤ n, ∀ l ≤ n, μ {ω | P k l ω} ≤ B) :
    μ {ω | ∃ k ≤ n, ∃ l ≤ n, P k l ω} ≤ ((n : ℝ≥0∞) + 1) ^ 2 * B := by
  have e : {ω | ∃ k ≤ n, ∃ l ≤ n, P k l ω} =
      ⋃ k ∈ Finset.range (n + 1), ⋃ l ∈ Finset.range (n + 1), {ω | P k l ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, Nat.lt_succ_iff, exists_prop]
  rw [e]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have h2 : ∀ k ∈ Finset.range (n + 1),
      μ (⋃ l ∈ Finset.range (n + 1), {ω | P k l ω}) ≤ ((n : ℝ≥0∞) + 1) * B := by
    intro k hk
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun l hl => h k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) l
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- `x^{-n} e^{-c x^{-b}} → 0` as `x ↓ 0`, for `b, c > 0`. -/
theorem tendsto_inv_pow_mul_exp_neg_div_rpow (n : ℕ) {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun x : ℝ => x⁻¹ ^ n * Real.exp (-(c / x ^ b))) (𝓝[>] 0) (𝓝 0) := by
  have hy : Tendsto (fun x : ℝ => x ^ (-b)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by linarith)
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n : ℝ) / b) c hc).comp hy
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  simp only [Function.comp]
  have e1 : (x ^ (-b)) ^ ((n : ℝ) / b) = x⁻¹ ^ n := by
    rw [← Real.rpow_mul hx.le, show -b * ((n : ℝ) / b) = -(n : ℝ) by field_simp,
      Real.rpow_neg hx.le, Real.rpow_natCast, inv_pow]
  have e2 : -c * x ^ (-b) = -(c / x ^ b) := by
    rw [Real.rpow_neg hx.le, div_eq_mul_inv, neg_mul]
  rw [e1, e2]

/-- For `0 < x ≤ 1` and `m = ⌈3 log₂(1/x)⌉`: `x^{-3} ≤ 2^m < 2 x^{-3}`. -/
theorem inv_pow_three_le_two_pow_ceil {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    x⁻¹ ^ 3 ≤ (2 : ℝ) ^ ⌈3 * Real.logb 2 (1 / x)⌉₊ ∧
      (2 : ℝ) ^ ⌈3 * Real.logb 2 (1 / x)⌉₊ < 2 * x⁻¹ ^ 3 := by
  set L := Real.logb 2 (1 / x) with hL
  have h1x : 1 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
  have hL0 : 0 ≤ L := Real.logb_nonneg one_lt_two h1x
  have hpow : (2 : ℝ) ^ (3 * L) = x⁻¹ ^ 3 := by
    rw [mul_comm, Real.rpow_mul zero_le_two, Real.rpow_logb two_pos (by norm_num)
      (by positivity), Real.rpow_ofNat, one_div]
  set m := ⌈3 * L⌉₊ with hm
  have hm1 : 3 * L ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < 3 * L + 1 := Nat.ceil_lt_add_one (by positivity)
  constructor
  · rw [← hpow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hm1
  · rw [← hpow, ← Real.rpow_natCast]
    calc (2 : ℝ) ^ (m : ℝ) < 2 ^ (3 * L + 1) := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hm2
      _ = 2 * 2 ^ (3 * L) := by
          rw [Real.rpow_add two_pos, Real.rpow_one, mul_comm]

/-- The grid points `k 2^{-m}`, `k ≤ 2^m`, lie in `[0, 1]`. -/
theorem div_two_pow_mem_Icc {m k : ℕ} (hk : k ≤ 2 ^ m) : (k : ℝ) / 2 ^ m ∈ Icc (0 : ℝ) 1 := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  refine ⟨by positivity, (div_le_one h2).2 ?_⟩
  exact_mod_cast hk

/-- `(2^m + 1)² ξ^{-6}`-type arithmetic: `ξ^{-6} ξ^{150/24} = ξ^{1/4}`. -/
theorem inv_pow_six_mul_rpow {x : ℝ} (hx : 0 < x) :
    x⁻¹ ^ 6 * x ^ (150 / 24 : ℝ) = x ^ (1 / 4 : ℝ) := by
  rw [show (150 / 24 : ℝ) = ((6 : ℕ) : ℝ) + 1 / 4 by norm_num, Real.rpow_add hx,
    Real.rpow_natCast, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hx.ne'), one_mul]

/-- `#S_m² = (2^m + 1)²` as an extended real. -/
theorem natCast_two_pow_add_one_sq (m : ℕ) :
    (((2 ^ m : ℕ) : ℝ≥0∞) + 1) ^ 2 = ENNReal.ofReal (((2 : ℝ) ^ m + 1) ^ 2) := by
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
    ENNReal.ofReal_one, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  push_cast
  rfl

/-! ## Compatibility names (cleanup W15) -/

alias one_le_norm_sI_sub_one_add_tI := one_le_norm_sI_sub

end Crossing

open Crossing

namespace Setup

variable (S : Setup)

/-! ## The grid and the residual -/

/-- The grid level `m(γ) = ⌈3 log₂(1/ξ_γ)⌉` (blueprint §6). -/
def gridLevel (γ : ℝ) : ℕ := ⌈3 * Real.logb 2 (1 / S.ξ γ)⌉₊

/-- `2^{-m(γ)} ≤ ξ_γ³`, in the form `ξ^{-3} ≤ 2^{m(γ)}`. -/
theorem inv_pow_three_le_two_pow_gridLevel {γ : ℝ} (hξ : 0 < S.ξ γ) (hξ1 : S.ξ γ ≤ 1) :
    (S.ξ γ)⁻¹ ^ 3 ≤ (2 : ℝ) ^ S.gridLevel γ :=
  (inv_pow_three_le_two_pow_ceil hξ hξ1).1

/-- `#S_{m(γ)}² = (2^{m(γ)} + 1)² ≤ 16 ξ_γ^{-6}`. -/
theorem sq_two_pow_gridLevel_add_one_le {γ : ℝ} (hξ : 0 < S.ξ γ) (hξ1 : S.ξ γ ≤ 1) :
    ((2 : ℝ) ^ S.gridLevel γ + 1) ^ 2 ≤ 16 * (S.ξ γ)⁻¹ ^ 6 := by
  have h := (inv_pow_three_le_two_pow_ceil hξ hξ1).2
  have h1 : (1 : ℝ) ≤ 2 ^ S.gridLevel γ := one_le_pow₀ one_le_two
  have h2 : (2 : ℝ) ^ S.gridLevel γ + 1 ≤ 4 * (S.ξ γ)⁻¹ ^ 3 := by
    unfold gridLevel at h1 ⊢
    linarith
  have h3 : 0 ≤ (2 : ℝ) ^ S.gridLevel γ + 1 := by positivity
  calc ((2 : ℝ) ^ S.gridLevel γ + 1) ^ 2 ≤ (4 * (S.ξ γ)⁻¹ ^ 3) ^ 2 := pow_le_pow_left₀ h3 h2 2
    _ = 16 * (S.ξ γ)⁻¹ ^ 6 := by ring

/-- The residual `𝓡(s,t) = (log D^γ(is, 1+it) - b_γ - ξ_γ Q_γ log r(s,t)) / ξ_γ - H(s,t)`, with
`r(s,t) = |is - (1+it)| = √(1 + (s-t)²)` (blueprint §6). -/
def residual (γ s t : ℝ) (ω : Coord) : ℝ :=
  (Real.log ((S.D γ ω).1 ((s : ℂ) * Complex.I, 1 + (t : ℂ) * Complex.I)) - S.b γ -
      S.ξ γ * Q γ * Real.log ‖(s : ℂ) * Complex.I - (1 + (t : ℂ) * Complex.I)‖) / S.ξ γ -
    S.H s t ω

theorem measurable_residual (γ s t : ℝ) : Measurable (S.residual γ s t) :=
  S.measurable_firstOrderErr γ _ _

/-- **Tail of the residual** (blueprint proof of Lemma `lem:grid-residual`): Proposition
`prop:first-order` with `K` the unit square, `δ = 1` and `p = 150`, and Chebyshev's inequality:
`P[|𝓡(s,t)| ≥ ε] ≤ (C/ε)^{150} ξ_γ^{150/24}` for `γ ∈ (0, γ*]`, uniformly in `s, t ∈ [0, 1]`. -/
theorem exists_residual_tail (hY : S.EnergyApprox) :
    ∃ γs C : ℝ, 0 < γs ∧ 0 ≤ C ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε →
        stdP {ω | ε ≤ |S.residual γ s t ω|} ≤
          ENNReal.ofReal ((C / ε) ^ (150 : ℝ) * S.ξ γ ^ (150 / 24 : ℝ)) := by
  obtain ⟨γs, C, hγs, hC⟩ := S.firstOrder hY isCompact_unitSquare one_pos
    (p := 150) (by norm_num)
  refine ⟨min γs 1, max C 0, lt_min hγs one_pos, le_max_right _ _,
    fun γ hγ s hs t ht ε hε => ?_⟩
  have hγ' : γ ∈ Ioc (0 : ℝ) γs := ⟨hγ.1, hγ.2.trans (min_le_left _ _)⟩
  have hξ : 0 < S.ξ γ :=
    S.ξ_pos γ hγ.1 ((hγ.2.trans (min_le_right _ _)).trans_lt one_lt_two)
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hb : eLpNorm (S.residual γ s t) (ENNReal.ofReal 150) stdP ≤
      ENNReal.ofReal (C' * S.ξ γ ^ (1 / 24 : ℝ)) :=
    (hC γ hγ' _ (sI_mem_unitSquare hs) _ (one_add_tI_mem_unitSquare ht)
      (one_le_norm_sI_sub s t)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hset : {ω | ε ≤ |S.residual γ s t ω|} =
      {ω | ENNReal.ofReal ε ≤ ‖S.residual γ s t ω‖ₑ} := by
    ext ω
    simp only [mem_ofPred_eq, Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).symm
  rw [hset]
  have h150 : (ENNReal.ofReal 150).toReal = 150 := ENNReal.toReal_ofReal (by norm_num)
  have hcheb := meas_ge_le_mul_pow_eLpNorm_enorm stdP (p := ENNReal.ofReal 150) (by simp)
    ENNReal.ofReal_ne_top (S.measurable_residual γ s t).aestronglyMeasurable
    (ε := ENNReal.ofReal ε) (by simpa using hε) (fun h => absurd h ENNReal.ofReal_ne_top)
  rw [h150] at hcheb
  refine hcheb.trans ?_
  calc (ENNReal.ofReal ε)⁻¹ ^ (150 : ℝ) *
        eLpNorm (S.residual γ s t) (ENNReal.ofReal 150) stdP ^ (150 : ℝ)
      ≤ (ENNReal.ofReal ε)⁻¹ ^ (150 : ℝ) *
          ENNReal.ofReal (C' * S.ξ γ ^ (1 / 24 : ℝ)) ^ (150 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal ((C' / ε) ^ (150 : ℝ) * S.ξ γ ^ (150 / 24 : ℝ)) := by
        rw [← ENNReal.ofReal_inv_of_pos hε,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow hC'0 (by positivity), ← Real.rpow_mul hξ.le, Real.div_rpow hC'0 hε.le,
          Real.inv_rpow hε.le, show (1 / 24 : ℝ) * 150 = 150 / 24 by norm_num]
        ring

/-- **Blueprint Lemma `lem:grid-residual`**, union-bound form: for every `ε > 0`,
`P[|𝓡(s,t)| ≥ ε for some (s,t) ∈ S_{m(γ)}²] → 0` as `γ ↓ 0`. -/
theorem tendsto_measure_exists_gridResidual (hY : S.EnergyApprox) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun γ => stdP {ω | ∃ k : ℕ, k ≤ 2 ^ S.gridLevel γ ∧ ∃ l : ℕ,
      l ≤ 2 ^ S.gridLevel γ ∧
        ε ≤ |S.residual γ ((k : ℝ) / 2 ^ S.gridLevel γ) ((l : ℝ) / 2 ^ S.gridLevel γ) ω|})
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨γs, C, hγs, hC0, hC⟩ := S.exists_residual_tail hY
  obtain ⟨⟨γe, C₁, hγe, hγe2, hb⟩, -, -⟩ := S.exponents
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (S.tendsto_ofReal_mul_xi_rpow (16 * (C / ε) ^ (150 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 4))
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioc_mem_nhdsGT (lt_min hγs hγe)] with γ hγ
  have hγs' : γ ∈ Ioc (0 : ℝ) γs := ⟨hγ.1, hγ.2.trans (min_le_left _ _)⟩
  have hγe' : γ ∈ Ioc (0 : ℝ) γe := ⟨hγ.1, hγ.2.trans (min_le_right _ _)⟩
  obtain ⟨h1, -, h3, -⟩ := hb γ hγe'
  have hξ : 0 < S.ξ γ := lt_of_lt_of_le (by linarith [hγ.1]) h1
  have hξ1 : S.ξ γ ≤ 1 := h3.trans (by norm_num)
  set m := S.gridLevel γ with hm
  refine (measure_exists_grid_le stdP (2 ^ m) _
    (B := ENNReal.ofReal ((C / ε) ^ (150 : ℝ) * S.ξ γ ^ (150 / 24 : ℝ)))
    fun k hk l hl => hC γ hγs' _ (div_two_pow_mem_Icc hk) _ (div_two_pow_mem_Icc hl) ε hε).trans ?_
  rw [natCast_two_pow_add_one_sq, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hgrid := S.sq_two_pow_gridLevel_add_one_le hξ hξ1
  rw [← hm] at hgrid
  calc ((2 : ℝ) ^ m + 1) ^ 2 * ((C / ε) ^ (150 : ℝ) * S.ξ γ ^ (150 / 24 : ℝ))
      ≤ 16 * (S.ξ γ)⁻¹ ^ 6 * ((C / ε) ^ (150 : ℝ) * S.ξ γ ^ (150 / 24 : ℝ)) :=
        mul_le_mul_of_nonneg_right hgrid (by positivity)
    _ = 16 * (C / ε) ^ (150 : ℝ) * ((S.ξ γ)⁻¹ ^ 6 * S.ξ γ ^ (150 / 24 : ℝ)) := by ring
    _ = 16 * (C / ε) ^ (150 : ℝ) * S.ξ γ ^ (1 / 4 : ℝ) := by rw [inv_pow_six_mul_rpow hξ]

/-- `max_{(s,t) ∈ S_{m(γ)}²} |𝓡(s,t)|` (blueprint Lemma `lem:grid-residual`). -/
def gridResidualMax (γ : ℝ) (ω : Coord) : ℝ :=
  ⨆ kl : Fin (2 ^ S.gridLevel γ + 1) × Fin (2 ^ S.gridLevel γ + 1),
    |S.residual γ (((kl.1 : ℕ) : ℝ) / 2 ^ S.gridLevel γ) (((kl.2 : ℕ) : ℝ) / 2 ^ S.gridLevel γ) ω|

/-- **Blueprint Lemma `lem:grid-residual`**, assuming Lemma `lem:energy-approx`: with
`m(γ) = ⌈3 log₂(1/ξ_γ)⌉`, `max_{(s,t) ∈ S_{m(γ)}²} |𝓡(s,t)| → 0` in probability as `γ ↓ 0`. -/
theorem gridResidual (hY : S.EnergyApprox) :
    TendstoInMeasure stdP S.gridResidualMax (𝓝[>] 0) fun _ => 0 := by
  refine tendstoInMeasure_iff_dist.2 fun ε hε => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (S.tendsto_measure_exists_gridResidual hY hε) (fun _ => zero_le) fun γ => measure_mono ?_
  intro ω hω
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  obtain ⟨kl, hkl⟩ := exists_eq_ciSup_of_finite (f := fun kl : Fin (2 ^ S.gridLevel γ + 1) ×
    Fin (2 ^ S.gridLevel γ + 1) => |S.residual γ (((kl.1 : ℕ) : ℝ) / 2 ^ S.gridLevel γ)
      (((kl.2 : ℕ) : ℝ) / 2 ^ S.gridLevel γ) ω|)
  refine ⟨kl.1, Nat.lt_succ_iff.1 kl.1.2, kl.2, Nat.lt_succ_iff.1 kl.2.2, ?_⟩
  have hmax : S.gridResidualMax γ ω = |S.residual γ (((kl.1 : ℕ) : ℝ) / 2 ^ S.gridLevel γ)
      (((kl.2 : ℕ) : ℝ) / 2 ^ S.gridLevel γ) ω| := hkl.symm
  rw [hmax, abs_abs] at hω
  exact hω

end Setup

end GaussianLQG
