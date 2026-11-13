import InteractingSLE.SLE8.TraceBridge
import InteractingSLE.SLE8.TimeGrid
import QuantumZipper.Proofs.RS.KoebeLoewner
import QuantumZipper.Proofs.RS.BMModulus
import Mathlib.Probability.BrownianMotion.Basic

/-!
# SLE₈ note, Proposition 5.1 from its inputs, and Theorem 1.1 from the scale count

Source: `source/sle8-continuity.pdf`, §5 (anchors `prop-5.1`, `prop-5.1-proof`, `thm-1.1-proof`,
PDF pp. 10–12), transcription `source/sle8/sle8-continuity.md`. Notation of the note, with the API of
`InteractingSLE/SLE8/TimeGrid.lean`: `y_k = 2^{-k}` (`dyadicHeight`), `t_k` (`gridTime`),
`A_k(t) = y_k |F_t'(i y_k)|` (`normalizedDeriv`), `Ω_M` of (2.11) (`DriverBound`),
`F_t = fwdMapInv W t`, `W = √8 B` (`drive 8 B ω`).

The proof of Proposition 5.1 combines

* Lemma 2.1 (consequence of Alvisio–Lawler): `sup_{t ≤ 1} A_k(t) ≤ C_β k^{-β}`;
* Proposition 4.1 (number of large scales): `sup_{t ≤ 1} |I_n(t)| ≤ r^7` eventually;
* Lemma 2.3 (comparison with a time grid) on the events `Ω_M`, proved in `TimeGrid.lean`
  (`exists_normalizedDeriv_le_gridTime`, with a fixed exponent `p` in place of `2`);
* `ℙ(⋃_M Ω_M) = 1` (here, `ae_exists_driveBound`, from QuantumZipper's Brownian modulus);
* fixed-factor Koebe distortion (5.5) (here, from QuantumZipper's vertical distortion).

Lemma 2.1 and Proposition 4.1 are the hypotheses of the conditional results below, stated as the note
states them. Everything else is proved: (5.5), the block bound (5.3), the summation (5.4), the final
bound (5.1), Brownian scaling, and the passage to the trace (`TraceBridge.lean`).

## Main results

* `radial_bound_of_scale_count`: pathwise (deterministic) form of the proof of Proposition 5.1.
* `ae_exists_driveBound`: `ℙ(⋃_M Ω_M) = 1` for `W = √8 B`.
* `ae_radial_bound_of_scale_count`: Proposition 5.1 from Lemma 2.1 and Proposition 4.1.
* `ae_exists_continuous_trace_of_scale_count`: the conclusion of the frozen Theorem 1.1
  (`ae_exists_continuous_trace`) from Lemma 2.1 and Proposition 4.1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Complex
open scoped NNReal ENNReal Topology

namespace InteractingSLE.SLE8

open QuantumZipper

theorem normalizedDeriv_nonneg (W : ℝ → ℝ) (k : ℕ) (t : ℝ) : 0 ≤ normalizedDeriv W k t := by
  unfold normalizedDeriv dyadicHeight
  positivity

variable {W : ℝ → ℝ}

/-! ## Fixed-factor Koebe distortion on a dyadic vertical interval, (5.5) -/

/-- The Koebe constant of (5.5): QuantumZipper's vertical distortion constant `koebeStepConst²`. -/
def koebeVertConst : ℝ := RS.koebeStepConst ^ 2

theorem koebeVertConst_nonneg : 0 ≤ koebeVertConst := by
  unfold koebeVertConst
  positivity

/-- **(5.5).** `∫_y^{2y} |F_t'(iv)| dv ≤ C y |F_t'(iy)|` (fixed-factor Koebe distortion). -/
theorem lintegral_Ioc_two_mul_le (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {y : ℝ} (hy : 0 < y) :
    ∫⁻ v in Ioc y (2 * y), ‖deriv (fwdMapInv W t) (v * I)‖ₑ ≤
      ENNReal.ofReal (koebeVertConst * (y * ‖deriv (fwdMapInv W t) (y * I)‖)) := by
  set f : ℂ → ℂ := fwdMapInv W t with hf
  have hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im} := RS.differentiableOn_fwdMapInv hW hW0 ht
  have hinj : InjOn f {z : ℂ | 0 < z.im} := RS.injOn_fwdMapInv hW hW0 ht
  calc ∫⁻ v in Ioc y (2 * y), ‖deriv f (v * I)‖ₑ
      ≤ ∫⁻ _ in Ioc y (2 * y), ENNReal.ofReal (koebeVertConst * ‖deriv f (y * I)‖) := by
        refine setLIntegral_mono measurable_const fun v hv => ?_
        have hs1 : 1 / 2 ≤ v / y := by
          rw [le_div_iff₀ hy]
          linarith [hv.1]
        have hs2 : v / y ≤ 2 := by
          rw [div_le_iff₀ hy]
          exact hv.2
        have h := (RS.deriv_ratio_le_vertical hd hinj hy hs1 hs2).1
        rw [div_mul_cancel₀ v hy.ne'] at h
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (koebeVertConst * (y * ‖deriv f (y * I)‖)) := by
        rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by
          have := koebeVertConst_nonneg
          positivity)]
        congr 1
        ring

/-! ## Dyadic coverings -/

/-- `(2^{-M'}, 2^{-M}] ⊆ ⋃_{M < k ≤ M'} (y_k, 2 y_k]`. -/
theorem Ioc_inv_two_pow_subset_biUnion (M M' : ℕ) :
    Ioc ((2 : ℝ) ^ M')⁻¹ ((2 : ℝ) ^ M)⁻¹ ⊆
      ⋃ k ∈ Finset.Ioc M M', Ioc ((2 : ℝ) ^ k)⁻¹ (2 * ((2 : ℝ) ^ k)⁻¹) := by
  intro v hv
  have hvpos : 0 < v := lt_of_le_of_lt (by positivity) hv.1
  have h1 : (2 : ℝ) ^ M ≤ v⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hvpos]
    exact hv.2
  have h2 : v⁻¹ < (2 : ℝ) ^ M' := by
    rw [inv_lt_comm₀ hvpos (by positivity)]
    exact hv.1
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) |>.trans h1)
    (by norm_num : (1 : ℝ) < 2)
  have hkM : M < m + 1 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 (h1.trans_lt hm2)
  have hkM' : m < M' := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 (hm1.trans_lt h2)
  refine mem_iUnion₂.2 ⟨m + 1, Finset.mem_Ioc.2 ⟨hkM, hkM'⟩, ?_, ?_⟩
  · rw [inv_lt_comm₀ (by positivity) hvpos]
    exact hm2
  · have : 2 * ((2 : ℝ) ^ (m + 1))⁻¹ = ((2 : ℝ) ^ m)⁻¹ := by
      rw [pow_succ]
      field_simp
    rw [this, le_inv_comm₀ hvpos (by positivity)]
    exact hm1

/-- Subadditivity of the set lintegral over a finite union. -/
theorem setLIntegral_biUnion_finset_le {ι : Type*} (s : Finset ι) (S : ι → Set ℝ)
    (f : ℝ → ℝ≥0∞) : ∫⁻ x in ⋃ i ∈ s, S i, f x ≤ ∑ i ∈ s, ∫⁻ x in S i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

/-- **Summing (5.5).** `∫_{2^{-M'}}^{2^{-M}} |F_t'(iv)| dv ≤ C Σ_{M < k ≤ M'} A_k(t)`. -/
theorem lintegral_Ioc_inv_two_pow_le (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (M M' : ℕ) :
    ∫⁻ v in Ioc ((2 : ℝ) ^ M')⁻¹ ((2 : ℝ) ^ M)⁻¹, ‖deriv (fwdMapInv W t) (v * I)‖ₑ ≤
      ENNReal.ofReal (koebeVertConst * ∑ k ∈ Finset.Ioc M M', normalizedDeriv W k t) := by
  refine (lintegral_mono_set (Ioc_inv_two_pow_subset_biUnion M M')).trans ?_
  refine (setLIntegral_biUnion_finset_le _ _ _).trans ?_
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun k _ =>
    mul_nonneg koebeVertConst_nonneg (normalizedDeriv_nonneg W k t)]
  refine Finset.sum_le_sum fun k _ => ?_
  exact lintegral_Ioc_two_mul_le hW hW0 ht (by positivity)

/-! ## The block bound (5.3) -/

/-- Superpolynomial decay of `a = exp(-r/n²)`, `r = N^δ`, `N = 2^n`: for every fixed `s`, eventually
`N^s a ≤ 1` ("`N^δ/n²` dominates every fixed multiple of `log N`", p. 11). -/
theorem eventually_two_pow_rpow_mul_exp_le_one (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ((2 : ℝ) ^ n) ^ s * Real.exp (-(((2 : ℝ) ^ n) ^ δ / (n : ℝ) ^ 2)) ≤ 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set b : ℝ := δ * Real.log 2 with hb
  have hb0 : 0 < b := mul_pos hδ hl2
  set c : ℝ := 1 / (|s| * Real.log 2 + 1) with hc
  have hc0 : 0 < c := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 3 hb0).bound hc0
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : ∀ e : ℝ, ((2 : ℝ) ^ n) ^ e = Real.exp (n * Real.log 2 * e) := by
    intro e
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  rw [hpow s, hpow δ, ← Real.exp_add, Real.exp_le_one_iff]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hn
  have hexp : Real.exp (n * Real.log 2 * δ) = Real.exp (b * n) := by
    rw [hb]
    ring_nf
  rw [hexp]
  have h3 : (n : ℝ) ^ 3 * (|s| * Real.log 2 + 1) ≤ Real.exp (b * n) := by
    have := mul_le_mul_of_nonneg_right hn (by positivity : (0 : ℝ) ≤ |s| * Real.log 2 + 1)
    calc (n : ℝ) ^ 3 * (|s| * Real.log 2 + 1)
        ≤ c * Real.exp (b * n) * (|s| * Real.log 2 + 1) := this
      _ = Real.exp (b * n) := by
        rw [hc]
        field_simp
  have key : s * (n * Real.log 2) * (n : ℝ) ^ 2 ≤ Real.exp (b * n) := by
    calc s * (n * Real.log 2) * (n : ℝ) ^ 2 = s * (Real.log 2 * (n : ℝ) ^ 3) := by ring
      _ ≤ |s| * (Real.log 2 * (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right (le_abs_self s) (by positivity)
      _ ≤ |s| * (Real.log 2 * (n : ℝ) ^ 3) + (n : ℝ) ^ 3 :=
        le_add_of_nonneg_right (by positivity)
      _ = (n : ℝ) ^ 3 * (|s| * Real.log 2 + 1) := by ring
      _ ≤ _ := h3
  have h4 : n * Real.log 2 * s ≤ Real.exp (b * n) / (n : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith [key]
  linarith [h4]

/-- The two grid-time expressions of the note agree: `t_k = y_k² ⌊t / y_k²⌋` of (2.12) equals
`4^{-k} ⌊4^k t⌋` of (4.2). -/
theorem gridTime_eq_inv_four_pow (k : ℕ) (t : ℝ) :
    gridTime k t = ((4 : ℝ) ^ k)⁻¹ * ⌊(4 : ℝ) ^ k * t⌋ := by
  unfold gridTime dyadicHeight
  have h : (((2 : ℝ) ^ k)⁻¹) ^ 2 = ((4 : ℝ) ^ k)⁻¹ := by
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h, div_inv_eq_mul, mul_comm t]

/-- **(5.3).** From Lemma 2.1 (`β`), Proposition 4.1 (`δ`) and Lemma 2.3 (exponent `p`), for all
large `n` and all `t ∈ [0, 1]`: `Σ_{N < k ≤ 2N} A_k(t) ≤ (C_β + |C₂| 2^{|p|}) N^{7δ − β}`. -/
theorem exists_sum_block_le {β δ Cβ C₂ p : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hCβ : 0 ≤ Cβ)
    (hL21 : ∀ k : ℕ, 1 ≤ k → ∀ t ∈ Icc (0 : ℝ) 1, normalizedDeriv W k t ≤ Cβ * (k : ℝ) ^ (-β))
    (hP41 : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (0 : ℝ) 1,
      (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k =>
          Real.exp (-(((2 : ℝ) ^ n) ^ δ / (n : ℝ) ^ 2)) ≤
            normalizedDeriv W k (gridTime k t)).card : ℝ) ≤
        (((2 : ℝ) ^ n) ^ δ) ^ 7)
    (hL23 : ∀ k : ℕ, 1 ≤ k → ∀ t ∈ Icc (0 : ℝ) 1, normalizedDeriv W k t ≤
      C₂ * (k : ℝ) ^ p * normalizedDeriv W k (gridTime k t)) :
    ∃ n₁ : ℕ, ∀ n ≥ n₁, ∀ t ∈ Icc (0 : ℝ) 1,
      ∑ k ∈ Finset.Ioc (2 ^ n) (2 * 2 ^ n), normalizedDeriv W k t ≤
        (Cβ + |C₂| * 2 ^ |p|) * ((2 : ℝ) ^ n) ^ (7 * δ - β) := by
  obtain ⟨n₀, hn₀⟩ := hP41
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1
    (eventually_two_pow_rpow_mul_exp_le_one (|p| + 1 - (7 * δ - β)) hδ)
  refine ⟨max n₀ n₂, fun n hn t ht => ?_⟩
  set N : ℝ := (2 : ℝ) ^ n with hN
  have hNpos : 0 < N := by positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  set a : ℝ := Real.exp (-(N ^ δ / (n : ℝ) ^ 2)) with ha
  have hcast : ∀ k : ℕ, k ∈ Finset.Ioc (2 ^ n) (2 * 2 ^ n) → N < k ∧ (k : ℝ) ≤ 2 * N ∧ 1 ≤ k :=
    fun k hk => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hk
      refine ⟨?_, ?_, ?_⟩
      · rw [hN]; exact_mod_cast h1
      · rw [hN]; exact_mod_cast h2
      · exact le_trans (Nat.one_le_two_pow) h1.le
  set I := (Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k =>
    a ≤ normalizedDeriv W k (gridTime k t) with hI
  have hcard : (I.card : ℝ) ≤ (N ^ δ) ^ 7 := hn₀ n (le_of_max_le_left hn) t ht
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc (2 ^ n) (2 * 2 ^ n))
    (fun k => a ≤ normalizedDeriv W k (gridTime k t))]
  -- the large scales: Lemma 2.1 at the actual time
  have hlarge : ∑ k ∈ I, normalizedDeriv W k t ≤ Cβ * N ^ (7 * δ - β) := by
    calc ∑ k ∈ I, normalizedDeriv W k t ≤ ∑ _k ∈ I, Cβ * N ^ (-β) := by
          refine Finset.sum_le_sum fun k hk => ?_
          obtain ⟨hNk, -, hk1⟩ := hcast k (Finset.mem_filter.1 hk).1
          exact (hL21 k hk1 t ht).trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hNpos hNk.le (by linarith)) hCβ)
      _ = I.card * (Cβ * N ^ (-β)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N ^ δ) ^ 7 * (Cβ * N ^ (-β)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = Cβ * N ^ (7 * δ - β) := by
          rw [← Real.rpow_natCast (N ^ δ) 7, ← Real.rpow_mul hNpos.le, mul_left_comm,
            ← Real.rpow_add hNpos]
          congr 2
          push_cast
          ring
  -- the small scales: Lemma 2.3 and `A_k(t_k) < a`
  have hsmall : ∑ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter (fun k =>
      ¬ a ≤ normalizedDeriv W k (gridTime k t)), normalizedDeriv W k t ≤
      |C₂| * 2 ^ |p| * N ^ (7 * δ - β) := by
    have hterm : ∀ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter (fun k =>
        ¬ a ≤ normalizedDeriv W k (gridTime k t)),
        normalizedDeriv W k t ≤ |C₂| * (2 * N) ^ |p| * a := by
      intro k hk
      obtain ⟨hkmem, hka⟩ := Finset.mem_filter.1 hk
      obtain ⟨-, hk2N, hk1⟩ := hcast k hkmem
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      set A₀ := normalizedDeriv W k (gridTime k t)
      have hA₀ : 0 ≤ A₀ := normalizedDeriv_nonneg _ _ _
      have hkp : (k : ℝ) ^ p ≤ (2 * N) ^ |p| :=
        (Real.rpow_le_rpow_of_exponent_le hk1' (le_abs_self p)).trans
          (Real.rpow_le_rpow (by positivity) hk2N (abs_nonneg p))
      calc normalizedDeriv W k t ≤ C₂ * (k : ℝ) ^ p * A₀ := hL23 k hk1 t ht
        _ ≤ |C₂| * (k : ℝ) ^ p * A₀ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C₂)
              (by positivity)) hA₀
        _ ≤ |C₂| * (2 * N) ^ |p| * a := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hkp (abs_nonneg _)) (le_of_not_ge hka)
              hA₀ (by positivity)
    have hcardB : (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter (fun k =>
        ¬ a ≤ normalizedDeriv W k (gridTime k t))).card : ℝ) ≤ N := by
      have h1 := Finset.card_filter_le (Finset.Ioc (2 ^ n) (2 * 2 ^ n)) (fun k =>
        ¬ a ≤ normalizedDeriv W k (gridTime k t))
      have hc : (Finset.Ioc (2 ^ n) (2 * 2 ^ n)).card = 2 ^ n := by
        rw [Nat.card_Ioc]
        omega
      rw [hc] at h1
      rw [hN]
      exact_mod_cast h1
    have hdecay : N ^ (|p| + 1) * a ≤ N ^ (7 * δ - β) := by
      have h := hn₂ n (le_of_max_le_right hn)
      have hsplit : N ^ (|p| + 1) = N ^ (|p| + 1 - (7 * δ - β)) * N ^ (7 * δ - β) := by
        rw [← Real.rpow_add hNpos]
        ring_nf
      rw [hsplit, mul_right_comm]
      calc N ^ (|p| + 1 - (7 * δ - β)) * a * N ^ (7 * δ - β) ≤ 1 * N ^ (7 * δ - β) :=
            mul_le_mul_of_nonneg_right h (by positivity)
        _ = N ^ (7 * δ - β) := one_mul _
    calc _ ≤ ∑ _k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter (fun k =>
            ¬ a ≤ normalizedDeriv W k (gridTime k t)),
            |C₂| * (2 * N) ^ |p| * a := Finset.sum_le_sum hterm
      _ = (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter (fun k =>
            ¬ a ≤ normalizedDeriv W k (gridTime k t))).card : ℝ) *
            (|C₂| * (2 * N) ^ |p| * a) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (|C₂| * (2 * N) ^ |p| * a) :=
          mul_le_mul_of_nonneg_right hcardB (by positivity)
      _ = |C₂| * 2 ^ |p| * (N ^ (|p| + 1) * a) := by
          rw [Real.mul_rpow (by norm_num) hNpos.le, Real.rpow_add_one hNpos.ne']
          ring
      _ ≤ |C₂| * 2 ^ |p| * N ^ (7 * δ - β) :=
          mul_le_mul_of_nonneg_left hdecay (by positivity)
  calc _ ≤ Cβ * N ^ (7 * δ - β) + |C₂| * 2 ^ |p| * N ^ (7 * δ - β) := add_le_add hlarge hsmall
    _ = (Cβ + |C₂| * 2 ^ |p|) * N ^ (7 * δ - β) := by ring

/-! ## Summation over blocks, (5.4), and the bound (5.1) -/

theorem two_pow_rpow_neg_eq (j : ℕ) (q : ℝ) : ((2 : ℝ) ^ j) ^ (-q) = ((2 : ℝ) ^ (-q)) ^ j := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm, Real.rpow_mul_natCast (by norm_num)]

/-- **(5.4) with (5.5).** If `Σ_{N < k ≤ 2N} A_k(t) ≤ C₁ N^{-q}` for all `n ≥ n₁` (`N = 2^n`) and
`t ∈ [0, 1]`, then `∫_0^{2^{-N}} |F_t'(iv)| dv ≤ C N^{-q}` for `n ≥ n₁`. -/
theorem lintegral_Ioc_zero_le_of_block {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q C₁ : ℝ}
    (hq : 0 < q) (hC₁ : 0 ≤ C₁) {n₁ : ℕ}
    (hblock : ∀ n ≥ n₁, ∀ t ∈ Icc (0 : ℝ) 1,
      ∑ k ∈ Finset.Ioc (2 ^ n) (2 * 2 ^ n), normalizedDeriv W k t ≤ C₁ * ((2 : ℝ) ^ n) ^ (-q))
    {n : ℕ} (hn : n₁ ≤ n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫⁻ v in Ioc 0 ((2 : ℝ) ^ (2 ^ n))⁻¹, ‖deriv (fwdMapInv W t) (v * I)‖ₑ ≤
      ENNReal.ofReal (koebeVertConst * C₁ * (1 - (2 : ℝ) ^ (-q))⁻¹ * ((2 : ℝ) ^ n) ^ (-q)) := by
  set r : ℝ := (2 : ℝ) ^ (-q) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set S : ℕ → Set ℝ := fun j => Ioc ((2 : ℝ) ^ (2 * 2 ^ (n + j)))⁻¹ ((2 : ℝ) ^ (2 ^ (n + j)))⁻¹
    with hS
  have hcover : Ioc 0 ((2 : ℝ) ^ (2 ^ n))⁻¹ ⊆ ⋃ j, S j := by
    intro v hv
    have hvpos : 0 < v := hv.1
    have hex : ∃ j : ℕ, ((2 : ℝ) ^ (2 * 2 ^ (n + j)))⁻¹ < v := by
      obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt v⁻¹ (by norm_num : (1 : ℝ) < 2)
      refine ⟨m, ?_⟩
      rw [inv_lt_comm₀ (by positivity) hvpos]
      refine hm.trans_le (pow_le_pow_right₀ (by norm_num) ?_)
      have h1 : n + m < 2 ^ (n + m) := Nat.lt_two_pow_self
      omega
    classical
    refine mem_iUnion.2 ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, add_zero]
      exact hv.2
    · have hmin := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      rw [not_lt] at hmin
      have h2 : 2 * 2 ^ (n + (Nat.find hex - 1)) = 2 ^ (n + Nat.find hex) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2] at hmin
      exact hmin
  have hsum : Summable fun j : ℕ => koebeVertConst * C₁ * ((2 : ℝ) ^ n) ^ (-q) * r ^ j :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  calc ∫⁻ v in Ioc 0 ((2 : ℝ) ^ (2 ^ n))⁻¹, ‖deriv (fwdMapInv W t) (v * I)‖ₑ
      ≤ ∫⁻ v in ⋃ j, S j, ‖deriv (fwdMapInv W t) (v * I)‖ₑ := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ v in S j, ‖deriv (fwdMapInv W t) (v * I)‖ₑ := lintegral_iUnion_le _ _
    _ ≤ ∑' j, ENNReal.ofReal (koebeVertConst * C₁ * ((2 : ℝ) ^ n) ^ (-q) * r ^ j) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        refine (lintegral_Ioc_inv_two_pow_le hW hW0 ht.1 _ _).trans (ENNReal.ofReal_le_ofReal ?_)
        have hb := hblock (n + j) (by omega) t ht
        have hpow : ((2 : ℝ) ^ (n + j)) ^ (-q) = ((2 : ℝ) ^ n) ^ (-q) * r ^ j := by
          rw [pow_add, Real.mul_rpow (by positivity) (by positivity), two_pow_rpow_neg_eq j q]
        rw [hpow] at hb
        calc koebeVertConst * ∑ k ∈ Finset.Ioc (2 ^ (n + j)) (2 * 2 ^ (n + j)),
              normalizedDeriv W k t
            ≤ koebeVertConst * (C₁ * (((2 : ℝ) ^ n) ^ (-q) * r ^ j)) :=
              mul_le_mul_of_nonneg_left hb koebeVertConst_nonneg
          _ = koebeVertConst * C₁ * ((2 : ℝ) ^ n) ^ (-q) * r ^ j := by ring
    _ = ENNReal.ofReal (∑' j, koebeVertConst * C₁ * ((2 : ℝ) ^ n) ^ (-q) * r ^ j) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => by
          have := koebeVertConst_nonneg
          positivity) hsum).symm
    _ = ENNReal.ofReal (koebeVertConst * C₁ * (1 - r)⁻¹ * ((2 : ℝ) ^ n) ^ (-q)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
        ring_nf

/-- For `y ∈ (0, 1/2]` there is `n` with `y ≤ 2^{-2^n}` and `log(e/y) ≤ 2^{n+2}` ("`K` is comparable
to `log(e/y_K)`", p. 11). -/
theorem exists_dyadic_bracket {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) (1 / 2)) :
    ∃ n : ℕ, y ≤ ((2 : ℝ) ^ (2 ^ n))⁻¹ ∧ Real.log (Real.exp 1 / y) ≤ (2 : ℝ) ^ (n + 2) := by
  have hy0 : 0 < y := hy.1
  have h2y : (2 : ℝ) ≤ y⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hy0]
    linarith [hy.2]
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (by linarith : (1 : ℝ) ≤ y⁻¹)
    (by norm_num : (1 : ℝ) < 2)
  have hm : 1 ≤ m := by
    by_contra h
    rw [not_le] at h
    interval_cases m
    norm_num at hm2
    linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (by exact_mod_cast hm : (1 : ℝ) ≤ m)
    (by norm_num : (1 : ℝ) < 2)
  have hn1' : 2 ^ n ≤ m := by exact_mod_cast hn1
  have hn2' : m < 2 ^ (n + 1) := by exact_mod_cast hn2
  refine ⟨n, ?_, ?_⟩
  · have h1 : y ≤ ((2 : ℝ) ^ m)⁻¹ := by
      rw [le_inv_comm₀ hy0 (by positivity)]
      exact hm1
    exact h1.trans (inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hn1'))
  · rw [Real.log_div (Real.exp_pos 1).ne' hy0.ne', Real.log_exp]
    have hlog : -Real.log y < ((m + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [← Real.log_inv, ← Real.log_pow]
      exact Real.log_lt_log (by positivity) hm2
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      norm_num at this
      linarith
    have hm1' : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by exact_mod_cast hn2'
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    have h3 : ((m + 1 : ℕ) : ℝ) * Real.log 2 ≤ ((m + 1 : ℕ) : ℝ) :=
      mul_le_of_le_one_right (by positivity) hl2
    have h4 : (2 : ℝ) ^ (n + 2) = 2 * (2 : ℝ) ^ (n + 1) := by ring
    linarith

/-- `1 ≤ log(e/y)` for `0 < y ≤ 1`. -/
theorem one_le_log_exp_one_div {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    1 ≤ Real.log (Real.exp 1 / y) := by
  rw [Real.log_div (Real.exp_pos 1).ne' hy0.ne', Real.log_exp]
  linarith [Real.log_nonpos hy0.le hy1]

/-! ## Proposition 5.1, pathwise form -/

/-- **Proposition 5.1, pathwise (deterministic) form of the proof (pp. 10–11).** Let `W` be a
continuous driver with `W 0 = 0`, and `0 < α < β − 7δ` with `β, δ > 0`. Suppose `W` satisfies the
conclusions of Lemma 2.1 (exponent `β`) and of Proposition 4.1 (parameter `δ`), and lies in some
`Ω_M` of (2.11) (`DriverBound M W`; Lemma 2.3 is then applied, `exists_normalizedDeriv_le_gridTime`).
Then there is `C_α` with
`sup_{t ≤ 1} ∫_0^y |F_t'(iv)| dv ≤ C_α [log(e/y)]^{-α}` for all `y ∈ (0, 1/2]` (improper integrals of
nonnegative functions, as lintegrals). -/
theorem radial_bound_of_scale_count (hW : Continuous W) (hW0 : W 0 = 0) {α β δ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (hαq : α < β - 7 * δ)
    (hL21 : ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ t ∈ Icc (0 : ℝ) 1,
      normalizedDeriv W k t ≤ C * (k : ℝ) ^ (-β))
    (hP41 : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (0 : ℝ) 1,
      (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k =>
          Real.exp (-(((2 : ℝ) ^ n) ^ δ / (n : ℝ) ^ 2)) ≤
            normalizedDeriv W k (gridTime k t)).card : ℝ) ≤
        (((2 : ℝ) ^ n) ^ δ) ^ 7)
    {M : ℝ} (hM : DriverBound M W) :
    ∃ C : ℝ, ∀ y ∈ Ioc (0 : ℝ) (1 / 2), ∀ t ∈ Icc (0 : ℝ) 1,
      ∫⁻ v in Ioc 0 y, ‖deriv (fwdMapInv W t) (v * I)‖ₑ ≤
        ENNReal.ofReal (C * Real.log (Real.exp 1 / y) ^ (-α)) := by
  obtain ⟨Cβ₀, hCβ₀⟩ := hL21
  set Cβ : ℝ := max Cβ₀ 0 with hCβdef
  have hCβ : 0 ≤ Cβ := le_max_right _ _
  have hL21' : ∀ k : ℕ, 1 ≤ k → ∀ t ∈ Icc (0 : ℝ) 1,
      normalizedDeriv W k t ≤ Cβ * (k : ℝ) ^ (-β) := fun k hk t ht =>
    (hCβ₀ k hk t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  -- Lemma 2.3 on `Ω_M`
  obtain ⟨p, -, hp⟩ := exists_normalizedDeriv_le_gridTime
  obtain ⟨C₂, -, hC₂⟩ := hp M
  have hL23' := hC₂ W hW hW0 hM
  obtain ⟨n₁, hn₁⟩ := exists_sum_block_le hβ hδ hCβ hL21' hP41 hL23'
  set q : ℝ := β - 7 * δ with hqdef
  have hq : 0 < q := by linarith
  set C₁ : ℝ := Cβ + |C₂| * 2 ^ |p| with hC₁def
  have hC₁ : 0 ≤ C₁ := by positivity
  have hblock : ∀ n ≥ n₁, ∀ t ∈ Icc (0 : ℝ) 1,
      ∑ k ∈ Finset.Ioc (2 ^ n) (2 * 2 ^ n), normalizedDeriv W k t ≤
        C₁ * ((2 : ℝ) ^ n) ^ (-q) := fun n hn t ht => by
    have h := hn₁ n hn t ht
    rwa [show 7 * δ - β = -q by rw [hqdef]; ring] at h
  have hr1 : (2 : ℝ) ^ (-q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set T : ℝ := koebeVertConst * C₁ * (1 - (2 : ℝ) ^ (-q))⁻¹ with hTdef
  have hT : 0 ≤ T := by
    have := koebeVertConst_nonneg
    have : 0 < 1 - (2 : ℝ) ^ (-q) := by linarith
    positivity
  have htail : ∀ n ≥ n₁, ∀ t ∈ Icc (0 : ℝ) 1,
      ∫⁻ v in Ioc 0 ((2 : ℝ) ^ (2 ^ n))⁻¹, ‖deriv (fwdMapInv W t) (v * I)‖ₑ ≤
        ENNReal.ofReal (T * ((2 : ℝ) ^ n) ^ (-q)) := fun n hn t ht =>
    lintegral_Ioc_zero_le_of_block hW hW0 hq hC₁ hblock hn ht
  -- the finitely many larger heights
  set D : ℝ := T * ((2 : ℝ) ^ n₁) ^ (-q) + koebeVertConst * ((2 : ℝ) ^ n₁ * Cβ) with hDdef
  have hD0 : 0 ≤ D := by
    have := koebeVertConst_nonneg
    positivity
  have hD : ∀ t ∈ Icc (0 : ℝ) 1,
      ∫⁻ v in Ioc (0 : ℝ) (1 / 2), ‖deriv (fwdMapInv W t) (v * I)‖ₑ ≤ ENNReal.ofReal D := by
    intro t ht
    have hle : ((2 : ℝ) ^ (2 ^ n₁))⁻¹ ≤ ((2 : ℝ) ^ 1)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) Nat.one_le_two_pow)
    have hsplit : Ioc (0 : ℝ) (1 / 2) =
        Ioc 0 ((2 : ℝ) ^ (2 ^ n₁))⁻¹ ∪ Ioc ((2 : ℝ) ^ (2 ^ n₁))⁻¹ ((2 : ℝ) ^ 1)⁻¹ := by
      rw [Ioc_union_Ioc_eq_Ioc (by positivity) hle]
      norm_num
    rw [hsplit, hDdef, ENNReal.ofReal_add (by positivity) (by
      have := koebeVertConst_nonneg
      positivity)]
    refine (lintegral_union_le _ _ _).trans (add_le_add (htail n₁ le_rfl t ht) ?_)
    refine (lintegral_Ioc_inv_two_pow_le hW hW0 ht.1 1 (2 ^ n₁)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ koebeVertConst_nonneg))
    calc ∑ k ∈ Finset.Ioc 1 (2 ^ n₁), normalizedDeriv W k t
        ≤ ∑ _k ∈ Finset.Ioc 1 (2 ^ n₁), Cβ := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk1 : 1 ≤ k := (Finset.mem_Ioc.1 hk).1.le
          have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
          refine (hL21' k hk1 t ht).trans ?_
          calc Cβ * (k : ℝ) ^ (-β) ≤ Cβ * 1 :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hk1'
                  (by linarith)) hCβ
            _ = Cβ := mul_one _
      _ = ((Finset.Ioc 1 (2 ^ n₁)).card : ℝ) * Cβ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ n₁ * Cβ := by
          refine mul_le_mul_of_nonneg_right ?_ hCβ
          rw [Nat.card_Ioc]
          have : 2 ^ n₁ - 1 ≤ 2 ^ n₁ := Nat.sub_le _ _
          exact_mod_cast this
  -- the final bound
  refine ⟨T * 4 ^ α + D * ((2 : ℝ) ^ (n₁ + 2)) ^ α, fun y hy t ht => ?_⟩
  obtain ⟨n, hyn, hlog⟩ := exists_dyadic_bracket hy
  have hlog1 : 1 ≤ Real.log (Real.exp 1 / y) := one_le_log_exp_one_div hy.1 (by linarith [hy.2])
  have hlogpos : 0 < Real.log (Real.exp 1 / y) := by linarith
  set X : ℝ := Real.log (Real.exp 1 / y) ^ (-α) with hXdef
  have hX : 0 ≤ X := by positivity
  have hmono : ((2 : ℝ) ^ (n + 2)) ^ (-α) ≤ X :=
    Real.rpow_le_rpow_of_nonpos hlogpos hlog (by linarith)
  have h4 : (4 : ℝ) ^ α * (4 : ℝ) ^ (-α) = 1 := by
    rw [Real.rpow_neg (by norm_num), mul_inv_cancel₀ (by positivity)]
  have hsplit4 : ∀ m : ℕ, ((2 : ℝ) ^ (m + 2)) ^ (-α) = ((2 : ℝ) ^ m) ^ (-α) * (4 : ℝ) ^ (-α) := by
    intro m
    rw [pow_add, Real.mul_rpow (by positivity) (by positivity)]
    norm_num
  have hDX : 0 ≤ D * ((2 : ℝ) ^ (n₁ + 2)) ^ α * X := by positivity
  have hTX : 0 ≤ T * 4 ^ α * X := by positivity
  rcases le_or_gt n₁ n with hn | hn
  · calc ∫⁻ v in Ioc 0 y, ‖deriv (fwdMapInv W t) (v * I)‖ₑ
        ≤ ∫⁻ v in Ioc 0 ((2 : ℝ) ^ (2 ^ n))⁻¹, ‖deriv (fwdMapInv W t) (v * I)‖ₑ :=
          lintegral_mono_set (Ioc_subset_Ioc_right hyn)
      _ ≤ ENNReal.ofReal (T * ((2 : ℝ) ^ n) ^ (-q)) := htail n hn t ht
      _ ≤ ENNReal.ofReal ((T * 4 ^ α + D * ((2 : ℝ) ^ (n₁ + 2)) ^ α) * X) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hqa : ((2 : ℝ) ^ n) ^ (-q) ≤ ((2 : ℝ) ^ n) ^ (-α) :=
            Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
          have heq : ((2 : ℝ) ^ n) ^ (-α) = 4 ^ α * ((2 : ℝ) ^ (n + 2)) ^ (-α) := by
            rw [hsplit4 n, mul_comm (((2 : ℝ) ^ n) ^ (-α)), ← mul_assoc, h4, one_mul]
          calc T * ((2 : ℝ) ^ n) ^ (-q) ≤ T * (4 ^ α * ((2 : ℝ) ^ (n + 2)) ^ (-α)) := by
                rw [← heq]
                exact mul_le_mul_of_nonneg_left hqa hT
            _ ≤ T * (4 ^ α * X) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono (by positivity)) hT
            _ = T * 4 ^ α * X := by ring
            _ ≤ T * 4 ^ α * X + D * ((2 : ℝ) ^ (n₁ + 2)) ^ α * X := le_add_of_nonneg_right hDX
            _ = (T * 4 ^ α + D * ((2 : ℝ) ^ (n₁ + 2)) ^ α) * X := by ring
  · calc ∫⁻ v in Ioc 0 y, ‖deriv (fwdMapInv W t) (v * I)‖ₑ
        ≤ ∫⁻ v in Ioc (0 : ℝ) (1 / 2), ‖deriv (fwdMapInv W t) (v * I)‖ₑ :=
          lintegral_mono_set (Ioc_subset_Ioc_right hy.2)
      _ ≤ ENNReal.ofReal D := hD t ht
      _ ≤ ENNReal.ofReal ((T * 4 ^ α + D * ((2 : ℝ) ^ (n₁ + 2)) ^ α) * X) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hpos : (0 : ℝ) < (2 : ℝ) ^ (n₁ + 2) := by positivity
          have hone : ((2 : ℝ) ^ (n₁ + 2)) ^ α * ((2 : ℝ) ^ (n₁ + 2)) ^ (-α) = 1 := by
            rw [Real.rpow_neg hpos.le, mul_inv_cancel₀ (by positivity)]
          have hmono' : ((2 : ℝ) ^ (n₁ + 2)) ^ (-α) ≤ ((2 : ℝ) ^ (n + 2)) ^ (-α) :=
            Real.rpow_le_rpow_of_nonpos (by positivity)
              (pow_le_pow_right₀ (by norm_num) (by omega)) (by linarith)
          calc D = D * (((2 : ℝ) ^ (n₁ + 2)) ^ α * ((2 : ℝ) ^ (n₁ + 2)) ^ (-α)) := by
                rw [hone, mul_one]
            _ ≤ D * (((2 : ℝ) ^ (n₁ + 2)) ^ α * X) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hmono'.trans hmono)
                  (by positivity)) hD0
            _ = D * ((2 : ℝ) ^ (n₁ + 2)) ^ α * X := by ring
            _ ≤ T * 4 ^ α * X + D * ((2 : ℝ) ^ (n₁ + 2)) ^ α * X := le_add_of_nonneg_left hTX
            _ = (T * 4 ^ α + D * ((2 : ℝ) ^ (n₁ + 2)) ^ α) * X := by ring

/-! ## The localization events `Ω_M` of (2.11) -/

/-- **`ℙ(⋃_M Ω_M) = 1`** (p. 4, after (2.11)): almost surely there is `M ∈ ℕ` with
`sup_{t ≤ 1} |W_t| ≤ M` and `|W_t − W_s| ≤ M √((t − s) log(e/(t − s)))` for `0 ≤ s < t ≤ 1`, where
`W = √8 B`. From QuantumZipper's Brownian modulus of continuity `RS.bm_modulus`. -/
theorem ae_exists_driveBound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ M : ℕ, DriverBound M (drive 8 B ω) := by
  filter_upwards [RS.bm_modulus hB, hB.cont] with ω hmod hc
  set W : ℝ → ℝ := drive 8 B ω with hWdef
  have hW : Continuous W := drive_continuous hc
  obtain ⟨Mb, hMb⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨C, hC⟩ := hmod 1
  set M₀ : ℝ := √8 * |C| + 8 * |Mb| with hM₀
  obtain ⟨M, hM⟩ := exists_nat_ge M₀
  have hW_le : ∀ t ∈ Icc (0 : ℝ) 1, |W t| ≤ |Mb| := fun t ht => by
    have := hMb t ht
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hs8 : 0 ≤ √(8 : ℝ) := Real.sqrt_nonneg 8
  refine ⟨M, fun t ht => ?_, fun s t hs hst ht1 => ?_⟩
  · show |W t| ≤ M
    calc |W t| ≤ |Mb| := hW_le t ht
      _ ≤ M₀ := by
        rw [hM₀]
        nlinarith [abs_nonneg C, abs_nonneg Mb]
      _ ≤ M := hM
  · set h : ℝ := t - s with hh
    have hh0 : 0 < h := by rw [hh]; linarith
    have hh1 : h ≤ 1 := by rw [hh]; linarith
    have hlog1 : 1 ≤ Real.log (Real.exp 1 / h) := one_le_log_exp_one_div hh0 hh1
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rcases le_or_gt h (1 / 2) with hsmall | hlarge
    · have ht' : s.toNNReal ≤ 1 := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs, NNReal.coe_one]
        linarith
      have hh' : 0 < h.toNNReal := Real.toNNReal_pos.2 hh0
      have hh'' : h.toNNReal ≤ 1 / 2 := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hh0.le]
        push_cast
        exact hsmall
      have key := hC s.toNNReal ht' h.toNNReal hh' hh''
      rw [Real.coe_toNNReal _ hh0.le, ← Real.toNNReal_add hs hh0.le,
        show s + h = t by rw [hh]; ring] at key
      have hWts : W t - W s = √8 * (B t.toNNReal ω - B s.toNNReal ω) := by
        simp only [hWdef, drive]
        ring
      have hlogle : h * Real.log (1 / h) ≤ h * Real.log (Real.exp 1 / h) := by
        refine mul_le_mul_of_nonneg_left ?_ hh0.le
        rw [Real.log_div (Real.exp_pos 1).ne' hh0.ne', Real.log_exp,
          Real.log_div one_ne_zero hh0.ne', Real.log_one]
        linarith
      calc |W t - W s| = √8 * |B t.toNNReal ω - B s.toNNReal ω| := by
            rw [hWts, abs_mul, abs_of_nonneg hs8]
        _ ≤ √8 * (|C| * √(h * Real.log (1 / h))) := by
            refine mul_le_mul_of_nonneg_left (key.trans ?_) hs8
            exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
        _ ≤ √8 * (|C| * √(h * Real.log (Real.exp 1 / h))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlogle)
              (abs_nonneg C)) hs8
        _ = (√8 * |C|) * √(h * Real.log (Real.exp 1 / h)) := by ring
        _ ≤ M * √(h * Real.log (Real.exp 1 / h)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
            refine le_trans ?_ hM
            rw [hM₀]
            linarith [abs_nonneg Mb]
    · have hsq : (1 / 2 : ℝ) ≤ √(h * Real.log (Real.exp 1 / h)) := by
        have h14 : (1 / 4 : ℝ) ≤ h * Real.log (Real.exp 1 / h) := by nlinarith
        calc (1 / 2 : ℝ) = √(1 / 4) := by
              rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          _ ≤ _ := Real.sqrt_le_sqrt h14
      have hMb8 : 8 * |Mb| ≤ M := by
        refine le_trans ?_ hM
        rw [hM₀]
        nlinarith [abs_nonneg C]
      calc |W t - W s| ≤ |W t| + |W s| := abs_sub _ _
        _ ≤ |Mb| + |Mb| := add_le_add (hW_le t ⟨by linarith, ht1⟩) (hW_le s ⟨hs, by linarith⟩)
        _ ≤ M * (1 / 2) := by nlinarith [abs_nonneg Mb]
        _ ≤ M * √(h * Real.log (Real.exp 1 / h)) := mul_le_mul_of_nonneg_left hsq hM0

/-! ## Proposition 5.1 and Theorem 1.1 from Lemma 2.1 and Proposition 4.1 -/

/-- **Proposition 5.1 (uniform radial variation), from Lemma 2.1 and Proposition 4.1** (SLE₈ note,
pp. 10–11).
Hypotheses, as the note states them for `W = √8 B`:
* `hL21` — Lemma 2.1: for every `β ∈ (0, 1/4)`, a.s. there is `C_β` with
  `sup_{t ≤ 1} A_k(t) ≤ C_β k^{-β}` for every `k ≥ 1`;
* `hP41` — Proposition 4.1: for every `δ ∈ (0, 1/10)`, a.s. there is `n₀` such that for `n ≥ n₀`,
  `N = 2^n`, `r = N^δ`, `a = exp(-r/n²)`: `sup_{t ≤ 1} #{N < k ≤ 2N : A_k(t_k) ≥ a} ≤ r^7`,
  `t_k = 4^{-k} ⌊4^k t⌋`;
  (`t_k = gridTime k t`, equal to `4^{-k} ⌊4^k t⌋` by `gridTime_eq_inv_four_pow`).

Lemma 2.3 (`exists_normalizedDeriv_le_gridTime`, exponent `p` in place of `2`) and `ℙ(⋃ Ω_M) = 1`
(`ae_exists_driveBound`) are used as proved results.

Conclusion (5.1): for every `α ∈ (0, 1/4)`, a.s. there is `C_α` with
`sup_{t ≤ 1} ∫_0^y |F_t'(iv)| dv ≤ C_α [log(e/y)]^{-α}` for all `y ∈ (0, 1/2]`. -/
theorem ae_radial_bound_of_scale_count {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hL21 : ∀ β : ℝ, 0 < β → β < 1 / 4 → ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      ∀ t ∈ Icc (0 : ℝ) 1, normalizedDeriv (drive 8 B ω) k t ≤ C * (k : ℝ) ^ (-β))
    (hP41 : ∀ δ : ℝ, 0 < δ → δ < 1 / 10 → ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ t ∈ Icc (0 : ℝ) 1,
        (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k =>
            Real.exp (-(((2 : ℝ) ^ n) ^ δ / (n : ℝ) ^ 2)) ≤
              normalizedDeriv (drive 8 B ω) k (gridTime k t)).card : ℝ) ≤
          (((2 : ℝ) ^ n) ^ δ) ^ 7)
    {α : ℝ} (hα : 0 < α) (hα4 : α < 1 / 4) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ y ∈ Ioc (0 : ℝ) (1 / 2), ∀ t ∈ Icc (0 : ℝ) 1,
      ∫⁻ v in Ioc 0 y, ‖deriv (fwdMapInv (drive 8 B ω) t) (v * I)‖ₑ ≤
        ENNReal.ofReal (C * Real.log (Real.exp 1 / y) ^ (-α)) := by
  -- the exponents of (5.2)
  set β : ℝ := (α + 1 / 4) / 2 with hβdef
  set δ : ℝ := (β - α) / 16 with hδdef
  have hβ : 0 < β := by rw [hβdef]; linarith
  have hβ4 : β < 1 / 4 := by rw [hβdef]; linarith
  have hδ : 0 < δ := by rw [hδdef, hβdef]; linarith
  have hδ10 : δ < 1 / 10 := by rw [hδdef, hβdef]; linarith
  have hαq : α < β - 7 * δ := by rw [hδdef, hβdef]; linarith
  filter_upwards [hL21 β hβ hβ4, hP41 δ hδ hδ10, ae_exists_driveBound hB, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω h1 h2 h3 hc h0
  have hW : Continuous (drive 8 B ω) := drive_continuous hc
  have hW0 : drive 8 B ω 0 = 0 := drive_zero h0
  obtain ⟨M, hM⟩ := h3
  exact radial_bound_of_scale_count hW hW0 hα hβ hδ hαq h1 h2 hM

/-- Brownian scaling of the driver: for `c > 0` and `a = √c`, the driver of the Brownian motion
`t ↦ c^{-1/2} B (c t)` is `r ↦ W (a² r) / a` with `W = √8 B`. -/
theorem drive_smul_eq {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (ω : Ω) (c : ℝ≥0) :
    drive 8 (fun t ω => (√(c : ℝ))⁻¹ * B (c * t) ω) ω =
      fun r => drive 8 B ω (√(c : ℝ) ^ 2 * r) / √(c : ℝ) := by
  funext r
  have hc0 : (0 : ℝ) ≤ c := c.2
  rw [Real.sq_sqrt hc0]
  simp only [drive]
  rw [Real.toNNReal_mul hc0, Real.toNNReal_coe]
  ring

/-- **Theorem 1.1 of the SLE₈ note from Lemma 2.1 and Proposition 4.1** (proof of Theorem 1.1,
pp. 11–12). The conclusion is that of the frozen `ae_exists_continuous_trace`; the only hypotheses are
Lemma 2.1 and Proposition 4.1, as the note states them, for every standard Brownian motion on `(Ω, P)`
(they are applied to the scaled motions `t ↦ c^{-1/2} B (c t)`: "Brownian scaling applies the same
conclusion on each deterministic interval `[0, j]`"). -/
theorem ae_exists_continuous_trace_of_scale_count {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (hL21 : ∀ B : ℝ≥0 → Ω → ℝ, IsBrownianReal B P → ∀ β : ℝ, 0 < β → β < 1 / 4 →
      ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
        ∀ t ∈ Icc (0 : ℝ) 1, normalizedDeriv (drive 8 B ω) k t ≤ C * (k : ℝ) ^ (-β))
    (hP41 : ∀ B : ℝ≥0 → Ω → ℝ, IsBrownianReal B P → ∀ δ : ℝ, 0 < δ → δ < 1 / 10 →
      ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (0 : ℝ) 1,
        (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k =>
            Real.exp (-(((2 : ℝ) ^ n) ^ δ / (n : ℝ) ^ 2)) ≤
              normalizedDeriv (drive 8 B ω) k (gridTime k t)).card : ℝ) ≤
          (((2 : ℝ) ^ n) ^ δ) ^ 7)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ,
      TendstoLocallyUniformly
          (fun (y : ℝ) (t : ℝ≥0) =>
            QuantumZipper.fwdMapInv (QuantumZipper.drive 8 B ω) t (y * Complex.I))
          γ (𝓝[>] 0) ∧
        Continuous γ ∧ (∀ t, γ t ∈ QuantumZipper.Hbar) ∧ γ 0 = 0 ∧
        ∀ t : ℝ≥0,
          (∃ z ∈ QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t,
              connectedComponentIn (QuantumZipper.H \ γ '' Icc 0 t) z =
                QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t) ∧
            ¬ Bornology.IsBounded
              (QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t) := by
  -- the scaled Brownian motions `t ↦ (j+1)^{-1/2} B ((j+1) t)`
  set cj : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) + 1 with hcj
  have hcj0 : ∀ j, cj j ≠ 0 := fun j => by rw [hcj]; positivity
  set Bj : ℕ → ℝ≥0 → Ω → ℝ := fun j t ω => (√(cj j : ℝ))⁻¹ * B (cj j * t) ω with hBjdef
  have hBj : ∀ j, IsBrownianReal (Bj j) P := fun j => hB.smul (hcj0 j)
  have hrad : ∀ j : ℕ, ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ y ∈ Ioc (0 : ℝ) (1 / 2), ∀ t ∈ Icc (0 : ℝ) 1,
      ∫⁻ v in Ioc 0 y, ‖deriv (fwdMapInv (drive 8 (Bj j) ω) t) (v * I)‖ₑ ≤
        ENNReal.ofReal (C * Real.log (Real.exp 1 / y) ^ (-(1 / 8 : ℝ))) := fun j =>
    ae_radial_bound_of_scale_count (hBj j) (hL21 _ (hBj j)) (hP41 _ (hBj j))
      (by norm_num) (by norm_num)
  filter_upwards [ae_all_iff.2 hrad, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hc h0
  set W : ℝ → ℝ := drive 8 B ω with hWdef
  have hW : Continuous W := drive_continuous hc
  have hW0 : W 0 = 0 := drive_zero h0
  refine exists_continuous_trace_of_lintegral_le hW hW0 fun T hT => ?_
  set j : ℕ := ⌈T⌉₊ with hj
  set a : ℝ := √(cj j : ℝ) with ha
  have hcpos : (0 : ℝ) < cj j := by
    rw [hcj]
    push_cast
    positivity
  have hapos : 0 < a := Real.sqrt_pos.2 hcpos
  have ha2 : a ^ 2 = cj j := Real.sq_sqrt hcpos.le
  have hTc : T ≤ a ^ 2 := by
    rw [ha2, hcj]
    push_cast
    linarith [Nat.le_ceil T]
  obtain ⟨C, hC⟩ := hω j
  have hdrive : drive 8 (Bj j) ω = fun r => W (a ^ 2 * r) / a := drive_smul_eq ω (cj j)
  refine ⟨fun y => a * (C * Real.log (Real.exp 1 / (y / a)) ^ (-(1 / 8 : ℝ))), ?_, a / 2,
    by positivity, fun t ht y hy => ?_⟩
  · -- the rate tends to `0`
    have h1 : Tendsto (fun y : ℝ => y / a) (𝓝[>] 0) (𝓝[>] 0) := by
      have := RS.tendsto_mul_nhdsGT (inv_pos.2 hapos)
      simpa [div_eq_inv_mul] using this
    have h2 : Tendsto (fun x : ℝ => Real.exp 1 / x) (𝓝[>] 0) atTop := by
      simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop (Real.exp_pos 1)
    have h3 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      (Real.tendsto_log_atTop.comp (h2.comp h1)))
    have h4 := (h3.const_mul C).const_mul a
    simpa using h4
  · -- the bound on `[0, T]` from the bound on `[0, 1]` for the scaled motion
    have hs : t / a ^ 2 ∈ Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg ht.1 (by positivity), ?_⟩
      rw [div_le_one (by positivity)]
      exact ht.2.trans hTc
    have hy' : y / a ∈ Ioc (0 : ℝ) (1 / 2) := by
      refine ⟨div_pos hy.1 hapos, ?_⟩
      rw [div_le_iff₀ hapos]
      linarith [hy.2]
    have h1 := hC (y / a) hy' (t / a ^ 2) hs
    rw [hdrive, lintegral_deriv_fwdMapInv_scale hW hW0 hapos hs.1 (y / a),
      mul_div_cancel₀ t (by positivity), mul_div_cancel₀ y hapos.ne'] at h1
    calc ∫⁻ v in Ioc 0 y, ‖deriv (fwdMapInv W t) (v * I)‖ₑ
        = ENNReal.ofReal a * (ENNReal.ofReal a⁻¹ *
            ∫⁻ v in Ioc 0 y, ‖deriv (fwdMapInv W t) (v * I)‖ₑ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hapos.le, mul_inv_cancel₀ hapos.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal a *
            ENNReal.ofReal (C * Real.log (Real.exp 1 / (y / a)) ^ (-(1 / 8 : ℝ))) :=
          by gcongr
      _ = ENNReal.ofReal (a * (C * Real.log (Real.exp 1 / (y / a)) ^ (-(1 / 8 : ℝ)))) :=
          (ENNReal.ofReal_mul hapos.le).symm

end InteractingSLE.SLE8
