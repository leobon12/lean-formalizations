import SupercriticalLQGUniqueness.Uniqueness.Objects.ShadowChecks.Checks
import Mathlib




 

set_option autoImplicit false

open Set Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachmentCore

 

theorem dyadic_time_bins {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) :
    ∃ M : ℕ, (M : ℝ) ≤ Real.logb 2 (U / L) + 2 ∧
      ∀ d ∈ Icc L U, ∃ j ∈ Finset.range M,
        L * (2 : ℝ) ^ j ≤ d ∧ d < 2 * (L * (2 : ℝ) ^ j) := by
  let M := ⌊Real.logb 2 (U / L)⌋₊ + 1
  have hratio : 1 ≤ U / L := (le_div_iff₀ hL).2 (by simpa using hLU)
  have hlog : 0 ≤ Real.logb 2 (U / L) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hratio
  refine ⟨M, ?_, ?_⟩
  · dsimp [M]
    have hf := Nat.floor_le hlog
    push_cast
    linarith
  · intro d hd
    have hdpos : 0 < d := hL.trans_le hd.1
    have hxd : 1 ≤ d / L := (le_div_iff₀ hL).2 (by simpa using hd.1)
    obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hxd (by norm_num : (1 : ℝ) < 2)
    have hxdU : d / L ≤ U / L := div_le_div_of_nonneg_right hd.2 hL.le
    have hjlog : (j : ℝ) ≤ Real.logb 2 (U / L) := by
      have hjlogd : (j : ℝ) ≤ Real.logb 2 (d / L) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
          (div_pos hdpos hL)]
        simpa only [Real.rpow_natCast] using hjlo
      exact hjlogd.trans (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (div_pos hdpos hL) hxdU)
    have hjM : j ∈ Finset.range M := by
      simp only [Finset.mem_range]
      dsimp [M]
      exact Nat.lt_succ_of_le (Nat.le_floor hjlog)
    refine ⟨j, hjM, ?_, ?_⟩
    · simpa only [mul_comm] using (le_div_iff₀ hL).mp hjlo
    · have := (div_lt_iff₀ hL).mp hjhi
      simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this


 

theorem many_in_one_dyadic_bin {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d : ι → ℝ) {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U)
    (hd : ∀ i ∈ S, d i ∈ Icc L U) (n : ℕ)
    (hquota : ∀ M : ℕ, (M : ℝ) ≤ Real.logb 2 (U / L) + 2 →
      M * n ≤ S.card) :
    ∃ M j : ℕ, (M : ℝ) ≤ Real.logb 2 (U / L) + 2 ∧
      j ∈ Finset.range M ∧
      n ≤ (S.filter fun i => L * (2 : ℝ) ^ j ≤ d i ∧
        d i < 2 * (L * (2 : ℝ) ^ j)).card := by
  classical
  obtain ⟨M, hM, hcover⟩ := dyadic_time_bins hL hLU
  let f : {i // i ∈ S} → ℕ := fun i => (hcover (d i.1) (hd i.1 i.2)).choose
  have hf (i : {i // i ∈ S}) : f i ∈ Finset.range M :=
    (hcover (d i.1) (hd i.1 i.2)).choose_spec.1
  have hMne : (Finset.range M).Nonempty := by
    obtain ⟨j, hj, _⟩ := hcover L ⟨le_rfl, hLU⟩
    exact ⟨j, hj⟩
  have hcard : M * n ≤ (Finset.univ : Finset {i // i ∈ S}).card := by
    simpa using hquota M hM
  obtain ⟨j, hj, hfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := (Finset.univ : Finset {i // i ∈ S})) (t := Finset.range M)
      (f := f) (by intro i _; exact hf i) hMne (by simpa using hcard)
  refine ⟨M, j, hM, hj, ?_⟩
  have hsubset :
      ((Finset.univ : Finset {i // i ∈ S}).filter fun i => f i = j).card ≤
        (S.filter fun i => L * (2 : ℝ) ^ j ≤ d i ∧
          d i < 2 * (L * (2 : ℝ) ^ j)).card := by
    apply Finset.card_le_card_of_injOn (fun i => i.1)
    · intro i hi
      have hspec := (hcover (d i.1) (hd i.1 i.2)).choose_spec.2
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      change i.1 ∈ S.filter (fun i => L * (2 : ℝ) ^ j ≤ d i ∧
        d i < 2 * (L * (2 : ℝ) ^ j))
      exact Finset.mem_filter.mpr ⟨i.2, hi ▸ hspec⟩
    · intro i _ j _ hij
      exact Subtype.ext hij
  exact hfiber.trans hsubset


 

theorem many_in_one_dyadic_bin_real {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (d : ι → ℝ) {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U)
    (hd : ∀ i ∈ S, d i ∈ Icc L U) (target : ℝ)
    (hquota : ∀ M : ℕ, (M : ℝ) ≤ Real.logb 2 (U / L) + 2 →
      (M : ℝ) * target ≤ S.card) :
    ∃ M j : ℕ, (M : ℝ) ≤ Real.logb 2 (U / L) + 2 ∧
      j ∈ Finset.range M ∧
      target ≤ ((S.filter fun i => L * (2 : ℝ) ^ j ≤ d i ∧
        d i < 2 * (L * (2 : ℝ) ^ j)).card : ℝ) := by
  classical
  obtain ⟨M, hM, hcover⟩ := dyadic_time_bins hL hLU
  let f : {i // i ∈ S} → ℕ := fun i => (hcover (d i.1) (hd i.1 i.2)).choose
  have hf (i : {i // i ∈ S}) : f i ∈ Finset.range M :=
    (hcover (d i.1) (hd i.1 i.2)).choose_spec.1
  have hMne : (Finset.range M).Nonempty := by
    obtain ⟨j, hj, _⟩ := hcover L ⟨le_rfl, hLU⟩
    exact ⟨j, hj⟩
  have hsum : (Finset.range M).card • target ≤
      ∑ _i ∈ (Finset.univ : Finset {i // i ∈ S}), (1 : ℝ) := by
    simpa only [Finset.card_range, nsmul_eq_mul, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_coe] using hquota M hM
  obtain ⟨j, hj, hfiber⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := (Finset.univ : Finset {i // i ∈ S})) (t := Finset.range M)
      (f := f) (w := fun _ => (1 : ℝ)) (b := target)
      (by intro i _; exact hf i) hMne hsum
  refine ⟨M, j, hM, hj, ?_⟩
  have hsubset :
      ((Finset.univ : Finset {i // i ∈ S}).filter fun i => f i = j).card ≤
        (S.filter fun i => L * (2 : ℝ) ^ j ≤ d i ∧
          d i < 2 * (L * (2 : ℝ) ^ j)).card := by
    apply Finset.card_le_card_of_injOn (fun i => i.1)
    · intro i hi
      have hspec := (hcover (d i.1) (hd i.1 i.2)).choose_spec.2
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      change i.1 ∈ S.filter (fun i => L * (2 : ℝ) ^ j ≤ d i ∧
        d i < 2 * (L * (2 : ℝ) ^ j))
      exact Finset.mem_filter.mpr ⟨i.2, hi ▸ hspec⟩
    · intro i _ j _ hij
      exact Subtype.ext hij
  have hfiber_card : target ≤
      (((Finset.univ : Finset {i // i ∈ S}).filter fun i => f i = j).card : ℝ) := by
    simpa only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, mul_one] using hfiber
  exact hfiber_card.trans (by exact_mod_cast hsubset)


 

theorem source_count_quota {c B x n : ℝ} {M : ℕ}
    (hx : 1 ≤ x) (hB : 0 < B) (hM : (M : ℝ) ≤ B)
    (hlarge : 21 * B ≤ c * x) (hcard : c * x ^ 2 ≤ n) :
    (M : ℝ) * (1 + 16 * ((2 : ℝ) ^ ((1 : ℝ) / 4) * x)) ≤ n := by
  have htarget : 0 ≤ 1 + 16 * ((2 : ℝ) ^ ((1 : ℝ) / 4) * x) := by positivity
  have hcount := Objects.ShadowChecks.count_suff hx hB hlarge hcard
  have hBtarget := (le_div_iff₀ hB).mp hcount
  exact (mul_le_mul_of_nonneg_right hM htarget).trans (by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hBtarget)


 

theorem endpoint_time_bin_log_ratio {k : ℕ} {a N A : ℝ}
    (hN : 0 < N) (hA : 0 < A) :
    Real.logb 2 ((2 * A * N) /
      ((2 : ℝ) ^ (-((k : ℝ) + 3) * a) * N)) + 2 =
      ((k : ℝ) + 3) * a + Real.logb 2 (2 * A) + 2 := by
  have hp : 0 < (2 : ℝ) ^ (((k : ℝ) + 3) * a) := by positivity
  have hratio : (2 * A * N) /
      ((2 : ℝ) ^ (-((k : ℝ) + 3) * a) * N) =
      (2 * A) * (2 : ℝ) ^ (((k : ℝ) + 3) * a) := by
    rw [show -((k : ℝ) + 3) * a = -(((k : ℝ) + 3) * a) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  rw [hratio, Real.logb_mul (by positivity : (2 : ℝ) * A ≠ 0) hp.ne',
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
  ring


 

theorem exists_eventual_scale_threshold {a A c : ℝ}
    (ha : 0 < a) (hA : 1 < A) (hc : 0 < c) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      21 * (((k : ℝ) + 3) * a + Real.logb 2 (2 * A) + 2) ≤
        c * (2 : ℝ) ^ ((k : ℝ) / 4) := by
  let b : ℝ := Real.log 2 / 4
  have hb : 0 < b := div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (by norm_num)
  let C : ℝ := 4 * a + Real.logb 2 (2 * A) + 2
  have hC : 0 < C := by
    have hlog : 0 ≤ Real.logb 2 (2 * A) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by linarith)
    dsimp [C]
    linarith
  have ht := tendsto_exp_mul_div_rpow_atTop 1 b hb
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 21 * C / c ≤
      Real.exp (b * x) / x := by
    simpa only [Real.rpow_one] using (Filter.tendsto_atTop.1 ht (21 * C / c))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (max N 1)
  refine ⟨k₀, ?_⟩
  intro k hkk₀
  have hk : max N 1 ≤ (k : ℝ) := hk₀.trans (by exact_mod_cast hkk₀)
  have hkN : N ≤ (k : ℝ) := (le_max_left _ _).trans hk
  have hk1 : (1 : ℝ) ≤ k := (le_max_right _ _).trans hk
  have hratio := hN (k : ℝ) hkN
  have hbound : ((k : ℝ) + 3) * a + Real.logb 2 (2 * A) + 2 ≤ C * k := by
    dsimp [C]
    have hlog : 0 ≤ Real.logb 2 (2 * A) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by linarith)
    nlinarith
  have hrpow : (2 : ℝ) ^ ((k : ℝ) / 4) = Real.exp (b * k) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [b]
    ring
  rw [hrpow]
  have hratio' : 21 * C * k ≤ c * Real.exp (b * k) := by
    have := (div_le_div_iff₀ hc (by linarith : (0 : ℝ) < k)).mp hratio
    nlinarith
  nlinarith


end SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachmentCore
