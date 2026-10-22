import HigherDimLQGMetric.DGZ.NiceBoxCases
import HigherDimLQGMetric.DGZ.NiceBoxConst

/-!
# DGZ §5.3: the numeric bounds of D-OSC (P1), (P2) for DGZ's sequence (packet L4a1)

Source: [2] Prop 5.10, (5.27) (`∑_{l≥s} 2^{-l}√l ≤ 2·2^{-s}√s`) and the last display of its proof;
planning audit MA7 D-OSC ("Consequences used later" (P1): `≤ 3K√a_{j+1}`, "the sum is geometric
because `a_{l+1} - a_l ≥ λ a_l ≥ λK⁴`"; (P2): `≤ L + 1` "as `a₁ = K⁴`"); blueprint Lemma
`r2:lem:oscconds`(d), (e).

For DGZ's exponents `a = dgzSeq λ K` with `λ ≥ 0`, `K ≥ 1` and a natural number `g ≥ 3` with `g ≤
λK⁴` (so consecutive exponents differ by at least `g`):
* `oscSum_le_three` ((P1)): for `1 ≤ i ≤ m`, `∑_{i<l≤m} K√a_{l-1} 2^{-(a_{l-1}-a_i)} + K√a_m
  2^{-(a_m-a_i)} ≤ 3K√a_i`;
* `oscSum_le_one` ((P2), `K ≥ 2`): `∑_{1<l≤m} K√a_{l-1} 2^{-a_{l-1}} + K√a_m 2^{-a_m} ≤ 1`;
* `dgz_weights_le` (blueprint Convention `r2:conv:coarse`, the hypothesis of `BypassShape`): `∑_{1 ≤
  j < m} 2·41^d e^{-K√a_j} ≤ 1/2` once `log 2 ≤ λK³/3` and `8·41^d ≤ e^{K³}`;
* combined with `osc_le_of_niceOscCond`, `osc_le_of_niceOscOne`: `osc_le_three_of_niceOscCond`
  (`osc_{B̄_r(y)} h_{n-a_i} ≤ 3K√a_i`) and `osc_le_add_one_of_niceOscOne` (`osc_{B̄_r(w)} h_n ≤ L +
  1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## Elementary bounds -/

/-- `t ↦ (1 + t) 2^{-t}` is antitone on `ℕ`. -/
theorem one_add_mul_half_pow_antitone :
    Antitone fun t : ℕ => (1 + (t : ℝ)) * (2 : ℝ)⁻¹ ^ t := by
  refine antitone_nat_of_succ_le fun t => ?_
  show (1 + ((t + 1 : ℕ) : ℝ)) * (2 : ℝ)⁻¹ ^ (t + 1) ≤ (1 + (t : ℝ)) * (2 : ℝ)⁻¹ ^ t
  rw [pow_succ]
  push_cast
  have h : (0 : ℝ) < (2 : ℝ)⁻¹ ^ t := by positivity
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  nlinarith

/-- `(1 + t) 2^{-t} ≤ 1`. -/
theorem one_add_mul_half_pow_le_one (t : ℕ) : (1 + (t : ℝ)) * (2 : ℝ)⁻¹ ^ t ≤ 1 := by
  have h := one_add_mul_half_pow_antitone (Nat.zero_le t)
  simpa using h

/-- `1 + g ≤ 2^{g-1}` for `g ≥ 3`. -/
theorem one_add_le_two_pow_sub_one {g : ℕ} (hg : 3 ≤ g) : 1 + g ≤ 2 ^ (g - 1) := by
  induction g, hg using Nat.le_induction with
  | base => norm_num
  | succ g hg ih =>
    rw [Nat.add_sub_cancel, show g = g - 1 + 1 by omega, pow_succ]
    omega

/-- `(1 + kg) 2^{-kg} ≤ 2^{-k}` for `g ≥ 3`. -/
theorem one_add_mul_half_pow_mul_le {g : ℕ} (hg : 3 ≤ g) (k : ℕ) :
    (1 + ((k * g : ℕ) : ℝ)) * (2 : ℝ)⁻¹ ^ (k * g) ≤ (2 : ℝ)⁻¹ ^ k := by
  have h1 : (1 + ((k * g : ℕ) : ℝ)) ≤ (1 + (g : ℝ)) ^ k := by
    push_cast
    have := one_add_mul_le_pow (a := (g : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) g]) k
    linarith
  have h2 : (1 + (g : ℝ)) ≤ (2 : ℝ) ^ (g - 1) := by
    exact_mod_cast one_add_le_two_pow_sub_one hg
  have h3 : (1 + (g : ℝ)) ^ k ≤ ((2 : ℝ) ^ (g - 1)) ^ k :=
    pow_le_pow_left₀ (by positivity) h2 k
  have e : ((2 : ℝ) ^ (g - 1)) ^ k * (2 : ℝ)⁻¹ ^ (k * g) = (2 : ℝ)⁻¹ ^ k := by
    have hkg : k * g = (g - 1) * k + k := by
      obtain ⟨g', rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ g)
      rw [Nat.add_sub_cancel_left]
      ring
    rw [hkg, ← pow_mul, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow,
      one_mul]
  calc (1 + ((k * g : ℕ) : ℝ)) * (2 : ℝ)⁻¹ ^ (k * g)
      ≤ ((2 : ℝ) ^ (g - 1)) ^ k * (2 : ℝ)⁻¹ ^ (k * g) :=
        mul_le_mul_of_nonneg_right (h1.trans h3) (by positivity)
    _ = (2 : ℝ)⁻¹ ^ k := e

/-- `√(a + t) ≤ √a (1 + t)` for `a ≥ 1`, `t ≥ 0`. -/
theorem sqrt_add_le_sqrt_mul {a t : ℝ} (ha : 1 ≤ a) (ht : 0 ≤ t) : √(a + t) ≤ √a * (1 + t) := by
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + t), ← Real.sqrt_mul (by linarith)]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [mul_nonneg ht (by linarith : (0 : ℝ) ≤ 2 * a - 1),
    mul_nonneg (by linarith : (0 : ℝ) ≤ a) (sq_nonneg t)]

/-- `∑_{a < l ≤ b} 2^{-(l-a)} = 1 - 2^{-(b-a)}` for `a ≤ b`. -/
theorem sum_Ioc_half_pow (a : ℕ) :
    ∀ b, a ≤ b → ∑ l ∈ Finset.Ioc a b, (2 : ℝ)⁻¹ ^ (l - a) = 1 - (2 : ℝ)⁻¹ ^ (b - a) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih, show b + 1 - a = (b - a) + 1 by omega, pow_succ]
    ring

theorem sum_Ioc_half_pow_le_one (a b : ℕ) : ∑ l ∈ Finset.Ioc a b, (2 : ℝ)⁻¹ ^ (l - a) ≤ 1 := by
  rcases le_or_gt a b with hab | hab
  · rw [sum_Ioc_half_pow a b hab]
    have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (b - a) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    norm_num

/-! ## Gap growth of DGZ's exponents -/

/-- Consecutive exponents differ by at least `g` (`g ≤ λK⁴`, `k ≥ 1`). -/
theorem dgzSeq_succ_sub_ge {lam : ℝ} {K : ℕ} (hlam : 0 ≤ lam) (hK : 1 ≤ K) {g : ℕ}
    (hg : (g : ℝ) ≤ lam * (K : ℝ) ^ 4) {k : ℕ} (hk : 1 ≤ k) :
    g ≤ dgzSeq lam K (k + 1) - dgzSeq lam K k := by
  have h1 := dgzSeq_gap (K := K) hlam hk
  have h2 : ((K ^ 4 : ℕ) : ℝ) ≤ dgzSeq lam K k := by exact_mod_cast pow_le_dgzSeq hlam hK hk
  push_cast at h2
  have h3 : (g : ℝ) ≤ ((dgzSeq lam K (k + 1) - dgzSeq lam K k : ℕ) : ℝ) := by nlinarith
  exact_mod_cast h3

/-- `a_k - a_i ≥ (k - i) g` for `1 ≤ i ≤ k`. -/
theorem dgzSeq_sub_ge {lam : ℝ} {K : ℕ} (hlam : 0 ≤ lam) (hK : 1 ≤ K) {g : ℕ}
    (hg : (g : ℝ) ≤ lam * (K : ℝ) ^ 4) {i : ℕ} (hi : 1 ≤ i) :
    ∀ k, i ≤ k → (k - i) * g ≤ dgzSeq lam K k - dgzSeq lam K i := by
  intro k hik
  induction k, hik using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
    have h1 := dgzSeq_succ_sub_ge hlam hK hg (le_trans hi hik)
    have h2 : dgzSeq lam K i ≤ dgzSeq lam K k := dgzSeq_monotone hlam hK hik
    have h3 : dgzSeq lam K k ≤ dgzSeq lam K (k + 1) := dgzSeq_monotone hlam hK (Nat.le_succ k)
    have e : (k + 1 - i) * g = (k - i) * g + g := by
      rw [show k + 1 - i = (k - i) + 1 by omega, add_mul, one_mul]
    omega

/-! ## (P1): `≤ 3K√a_i` -/

/-- **(P1), numeric** (MA7 D-OSC; blueprint `r2:lem:oscconds`(d)): for DGZ's sequence with a gap
`g ≥ 3`, `g ≤ λK⁴`, and `1 ≤ i ≤ m`:
`∑_{i<l≤m} K√a_{l-1} 2^{-(a_{l-1}-a_i)} + K√a_m 2^{-(a_m-a_i)} ≤ 3K√a_i`. -/
theorem oscSum_le_three (p : NiceParams) {lam : ℝ} (hlam : 0 ≤ lam) (hK : 1 ≤ p.K)
    (ha : p.a = dgzSeq lam p.K) {g : ℕ} (hg3 : 3 ≤ g) (hg : (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4)
    {i m : ℕ} (hi : 1 ≤ i) (him : i ≤ m) :
    (∑ l ∈ Finset.Ioc i m, p.K * √(p.a (l - 1) : ℝ) * (2 : ℝ)⁻¹ ^ (p.a (l - 1) - p.a i)) +
      p.K * √(p.a m : ℝ) * (2 : ℝ)⁻¹ ^ (p.a m - p.a i) ≤ 3 * p.K * √(p.a i : ℝ) := by
  have hmono : Monotone p.a := by rw [ha]; exact dgzSeq_monotone hlam hK
  have hai : (1 : ℝ) ≤ p.a i := by
    have := (le_dgzSeq hlam hK i).trans_eq (congrFun ha i).symm
    exact_mod_cast le_trans hi this
  have hK0 : (0 : ℝ) ≤ p.K := Nat.cast_nonneg _
  set A := (p.K : ℝ) * √(p.a i : ℝ) with hA
  have hA0 : 0 ≤ A := by positivity
  -- each term: `K√a_{l'} 2^{-(a_{l'}-a_i)} ≤ A (1 + t) 2^{-t}`, `t = a_{l'} - a_i`
  have hterm : ∀ l', i ≤ l' → (p.K : ℝ) * √(p.a l' : ℝ) * (2 : ℝ)⁻¹ ^ (p.a l' - p.a i) ≤
      A * ((1 + ((p.a l' - p.a i : ℕ) : ℝ)) * (2 : ℝ)⁻¹ ^ (p.a l' - p.a i)) := by
    intro l' hl'
    have hle : p.a i ≤ p.a l' := hmono hl'
    have e : (p.a l' : ℝ) = p.a i + ((p.a l' - p.a i : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]
      ring
    have hs := sqrt_add_le_sqrt_mul hai (Nat.cast_nonneg (p.a l' - p.a i))
    rw [← e] at hs
    have hpow : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (p.a l' - p.a i) := by positivity
    calc (p.K : ℝ) * √(p.a l' : ℝ) * (2 : ℝ)⁻¹ ^ (p.a l' - p.a i)
        ≤ (p.K : ℝ) * (√(p.a i : ℝ) * (1 + ((p.a l' - p.a i : ℕ) : ℝ))) *
            (2 : ℝ)⁻¹ ^ (p.a l' - p.a i) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hK0) hpow
      _ = A * ((1 + ((p.a l' - p.a i : ℕ) : ℝ)) * (2 : ℝ)⁻¹ ^ (p.a l' - p.a i)) := by
          rw [hA]
          ring
  -- the final term
  have hlast : (p.K : ℝ) * √(p.a m : ℝ) * (2 : ℝ)⁻¹ ^ (p.a m - p.a i) ≤ A :=
    (hterm m him).trans (by
      have := one_add_mul_half_pow_le_one (p.a m - p.a i)
      nlinarith)
  -- the sum
  have hsum : ∑ l ∈ Finset.Ioc i m, (p.K : ℝ) * √(p.a (l - 1) : ℝ) *
      (2 : ℝ)⁻¹ ^ (p.a (l - 1) - p.a i) ≤ 2 * A := by
    rcases Nat.eq_or_lt_of_le him with rfl | hlt
    · rw [Finset.Ioc_self, Finset.sum_empty]
      linarith
    · have e : Finset.Ioc i m = insert (i + 1) (Finset.Ioc (i + 1) m) := by
        ext l
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      rw [e, Finset.sum_insert (by simp)]
      have h1 : (p.K : ℝ) * √(p.a (i + 1 - 1) : ℝ) * (2 : ℝ)⁻¹ ^ (p.a (i + 1 - 1) - p.a i) = A := by
        rw [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
      have h2 : ∑ l ∈ Finset.Ioc (i + 1) m, (p.K : ℝ) * √(p.a (l - 1) : ℝ) *
          (2 : ℝ)⁻¹ ^ (p.a (l - 1) - p.a i) ≤
          ∑ l ∈ Finset.Ioc (i + 1) m, A * (2 : ℝ)⁻¹ ^ (l - (i + 1)) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hl' := Finset.mem_Ioc.1 hl
        have hil : i ≤ l - 1 := by omega
        refine (hterm (l - 1) hil).trans (mul_le_mul_of_nonneg_left ?_ hA0)
        -- `t = a_{l-1} - a_i ≥ (l-1-i) g`
        have hgap : (l - 1 - i) * g ≤ p.a (l - 1) - p.a i := by
          rw [ha]
          exact dgzSeq_sub_ge hlam hK hg hi (l - 1) hil
        have hk : l - (i + 1) = l - 1 - i := by omega
        rw [hk]
        exact (one_add_mul_half_pow_antitone hgap).trans (one_add_mul_half_pow_mul_le hg3 _)
      have h3 : ∑ l ∈ Finset.Ioc (i + 1) m, A * (2 : ℝ)⁻¹ ^ (l - (i + 1)) ≤ A := by
        rw [← Finset.mul_sum]
        have := sum_Ioc_half_pow_le_one (i + 1) m
        nlinarith
      rw [h1]
      linarith
  linarith

/-! ## (P2): `≤ 1` -/

/-- `3(1 + T) ≤ 2^T` for `T ≥ 5`. -/
theorem three_mul_one_add_le_two_pow {T : ℕ} (hT : 5 ≤ T) : 3 * (1 + T) ≤ 2 ^ T := by
  induction T, hT using Nat.le_induction with
  | base => norm_num
  | succ T hT ih =>
    rw [pow_succ]
    omega

/-- **(P2), numeric** (MA7 D-OSC; blueprint `r2:lem:oscconds`(e)): for DGZ's sequence with `K ≥ 2`
and a gap `g ≥ 3`, `g ≤ λK⁴`, and `m ≥ 1`:
`∑_{1<l≤m} K√a_{l-1} 2^{-(a_{l-1}-a_0)} + K√a_m 2^{-(a_m-a_0)} ≤ 1`. -/
theorem oscSum_le_one (p : NiceParams) {lam : ℝ} (hlam : 0 ≤ lam) (hK : 2 ≤ p.K)
    (ha : p.a = dgzSeq lam p.K) {g : ℕ} (hg3 : 3 ≤ g) (hg : (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4)
    {m : ℕ} (hm : 1 ≤ m) :
    (∑ l ∈ Finset.Ioc 1 m, p.K * √(p.a (l - 1) : ℝ) * (2 : ℝ)⁻¹ ^ (p.a (l - 1) - p.a 0)) +
      p.K * √(p.a m : ℝ) * (2 : ℝ)⁻¹ ^ (p.a m - p.a 0) ≤ 1 := by
  have hK1 : 1 ≤ p.K := by omega
  have hmono : Monotone p.a := by rw [ha]; exact dgzSeq_monotone hlam hK1
  have ha0 : p.a 0 = 0 := by rw [ha]; rfl
  set T := p.K ^ 4 with hT
  have hT16 : 16 ≤ T := by
    rw [hT]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ p.K ^ 4 := Nat.pow_le_pow_left hK 4
  set B : ℝ := (1 + (T : ℝ)) * (2 : ℝ)⁻¹ ^ T with hB
  have hB0 : 0 ≤ B := by positivity
  have hB3 : 3 * B ≤ 1 := by
    have h1 : (3 * (1 + T) : ℕ) ≤ 2 ^ T := three_mul_one_add_le_two_pow (by omega)
    have h2 : (3 : ℝ) * (1 + (T : ℝ)) ≤ (2 : ℝ) ^ T := by exact_mod_cast h1
    rw [hB, ← mul_assoc, inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact h2
  -- each term with `b = a_{l'} ≥ K⁴`: `K√b 2^{-b} ≤ (1 + b) 2^{-b}`
  have hterm : ∀ l', 1 ≤ l' → (p.K : ℝ) * √(p.a l' : ℝ) * (2 : ℝ)⁻¹ ^ (p.a l' - p.a 0) ≤
      (1 + (p.a l' : ℝ)) * (2 : ℝ)⁻¹ ^ (p.a l') := by
    intro l' hl'
    rw [ha0, Nat.sub_zero]
    have hb : (T : ℝ) ≤ p.a l' := by
      have := pow_le_dgzSeq (K := p.K) hlam hK1 hl'
      rw [← ha] at this
      exact_mod_cast this
    have hK2 : (p.K : ℝ) ^ 2 ≤ p.a l' := by
      have : (p.K : ℝ) ^ 2 ≤ (p.K : ℝ) ^ 4 :=
        pow_le_pow_right₀ (by exact_mod_cast hK1) (by norm_num)
      have hT' : (T : ℝ) = (p.K : ℝ) ^ 4 := by rw [hT]; push_cast; ring
      linarith
    have hKs : (p.K : ℝ) ≤ √(p.a l' : ℝ) := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg p.K)]
      exact Real.sqrt_le_sqrt hK2
    have hss : √(p.a l' : ℝ) * √(p.a l' : ℝ) = p.a l' :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    have h1 : (p.K : ℝ) * √(p.a l' : ℝ) ≤ 1 + p.a l' := by
      have := mul_le_mul_of_nonneg_right hKs (Real.sqrt_nonneg (p.a l' : ℝ))
      linarith
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  -- the final term
  have hlast : (p.K : ℝ) * √(p.a m : ℝ) * (2 : ℝ)⁻¹ ^ (p.a m - p.a 0) ≤ B := by
    refine (hterm m hm).trans ?_
    have hb : T ≤ p.a m := by
      have := pow_le_dgzSeq (K := p.K) hlam hK1 hm
      rwa [← ha] at this
    exact one_add_mul_half_pow_antitone hb
  -- the sum: `≤ 2B`
  have hsum : ∑ l ∈ Finset.Ioc 1 m, (p.K : ℝ) * √(p.a (l - 1) : ℝ) *
      (2 : ℝ)⁻¹ ^ (p.a (l - 1) - p.a 0) ≤ 2 * B := by
    have h2 : ∑ l ∈ Finset.Ioc 1 m, (p.K : ℝ) * √(p.a (l - 1) : ℝ) *
        (2 : ℝ)⁻¹ ^ (p.a (l - 1) - p.a 0) ≤
        ∑ l ∈ Finset.Ioc 1 m, 2 * B * (2 : ℝ)⁻¹ ^ (l - 1) := by
      refine Finset.sum_le_sum fun l hl => ?_
      have hl' := Finset.mem_Ioc.1 hl
      by_cases hl2 : l = 1
      · -- `l = 1`: the term `K√a₀ 2^0 = 0`
        subst hl2
        rw [Nat.sub_self, ha0, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_mul]
        positivity
      · have hl1 : 1 ≤ l - 1 := by omega
        refine (hterm (l - 1) hl1).trans ?_
        -- `a_{l-1} ≥ K⁴ + (l-2) g`
        have hgap : (l - 1 - 1) * g ≤ p.a (l - 1) - p.a 1 := by
          rw [ha]
          exact dgzSeq_sub_ge hlam hK1 hg le_rfl (l - 1) hl1
        have ha1 : p.a 1 = T := by rw [ha]; rfl
        have hge : T + (l - 1 - 1) * g ≤ p.a (l - 1) := by
          have := hmono hl1
          rw [ha1] at hgap this
          omega
        have h3 := one_add_mul_half_pow_antitone hge
        have h4 : (1 + ((T + (l - 1 - 1) * g : ℕ) : ℝ)) * (2 : ℝ)⁻¹ ^ (T + (l - 1 - 1) * g) ≤
            B * ((2 : ℝ)⁻¹ ^ (l - 1 - 1)) := by
          have h5 := one_add_mul_half_pow_mul_le hg3 (l - 1 - 1)
          have hx : (0 : ℝ) ≤ ((l - 1 - 1) * g : ℕ) := Nat.cast_nonneg _
          have hpos1 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ T := by positivity
          have hpos2 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ ((l - 1 - 1) * g) := by positivity
          calc (1 + ((T + (l - 1 - 1) * g : ℕ) : ℝ)) * (2 : ℝ)⁻¹ ^ (T + (l - 1 - 1) * g)
              ≤ ((1 + (T : ℝ)) * (1 + (((l - 1 - 1) * g : ℕ) : ℝ))) *
                  ((2 : ℝ)⁻¹ ^ T * (2 : ℝ)⁻¹ ^ ((l - 1 - 1) * g)) := by
                rw [← pow_add]
                refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                push_cast
                have : (0 : ℝ) ≤ (T : ℝ) * (((l - 1 - 1 : ℕ) : ℝ) * (g : ℝ)) := by positivity
                nlinarith [this]
            _ = B * ((1 + (((l - 1 - 1) * g : ℕ) : ℝ)) * (2 : ℝ)⁻¹ ^ ((l - 1 - 1) * g)) := by
                rw [hB]
                ring
            _ ≤ B * ((2 : ℝ)⁻¹ ^ (l - 1 - 1)) := mul_le_mul_of_nonneg_left h5 hB0
        have h6 : B * ((2 : ℝ)⁻¹ ^ (l - 1 - 1)) = 2 * B * (2 : ℝ)⁻¹ ^ (l - 1) := by
          obtain ⟨k, hk⟩ : ∃ k, l - 1 = k + 1 := ⟨l - 1 - 1, by omega⟩
          rw [hk, Nat.add_sub_cancel, pow_succ]
          ring
        rw [← h6]
        exact h3.trans h4
    have h3 : ∑ l ∈ Finset.Ioc 1 m, 2 * B * (2 : ℝ)⁻¹ ^ (l - 1) ≤ 2 * B := by
      rw [← Finset.mul_sum]
      have := sum_Ioc_half_pow_le_one 1 m
      nlinarith
    linarith
  linarith

/-! ## The weights of the bypass lemma -/

/-- `1 + λ/3 ≤ √(1 + λ)` for `0 ≤ λ ≤ 3`. -/
theorem one_add_div_three_le_sqrt {lam : ℝ} (h0 : 0 ≤ lam) (h3 : lam ≤ 3) :
    1 + lam / 3 ≤ √(1 + lam) := by
  rw [Real.le_sqrt (by linarith) (by linarith)]
  nlinarith

/-- `K√a_j ≥ K³ + (j - 1) λK³/3` for DGZ's exponents (`j ≥ 1`, `0 ≤ λ ≤ 3`). -/
theorem mul_sqrt_dgzSeq_ge {lam : ℝ} (h0 : 0 ≤ lam) (h3 : lam ≤ 3) {K : ℕ} (hK : 1 ≤ K) :
    ∀ j, 1 ≤ j → (K : ℝ) ^ 3 + ((j - 1 : ℕ) : ℝ) * (lam * (K : ℝ) ^ 3 / 3) ≤
      K * √(dgzSeq lam K j : ℝ) := by
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hsqK : ∀ j, 1 ≤ j → (K : ℝ) ^ 2 ≤ √(dgzSeq lam K j : ℝ) := by
    intro j hj
    have h1 : ((K ^ 4 : ℕ) : ℝ) ≤ dgzSeq lam K j := by exact_mod_cast pow_le_dgzSeq h0 hK hj
    rw [Real.le_sqrt (by positivity) (Nat.cast_nonneg _)]
    push_cast at h1
    nlinarith
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    have e : √(dgzSeq lam K 1 : ℝ) = (K : ℝ) ^ 2 := by
      rw [dgzSeq_one, Nat.cast_pow, show (K : ℝ) ^ 4 = ((K : ℝ) ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [e, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    ring_nf
    rfl
  | succ j hj ih =>
    have h1 := dgzSeq_succ_ge (K := K) (lam := lam) hj
    have h2 : √(1 + lam) * √(dgzSeq lam K j : ℝ) ≤ √(dgzSeq lam K (j + 1) : ℝ) := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt h1
    have h3' := one_add_div_three_le_sqrt h0 h3
    have h4 := hsqK j hj
    have hsj : 0 ≤ √(dgzSeq lam K j : ℝ) := Real.sqrt_nonneg _
    have h5 : (1 + lam / 3) * √(dgzSeq lam K j : ℝ) ≤ √(dgzSeq lam K (j + 1) : ℝ) :=
      (mul_le_mul_of_nonneg_right h3' hsj).trans h2
    have e : ((j + 1 - 1 : ℕ) : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
      rw [show j + 1 - 1 = (j - 1) + 1 by omega]
      push_cast
      ring
    rw [e]
    have h6 : (K : ℝ) * ((lam / 3) * √(dgzSeq lam K j : ℝ)) ≥ (K : ℝ) * ((lam / 3) * (K : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity)) hK0
    have h7 : (K : ℝ) * ((1 + lam / 3) * √(dgzSeq lam K j : ℝ)) ≤
        K * √(dgzSeq lam K (j + 1) : ℝ) := mul_le_mul_of_nonneg_left h5 hK0
    nlinarith

/-- **The weights of the bypass lemma** (blueprint Convention `r2:conv:coarse`; DGZ Lemma 5.11 with
`w_j = e^{-K√a_j}`): for DGZ's exponents with `0 ≤ λ ≤ 3`, `K ≥ 1`, `log 2 ≤ λK³/3` and
`8·41^d ≤ e^{K³}`, `∑_{1 ≤ j < m} 2·41^d e^{-K√a_j} ≤ 1/2` for every `m`. -/
theorem dgz_weights_le {lam : ℝ} (h0 : 0 ≤ lam) (h3 : lam ≤ 3) {K : ℕ} (hK : 1 ≤ K)
    (hr : Real.log 2 ≤ lam * (K : ℝ) ^ 3 / 3) (d : ℕ)
    (hc : 8 * (41 : ℝ) ^ d ≤ Real.exp ((K : ℝ) ^ 3)) (m : ℕ) :
    (∑ j ∈ Finset.Ico 1 m, 2 * (41 : ℝ) ^ d * Real.exp (-(K * √(dgzSeq lam K j : ℝ)))) ≤
      1 / 2 := by
  have hE : 0 < Real.exp ((K : ℝ) ^ 3) := Real.exp_pos _
  -- each term is at most `2·41^d e^{-K³} 2^{-(j-1)}`
  have hterm : ∀ j ∈ Finset.Ico 1 m, 2 * (41 : ℝ) ^ d * Real.exp (-(K * √(dgzSeq lam K j : ℝ))) ≤
      2 * (41 : ℝ) ^ d * Real.exp (-((K : ℝ) ^ 3)) * (1 / 2) ^ (j - 1) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.1 hj).1
    have h1 := mul_sqrt_dgzSeq_ge h0 h3 hK j hj1
    have h2 : Real.exp (-(K * √(dgzSeq lam K j : ℝ))) ≤
        Real.exp (-((K : ℝ) ^ 3)) * Real.exp (-(lam * (K : ℝ) ^ 3 / 3)) ^ (j - 1) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      linarith
    have h3' : Real.exp (-(lam * (K : ℝ) ^ 3 / 3)) ≤ 1 / 2 := by
      rw [show (1 : ℝ) / 2 = Real.exp (-Real.log 2) by
        rw [Real.exp_neg, Real.exp_log two_pos, one_div]]
      exact Real.exp_le_exp.2 (by linarith)
    have h4 : Real.exp (-(lam * (K : ℝ) ^ 3 / 3)) ^ (j - 1) ≤ (1 / 2) ^ (j - 1) :=
      pow_le_pow_left₀ (Real.exp_pos _).le h3' _
    have h5 : Real.exp (-(K * √(dgzSeq lam K j : ℝ))) ≤
        Real.exp (-((K : ℝ) ^ 3)) * (1 / 2) ^ (j - 1) :=
      h2.trans (mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le)
    calc 2 * (41 : ℝ) ^ d * Real.exp (-(K * √(dgzSeq lam K j : ℝ)))
        ≤ 2 * (41 : ℝ) ^ d * (Real.exp (-((K : ℝ) ^ 3)) * (1 / 2) ^ (j - 1)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = 2 * (41 : ℝ) ^ d * Real.exp (-((K : ℝ) ^ 3)) * (1 / 2) ^ (j - 1) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
  have hgeo : ∑ k ∈ Finset.range (m - 1), (1 / 2 : ℝ) ^ (1 + k - 1) ≤ 2 := by
    have e : ∀ k : ℕ, 1 + k - 1 = k := fun k => by omega
    simp only [e]
    exact sum_geometric_two_le _
  have hmain : 2 * (41 : ℝ) ^ d * Real.exp (-((K : ℝ) ^ 3)) ≤ 1 / 4 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]
    linarith
  have hpos : 0 ≤ 2 * (41 : ℝ) ^ d * Real.exp (-((K : ℝ) ^ 3)) := by positivity
  nlinarith

/-! ## Combined forms -/

/-- **D-OSC (P1)** for DGZ's sequence: `osc_{B̄_r(y)} h_{n-a_i} ≤ 3K√a_i` (`y = s_i v`, `r ≤ 8 s_i`,
`1 ≤ i ≤ m`, the containing boxes satisfy (a′), `𝒥₂′`, `y ∈ B₃(0)`). -/
theorem osc_le_three_of_niceOscCond (p : NiceParams) (H : ℕ → Rd d → ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hK : 1 ≤ p.K) (ha : p.a = dgzSeq lam p.K) {g : ℕ} (hg3 : 3 ≤ g)
    (hg : (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4) {i m : ℕ} (hi : 1 ≤ i) (him : i ≤ m) (v : Zd d)
    {r : ℝ} (hr : r ≤ 8 * p.s i)
    (hbox : ∀ l, i < l → l ≤ m → ∃ u : Zd d,
      latPt (p.s i) v ∈ obox (latPt (p.s l) u) (4 * p.s l) ∧ NiceOscCond p H l u)
    (hJ : EventJ2' p H m) (hy : latPt (p.s i) v ∈ obox (0 : Rd d) 3) :
    ∀ z ∈ cbox (latPt (p.s i) v) r, ∀ w ∈ cbox (latPt (p.s i) v) r,
      |H (p.n - p.a i) z - H (p.n - p.a i) w| ≤ 3 * p.K * √(p.a i : ℝ) := fun z hz w hw =>
  (osc_le_of_niceOscCond p H him v hr hbox hJ hy z hz w hw).trans
    (oscSum_le_three p hlam hK ha hg3 hg hi him)

/-- **D-OSC (P2)** for DGZ's sequence (`K ≥ 2`): `osc_{B̄_r(w)} h_n ≤ L + 1` (`w = s₀ v`,
`r ≤ 3 s₀`, the containing `a₁`-box satisfies (1′), the higher containing boxes satisfy (a′),
`𝒥₂′`, `w ∈ B₃(0)`). -/
theorem osc_le_add_one_of_niceOscOne (p : NiceParams) (H : ℕ → Rd d → ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hK : 2 ≤ p.K) (ha : p.a = dgzSeq lam p.K) {g : ℕ} (hg3 : 3 ≤ g)
    (hg : (g : ℝ) ≤ lam * (p.K : ℝ) ^ 4) {m : ℕ} (hm : 1 ≤ m) (v : Zd d) {r : ℝ}
    (hr : r ≤ 3 * p.s 0) {u₁ : Zd d}
    (hu₁ : latPt (p.s 0) v ∈ obox (latPt (p.s 1) u₁) (p.s 1)) (h1 : NiceOscOne p H u₁)
    (hbox : ∀ l, 1 < l → l ≤ m → ∃ u : Zd d,
      latPt (p.s 0) v ∈ obox (latPt (p.s l) u) (4 * p.s l) ∧ NiceOscCond p H l u)
    (hJ : EventJ2' p H m) (hy : latPt (p.s 0) v ∈ obox (0 : Rd d) 3) :
    ∀ z ∈ cbox (latPt (p.s 0) v) r, ∀ w ∈ cbox (latPt (p.s 0) v) r,
      |H p.n z - H p.n w| ≤ p.L + 1 := by
  have ha0 : p.a 0 = 0 := by rw [ha]; rfl
  intro z hz w hw
  have h := osc_le_of_niceOscOne p H ha0 hm v hr hu₁ h1 hbox hJ hy z hz w hw
  have h2 := oscSum_le_one p hlam hK ha hg3 hg hm
  linarith

end DGZ

end HigherDimLQGMetric
