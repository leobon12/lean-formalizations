import HigherDimLQGMetric.DGZ.NiceBoxMeas

/-!
# DGZ §5.1: the coarse-graining constants (5.3)–(5.7) (packet L4a1)

Source: [2] (5.3)–(5.7) (TeX l. 2058–2091); planning audit MA7 §2.2 row "(5.3)–(5.7)" ("checked: `α
> 0 ⟺ Q > √(2d)`; `(1-2λ)n ≤ a_m ≤ (1-λ)n`; `𝒴_{j+1} ⊂ 𝒴_j`; `2/s_j ∈ ℤ`"); blueprint Convention
`r2:conv:coarse` ("for `K ≥ C`: `s_{j+1}/s_j ≥ 2^{λK⁴}`").

* `α = Q²/4 - d/2`: `dgzAlpha_pos_iff` (`α > 0 ⟺ √(2d) < Q`, for `Q ≥ 0`), `dgzAlpha_pos`.
* `λ = α/(4(α+d))`: `dgzLambda_pos`, `dgzLambda_le_quarter`, `dgzLambda_lt_half` (`λ < α/(2(α+d))`,
  Lemma 5.9), `dgzLambda_lt_alpha_div` (`λ < α/(2d+α)`, Lemma 5.8).
* `R = ⌊100 r₀⌋ + 100`: `le_dgzR` (`2 r₀ + 10 ≤ R` for every `r₀`, the hypothesis of the
  independence lemmas).
* `a_i` (`dgzSeq`): `dgzSeq_succ_ge` (`(1+λ)a_i ≤ a_{i+1}`), `dgzSeq_succ_le` (`a_{i+1} ≤ (1+λ)a_i +
  1`), `dgzSeq_strictMono`, `dgzSeq_monotone`, `pow_le_dgzSeq` (`K⁴ ≤ a_i`), `dgzSeq_gap` (`λ a_i ≤
  a_{i+1} - a_i`), `one_add_pow_mul_le_dgzSeq` (`(1+λ)^{i-1} K⁴ ≤ a_i`).
* `m` (`dgzLevel`): `dgzLevel_spec` (`1 ≤ m`, `a_m ≤ (1-λ)n < a_{m+1}`), `dgzLevel_lower` (`(1-2λ)n
  ≤ a_m` once `2λ²n ≥ 1`).
* Scales: `NiceParams.s_succ_eq` (`s_{i+1} = 2^{a_{i+1}-a_i} s_i`), `NiceParams.s_mul_two_pow`
  (`2/s_i ∈ ℤ`), `NiceParams.latPt_succ_eq` (`𝒴_{i+1} ⊆ 𝒴_i`), `dgz_rpow_mul_s_le` (`2^{λK⁴} s_i ≤
  s_{i+1}` for the DGZ sequence, `1 ≤ i`, `a_{i+1} ≤ n`), `dgz_gap_of_le` (the gap hypotheses `c
  s_{i-1} ≤ s_i`, `2 ≤ i ≤ j`, of the locality and independence lemmas, for `c ≤ 2^{λK⁴}` and `a_j ≤
  n`).
* `superScale_le_self` (`m(N) ≤ N` for `N ≥ 8`; the hypothesis of the certificate lemmas).
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

/-! ## `α`, `λ`, `R` -/

theorem dgzAlpha_pos_iff (d : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) : 0 < dgzAlpha d Q ↔ √(2 * d) < Q := by
  unfold dgzAlpha
  have hd : (0 : ℝ) ≤ 2 * d := by positivity
  constructor
  · intro h
    have h1 : 2 * (d : ℝ) < Q ^ 2 := by linarith
    calc √(2 * d) < √(Q ^ 2) := Real.sqrt_lt_sqrt hd h1
      _ = Q := Real.sqrt_sq hQ
  · intro h
    have h1 : 2 * (d : ℝ) < Q ^ 2 := by
      have := Real.sq_sqrt hd
      nlinarith [Real.sqrt_nonneg (2 * (d : ℝ))]
    linarith

theorem dgzAlpha_pos {Q : ℝ} (hQ : √(2 * d) < Q) : 0 < dgzAlpha d Q := by
  have hQ0 : 0 < Q := lt_of_le_of_lt (Real.sqrt_nonneg _) hQ
  have h1 : (2 * d : ℝ) < Q ^ 2 := by
    have := (Real.sqrt_lt' hQ0).1 hQ
    exact this
  unfold dgzAlpha
  linarith

theorem dgzLambda_pos {Q : ℝ} (hα : 0 < dgzAlpha d Q) : 0 < dgzLambda d Q := by
  unfold dgzLambda
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  positivity

theorem dgzLambda_le_quarter {Q : ℝ} (hα : 0 < dgzAlpha d Q) : dgzLambda d Q ≤ 1 / 4 := by
  unfold dgzLambda
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- `λ < α/(2(α+d))` (used in DGZ Lemma 5.9). -/
theorem dgzLambda_lt_half {Q : ℝ} (hα : 0 < dgzAlpha d Q) :
    dgzLambda d Q < dgzAlpha d Q / (2 * (dgzAlpha d Q + d)) := by
  unfold dgzLambda
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  apply div_lt_div_of_pos_left hα (by positivity)
  linarith

/-- `λ < α/(2d+α)` (used in DGZ Lemma 5.8). -/
theorem dgzLambda_lt_alpha_div {Q : ℝ} (hα : 0 < dgzAlpha d Q) :
    dgzLambda d Q < dgzAlpha d Q / (2 * d + dgzAlpha d Q) := by
  unfold dgzLambda
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  apply div_lt_div_of_pos_left hα (by positivity)
  linarith

/-- `R = ⌊100 r₀⌋ + 100 ≥ 2 r₀ + 10` (DGZ's `R ≥ 2(5 + r₀)`). -/
theorem le_dgzR (r₀ : ℝ) : 2 * r₀ + 10 ≤ (dgzR r₀ : ℝ) := by
  unfold dgzR
  push_cast
  have := Nat.lt_floor_add_one (100 * r₀)
  linarith

/-! ## The exponents `a_i` -/

section Seq

variable {lam : ℝ} {K : ℕ}

theorem dgzSeq_zero : dgzSeq lam K 0 = 0 := rfl

theorem dgzSeq_one : dgzSeq lam K 1 = K ^ 4 := rfl

theorem dgzSeq_succ {i : ℕ} (hi : 1 ≤ i) :
    dgzSeq lam K (i + 1) = ⌊(1 + lam) * (dgzSeq lam K i : ℝ)⌋₊ + 1 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  rfl

/-- `(1+λ) a_i ≤ a_{i+1}` (`i ≥ 1`, `λ ≥ 0`). -/
theorem dgzSeq_succ_ge {i : ℕ} (hi : 1 ≤ i) :
    (1 + lam) * (dgzSeq lam K i : ℝ) ≤ dgzSeq lam K (i + 1) := by
  rw [dgzSeq_succ hi]
  push_cast
  exact (Nat.lt_floor_add_one _).le

/-- `a_{i+1} ≤ (1+λ) a_i + 1` (`i ≥ 1`, `λ ≥ 0`). -/
theorem dgzSeq_succ_le (hlam : 0 ≤ lam) {i : ℕ} (hi : 1 ≤ i) :
    (dgzSeq lam K (i + 1) : ℝ) ≤ (1 + lam) * dgzSeq lam K i + 1 := by
  rw [dgzSeq_succ hi]
  push_cast
  have := Nat.floor_le (a := (1 + lam) * (dgzSeq lam K i : ℝ)) (by positivity)
  linarith

/-- `a_i < a_{i+1}` (`λ ≥ 0`, `K ≥ 1`). -/
theorem dgzSeq_lt_succ (hlam : 0 ≤ lam) (hK : 1 ≤ K) (i : ℕ) :
    dgzSeq lam K i < dgzSeq lam K (i + 1) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · show 0 < K ^ 4
    positivity
  · have h := dgzSeq_succ_ge (K := K) (lam := lam) hi
    have h2 : (dgzSeq lam K i : ℝ) ≤ (1 + lam) * dgzSeq lam K i := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (dgzSeq lam K i)]
    rw [dgzSeq_succ hi]
    have h3 : dgzSeq lam K i ≤ ⌊(1 + lam) * (dgzSeq lam K i : ℝ)⌋₊ :=
      Nat.le_floor h2
    omega

theorem dgzSeq_strictMono (hlam : 0 ≤ lam) (hK : 1 ≤ K) : StrictMono (dgzSeq lam K) :=
  strictMono_nat_of_lt_succ (dgzSeq_lt_succ hlam hK)

theorem dgzSeq_monotone (hlam : 0 ≤ lam) (hK : 1 ≤ K) : Monotone (dgzSeq lam K) :=
  (dgzSeq_strictMono hlam hK).monotone

/-- `i ≤ a_i`. -/
theorem le_dgzSeq (hlam : 0 ≤ lam) (hK : 1 ≤ K) (i : ℕ) : i ≤ dgzSeq lam K i :=
  (dgzSeq_strictMono hlam hK).le_apply

/-- `K⁴ ≤ a_i` for `i ≥ 1`. -/
theorem pow_le_dgzSeq (hlam : 0 ≤ lam) (hK : 1 ≤ K) {i : ℕ} (hi : 1 ≤ i) :
    K ^ 4 ≤ dgzSeq lam K i :=
  (dgzSeq_monotone hlam hK hi : dgzSeq lam K 1 ≤ dgzSeq lam K i)

/-- `λ a_i ≤ a_{i+1} - a_i` (`i ≥ 1`). -/
theorem dgzSeq_gap (hlam : 0 ≤ lam) {i : ℕ} (hi : 1 ≤ i) :
    lam * (dgzSeq lam K i : ℝ) ≤ ((dgzSeq lam K (i + 1) - dgzSeq lam K i : ℕ) : ℝ) := by
  have h := dgzSeq_succ_ge (K := K) (lam := lam) hi
  have hle : dgzSeq lam K i ≤ dgzSeq lam K (i + 1) := by
    have : (dgzSeq lam K i : ℝ) ≤ dgzSeq lam K (i + 1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (dgzSeq lam K i)]
    exact_mod_cast this
  rw [Nat.cast_sub hle]
  linarith

/-- `(1+λ)^{i-1} K⁴ ≤ a_i` for `i ≥ 1` (so `i ≤ 1 + log(a_i/K⁴)/log(1+λ)`). -/
theorem one_add_pow_mul_le_dgzSeq (hlam : 0 ≤ lam) :
    ∀ i : ℕ, (1 + lam) ^ i * ((K : ℝ) ^ 4) ≤ dgzSeq lam K (i + 1)
  | 0 => by simp [dgzSeq_one]
  | i + 1 => by
      have ih := one_add_pow_mul_le_dgzSeq hlam i
      have h := dgzSeq_succ_ge (K := K) (lam := lam) (i := i + 1) (Nat.le_add_left 1 i)
      rw [pow_succ]
      nlinarith

end Seq

/-! ## The top level `m` -/

section Level

variable {lam : ℝ} {K n : ℕ}

theorem bddAbove_dgzLevelSet (hlam : 0 ≤ lam) (hK : 1 ≤ K) (n : ℕ) :
    BddAbove {i : ℕ | 1 ≤ i ∧ (dgzSeq lam K i : ℝ) ≤ (1 - lam) * n} := by
  refine ⟨n, fun i hi => ?_⟩
  have h1 : (i : ℝ) ≤ dgzSeq lam K i := by exact_mod_cast le_dgzSeq hlam hK i
  have h2 : (1 - lam) * (n : ℝ) ≤ n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact_mod_cast h1.trans (hi.2.trans h2)

/-- **The top level** (DGZ (5.5)): if `K⁴ ≤ (1-λ)n`, then `1 ≤ m`, `a_m ≤ (1-λ)n < a_{m+1}`. -/
theorem dgzLevel_spec (hlam : 0 ≤ lam) (hK : 1 ≤ K) (hn : ((K ^ 4 : ℕ) : ℝ) ≤ (1 - lam) * n) :
    1 ≤ dgzLevel lam K n ∧ (dgzSeq lam K (dgzLevel lam K n) : ℝ) ≤ (1 - lam) * n ∧
      (1 - lam) * n < dgzSeq lam K (dgzLevel lam K n + 1) := by
  have hbdd := bddAbove_dgzLevelSet hlam hK n (lam := lam)
  have hne : ({i : ℕ | 1 ≤ i ∧ (dgzSeq lam K i : ℝ) ≤ (1 - lam) * n}).Nonempty :=
    ⟨1, le_rfl, hn⟩
  have hmem := Nat.sSup_mem hne hbdd
  refine ⟨hmem.1, hmem.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 : dgzLevel lam K n + 1 ≤ dgzLevel lam K n :=
    le_csSup hbdd ⟨Nat.le_add_left 1 _, hcon⟩
  omega

/-- **`(1-2λ)n ≤ a_m`** (DGZ (5.6)) once `K⁴ ≤ (1-λ)n` and `2λ² n ≥ 1`. -/
theorem dgzLevel_lower (hlam : 0 ≤ lam) (hK : 1 ≤ K) (hn : ((K ^ 4 : ℕ) : ℝ) ≤ (1 - lam) * n)
    (hn' : 1 ≤ 2 * lam ^ 2 * n) :
    (1 - 2 * lam) * n ≤ dgzSeq lam K (dgzLevel lam K n) := by
  obtain ⟨hm1, -, hm⟩ := dgzLevel_spec hlam hK hn
  have h := dgzSeq_succ_le (K := K) hlam hm1
  nlinarith

end Level

/-! ## Scales -/

namespace NiceParams

variable (p : NiceParams)

/-- `s_{i+1} = 2^{a_{i+1} - a_i} s_i` (`a_i ≤ a_{i+1} ≤ n`). -/
theorem s_succ_eq {i : ℕ} (h₁ : p.a i ≤ p.a (i + 1)) (h₂ : p.a (i + 1) ≤ p.n) :
    p.s (i + 1) = 2 ^ (p.a (i + 1) - p.a i) * p.s i := by
  unfold NiceParams.s
  have e : p.n - p.a i = (p.n - p.a (i + 1)) + (p.a (i + 1) - p.a i) := by omega
  rw [e, pow_add, ← mul_assoc, mul_comm ((2 : ℝ) ^ _), mul_assoc, ← mul_pow,
    mul_inv_cancel₀ two_ne_zero, one_pow, mul_one]

/-- `s_i = 2^{-n+a_i}` as a real power (`a_i ≤ n`). -/
theorem s_eq_rpow {i : ℕ} (h : p.a i ≤ p.n) : p.s i = (2 : ℝ) ^ (-(p.n : ℝ) + p.a i) := by
  unfold NiceParams.s
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg two_pos.le, Nat.cast_sub h]
  congr 1
  ring

/-- `2/s_i = 2^{n-a_i+1} ∈ ℤ`. -/
theorem s_mul_two_pow (i : ℕ) : p.s i * ((2 ^ (p.n - p.a i + 1) : ℕ) : ℝ) = 2 := by
  unfold NiceParams.s
  push_cast
  rw [pow_succ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, one_mul]

/-- `𝒴_{i+1} ⊆ 𝒴_i`: `s_{i+1} t = s_i (2^{a_{i+1}-a_i} t)` (`a_i ≤ a_{i+1} ≤ n`). -/
theorem latPt_succ_eq {i : ℕ} (h₁ : p.a i ≤ p.a (i + 1)) (h₂ : p.a (i + 1) ≤ p.n) (t : Zd d) :
    latPt (p.s (i + 1)) t = latPt (p.s i) ((2 : ℤ) ^ (p.a (i + 1) - p.a i) • t) := by
  ext k
  rw [latPt_apply, latPt_apply, p.s_succ_eq h₁ h₂]
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  ring

end NiceParams

/-- **Scale separation for DGZ's sequence** (blueprint Convention `r2:conv:coarse`):
`2^{λK⁴} s_i ≤ s_{i+1}` for `1 ≤ i` and `a_{i+1} ≤ n` (`λ ≥ 0`, `K ≥ 1`). -/
theorem dgz_rpow_mul_s_le (p : NiceParams) {lam : ℝ} (hlam : 0 ≤ lam) (hK : 1 ≤ p.K)
    (ha : p.a = dgzSeq lam p.K) {i : ℕ} (hi : 1 ≤ i) (hn : p.a (i + 1) ≤ p.n) :
    (2 : ℝ) ^ (lam * ((p.K : ℝ) ^ 4)) * p.s i ≤ p.s (i + 1) := by
  have hmono : p.a i ≤ p.a (i + 1) := by
    rw [ha]
    exact dgzSeq_monotone hlam hK (Nat.le_succ i)
  rw [p.s_succ_eq hmono hn]
  refine mul_le_mul_of_nonneg_right ?_ (p.s_pos i).le
  rw [← Real.rpow_natCast 2 (p.a (i + 1) - p.a i)]
  refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
  have h1 := dgzSeq_gap (K := p.K) hlam hi
  have h2 : ((p.K ^ 4 : ℕ) : ℝ) ≤ dgzSeq lam p.K i := by
    exact_mod_cast pow_le_dgzSeq hlam hK hi
  rw [ha]
  push_cast at h2 ⊢
  nlinarith

/-- **The gap conditions of the locality and independence lemmas for DGZ's sequence**: if
`c ≤ 2^{λK⁴}` and `a_j ≤ n`, then `c s_{i-1} ≤ s_i` for `2 ≤ i ≤ j`. -/
theorem dgz_gap_of_le (p : NiceParams) {lam : ℝ} (hlam : 0 ≤ lam) (hK : 1 ≤ p.K)
    (ha : p.a = dgzSeq lam p.K) {c : ℝ} (hc : c ≤ (2 : ℝ) ^ (lam * ((p.K : ℝ) ^ 4))) {j : ℕ}
    (hjn : p.a j ≤ p.n) : ∀ i, 2 ≤ i → i ≤ j → c * p.s (i - 1) ≤ p.s i := by
  intro i hi hij
  have hmono : Monotone p.a := by rw [ha]; exact dgzSeq_monotone hlam hK
  have hin : p.a (i - 1 + 1) ≤ p.n := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]
    exact (hmono hij).trans hjn
  have h := dgz_rpow_mul_s_le p hlam hK ha (i := i - 1) (by omega) hin
  rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at h
  exact (mul_le_mul_of_nonneg_right hc (p.s_pos _).le).trans h

/-- `2L + 2 ≤ 2^L` for `L ≥ 3`. -/
theorem two_mul_add_two_le_two_pow {L : ℕ} (hL : 3 ≤ L) : 2 * L + 2 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    omega

/-- `m(N) = 2⌊log₂ N⌋ + 2 ≤ N` for `N ≥ 8` (the split index of the certificate is `≤ n`; DGZ's
`a_{j-1} ≥ K⁴ ≥ 8`). -/
theorem superScale_le_self {N : ℕ} (hN : 8 ≤ N) : superScale N ≤ N := by
  unfold superScale
  have h1 : 3 ≤ Nat.log 2 N := by
    have : Nat.log 2 8 ≤ Nat.log 2 N := Nat.log_mono_right hN
    have h8 : Nat.log 2 8 = 3 := by decide
    omega
  have h2 := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have h3 := two_mul_add_two_le_two_pow h1
  omega

end DGZ

end HigherDimLQGMetric
