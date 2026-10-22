import HigherDimLQGMetric.DGZ.TightBasics

/-!
# DGZ Lemma 6.1: the self-internal Hölder bound (packet L5a)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 6.1 (TeX l. 2840–2875, p. 56);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-6.1–6.3; blueprint Part C,
Lemma `r2:lem:61` (authoritative: self-internal form on `B_ρ(0)`, `ρ ∈ [1, 3/2]`, and `β < 1` from
`xi_mul_sub_sqrt_le_one`).

**Statement (`holder_selfInternal`).** Assume `Cor52Shape d κ ξ Q` (DGZ Cor 5.2, proved by packet
L4c) and `DGZHyp d κ ξ Q`. For every `β ∈ (0, ξ(Q - √(2d)))` there is `q₀ < 1` such that for every
`q ∈ [q₀, 1)` and `θ > 0` there is `M > 0` with, for every dyadic realization, every `ρ ∈ [1, 3/2]`
and every `n`,
`P[∃ x, y ∈ B_ρ(0) : D_n(x, y; B_ρ(0)) > M a^{(q)}_n ‖x - y‖^β] ≤ θ`.
(The Euclidean norm is used; since `|x - y|_∞ ≤ ‖x - y‖ ≤ √d |x - y|_∞`, this is equivalent to the
`ℓ^∞` form of [2] up to the factor `d^{β/2}` in `M`.)

**Proof** (MA7 D-6.1). Put `g := ξ(Q - √(2d))`, `η := (β + g)/2`, `ε' := (g - β)/4`, so
`β + ε' < η < g`. Let `c₄ < 1` be the threshold of `prob_eventA_compl_le` (L3c2) for `η`, choose
`c₄ < q_A < q₀ < 1` and `q ∈ [q₀, 1)`. On `𝒜_{r,n}` (`110 ≤ r < n`), `chain_selfInternal` (L3c2) and
`Cor52Shape` (`a^{(q_A)}_{n-k} ≤ C₅ 2^{(1-ξQ+ε')k} a^{(q)}_n`), together with
`a^{(q)}_n ≥ c 2^{-(1-ξQ+ε')n}` (L3c2's `exists_le_aQ`), give
`chainSum j n ≤ max(C₅, 1/c) S a^{(q)}_n 2^{-βj}` with `S = Σ_k k^{2d} 2^{-(η-ε'-β)k}`
(`chainSum_le_aQ_holder`). Then, for `x, y ∈ B_ρ(0)` and `s = ‖x - y‖`:
* `s ≤ 2^{-n}`: the segment on `𝒢_n` gives `D ≤ √d s 2^{(ξQ-η)n} ≤ (√d/c) a s^β`, because
  `s^{1-β} ≤ 2^{-(1-β)n}` (here `β ≤ 1` is used) and `η - β ≥ ε'`;
* `2^{-n} < s ≤ 2^{-r}`: with `k` the largest `j ≤ n` with `s ≤ 2^{-j}`, chaining (i) at scale
  `k` gives `D ≤ C₀ chainSum k n ≤ B a 2^{-βk} ≤ B 2^β a s^β`;
* `s > 2^{-r}`: chaining (ii) gives `D ≤ selfDiam ≤ C₀ 2^r chainSum r n ≤ B 2^r 2^{βr} a s^β`.
`P[𝒜_{r,n}ᶜ] ≤ C e^{-r/C} ≤ θ` for `r` large. For the finitely many `n ≤ r`,
`D_n(x, y; B_ρ(0)) ≤ e^{ξ sup_{B̄₃} |h_n|} ‖x - y‖ ≤ e^{ξ L_n} (1 + 3√d) ‖x - y‖^β` and
`P[sup_{B̄₃} |h_n| > L_n] ≤ θ` (`exists_sup_tail_level_tight`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-! ### Real-analysis lemmas -/

/-- `t ^ α ≤ 1 + t` for `t ≥ 0` and `0 ≤ α ≤ 1`. -/
lemma th_rpow_le_one_add {t α : ℝ} (ht : 0 ≤ t) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    t ^ α ≤ 1 + t := by
  rcases le_or_gt t 1 with h1 | h1
  · have := Real.rpow_le_one ht h1 hα0
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h1.le hα1
    rw [Real.rpow_one] at this
    linarith

/-- `((2⁻¹)^j)^β = (2^{-β})^j`. -/
lemma th_inv_two_pow_rpow (j : ℕ) (β : ℝ) :
    ((2 : ℝ)⁻¹ ^ j) ^ β = ((2 : ℝ) ^ (-β)) ^ j := by
  rw [← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2⁻¹), Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

/-- **The short-distance segment estimate**: for `0 < s ≤ 2^{-n}`, `β ≤ 1` and `β + ε ≤ η`,
`s 2^n 2^{-(1-ξQ+η)n} ≤ s^β 2^{-(1-ξQ+ε)n}`. -/
lemma th_seg_bound {s β ε η ξ Q : ℝ} {n : ℕ} (hs0 : 0 < s) (hs : s ≤ (2 : ℝ)⁻¹ ^ n)
    (hβ1 : β ≤ 1) (hβη : β + ε ≤ η) :
    s * (2 : ℝ) ^ n * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) ≤
      s ^ β * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * n) := by
  have hsplit : s = s ^ β * s ^ (1 - β) := by
    rw [← Real.rpow_add hs0, add_sub_cancel, Real.rpow_one]
  have hle : s ^ (1 - β) ≤ ((2 : ℝ)⁻¹ ^ n) ^ (1 - β) :=
    Real.rpow_le_rpow hs0.le hs (by linarith)
  have e1 : ((2 : ℝ)⁻¹ ^ n) ^ (1 - β) = (2 : ℝ) ^ (-(1 - β) * n) := by
    rw [inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  have e2 : (2 : ℝ) ^ n = (2 : ℝ) ^ ((n : ℝ)) := (Real.rpow_natCast 2 n).symm
  have hsβ : 0 ≤ s ^ β := Real.rpow_nonneg hs0.le β
  calc s * (2 : ℝ) ^ n * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)
      = s ^ β * s ^ (1 - β) * ((2 : ℝ) ^ n * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)) := by
        rw [← hsplit]; ring
    _ ≤ s ^ β * (2 : ℝ) ^ (-(1 - β) * n) * ((2 : ℝ) ^ n * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)) := by
        rw [← e1]
        gcongr
    _ = s ^ β * (2 : ℝ) ^ (-(1 - ξ * Q + η - β) * n) := by
        rw [e2, mul_assoc, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
        congr 2
        ring
    _ ≤ s ^ β * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * n) := by
        gcongr
        · norm_num
        · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith

/-! ### The chain sum against the quantile `a^{(q)}_n` -/

section ChainSum

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℕ → Rd d → Ω → ℝ}

/-- The summability constant `S = Σ_k k^{2d} y^k`, `y = 2^{-(η - ε' - β)}`. -/
def holderSumConst (d : ℕ) (γ : ℝ) : ℝ := ∑' k : ℕ, (k : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-γ)) ^ k

lemma summable_holderSum (d : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    Summable fun k : ℕ => (k : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-γ)) ^ k := by
  refine summable_pow_mul_geometric_of_norm_lt_one (2 * d) ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos two_pos _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)

lemma holderSumConst_nonneg (d : ℕ) (γ : ℝ) : 0 ≤ holderSumConst d γ :=
  tsum_nonneg fun k => mul_nonneg (pow_nonneg (Nat.cast_nonneg k) _)
    (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)

/-- **The chain sum against `a^{(q')}_n`** (D-6.1): if `a^{(q)}_{n-k} ≤ C₅ 2^{(1-ξQ+ε')k} a` for
`k < n` and `c 2^{-(1-ξQ+ε')n} ≤ a`, then
`chainSum j n ≤ max(C₅, 1/c) a S 2^{-βj}` for `j ≤ n`, where `S = Σ_k k^{2d} 2^{-(η-ε'-β)k}`. -/
theorem chainSum_le_aQ_holder {ξ Q η ε' β : ℝ} {q : ℝ≥0∞} {n : ℕ} {a C₅ c : ℝ} (hc : 0 < c)
    (hC₅ : 0 ≤ C₅) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hβη : β + ε' < η)
    (hcomp : ∀ k, k < n → aQ P H ξ (n - k) q ≤ C₅ * (2 : ℝ) ^ ((1 - ξ * Q + ε') * k) * a)
    (hlow : c * (2 : ℝ) ^ (-(1 - ξ * Q + ε') * n) ≤ a) {j : ℕ} (hjn : j ≤ n) :
    chainSum P H ξ Q η q j n ≤
      max C₅ c⁻¹ * a * holderSumConst d (η - ε' - β) * ((2 : ℝ) ^ (-β)) ^ j := by
  set C₆ := max C₅ c⁻¹ with hC₆
  have hC₆0 : 0 ≤ C₆ := le_trans hC₅ (le_max_left _ _)
  set y₁ : ℝ := (2 : ℝ) ^ (-(η - ε' - β)) with hy₁
  set y₂ : ℝ := (2 : ℝ) ^ (-β) with hy₂
  have hy₂0 : 0 ≤ y₂ := Real.rpow_nonneg (by norm_num) _
  have hy₂1 : y₂ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  set f : ℕ → ℝ := fun k => (k : ℝ) ^ (2 * d) * y₁ ^ k with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k =>
    mul_nonneg (pow_nonneg (Nat.cast_nonneg k) _) (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
  -- the factorization `2^{-(η-ε')k} = y₁^k y₂^k`
  have hfac : ∀ k : ℕ, (2 : ℝ) ^ (-(η - ε') * k) = y₁ ^ k * y₂ ^ k := by
    intro k
    rw [← mul_pow, hy₁, hy₂, ← Real.rpow_add two_pos, ← tb_two_rpow_mul_nat]
    congr 1
    ring
  -- each term of the chain sum
  have hterm : ∀ k : ℕ, k < n →
      (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * aQ P H ξ (n - k) q ≤
        C₆ * a * (f k * y₂ ^ k) := by
    intro k hk
    have h1 := hcomp k hk
    have hp : 0 ≤ (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) :=
      mul_nonneg (pow_nonneg (Nat.cast_nonneg k) _) (Real.rpow_nonneg (by norm_num) _)
    calc (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * aQ P H ξ (n - k) q
        ≤ (k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) *
            (C₅ * (2 : ℝ) ^ ((1 - ξ * Q + ε') * k) * a) := mul_le_mul_of_nonneg_left h1 hp
      _ = C₅ * a * ((k : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(η - ε') * k)) := by
          have : (2 : ℝ) ^ (-(1 - ξ * Q + η) * k) * (2 : ℝ) ^ ((1 - ξ * Q + ε') * k) =
              (2 : ℝ) ^ (-(η - ε') * k) := by
            rw [← Real.rpow_add two_pos]; congr 1; ring
          calc _ = C₅ * a * ((k : ℝ) ^ (2 * d) * ((2 : ℝ) ^ (-(1 - ξ * Q + η) * k) *
                (2 : ℝ) ^ ((1 - ξ * Q + ε') * k))) := by ring
            _ = _ := by rw [this]
      _ = C₅ * a * (f k * y₂ ^ k) := by rw [hfac, hf]; ring
      _ ≤ C₆ * a * (f k * y₂ ^ k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
            (mul_nonneg (hf0 k) (pow_nonneg hy₂0 _))
  -- the last term
  have hlast : (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) ≤ C₆ * a * (f n * y₂ ^ n) := by
    have e : (2 : ℝ) ^ (-(1 - ξ * Q + η) * n) =
        (2 : ℝ) ^ (-(η - ε') * n) * (2 : ℝ) ^ (-(1 - ξ * Q + ε') * n) := by
      rw [← Real.rpow_add two_pos]; congr 1; ring
    have h2 : (2 : ℝ) ^ (-(1 - ξ * Q + ε') * n) ≤ c⁻¹ * a := by
      rw [le_inv_mul_iff₀ hc]; exact hlow
    have hp : 0 ≤ (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(η - ε') * n) :=
      mul_nonneg (pow_nonneg (Nat.cast_nonneg n) _) (Real.rpow_nonneg (by norm_num) _)
    calc (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)
        = (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(η - ε') * n) * (2 : ℝ) ^ (-(1 - ξ * Q + ε') * n) := by
          rw [e]; ring
      _ ≤ (n : ℝ) ^ (2 * d) * (2 : ℝ) ^ (-(η - ε') * n) * (c⁻¹ * a) :=
          mul_le_mul_of_nonneg_left h2 hp
      _ = c⁻¹ * a * (f n * y₂ ^ n) := by rw [hfac, hf]; ring
      _ ≤ C₆ * a * (f n * y₂ ^ n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) ha)
            (mul_nonneg (hf0 n) (pow_nonneg hy₂0 _))
  -- sum up
  have hsum : chainSum P H ξ Q η q j n ≤
      C₆ * a * ∑ k ∈ Finset.Ico j (n + 1), f k * y₂ ^ k := by
    unfold chainSum
    rw [Finset.sum_Ico_succ_top hjn, mul_add, Finset.mul_sum]
    exact add_le_add (Finset.sum_le_sum fun k hk => hterm k (Finset.mem_Ico.1 hk).2) hlast
  have hγ : 0 < η - ε' - β := by linarith
  have hsum2 : ∑ k ∈ Finset.Ico j (n + 1), f k * y₂ ^ k ≤
      holderSumConst d (η - ε' - β) * y₂ ^ j := by
    calc ∑ k ∈ Finset.Ico j (n + 1), f k * y₂ ^ k ≤ ∑ k ∈ Finset.Ico j (n + 1), f k * y₂ ^ j :=
          Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hy₂0 hy₂1 (Finset.mem_Ico.1 hk).1) (hf0 k)
      _ = (∑ k ∈ Finset.Ico j (n + 1), f k) * y₂ ^ j := by rw [Finset.sum_mul]
      _ ≤ holderSumConst d (η - ε' - β) * y₂ ^ j := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hy₂0 _)
          exact (summable_holderSum d hγ).sum_le_tsum _ fun k _ => hf0 k
  calc chainSum P H ξ Q η q j n ≤ C₆ * a * ∑ k ∈ Finset.Ico j (n + 1), f k * y₂ ^ k := hsum
    _ ≤ C₆ * a * (holderSumConst d (η - ε' - β) * y₂ ^ j) :=
        mul_le_mul_of_nonneg_left hsum2 (mul_nonneg hC₆0 ha)
    _ = _ := by ring

end ChainSum

/-! ### The deterministic core on `𝒜_{r,n}` -/

/-- `y₂^k ≤ 2^β s^β` when `s > 2^{-(k+1)}` (`y₂ = 2^{-β}`). -/
lemma th_pow_le_of_lt {β s : ℝ} (hβ : 0 < β) {k : ℕ} (hs : (2 : ℝ)⁻¹ ^ (k + 1) < s) :
    ((2 : ℝ) ^ (-β)) ^ k ≤ (2 : ℝ) ^ β * s ^ β := by
  have h1 : ((2 : ℝ) ^ (-β)) ^ (k + 1) ≤ s ^ β := by
    rw [← th_inv_two_pow_rpow]
    exact Real.rpow_le_rpow (by positivity) hs.le hβ.le
  have h2 : ((2 : ℝ) ^ (-β)) ^ (k + 1) = (2 : ℝ) ^ (-β) * ((2 : ℝ) ^ (-β)) ^ k := by
    rw [pow_succ]; ring
  have h3 : (2 : ℝ) ^ β * (2 : ℝ) ^ (-β) = 1 := by
    rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
  have h4 : 0 < (2 : ℝ) ^ β := Real.rpow_pos_of_pos two_pos β
  calc ((2 : ℝ) ^ (-β)) ^ k = (2 : ℝ) ^ β * ((2 : ℝ) ^ (-β) * ((2 : ℝ) ^ (-β)) ^ k) := by
        rw [← mul_assoc, h3, one_mul]
    _ ≤ (2 : ℝ) ^ β * s ^ β := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 h4.le

/-- **Lemma 6.1, deterministic part** (D-6.1): suppose the chain sums `cs j` satisfy
`cs j ≤ K a 2^{-βj}` (`j ≤ n`), the chaining bounds (i), (ii) of `chain_selfInternal` hold with
constant `C₀`, the field satisfies `𝒢_n`, and `a ≥ c 2^{-(1-ξQ+ε)n}`. Then
`D(x, y; B_ρ(0)) ≤ (C₀ K (2^β + 2^r) + √d/c) a ‖x - y‖^β` for all `x, y ∈ B_ρ(0)`. -/
theorem holder_det {φ : Rd d → ℝ} (hφ : Continuous φ) {ξ Q η ε β ρ a c K C₀ : ℝ} {r n : ℕ}
    (hξ : 0 < ξ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hβη : β + ε ≤ η) (hc : 0 < c) (hK : 0 ≤ K)
    (hC₀ : 0 ≤ C₀) (hρ2 : ρ ≤ 3 / 2) (hrn : r ≤ n)
    (ha : c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * n) ≤ a) (cs : ℕ → ℝ)
    (hcs : ∀ j, j ≤ n → cs j ≤ K * a * ((2 : ℝ) ^ (-β)) ^ j)
    (hI : ∀ j : ℕ, r ≤ j → j ≤ n → ∀ x ∈ obox (0 : Rd d) ρ, ∀ y ∈ obox (0 : Rd d) ρ,
      (∀ i, |x i - y i| ≤ (2 : ℝ)⁻¹ ^ j) → lfppDistOn ξ φ (obox (0 : Rd d) ρ) x y ≤ C₀ * cs j)
    (hII : selfDiam ξ φ 0 ρ ≤ C₀ * 2 ^ r * cs r)
    (hG : ∀ z ∈ cbox (0 : Rd d) 3, φ z ≤ n * (Q - η / ξ) * Real.log 2) :
    ∀ x ∈ obox (0 : Rd d) ρ, ∀ y ∈ obox (0 : Rd d) ρ,
      lfppDistOn ξ φ (obox (0 : Rd d) ρ) x y ≤
        (C₀ * K * ((2 : ℝ) ^ β + 2 ^ r) + Real.sqrt d / c) * a * ‖x - y‖ ^ β := by
  intro x hx y hy
  have ha0 : 0 < a := lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos two_pos _)) ha
  set s := ‖x - y‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  have hsβ : 0 ≤ s ^ β := Real.rpow_nonneg hs0 β
  have h2β : 0 < (2 : ℝ) ^ β := Real.rpow_pos_of_pos two_pos β
  have hA : 0 ≤ C₀ * K * ((2 : ℝ) ^ β + 2 ^ r) := by positivity
  have hB : 0 ≤ Real.sqrt d / c := div_nonneg (Real.sqrt_nonneg _) hc.le
  have hcoord : ∀ i, |x i - y i| ≤ s := fun i => by
    have := HigherDimLFPP.DGZ.abs_apply_le_norm (x - y) i
    rwa [PiLp.sub_apply] at this
  -- the three regimes
  rcases eq_or_lt_of_le hs0 with hs00 | hspos
  · -- `x = y`
    have hxy : x = y := by rw [← sub_eq_zero, ← norm_eq_zero]; exact hs00.symm
    rw [hxy, lfppDistOn_self]
    positivity
  by_cases h1 : s ≤ (2 : ℝ)⁻¹ ^ n
  · -- the segment on `𝒢_n`
    have hseg := lfppDistOn_le_segment hφ hξ (by linarith) hG hx hy (L := s * 2 ^ n)
      (fun i => by
        rw [abs_sub_comm, mul_assoc, ← mul_pow, mul_inv_cancel₀ (two_ne_zero), one_pow, mul_one]
        exact hcoord i)
    have hsb := th_seg_bound (ξ := ξ) (Q := Q) hspos h1 hβ1 hβη
    have hca : (2 : ℝ) ^ (-(1 - ξ * Q + ε) * n) ≤ a / c := by
      rw [le_div_iff₀ hc, mul_comm]; exact ha
    calc lfppDistOn ξ φ (obox (0 : Rd d) ρ) x y
        ≤ Real.sqrt d * (s * 2 ^ n * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)) := by
          calc _ ≤ _ := hseg
            _ = _ := by ring
      _ ≤ Real.sqrt d * (s ^ β * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * n)) :=
          mul_le_mul_of_nonneg_left hsb (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt d * (s ^ β * (a / c)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hca hsβ) (Real.sqrt_nonneg _)
      _ = Real.sqrt d / c * a * s ^ β := by ring
      _ ≤ (C₀ * K * ((2 : ℝ) ^ β + 2 ^ r) + Real.sqrt d / c) * a * s ^ β := by
          gcongr
          linarith
  push Not at h1
  by_cases h2 : s ≤ (2 : ℝ)⁻¹ ^ r
  · -- intermediate scales: chaining (i) at the largest admissible scale
    classical
    set k := Nat.findGreatest (fun j => s ≤ (2 : ℝ)⁻¹ ^ j) n with hk
    have hk_ge : r ≤ k := Nat.le_findGreatest hrn h2
    have hk_le : k ≤ n := Nat.findGreatest_le n
    have hk_spec : s ≤ (2 : ℝ)⁻¹ ^ k := Nat.findGreatest_spec (P := fun j => s ≤ (2 : ℝ)⁻¹ ^ j)
      hrn h2
    have hk_lt : k < n := by
      rcases lt_or_eq_of_le hk_le with h | h
      · exact h
      · exact absurd (h ▸ hk_spec) (not_le.2 h1)
    have hk_next : (2 : ℝ)⁻¹ ^ (k + 1) < s := by
      have := Nat.findGreatest_is_greatest (P := fun j => s ≤ (2 : ℝ)⁻¹ ^ j)
        (Nat.lt_succ_self k) hk_lt
      exact not_le.1 this
    have hD := hI k hk_ge hk_le x hx y hy fun i => (hcoord i).trans hk_spec
    have hcsk := hcs k hk_le
    have hpk := th_pow_le_of_lt hβ0 hk_next
    calc lfppDistOn ξ φ (obox (0 : Rd d) ρ) x y ≤ C₀ * cs k := hD
      _ ≤ C₀ * (K * a * ((2 : ℝ) ^ (-β)) ^ k) := mul_le_mul_of_nonneg_left hcsk hC₀
      _ ≤ C₀ * (K * a * ((2 : ℝ) ^ β * s ^ β)) := by gcongr
      _ = C₀ * K * (2 : ℝ) ^ β * a * s ^ β := by ring
      _ ≤ (C₀ * K * ((2 : ℝ) ^ β + 2 ^ r) + Real.sqrt d / c) * a * s ^ β := by
          gcongr
          have : C₀ * K * (2 : ℝ) ^ β ≤ C₀ * K * ((2 : ℝ) ^ β + 2 ^ r) := by
            gcongr; linarith [pow_pos (two_pos : (0 : ℝ) < 2) r]
          linarith
  · -- large distances: chaining (ii)
    push Not at h2
    have hD := lfppDistOn_le_selfDiam (ξ := ξ) hφ hx hy
    have hcsr := hcs r hrn
    have hpr : ((2 : ℝ) ^ (-β)) ^ r ≤ s ^ β := by
      rw [← th_inv_two_pow_rpow]
      exact Real.rpow_le_rpow (by positivity) h2.le hβ0.le
    calc lfppDistOn ξ φ (obox (0 : Rd d) ρ) x y ≤ C₀ * 2 ^ r * cs r := hD.trans hII
      _ ≤ C₀ * 2 ^ r * (K * a * ((2 : ℝ) ^ (-β)) ^ r) :=
          mul_le_mul_of_nonneg_left hcsr (by positivity)
      _ ≤ C₀ * 2 ^ r * (K * a * s ^ β) := by gcongr
      _ = C₀ * K * 2 ^ r * a * s ^ β := by ring
      _ ≤ (C₀ * K * ((2 : ℝ) ^ β + 2 ^ r) + Real.sqrt d / c) * a * s ^ β := by
          gcongr
          have : C₀ * K * 2 ^ r ≤ C₀ * K * ((2 : ℝ) ^ β + 2 ^ r) := by
            gcongr; linarith
          linarith

/-- `t ≤ t^β (1 + T)` for `0 ≤ t ≤ T` and `0 < β ≤ 1`. -/
lemma th_le_rpow_mul {t T β : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    t ≤ t ^ β * (1 + T) := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0, Real.zero_rpow hβ0.ne', zero_mul]
  · have hsplit : t = t ^ β * t ^ (1 - β) := by
      rw [← Real.rpow_add hpos, add_sub_cancel, Real.rpow_one]
    have h1 : t ^ (1 - β) ≤ 1 + t := th_rpow_le_one_add ht (by linarith) (by linarith)
    calc t = t ^ β * t ^ (1 - β) := hsplit
      _ ≤ t ^ β * (1 + T) :=
          mul_le_mul_of_nonneg_left (h1.trans (by linarith)) (Real.rpow_nonneg ht β)

/-! ### DGZ Lemma 6.1 -/

/-- **DGZ Lemma 6.1** (self-internal Hölder bound; blueprint `r2:lem:61`, MA7 D-6.1). Given
`Cor52Shape d κ ξ Q` (DGZ Cor 5.2) and `DGZHyp d κ ξ Q`: for every `β ∈ (0, ξ(Q - √(2d)))` there is
`q₀ ∈ (0, 1)` such that for every `q ∈ [q₀, 1)` and `θ > 0` there is `M > 0` with
`P[∃ x, y ∈ B_ρ(0) : D_n(x, y; B_ρ(0)) > M a^{(q)}_n ‖x - y‖^β] ≤ θ` for every dyadic realization,
every `ρ ∈ [1, 3/2]` and every `n`. -/
theorem holder_selfInternal {κ : Rd d → ℝ} {ξ Q : ℝ} (hC52 : Cor52Shape d κ ξ Q)
    (h : DGZHyp d κ ξ Q) {β : ℝ} (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d))) :
    ∃ q₀ : ℝ≥0∞, 0 < q₀ ∧ q₀ < 1 ∧ ∀ q : ℝ≥0∞, q₀ ≤ q → q < 1 → ∀ θ : ℝ, 0 < θ →
      ∃ M : ℝ, 0 < M ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ ρ : ℝ, 1 ≤ ρ → ρ ≤ 3 / 2 →
          ∀ n : ℕ, P {ω | ∃ x ∈ obox (0 : Rd d) ρ, ∃ y ∈ obox (0 : Rd d) ρ,
            M * aQ P H ξ n q * ‖x - y‖ ^ β <
              lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) ρ) x y} ≤ ENNReal.ofReal θ := by
  have hd := h.dim
  have hξ := h.xi_pos
  have hκ := h.kernel
  have hg1 : ξ * (Q - Real.sqrt (2 * d)) ≤ 1 := xi_mul_sub_sqrt_le_one h
  set g := ξ * (Q - Real.sqrt (2 * d)) with hg
  have hβ1 : β ≤ 1 := by linarith
  set η := (β + g) / 2 with hη
  set ε' := (g - β) / 4 with hε'
  have hηg : η < ξ * (Q - Real.sqrt (2 * d)) := by rw [hη]; linarith
  have hβη : β + ε' < η := by rw [hη, hε']; linarith
  have hε'0 : 0 < ε' := by rw [hε']; linarith
  obtain ⟨c₄, hc₄, CA, hCA, hA⟩ := prob_eventA_compl_le hd hκ hξ hηg
  obtain ⟨qA, hc₄qA, hqA1⟩ := exists_between hc₄
  obtain ⟨q₀, hqAq₀, hq₀1⟩ := exists_between hqA1
  obtain ⟨C₀, hC₀, hchain⟩ := chain_selfInternal.{0} hd
  have hqA0 : 0 < qA := lt_of_le_of_lt zero_le hc₄qA
  refine ⟨q₀, hqA0.trans hqAq₀, hq₀1, fun q hq₀q hq1 θ hθ => ?_⟩
  have hqAq : qA < q := lt_of_lt_of_le hqAq₀ hq₀q
  have hq0 : 0 < q := lt_trans hqA0 hqAq
  obtain ⟨C₅, hC₅, hcor⟩ := hC52 h ε' hε'0 qA q hqA0 hqAq hq1
  obtain ⟨c, hc, hlow⟩ := exists_le_aQ h hq0 hq1 hε'0
  -- the scale `r` of the event `𝒜_{r,n}`
  obtain ⟨k₀, hk₀⟩ := exists_mul_exp_neg_div_le hCA hθ
  set r := max 110 k₀ with hr
  have hr110 : 110 ≤ r := le_max_left _ _
  -- the finitely many small levels
  have hL : ∀ n : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WN d → Ω → ℝ}, IsWhiteNoise P W → ∀ {X : Rd d → Ω → ℝ},
        IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) 1 X → ∀ c : Rd d,
          P {ω | ∃ z ∈ cbox c 3, L < |X z ω|} ≤ ENNReal.ofReal θ := fun n =>
    exists_sup_tail_level_tight hκ n (by norm_num) hθ
  choose L hL0 hLt using hL
  set Msmall : ℝ := ∑ n ∈ Finset.range (r + 1),
    Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) * (2 : ℝ) ^ ((1 - ξ * Q + ε') * n) / c
    with hMsmall
  have hMsmall0 : 0 ≤ Msmall := Finset.sum_nonneg fun n _ => by positivity
  set K := max C₅ c⁻¹ * holderSumConst d (η - ε' - β) with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (le_trans hC₅.le (le_max_left _ _)) (holderSumConst_nonneg d _)
  set Mlarge := C₀ * K * ((2 : ℝ) ^ β + 2 ^ r) + Real.sqrt d / c with hMlarge
  have hMlarge0 : 0 ≤ Mlarge := by positivity
  refine ⟨Mlarge + Msmall + 1, by positivity, fun Ω _ P W H hH ρ hρ1 hρ2 n => ?_⟩
  have ha := hlow Ω P W H hH n
  set a := aQ P H ξ n q with ha_def
  have ha0 : 0 < a := lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos two_pos _)) ha
  by_cases hnr : n ≤ r
  · -- small `n`: `D_n ≤ e^{ξ L_n} ‖x - y‖`
    refine (measure_mono ?_).trans (hLt n hH.whiteNoise (hH.band n) 0)
    intro ω hω
    by_contra hgood
    simp only [mem_ofPred_eq, not_exists, not_and, not_lt] at hgood hω
    obtain ⟨x, hx, y, hy, hlt⟩ := hω
    have hM : ∀ z ∈ obox (0 : Rd d) ρ, ξ * H n z ω ≤ ξ * L n := fun z hz => by
      have hz3 : z ∈ cbox (0 : Rd d) 3 := fun i => by
        have := hz i
        simp only [PiLp.zero_apply, sub_zero] at this ⊢
        linarith
      have h1 := hgood z hz3
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) hξ.le
    have hD := lfppDistOn_le_exp_mul_norm_of_convex ((hH.band n).continuous ω)
      (HigherDimLFPP.DGZ.convex_obox 0 ρ) hx hy hM
    rw [norm_sub_rev] at hD
    have hxy3 : ‖x - y‖ ≤ 3 * Real.sqrt d := by
      have := norm_sub_le_of_forall_abs_le (x := x) (y := y) (s := 3) fun i => by
        have h1 := hx i
        have h2 := hy i
        simp only [PiLp.zero_apply, sub_zero] at h1 h2
        rw [abs_lt] at h1 h2
        rw [abs_le]; constructor <;> linarith
      linarith
    have hnorm := th_le_rpow_mul (norm_nonneg (x - y)) hxy3 hβ0 hβ1
    have hterm : Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) ≤ Msmall * a := by
      have hsingle : Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) *
          (2 : ℝ) ^ ((1 - ξ * Q + ε') * n) / c ≤ Msmall :=
        Finset.single_le_sum (f := fun n => Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) *
          (2 : ℝ) ^ ((1 - ξ * Q + ε') * n) / c) (fun n _ => by positivity)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hnr))
      have e : (2 : ℝ) ^ ((1 - ξ * Q + ε') * n) * (2 : ℝ) ^ (-(1 - ξ * Q + ε') * n) = 1 := by
        rw [← Real.rpow_add two_pos,
          show (1 - ξ * Q + ε') * (n : ℝ) + -(1 - ξ * Q + ε') * n = 0 by ring, Real.rpow_zero]
      calc Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d)
          = Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) * ((2 : ℝ) ^ ((1 - ξ * Q + ε') * n) *
              (2 : ℝ) ^ (-(1 - ξ * Q + ε') * n)) * (c / c) := by
            rw [e, div_self hc.ne']; ring
        _ = Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) * (2 : ℝ) ^ ((1 - ξ * Q + ε') * n) / c *
              (c * (2 : ℝ) ^ (-(1 - ξ * Q + ε') * n)) := by ring
        _ ≤ Msmall * a := mul_le_mul hsingle ha (by positivity) hMsmall0
    have hfin : lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) ρ) x y ≤
        (Mlarge + Msmall + 1) * a * ‖x - y‖ ^ β := by
      have hsβ : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
      calc lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) ρ) x y
          ≤ Real.exp (ξ * L n) * ‖x - y‖ := hD
        _ ≤ Real.exp (ξ * L n) * (‖x - y‖ ^ β * (1 + 3 * Real.sqrt d)) :=
            mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
        _ = Real.exp (ξ * L n) * (1 + 3 * Real.sqrt d) * ‖x - y‖ ^ β := by ring
        _ ≤ Msmall * a * ‖x - y‖ ^ β := mul_le_mul_of_nonneg_right hterm hsβ
        _ ≤ (Mlarge + Msmall + 1) * a * ‖x - y‖ ^ β := by
            gcongr
            linarith
    exact absurd hlt (not_lt.2 hfin)
  · -- large `n`: on `𝒜_{r,n}`, the deterministic core
    push Not at hnr
    refine (measure_mono ?_).trans ((hA qA hc₄qA hqA1 hH r n (by omega) hnr).trans
      (ENNReal.ofReal_le_ofReal (hk₀ r (le_max_right _ _))))
    intro ω hω hgood
    simp only [mem_ofPred_eq] at hω
    obtain ⟨x, hx, y, hy, hlt⟩ := hω
    obtain ⟨hI, hII⟩ := hchain P H ξ Q η qA r n ρ ω hξ hr110 hnr hρ1 hρ2
      ((hH.band n).continuous ω) hgood
    have hG := (mem_eventA_iff.1 hgood).1
    have hcomp : ∀ k, k < n →
        aQ P H ξ (n - k) qA ≤ C₅ * (2 : ℝ) ^ ((1 - ξ * Q + ε') * k) * a := fun k hk =>
      hcor Ω P W H hH n k hk.le
    have hcs : ∀ j, j ≤ n → chainSum P H ξ Q η qA j n ≤ K * a * ((2 : ℝ) ^ (-β)) ^ j :=
      fun j hj => by
        have := chainSum_le_aQ_holder (d := d) (P := P) (H := H) (η := η) hc hC₅.le ha0.le
          hβ0.le hβη hcomp ha hj
        calc _ ≤ _ := this
          _ = K * a * ((2 : ℝ) ^ (-β)) ^ j := by rw [hK]; ring
    have hdet := holder_det ((hH.band n).continuous ω) hξ hβ0 hβ1 hβη.le hc hK0 hC₀.le hρ2
      hnr.le ha (fun j => chainSum P H ξ Q η qA j n) hcs hI hII hG x hx y hy
    have hsβ : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
    have hfin : lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) ρ) x y ≤
        (Mlarge + Msmall + 1) * a * ‖x - y‖ ^ β := by
      calc _ ≤ Mlarge * a * ‖x - y‖ ^ β := hdet
        _ ≤ (Mlarge + Msmall + 1) * a * ‖x - y‖ ^ β := by
            gcongr
            linarith
    exact absurd hlt (not_lt.2 hfin)

end DGZ

end HigherDimLQGMetric
