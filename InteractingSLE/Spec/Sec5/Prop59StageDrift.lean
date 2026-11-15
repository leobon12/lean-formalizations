/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageCross
import InteractingSLE.Spec.Sec5.ProbRestart
import InteractingSLE.Spec.Supplement.S8Abel

/-!
# Proposition 5.9's stage-independent drift bound

Packet PROVE-PROP59T2. Specification §5.2, proof of Proposition 5.9, pp. 146–147:

> The weights produced by the previous angle changes satisfy `ρ^{i,R} = (χ/λ)(θ_{j−i+1} − θ_{j−i})`,
> `ρ^{i,L} = −ρ^{i,R}`.
> Every partial sum of these left weights has absolute value at most `M`, and the same is true of the right weights
> after omitting the first one. […] Apply this with the decreasing reciprocal force-point gaps. The total drift from
> all the angle-change marks other than the first right mark is bounded in absolute value by `8M/3`. The finitely
> many marks inherited from the initial configuration add at most `(4/3) Σ |ρ_i^{initial}|`. These bounds do not
> depend on `j`.

Here `M = πχ/λ = 2 − κ/2` (`angleWeightBound`). The angle-change weights at depth `j` are `newL κ (j − 1), …, newL κ 0`
(alternating signs), then the initial weights (`consAlt`). This file proves the bound `otherDrift_stage_le`: if every
mark other than the first right one is at distance at least `3/4` from the driver, the drift of Lemma 5.10's
remaining word is at most `stageDriftBound κ ρL₀ ρR₀ = 8M/3 + (4/3)(Σ |ρL₀| + Σ |ρR₀|)`, for every depth.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

namespace Prop59Stage

/-! ### The prepended weights -/

section ConsAlt

variable {c : ℕ → ℝ} {n₀ : ℕ} {ρ₀ : Fin n₀ → ℝ}

/-- The prepended weights as a function on `ℕ` (`0` beyond the last index). -/
def consAltN (c : ℕ → ℝ) {n₀ : ℕ} (ρ₀ : Fin n₀ → ℝ) (m : ℕ) (i : ℕ) : ℝ :=
  if i < m then c (m - 1 - i) else if h : i - m < n₀ then ρ₀ ⟨i - m, h⟩ else 0

theorem consAlt_apply (c : ℕ → ℝ) (ρ₀ : Fin n₀ → ℝ) (m : ℕ) (i : Fin (n₀ + m)) :
    consAlt c ρ₀ m i = consAltN c ρ₀ m i := by
  induction m with
  | zero =>
    have hi : (i : ℕ) - 0 < n₀ := by simp
    simp only [consAltN, Nat.not_lt_zero, ↓reduceIte, hi, ↓reduceDIte]
    rfl
  | succ m ih =>
    show (Fin.cons (c m) (consAlt c ρ₀ m) : Fin (n₀ + m + 1) → ℝ) i = _
    rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨i', rfl⟩
    · subst h0
      simp only [Fin.cons_zero, consAltN, Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte]
      congr 1
    · rw [Fin.cons_succ, ih i']
      simp only [consAltN, Fin.val_succ]
      by_cases hlt : (i' : ℕ) < m
      · simp only [hlt, ↓reduceIte, show (i' : ℕ) + 1 < m + 1 by omega]
        congr 1
        omega
      · have h2 : ¬ ((i' : ℕ) + 1 < m + 1) := by omega
        have e : (i' : ℕ) + 1 - (m + 1) = (i' : ℕ) - m := by omega
        simp only [hlt, h2, ↓reduceIte, e]

/-- The alternating sign sums `Σ_{i < n} (−1)^i` are `0` or `1`. -/
theorem abs_sum_neg_one_pow_le (n : ℕ) : |∑ i ∈ range n, (-1 : ℝ) ^ i| ≤ 1 := by
  have key : ∀ n : ℕ, ∑ i ∈ range n, (-1 : ℝ) ^ i = if Even n then 0 else 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      rcases Nat.even_or_odd n with he | ho
      · have : ¬ Even (n + 1) := Nat.not_even_iff_odd.2 (he.add_one)
        simp only [he, ↓reduceIte, this, he.neg_one_pow, zero_add]
      · have : Even (n + 1) := ho.add_one
        simp only [Nat.not_even_iff_odd.2 ho, ↓reduceIte, this, ho.neg_one_pow]
        ring
  rw [key]
  split_ifs <;> norm_num

/-- **Partial sums of alternating new weights**: if `c k = s (−1)^k M` with `|s| ≤ 1`, the partial sums of the
prepended weights `c (m − 1), c (m − 2), …` have modulus at most `|M|`. -/
theorem abs_sum_alt_le {s M : ℝ} (hs : |s| ≤ 1) (hc : ∀ k, c k = s * ((-1) ^ k * M)) {m l : ℕ} (hl : l < m) :
    |∑ i ∈ range (l + 1), c (m - 1 - i)| ≤ |M| := by
  have e : ∀ i ∈ range (l + 1), c (m - 1 - i) = s * M * (-1) ^ (m - 1) * (-1) ^ i := by
    intro i hi
    have hi' : i ≤ m - 1 := by simp only [Finset.mem_range] at hi; omega
    rw [hc]
    have h1 : (-1 : ℝ) ^ (m - 1) = (-1) ^ (m - 1 - i) * (-1) ^ i := by
      rw [← pow_add]; congr 1; omega
    rw [h1]
    have h2 : (-1 : ℝ) ^ i * (-1) ^ i = 1 := by rw [← mul_pow]; norm_num
    calc s * ((-1) ^ (m - 1 - i) * M) = s * M * ((-1) ^ (m - 1 - i) * ((-1) ^ i * (-1) ^ i)) := by
          rw [h2]; ring
      _ = s * M * ((-1) ^ (m - 1 - i) * (-1) ^ i) * (-1) ^ i := by ring
  rw [sum_congr rfl e, ← mul_sum, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
  calc |s| * |M| * |∑ i ∈ range (l + 1), (-1 : ℝ) ^ i| ≤ 1 * |M| * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hs (abs_nonneg _)) (abs_sum_neg_one_pow_le _) (abs_nonneg _)
          (by positivity)
    _ = |M| := by ring

/-- **One side of the drift bound**: for prepended alternating weights (partial sums of modulus at most `M`) and gaps
`g ≥ 3/4` that increase with the index, `|Σ_i ρ_i / g_i| ≤ 4M/3 + (4/3) Σ |ρ₀|`. -/
theorem abs_sum_consAlt_div_le {s M : ℝ} (hM : 0 ≤ M) (hs : |s| ≤ 1) (hc : ∀ k, c k = s * ((-1) ^ k * M))
    (m : ℕ) {g : Fin (n₀ + m) → ℝ} (hg : ∀ i, 3 / 4 ≤ g i) (hmono : Monotone g) :
    |∑ i, consAlt c ρ₀ m i * (1 / g i)| ≤ 4 * M / 3 + 4 / 3 * ∑ i, |ρ₀ i| := by
  set gN : ℕ → ℝ := fun i => if h : i < n₀ + m then g ⟨i, h⟩ else 1 with hgN
  set F : ℕ → ℝ := fun i => consAltN c ρ₀ m i * (1 / gN i) with hF
  have hsum : ∑ i, consAlt c ρ₀ m i * (1 / g i) = ∑ i ∈ range (n₀ + m), F i := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun i _ => ?_
    simp only [hF, hgN, i.2, ↓reduceDIte, consAlt_apply]
  rw [hsum, ← sum_range_add_sum_Ico F (show m ≤ n₀ + m by omega)]
  have h1 : |∑ i ∈ range m, F i| ≤ 4 * M / 3 := by
    have e : ∑ i ∈ range m, F i = ∑ i ∈ range m, c (m - 1 - i) * (1 / gN i) := by
      refine sum_congr rfl fun i hi => ?_
      simp only [hF, consAltN, show i < m from Finset.mem_range.1 hi, ↓reduceIte]
    rw [e]
    refine Supp8.gb9_side_drift_le hM (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    · simp only [hgN, show i < n₀ + m by omega, ↓reduceDIte]; exact hg _
    · simp only [hgN, show i < n₀ + m by omega, show i + 1 < n₀ + m by omega, ↓reduceDIte]
      exact hmono (Fin.mk_le_mk.2 (by omega))
    · exact (abs_sum_alt_le hs hc hi).trans (le_of_eq (abs_of_nonneg hM))
  have h2 : |∑ i ∈ Ico m (n₀ + m), F i| ≤ 4 / 3 * ∑ i, |ρ₀ i| := by
    rw [sum_Ico_eq_sum_range, show n₀ + m - m = n₀ by omega]
    set ρN : ℕ → ℝ := fun k => if h : k < n₀ then ρ₀ ⟨k, h⟩ else 0 with hρN
    have e : ∀ k ∈ range n₀, F (m + k) = ρN k * (1 / gN (m + k)) := by
      intro k hk
      have hk' : k < n₀ := Finset.mem_range.1 hk
      simp only [hF, hρN, consAltN, show ¬ (m + k < m) by omega, ↓reduceIte, show m + k - m = k by omega, hk',
        ↓reduceDIte]
    rw [sum_congr rfl e]
    have hgk : ∀ k ∈ range n₀, 3 / 4 ≤ gN (m + k) := fun k hk => by
      simp only [hgN, show m + k < n₀ + m by have := Finset.mem_range.1 hk; omega, ↓reduceDIte]; exact hg _
    calc |∑ k ∈ range n₀, ρN k * (1 / gN (m + k))|
        ≤ ∑ k ∈ range n₀, |ρN k| * (4 / 3) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
          have hpos : 0 < gN (m + k) := lt_of_lt_of_le (by norm_num) (hgk k hk)
          rw [abs_mul, abs_of_pos (one_div_pos.2 hpos)]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [div_le_iff₀ hpos]; linarith [hgk k hk]
      _ = 4 / 3 * ∑ i, |ρ₀ i| := by
          rw [← sum_mul, mul_comm, ← Fin.sum_univ_eq_sum_range (fun k => |ρN k|) n₀]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hρN, i.2, ↓reduceDIte]
  calc |∑ i ∈ range m, F i + ∑ i ∈ Ico m (n₀ + m), F i|
      ≤ |∑ i ∈ range m, F i| + |∑ i ∈ Ico m (n₀ + m), F i| := abs_add_le _ _
    _ ≤ 4 * M / 3 + 4 / 3 * ∑ i, |ρ₀ i| := add_le_add h1 h2

end ConsAlt

/-! ### The drift bound of the even stages -/

section Drift

variable {κ : ℝ} {nL₀ nR₀ : ℕ}

/-- **The stage-independent drift bound** `8M/3 + (4/3)(Σ |ρL₀| + Σ |ρR₀|)`. -/
def stageDriftBound (κ : ℝ) {nL₀ nR₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) : ℝ :=
  8 * angleWeightBound κ / 3 + 4 / 3 * ((∑ i, |ρL₀ i|) + ∑ k, |ρR₀ k|)

theorem newL_eq (κ : ℝ) (k : ℕ) : newL κ k = 1 * ((-1) ^ k * angleWeightBound κ) := by
  rw [newL, one_mul]

theorem newR_eq (κ : ℝ) (k : ℕ) : newR κ k = -1 * ((-1) ^ k * angleWeightBound κ) := by
  rw [newR]; ring

/-- **The drift bound at every depth** (pp. 146–147): at depth `j + 1`, if every left mark and every right mark other
than the first is at distance at least `3/4` from the driver (marks ordered), the remaining drift of Lemma 5.10 is at
most `stageDriftBound`. -/
theorem otherDrift_stage_le (hκ : 0 < κ) (hκ4 : κ < 4) (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) (j : ℕ)
    {w : ℝ} {vL : Fin (nL₀ + (j + 1)) → ℝ} {vR : Fin (nR₀ + j + 1) → ℝ} (hvL : Antitone vL) (hvR : Monotone vR)
    (hgL : ∀ i, 3 / 4 ≤ w - vL i) (hgR : ∀ k : Fin (nR₀ + j), 3 / 4 ≤ vR k.succ - w) :
    |otherDrift (stageρL κ ρL₀ (j + 1)) (stageρR κ ρR₀ (j + 1)) w vL vR| ≤ stageDriftBound κ ρL₀ ρR₀ := by
  have hM : 0 ≤ angleWeightBound κ := (angleWeightBound_pos hκ hκ4).le
  have hL := abs_sum_consAlt_div_le (c := newL κ) (ρ₀ := ρL₀) hM (s := 1) (by norm_num) (newL_eq κ) (j + 1)
    (g := fun i => w - vL i) hgL (fun a b hab => by simp only; linarith [hvL hab])
  have hR := abs_sum_consAlt_div_le (c := newR κ) (ρ₀ := ρR₀) hM (s := -1) (by norm_num) (newR_eq κ) j
    (g := fun k => vR k.succ - w) hgR (fun a b hab => by simp only; linarith [hvR (Fin.succ_le_succ_iff.2 hab)])
  have eL : ∑ i, stageρL κ ρL₀ (j + 1) i / (w - vL i) =
      ∑ i, consAlt (newL κ) ρL₀ (j + 1) i * (1 / (w - vL i)) :=
    sum_congr rfl fun i _ => by rw [stageρL, mul_one_div]
  have eR : ∑ i : Fin (nR₀ + j), stageρR κ ρR₀ (j + 1) i.succ / (w - vR i.succ) =
      -∑ k, consAlt (newR κ) ρR₀ j k * (1 / (vR k.succ - w)) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    have : stageρR κ ρR₀ (j + 1) k.succ = consAlt (newR κ) ρR₀ j k := by
      rw [stageρR_succ, Fin.cons_succ]; rfl
    rw [this]
    have hne : vR k.succ - w ≠ 0 := by linarith [hgR k]
    have hne' : w - vR k.succ ≠ 0 := by linarith [hgR k]
    field_simp
    ring
  rw [otherDrift, eL]
  erw [eR]
  rw [stageDriftBound]
  calc |∑ i, consAlt (newL κ) ρL₀ (j + 1) i * (1 / (w - vL i)) +
        -∑ k, consAlt (newR κ) ρR₀ j k * (1 / (vR k.succ - w))|
      ≤ |∑ i, consAlt (newL κ) ρL₀ (j + 1) i * (1 / (w - vL i))| +
        |∑ k, consAlt (newR κ) ρR₀ j k * (1 / (vR k.succ - w))| := by
        refine (abs_add_le _ _).trans ?_; rw [abs_neg]
    _ ≤ (4 * angleWeightBound κ / 3 + 4 / 3 * ∑ i, |ρL₀ i|) +
        (4 * angleWeightBound κ / 3 + 4 / 3 * ∑ i, |ρR₀ i|) := add_le_add hL hR
    _ = 8 * angleWeightBound κ / 3 + 4 / 3 * ((∑ i, |ρL₀ i|) + ∑ k, |ρR₀ k|) := by ring

/-- The first right weight at depth `j + 1` is `newR κ j`, of modulus `M`. -/
theorem stageρR_succ_zero (κ : ℝ) (ρR₀ : Fin nR₀ → ℝ) (j : ℕ) :
    stageρR κ ρR₀ (j + 1) 0 = newR κ j := by
  rw [stageρR_succ]; rfl

theorem newR_mem_Icc (hκ : 0 < κ) (hκ4 : κ < 4) (j : ℕ) :
    newR κ j ∈ Icc (-angleWeightBound κ) (angleWeightBound κ) := by
  have hM : 0 ≤ angleWeightBound κ := (angleWeightBound_pos hκ hκ4).le
  rw [newR]
  rcases neg_one_pow_eq_or ℝ j with h | h <;> rw [h] <;> constructor <;> linarith

end Drift

end Prop59Stage

end Sec5

end InteractingSLE
