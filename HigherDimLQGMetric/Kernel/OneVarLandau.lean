import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Landau's inequality on half-lines and log-convexity of sup norms of derivatives

Packet L1b (block B1), audit MA5 Details (a) A2.2, steps (i)–(ii): for a smooth `G : ℝ → ℝ` whose
derivatives are bounded on a half-line `[x, ∞)`, the sup norms
`M_j = supFrom (iteratedDeriv j G) x = sup_{y ≥ x} |G^{(j)}(y)|` satisfy Landau's inequality
`M_{j+1}² ≤ 8 M_j M_{j+2}` (`supFrom_succ_sq_le`), hence `j ↦ log M_j + (log 8 / 2) j²` is convex, and
for `i ≤ N` (`1 ≤ N`) the interpolation inequality
`M_i ≤ M_0 · exp((log M_N - log M_0)/N + (log 8 / 2) N)^i` holds (`supFrom_le_interp`).

The constant `8` (instead of the optimal `4` of MA5's Taylor argument) comes from a proof by the mean
value theorem and the mean value inequality (`sq_deriv_le_of_halfLine`); any constant works for A2.2.

Main declarations:
* `sq_le_eight_mul_of_forall_pos` — the optimization step `L s ≤ 2A + B s² ∀ s > 0 ⇒ L² ≤ 8AB`;
* `sq_deriv_le_of_halfLine` — Landau's inequality on `[x, ∞)`;
* `chord_of_convex_seq` — a convex sequence lies below its chords;
* `le_mul_exp_pow_of_logConvex` — the multiplicative (log-convex) form;
* `supFrom`, `supFrom_succ_sq_le`, `supFrom_pos_of_pos`, `supFrom_le_interp`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric

/-! ### The optimization step -/

/-- If `L s ≤ 2A + B s²` for every `s > 0` (with `L, A, B ≥ 0`), then `L² ≤ 8AB`. -/
lemma sq_le_eight_mul_of_forall_pos {L A B : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ s : ℝ, 0 < s → L * s ≤ 2 * A + B * s ^ 2) : L ^ 2 ≤ 8 * A * B := by
  rcases hL.eq_or_lt with hL0 | hLpos
  · rw [← hL0]
    have : 0 ≤ 8 * A * B := by positivity
    simpa using this
  rcases hB.eq_or_lt with hB0 | hBpos
  · exfalso
    have hs : 0 < (2 * A + 1) / L := by positivity
    have h1 := h _ hs
    rw [← hB0, zero_mul, add_zero, mul_div_cancel₀ _ hLpos.ne'] at h1
    linarith
  · have h1 := h (L / (2 * B)) (by positivity)
    have e1 : L * (L / (2 * B)) = 2 * (L ^ 2 / (4 * B)) := by
      field_simp
      ring
    have e2 : B * (L / (2 * B)) ^ 2 = L ^ 2 / (4 * B) := by
      field_simp
      ring
    rw [e1, e2] at h1
    have key : L ^ 2 / (4 * B) ≤ 2 * A := by linarith
    rw [div_le_iff₀ (by positivity)] at key
    linarith

/-! ### Landau's inequality on a half-line -/

/-- **Landau's inequality on a half-line** (constant `8`): if `u` and `u'` are differentiable,
`|u| ≤ A` and `|u''| ≤ B` on `[x, ∞)`, then `u'(y)² ≤ 8AB` for every `y ≥ x`.

Proof: for `s > 0`, the mean value theorem gives `c ∈ (y, y+s)` with `|u'(c)| = |u(y+s) - u(y)|/s ≤ 2A/s`,
and the mean value inequality for `u'` gives `|u'(c) - u'(y)| ≤ Bs`; so `|u'(y)| s ≤ 2A + Bs²`. -/
theorem sq_deriv_le_of_halfLine {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) {x A B : ℝ}
    (hA : ∀ y, x ≤ y → |u y| ≤ A) (hB : ∀ y, x ≤ y → |deriv (deriv u) y| ≤ B)
    {y : ℝ} (hy : x ≤ y) : deriv u y ^ 2 ≤ 8 * A * B := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA y hy)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB y hy)
  have key : ∀ s : ℝ, 0 < s → |deriv u y| * s ≤ 2 * A + B * s ^ 2 := by
    intro s hs
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u (show y < y + s by linarith)
      hu.continuous.continuousOn hu.differentiableOn
    have h1 : |deriv u c| * s ≤ 2 * A := by
      rw [hcd, show y + s - y = s by ring, abs_div, abs_of_pos hs, div_mul_cancel₀ _ hs.ne']
      calc |u (y + s) - u y| ≤ |u (y + s)| + |u y| := abs_sub _ _
        _ ≤ A + A := add_le_add (hA _ (by linarith)) (hA _ hy)
        _ = 2 * A := by ring
    have h2 : |deriv u c - deriv u y| ≤ B * s := by
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv u) (s := Icc y c)
        (fun z _ => hu'.differentiableAt)
        (fun z hz => by rw [Real.norm_eq_abs]; exact hB z (hy.trans hz.1)) (convex_Icc y c)
        (left_mem_Icc.2 hc.1.le) (right_mem_Icc.2 hc.1.le)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (sub_pos.2 hc.1)] at hmv
      calc |deriv u c - deriv u y| ≤ B * (c - y) := hmv
        _ ≤ B * s := by
          apply mul_le_mul_of_nonneg_left _ hB0
          linarith [hc.2]
    have h3 : |deriv u y| ≤ |deriv u c| + B * s := by
      calc |deriv u y| = |deriv u c - (deriv u c - deriv u y)| := by ring_nf
        _ ≤ |deriv u c| + |deriv u c - deriv u y| := abs_sub _ _
        _ ≤ |deriv u c| + B * s := by linarith
    calc |deriv u y| * s ≤ (|deriv u c| + B * s) * s := mul_le_mul_of_nonneg_right h3 hs.le
      _ = |deriv u c| * s + B * s ^ 2 := by ring
      _ ≤ 2 * A + B * s ^ 2 := by linarith
  have h := sq_le_eight_mul_of_forall_pos (abs_nonneg _) hA0 hB0 key
  rwa [sq_abs] at h

/-! ### Convex sequences -/

/-- A convex sequence (`2 b (j+1) ≤ b j + b (j+2)`) lies below its chords:
`N b_i ≤ (N - i) b_0 + i b_N` for `i ≤ N`. -/
theorem chord_of_convex_seq (b : ℕ → ℝ) (h : ∀ j, 2 * b (j + 1) ≤ b j + b (j + 2))
    {i N : ℕ} (hiN : i ≤ N) : (N : ℝ) * b i ≤ ((N : ℝ) - i) * b 0 + (i : ℝ) * b N := by
  set Δ : ℕ → ℝ := fun j => b (j + 1) - b j with hΔ
  have hmono : Monotone Δ := monotone_nat_of_le_succ fun j => by
    simp only [hΔ]
    linarith [h j]
  have tel : ∀ m, b m - b 0 = ∑ j ∈ Finset.range m, Δ j := fun m =>
    (Finset.sum_range_sub b m).symm
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    simp
  -- the slope `Δ (i-1)` separates the two halves
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hleft : b (k + 1) - b 0 ≤ ((k : ℝ) + 1) * Δ k := by
    rw [tel]
    have := Finset.sum_le_card_nsmul (Finset.range (k + 1)) Δ (Δ k) fun j hj =>
      hmono (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    simpa [nsmul_eq_mul] using this
  have hright : ((N : ℝ) - (k + 1)) * Δ k ≤ b N - b (k + 1) := by
    have hsplit : b N - b (k + 1) = ∑ j ∈ Finset.Ico (k + 1) N, Δ j := by
      rw [Finset.sum_Ico_eq_sub _ hiN, ← tel, ← tel]
      ring
    rw [hsplit]
    have := Finset.card_nsmul_le_sum (Finset.Ico (k + 1) N) Δ (Δ k) fun j hj =>
      hmono (by have := (Finset.mem_Ico.1 hj).1; omega)
    have hcard : ((Finset.Ico (k + 1) N).card : ℝ) = (N : ℝ) - (k + 1) := by
      rw [Nat.card_Ico, Nat.cast_sub hiN]
      push_cast
      ring
    rw [nsmul_eq_mul, hcard] at this
    exact this
  have hNk : (0 : ℝ) ≤ (N : ℝ) - (k + 1) := by
    have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hiN
    push_cast at this
    linarith
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  -- combine: (N - i)(b_i - b_0) ≤ (N - i) i Δ ≤ i (b_N - b_i)
  have hcomb : ((N : ℝ) - (k + 1)) * (b (k + 1) - b 0) ≤ ((k : ℝ) + 1) * (b N - b (k + 1)) :=
    calc ((N : ℝ) - (k + 1)) * (b (k + 1) - b 0)
        ≤ ((N : ℝ) - (k + 1)) * (((k : ℝ) + 1) * Δ k) := mul_le_mul_of_nonneg_left hleft hNk
      _ = ((k : ℝ) + 1) * (((N : ℝ) - (k + 1)) * Δ k) := by ring
      _ ≤ ((k : ℝ) + 1) * (b N - b (k + 1)) := mul_le_mul_of_nonneg_left hright hk
  push_cast
  linarith

/-- **Log-convex sequences.** If `M j > 0` and `M (j+1)² ≤ K M j M (j+2)` for all `j` (`K ≥ 1`), then
for `i ≤ N`, `1 ≤ N`: `M i ≤ M 0 · exp((log M_N - log M_0)/N + (log K / 2) N)^i`. -/
theorem le_mul_exp_pow_of_logConvex (M : ℕ → ℝ) (hpos : ∀ j, 0 < M j) {K : ℝ} (hK : 1 ≤ K)
    (h : ∀ j, M (j + 1) ^ 2 ≤ K * M j * M (j + 2)) {i N : ℕ} (hiN : i ≤ N) (hN : 1 ≤ N) :
    M i ≤ M 0 * Real.exp ((Real.log (M N) - Real.log (M 0)) / N + Real.log K / 2 * N) ^ i := by
  set c : ℝ := Real.log K / 2 with hc
  have hc0 : 0 ≤ c := by
    have := Real.log_nonneg hK
    rw [hc]
    linarith
  set b : ℕ → ℝ := fun j => Real.log (M j) + c * (j : ℝ) ^ 2 with hb
  have hconv : ∀ j, 2 * b (j + 1) ≤ b j + b (j + 2) := by
    intro j
    have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
    have hlog : 2 * Real.log (M (j + 1)) ≤ Real.log K + Real.log (M j) + Real.log (M (j + 2)) := by
      have h1 : Real.log (M (j + 1) ^ 2) ≤ Real.log (K * M j * M (j + 2)) :=
        Real.log_le_log (by have := hpos (j + 1); positivity) (h j)
      rw [Real.log_pow, Real.log_mul (by have := hpos j; positivity) (hpos (j + 2)).ne',
        Real.log_mul hK0.ne' (hpos j).ne'] at h1
      push_cast at h1
      linarith
    simp only [hb]
    push_cast
    have e : c * (j : ℝ) ^ 2 + c * ((j : ℝ) + 2) ^ 2 = 2 * (c * ((j : ℝ) + 1) ^ 2) + 2 * c := by
      ring
    have hcK : 2 * c = Real.log K := by rw [hc]; ring
    linarith [hlog, e, hcK]
  have hchord := chord_of_convex_seq b hconv hiN
  simp only [hb, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero] at hchord
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- `log M_i ≤ log M_0 + i L`
  set L : ℝ := (Real.log (M N) - Real.log (M 0)) / N + c * N with hL
  have hkey : Real.log (M i) ≤ Real.log (M 0) + (i : ℝ) * L := by
    have hiN' : (i : ℝ) ≤ N := by exact_mod_cast hiN
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have h2 : (N : ℝ) * (Real.log (M i) - Real.log (M 0)) ≤
        (i : ℝ) * (Real.log (M N) - Real.log (M 0)) + c * (i : ℝ) * (N : ℝ) ^ 2 := by
      have hnn : 0 ≤ c * (N : ℝ) * (i : ℝ) ^ 2 := by positivity
      nlinarith [hchord, hnn]
    have h3 : (N : ℝ) * (Real.log (M i) - Real.log (M 0)) ≤ (N : ℝ) * ((i : ℝ) * L) := by
      rw [hL]
      have : (N : ℝ) * ((i : ℝ) * ((Real.log (M N) - Real.log (M 0)) / N + c * N)) =
          (i : ℝ) * (Real.log (M N) - Real.log (M 0)) + c * (i : ℝ) * (N : ℝ) ^ 2 := by
        field_simp
      rw [this]
      exact h2
    have := le_of_mul_le_mul_left h3 hNpos
    linarith
  calc M i = Real.exp (Real.log (M i)) := (Real.exp_log (hpos i)).symm
    _ ≤ Real.exp (Real.log (M 0) + (i : ℝ) * L) := Real.exp_le_exp.2 hkey
    _ = M 0 * Real.exp L ^ i := by
      rw [Real.exp_add, Real.exp_log (hpos 0), Real.exp_nat_mul]

/-! ### Sup norms on a half-line -/

/-- `supFrom u x = sup_{y ≥ x} |u y|` (an `sSup` in `ℝ`; meaningful when the set is bounded above). -/
def supFrom (u : ℝ → ℝ) (x : ℝ) : ℝ := sSup ((fun y => |u y|) '' Ici x)

lemma le_supFrom {u : ℝ → ℝ} {x : ℝ} (hb : BddAbove ((fun y => |u y|) '' Ici x)) {y : ℝ}
    (hy : x ≤ y) : |u y| ≤ supFrom u x :=
  le_csSup hb ⟨y, mem_Ici.2 hy, rfl⟩

lemma supFrom_le {u : ℝ → ℝ} {x C : ℝ} (h : ∀ y, x ≤ y → |u y| ≤ C) : supFrom u x ≤ C :=
  csSup_le ⟨|u x|, x, mem_Ici.2 le_rfl, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)

lemma supFrom_nonneg {u : ℝ → ℝ} {x : ℝ} (hb : BddAbove ((fun y => |u y|) '' Ici x)) :
    0 ≤ supFrom u x :=
  (abs_nonneg _).trans (le_supFrom hb le_rfl)

/-- Landau's inequality for the sup norms of consecutive derivatives on `[x, ∞)`:
`M_{j+1}² ≤ 8 M_j M_{j+2}`. -/
theorem supFrom_succ_sq_le {G : ℝ → ℝ} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) {x : ℝ}
    (hb : ∀ j, BddAbove ((fun y => |iteratedDeriv j G y|) '' Ici x)) (j : ℕ) :
    supFrom (iteratedDeriv (j + 1) G) x ^ 2 ≤
      8 * supFrom (iteratedDeriv j G) x * supFrom (iteratedDeriv (j + 2) G) x := by
  set A := supFrom (iteratedDeriv j G) x
  set B := supFrom (iteratedDeriv (j + 2) G) x
  have hA0 : 0 ≤ A := supFrom_nonneg (hb j)
  have hB0 : 0 ≤ B := supFrom_nonneg (hb (j + 2))
  have hdiff : ∀ m : ℕ, Differentiable ℝ (iteratedDeriv m G) := fun m =>
    hG.differentiable_iteratedDeriv m (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top m))
  have hu' : deriv (iteratedDeriv j G) = iteratedDeriv (j + 1) G := iteratedDeriv_succ.symm
  have hu'' : deriv (deriv (iteratedDeriv j G)) = iteratedDeriv (j + 2) G := by
    rw [hu', ← iteratedDeriv_succ]
  have hpt : ∀ y, x ≤ y → |iteratedDeriv (j + 1) G y| ≤ Real.sqrt (8 * A * B) := by
    intro y hy
    apply Real.abs_le_sqrt
    have := sq_deriv_le_of_halfLine (u := iteratedDeriv j G) (hdiff j) (by rw [hu']; exact hdiff _)
      (fun z hz => le_supFrom (hb j) hz)
      (fun z hz => by rw [hu'']; exact le_supFrom (hb (j + 2)) hz) hy
    rwa [hu'] at this
  have hle := supFrom_le hpt
  have hnn : 0 ≤ supFrom (iteratedDeriv (j + 1) G) x := supFrom_nonneg (hb (j + 1))
  calc supFrom (iteratedDeriv (j + 1) G) x ^ 2 ≤ Real.sqrt (8 * A * B) ^ 2 :=
        pow_le_pow_left₀ hnn hle 2
    _ = 8 * A * B := Real.sq_sqrt (by positivity)

/-- If `M_0 > 0` and `M_1 > 0`, all the sup norms `M_j` are positive (Landau's inequality propagates
positivity upwards). -/
theorem supFrom_pos_of_pos {G : ℝ → ℝ} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) {x : ℝ}
    (hb : ∀ j, BddAbove ((fun y => |iteratedDeriv j G y|) '' Ici x))
    (h0 : 0 < supFrom (iteratedDeriv 0 G) x) (h1 : 0 < supFrom (iteratedDeriv 1 G) x) (j : ℕ) :
    0 < supFrom (iteratedDeriv j G) x := by
  have hpair : ∀ k, 0 < supFrom (iteratedDeriv k G) x ∧ 0 < supFrom (iteratedDeriv (k + 1) G) x := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hL := supFrom_succ_sq_le hG hb k
      have hsq : 0 < supFrom (iteratedDeriv (k + 1) G) x ^ 2 := by have := ih.2; positivity
      rcases (supFrom_nonneg (hb (k + 2))).eq_or_lt with heq | hlt
      · rw [← heq, mul_zero] at hL
        linarith
      · exact hlt
  exact (hpair j).1

/-- **Interpolation on a half-line** (MA5 A2.2 (ii)): if the sup norms `M_j` of the derivatives of a
smooth `G` on `[x, ∞)` are finite and `M_0, M_1 > 0`, then for `i ≤ N`, `1 ≤ N`,
`M_i ≤ M_0 · exp((log M_N - log M_0)/N + (log 8 / 2) N)^i`. -/
theorem supFrom_le_interp {G : ℝ → ℝ} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) {x : ℝ}
    (hb : ∀ j, BddAbove ((fun y => |iteratedDeriv j G y|) '' Ici x))
    (h0 : 0 < supFrom (iteratedDeriv 0 G) x) (h1 : 0 < supFrom (iteratedDeriv 1 G) x)
    {i N : ℕ} (hiN : i ≤ N) (hN : 1 ≤ N) :
    supFrom (iteratedDeriv i G) x ≤ supFrom (iteratedDeriv 0 G) x *
      Real.exp ((Real.log (supFrom (iteratedDeriv N G) x) -
        Real.log (supFrom (iteratedDeriv 0 G) x)) / N + Real.log 8 / 2 * N) ^ i :=
  le_mul_exp_pow_of_logConvex (fun j => supFrom (iteratedDeriv j G) x)
    (supFrom_pos_of_pos hG hb h0 h1) (by norm_num) (supFrom_succ_sq_le hG hb) hiN hN

end HigherDimLQGMetric
