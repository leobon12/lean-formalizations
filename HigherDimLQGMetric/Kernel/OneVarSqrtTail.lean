import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HigherDimLQGMetric.Kernel.OneVarTail

/-!
# The square root of a tail integral (corrected [1] Lemma 2.11; target `L1b_sqrtTail`)

Packet L1b (block B1). Source: audit MA5 Details (a) A2.2 (complete written proof) and Details (c)
(the target statement, copied verbatim as `L1b_sqrtTail`); [1] = arXiv 2512.06292, Lemma 2.11.

Statement: let `f ∈ C^∞(ℝ)`, `f ≥ 0` on `(0, ∞)`, `sup_{s ≥ 1} s^N |f^{(n)}(s)| < ∞` for all `n, N`, and
`G(x) = ∫_x^∞ f > 0` for `x > 0`. Then `√G` is smooth on `(0, ∞)` and all its derivatives decay faster than
any power on `[1, ∞)`.

Proof (MA5 A2.2 with a different step (iii)–(iv)): fix `x ≥ 1` and `n ≥ 1`, `N = 2n`, and let
`M_j = sup_{y ≥ x} |G^{(j)}(y)|` (`supFrom`), so `M_0 = G(x)`. Landau's inequality and log-convexity
(`supFrom_le_interp`) give `|G^{(i)}(x)| ≤ G(x) D^i` (`i ≤ n`) with
`D = exp((log M_N - log M_0)/N + (log 8/2) N)`. Writing `√G(y) = √G(x) · √(G(y)/G(x))`, Faà di Bruno's
bound `norm_iteratedFDerivWithin_comp_le` for `√· ∘ (G/G(x))` at `x` (where `G/G(x) = 1`) gives
`|(√G)^{(n)}(x)| ≤ n! C_n √G(x) D^n = n! C_n 8^{n²} √M_{2n}` (`C_n` bounds the first `n` derivatives of
`√·` at `1`), and `M_{2n} = sup_{y ≥ x} |f^{(2n-1)}(y)|` decays faster than any power. This replaces
MA5's explicit structure formula for `(√G)^{(n)}` (step (iii)) by Mathlib's Faà di Bruno bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Nat

namespace HigherDimLQGMetric

/-- `C_n = Σ_{i ≤ n} ‖D^i √· (1)‖` (derivatives within `(0, ∞)`): it bounds the first `n` derivatives
of `√·` at `1`. -/
def sqrtDerivBound (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ‖iteratedFDerivWithin ℝ i Real.sqrt (Ioi 0) 1‖

lemma norm_iteratedFDerivWithin_sqrt_one_le {i n : ℕ} (hi : i ≤ n) :
    ‖iteratedFDerivWithin ℝ i Real.sqrt (Ioi 0) 1‖ ≤ sqrtDerivBound n :=
  Finset.single_le_sum (f := fun i => ‖iteratedFDerivWithin ℝ i Real.sqrt (Ioi 0) 1‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-- **Faà di Bruno step.** If `G` is smooth and positive on `(0, ∞)`, `x > 0`, and
`|G^{(i)}(x)| ≤ G(x) D^i` for `1 ≤ i ≤ n`, then `|(√G)^{(n)}(x)| ≤ n! C_n √G(x) D^n`. -/
theorem abs_iteratedDeriv_sqrt_le_of_bound {G : ℝ → ℝ}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (hGpos : ∀ y, 0 < y → 0 < G y) {x : ℝ}
    (hx : 0 < x) {n : ℕ} {D : ℝ}
    (hD : ∀ i, 1 ≤ i → i ≤ n → |iteratedDeriv i G x| ≤ G x * D ^ i) :
    |iteratedDeriv n (fun y => Real.sqrt (G y)) x| ≤
      n ! * sqrtDerivBound n * Real.sqrt (G x) * D ^ n := by
  have hGx : 0 < G x := hGpos x hx
  set H : ℝ → ℝ := fun y => (G x)⁻¹ * G y with hH
  have hHcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H := contDiff_const.mul hG
  have hHx : H x = 1 := by simp only [hH]; exact inv_mul_cancel₀ hGx.ne'
  have hsplit : (fun y => Real.sqrt (G y)) = fun y => Real.sqrt (G x) * Real.sqrt (H y) := by
    funext y
    rw [← Real.sqrt_mul hGx.le, hH, mul_inv_cancel_left₀ hGx.ne']
  have hle : ∀ m : ℕ, (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun m => by
    exact_mod_cast le_top
  have hcdH : ContDiffAt ℝ n (fun y => Real.sqrt (H y)) x :=
    (hHcd.contDiffAt.of_le (hle n)).sqrt (by rw [hHx]; norm_num)
  rw [hsplit, iteratedDeriv_const_mul _ hcdH, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hFdB := norm_iteratedFDerivWithin_comp_le (g := Real.sqrt) (f := H) (n := n)
    (s := Ioi 0) (t := Ioi 0) (x := x) (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (fun y hy => (Real.contDiffAt_sqrt (ne_of_gt hy)).contDiffWithinAt)
    hHcd.contDiffOn (hle n) (uniqueDiffOn_Ioi 0) (uniqueDiffOn_Ioi 0)
    (fun y hy => mul_pos (inv_pos.2 hGx) (hGpos y hy)) hx
    (C := sqrtDerivBound n) (D := D)
    (fun i hi => by rw [hHx]; exact norm_iteratedFDerivWithin_sqrt_one_le hi)
    (fun i hi1 hin => by
      rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi hx,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, hH,
        iteratedDeriv_const_mul _ (hG.contDiffAt.of_le (hle i)), norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_inv, abs_of_pos hGx, inv_mul_le_iff₀ hGx]
      exact hD i hi1 hin)
  rw [iteratedFDerivWithin_of_isOpen n isOpen_Ioi hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs] at hFdB
  calc Real.sqrt (G x) * |iteratedDeriv n (fun y => Real.sqrt (H y)) x|
      ≤ Real.sqrt (G x) * (n ! * sqrtDerivBound n * D ^ n) :=
        mul_le_mul_of_nonneg_left hFdB (Real.sqrt_nonneg _)
    _ = n ! * sqrtDerivBound n * Real.sqrt (G x) * D ^ n := by ring

/-- **Pointwise estimate for `√G`** (MA5 A2.2 (iv)). Let `G` be smooth, positive on `(0, ∞)`, `x > 0`,
with finite sup norms `M_j = sup_{y ≥ x} |G^{(j)}(y)|`, `M_0 = G(x)` and `M_1 > 0`. Then for `n ≥ 1`,
`|(√G)^{(n)}(x)| ≤ n! C_n 8^{n²} √M_{2n}`. -/
theorem abs_iteratedDeriv_sqrt_le_supFrom {G : ℝ → ℝ}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (hGpos : ∀ y, 0 < y → 0 < G y) {x : ℝ}
    (hx : 0 < x) (hb : ∀ j, BddAbove ((fun y => |iteratedDeriv j G y|) '' Ici x))
    (hM0 : supFrom (iteratedDeriv 0 G) x = G x) (hM1 : 0 < supFrom (iteratedDeriv 1 G) x)
    {n : ℕ} (hn : 1 ≤ n) :
    |iteratedDeriv n (fun y => Real.sqrt (G y)) x| ≤
      n ! * sqrtDerivBound n * 8 ^ (n ^ 2) *
        Real.sqrt (supFrom (iteratedDeriv (2 * n) G) x) := by
  have hGx : 0 < G x := hGpos x hx
  have h0 : 0 < supFrom (iteratedDeriv 0 G) x := hM0 ▸ hGx
  have hMpos := supFrom_pos_of_pos hG hb h0 hM1
  set M0 := supFrom (iteratedDeriv 0 G) x with hM0def
  set MN := supFrom (iteratedDeriv (2 * n) G) x with hMNdef
  set L : ℝ := (Real.log MN - Real.log M0) / ((2 * n : ℕ) : ℝ) +
    Real.log 8 / 2 * ((2 * n : ℕ) : ℝ) with hL
  have hD : ∀ i, 1 ≤ i → i ≤ n → |iteratedDeriv i G x| ≤ G x * Real.exp L ^ i := by
    intro i _ hin
    have h1 := le_supFrom (hb i) (le_refl x)
    have h2 := supFrom_le_interp hG hb h0 hM1 (i := i) (N := 2 * n) (by omega) (by omega)
    rw [← hM0]
    exact h1.trans h2
  have hmain := abs_iteratedDeriv_sqrt_le_of_bound hG hGpos hx hD
  have hid : Real.sqrt (G x) * Real.exp L ^ n = 8 ^ (n ^ 2) * Real.sqrt MN := by
    have hMN : 0 < MN := hMpos (2 * n)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have h8 : (8 : ℝ) ^ (n ^ 2) = Real.exp (((n ^ 2 : ℕ) : ℝ) * Real.log 8) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [← hM0, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_def_of_pos h0,
      Real.rpow_def_of_pos hMN, ← Real.exp_nat_mul, h8, ← Real.exp_add, ← Real.exp_add, hL]
    congr 1
    push_cast
    field_simp
    ring
  calc |iteratedDeriv n (fun y => Real.sqrt (G y)) x|
      ≤ n ! * sqrtDerivBound n * Real.sqrt (G x) * Real.exp L ^ n := hmain
    _ = n ! * sqrtDerivBound n * (Real.sqrt (G x) * Real.exp L ^ n) := by ring
    _ = n ! * sqrtDerivBound n * 8 ^ (n ^ 2) * Real.sqrt MN := by rw [hid]; ring

/-! ### The tail integral of a rapidly decreasing function -/

section Tail

variable {f : ℝ → ℝ}

/-- Integrability on every `Ioi a`, from the decay hypothesis of `L1b_sqrtTail`. -/
theorem integrableOn_Ioi_of_iteratedDeriv_decay (hf : Continuous f)
    (hdecay : ∀ n N : ℕ, ∃ C : ℝ, ∀ s, 1 ≤ s → s ^ N * |iteratedDeriv n f s| ≤ C) (a : ℝ) :
    IntegrableOn f (Ioi a) := by
  obtain ⟨C, hC⟩ := hdecay 0 2
  simp only [iteratedDeriv_zero] at hC
  exact integrableOn_Ioi_of_decay hf hC a

/-- The sup norms of the derivatives of `G = ∫_·^∞ f` on `[x, ∞)` (`x ≥ 1`) are finite, `M_0 = G(x)`,
and `M_1 > 0`. -/
theorem supFrom_integral_Ioi_facts (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hnn : ∀ s, 0 < s → 0 ≤ f s)
    (hdecay : ∀ n N : ℕ, ∃ C : ℝ, ∀ s, 1 ≤ s → s ^ N * |iteratedDeriv n f s| ≤ C)
    (hpos : ∀ x, 0 < x → 0 < ∫ s in Ioi x, f s) {x : ℝ} (hx : 1 ≤ x) :
    (∀ j, BddAbove ((fun y => |iteratedDeriv j (fun x => ∫ s in Ioi x, f s) y|) '' Ici x)) ∧
      supFrom (iteratedDeriv 0 (fun x => ∫ s in Ioi x, f s)) x = ∫ s in Ioi x, f s ∧
      0 < supFrom (iteratedDeriv 1 (fun x => ∫ s in Ioi x, f s)) x := by
  have hint := integrableOn_Ioi_of_iteratedDeriv_decay hf.continuous hdecay
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  set G : ℝ → ℝ := fun x => ∫ s in Ioi x, f s with hGdef
  have hder := iteratedDeriv_succ_integral_Ioi hf.continuous hint
  have hG0 : ∀ y, x ≤ y → |iteratedDeriv 0 G y| ≤ G x := by
    intro y hy
    rw [iteratedDeriv_zero, abs_of_pos (hpos y (lt_of_lt_of_le hx0 hy))]
    exact integral_Ioi_le_integral_Ioi hint hnn hx0 hy
  have hb : ∀ j, BddAbove ((fun y => |iteratedDeriv j G y|) '' Ici x) := by
    intro j
    cases j with
    | zero => exact ⟨G x, by rintro _ ⟨y, hy, rfl⟩; exact hG0 y hy⟩
    | succ k =>
      obtain ⟨C, hC⟩ := hdecay k 0
      refine ⟨C, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have := hC y (hx.trans hy)
      simp only [pow_zero, one_mul] at this
      simp only [hGdef, hder k, abs_neg]
      exact this
  refine ⟨hb, le_antisymm (supFrom_le hG0) ?_, ?_⟩
  · have := le_supFrom (hb 0) (le_refl x)
    rw [iteratedDeriv_zero, abs_of_pos (hpos x hx0)] at this
    exact this
  · by_contra hcon'
    have hcon := not_lt.1 hcon'
    have hzero : ∀ y ∈ Ioi x, f y = 0 := by
      intro y hy
      have h1 := le_supFrom (hb 1) (le_of_lt (mem_Ioi.1 hy))
      have h2 : |iteratedDeriv 1 G y| ≤ 0 := h1.trans hcon
      rw [hder 0, iteratedDeriv_zero, abs_neg] at h2
      exact abs_nonpos_iff.1 h2
    have := hpos x hx0
    rw [setIntegral_eq_zero_of_forall_eq_zero hzero] at this
    exact lt_irrefl 0 this

end Tail

/-- **L1b** (= corrected [1] Lemma 2.11, one variable; MA5 Details (c), verbatim): for `f ≥ 0` on
`(0,∞)` with all derivatives rapidly decaying and `G(x) = ∫_x^∞ f > 0`, `√G` is smooth on `(0,∞)` and
all its derivatives decay faster than any power (proof: Landau on half-lines + log-convexity,
MA5 Details (a) A2.2). -/
def L1b_sqrtTail : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → (∀ s, 0 < s → 0 ≤ f s) →
    (∀ n N : ℕ, ∃ C : ℝ, ∀ s, 1 ≤ s → s ^ N * |iteratedDeriv n f s| ≤ C) →
    (∀ x, 0 < x → 0 < ∫ s in Ioi x, f s) →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Real.sqrt (∫ s in Ioi x, f s)) (Ioi 0) ∧
    ∀ n N : ℕ, ∃ C : ℝ, ∀ x, 1 ≤ x →
      x ^ N * |iteratedDeriv n (fun x => Real.sqrt (∫ s in Ioi x, f s)) x| ≤ C

/-- Smoothness part of `L1b_sqrtTail`. -/
theorem contDiffOn_sqrt_integral_Ioi {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hdecay : ∀ n N : ℕ, ∃ C : ℝ, ∀ s, 1 ≤ s → s ^ N * |iteratedDeriv n f s| ≤ C)
    (hpos : ∀ x, 0 < x → 0 < ∫ s in Ioi x, f s) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Real.sqrt (∫ s in Ioi x, f s)) (Ioi 0) :=
  (contDiff_integral_Ioi hf (integrableOn_Ioi_of_iteratedDeriv_decay hf.continuous hdecay)).contDiffOn.sqrt
    fun x hx => (hpos x hx).ne'

/-- Decay part of `L1b_sqrtTail`: `sup_{x ≥ 1} x^N |(√G)^{(n)}(x)| < ∞` for all `n, N`. -/
theorem sqrt_integral_Ioi_decay {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hnn : ∀ s, 0 < s → 0 ≤ f s)
    (hdecay : ∀ n N : ℕ, ∃ C : ℝ, ∀ s, 1 ≤ s → s ^ N * |iteratedDeriv n f s| ≤ C)
    (hpos : ∀ x, 0 < x → 0 < ∫ s in Ioi x, f s) (n N : ℕ) :
    ∃ C : ℝ, ∀ x, 1 ≤ x →
      x ^ N * |iteratedDeriv n (fun x => Real.sqrt (∫ s in Ioi x, f s)) x| ≤ C := by
  have hint := integrableOn_Ioi_of_iteratedDeriv_decay hf.continuous hdecay
  set G : ℝ → ℝ := fun x => ∫ s in Ioi x, f s with hGdef
  have hGcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := contDiff_integral_Ioi hf hint
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · -- `n = 0`: `x^{2N} G(x) ≤ C / x ≤ C`
    subst hn0
    obtain ⟨C, hC⟩ := hdecay 0 (2 * N + 2)
    simp only [iteratedDeriv_zero] at hC
    refine ⟨Real.sqrt C, fun x hx => ?_⟩
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
    have hGx := integral_Ioi_le_of_decay hf.continuous (K := 2 * N) hC hx
    have hGpos := hpos x hx0
    rw [iteratedDeriv_zero, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsq : (x ^ N * Real.sqrt (G x)) ^ 2 ≤ C := by
      rw [mul_pow, Real.sq_sqrt hGpos.le]
      have hxp : 0 < x ^ (2 * N + 1) := pow_pos hx0 _
      have h1 : G x * x ^ (2 * N + 1) ≤ C := by
        have := hGx
        rwa [le_div_iff₀ hxp] at this
      have h2 : (x ^ N) ^ 2 ≤ x ^ (2 * N + 1) := by
        rw [← pow_mul]
        exact pow_le_pow_right₀ hx (by omega)
      nlinarith [hGpos.le, h1, h2]
    have hC0 : 0 ≤ C := (sq_nonneg _).trans hsq
    calc x ^ N * Real.sqrt (G x) = Real.sqrt ((x ^ N * Real.sqrt (G x)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt C := Real.sqrt_le_sqrt hsq
  · -- `n ≥ 1`: the pointwise estimate with `M_{2n} ≤ C / x^{2N}`
    obtain ⟨C, hC⟩ := hdecay (2 * n - 1) (2 * N)
    refine ⟨n ! * sqrtDerivBound n * 8 ^ (n ^ 2) * Real.sqrt C, fun x hx => ?_⟩
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
    obtain ⟨hb, hM0, hM1⟩ := supFrom_integral_Ioi_facts hf hnn hdecay hpos hx
    have hest := abs_iteratedDeriv_sqrt_le_supFrom hGcd (fun y hy => hpos y hy) hx0 hb hM0 hM1 hn1
    set MN := supFrom (iteratedDeriv (2 * n) G) x with hMN
    have hder : iteratedDeriv (2 * n) G = fun y => -iteratedDeriv (2 * n - 1) f y := by
      have := iteratedDeriv_succ_integral_Ioi hf.continuous hint (2 * n - 1)
      rwa [show 2 * n - 1 + 1 = 2 * n by omega] at this
    have hxN : 0 < x ^ (2 * N) := pow_pos hx0 _
    have hMNle : MN ≤ C / x ^ (2 * N) := by
      refine supFrom_le fun y hy => ?_
      have hy1 : 1 ≤ y := hx.trans hy
      rw [hder, abs_neg]
      refine (abs_le_div_pow_of_decay hC hy1).trans ?_
      have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ y ^ (2 * N) *
        |iteratedDeriv (2 * n - 1) f y|).trans (hC y hy1)
      exact div_le_div_of_nonneg_left hC0 hxN (pow_le_pow_left₀ hx0.le hy _)
    have hMN0 : 0 ≤ MN := supFrom_nonneg (hb (2 * n))
    have hxMN : x ^ N * Real.sqrt MN ≤ Real.sqrt C := by
      have hsq : (x ^ N * Real.sqrt MN) ^ 2 ≤ C := by
        rw [mul_pow, Real.sq_sqrt hMN0, ← pow_mul, mul_comm N 2]
        have := hMNle
        rwa [le_div_iff₀ hxN, mul_comm] at this
      calc x ^ N * Real.sqrt MN = Real.sqrt ((x ^ N * Real.sqrt MN) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt C := Real.sqrt_le_sqrt hsq
    have hA : 0 ≤ (n ! : ℝ) * sqrtDerivBound n * 8 ^ (n ^ 2) := by
      have : 0 ≤ sqrtDerivBound n :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      positivity
    calc x ^ N * |iteratedDeriv n (fun x => Real.sqrt (G x)) x|
        ≤ x ^ N * (n ! * sqrtDerivBound n * 8 ^ (n ^ 2) * Real.sqrt MN) :=
          mul_le_mul_of_nonneg_left hest (by positivity)
      _ = n ! * sqrtDerivBound n * 8 ^ (n ^ 2) * (x ^ N * Real.sqrt MN) := by ring
      _ ≤ n ! * sqrtDerivBound n * 8 ^ (n ^ 2) * Real.sqrt C :=
          mul_le_mul_of_nonneg_left hxMN hA

/-- **Target `L1b_sqrtTail`** (packet L1b; corrected [1] Lemma 2.11). -/
theorem l1b_sqrtTail : L1b_sqrtTail := fun _ hf hnn hdecay hpos =>
  ⟨contDiffOn_sqrt_integral_Ioi hf hdecay hpos, sqrt_integral_Ioi_decay hf hnn hdecay hpos⟩

end HigherDimLQGMetric
