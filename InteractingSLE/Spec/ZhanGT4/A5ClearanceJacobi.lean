/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Algebra.Ring.GeomSum

/-!
# Protected-ray clearance, I: a polynomial solution of the Jacobi Poisson equation

Packet PROVE-ZHAN-CLEAR (R53, Astra *Follow-up A–E* B.3/B.4, `ig1_followup_a_e_audited.txt` L400–L467). For the separated
two-force law `SLE_κ(ρ_L; ρ_R)` write `Z = V^R − W`, `Y = W − V^L`, `S = Y + Z`, `v = Y/S`. In the logarithmic clock
`dτ = 2 dt/(YZ)` the angle `v` is the Jacobi diffusion with generator

  `L f(v) = (a − b v) f'(v) + c v (1 − v) f''(v)`,  `a = (2 + ρ_L)/2`, `b = (4 + ρ_L + ρ_R)/2`, `c = κ/4`,

and `Φ = log Z + s/3` (`s = ∫ Z⁻² dt`) has drift `(k/2) v/(1 − v) − ρ_L/2` per unit of `τ`, `k = 2 + ρ_R − κ/2 + 1/3`.
The drift has a positive Beta mean but is negative near `v = 0`; this file builds the corrector (added here; the
source does not prove (B.3), see B.5).

* `rP j`: the polynomial with `L r_j = m_j − v^j`, `m_j = ∏_{i<j} (a + ci)/(b + ci)` (`gen_rP`), from
  `L(v^j) = j(a + c(j−1)) v^{j−1} − j(b + c(j−1)) v^j`;
* the telescoping identity `d · m_{j+1} = x_j − x_{j+1}`, `x_j = m_j (a + cj)`, `d = b − a − c`
  (`mul_mom_succ_eq`), which gives `k ∑_{j ≤ n} m_j > ρ_L` for some `n` (`exists_sum_mom_gt`): if `d > 0`, then
  `x_n → 0`; if `d = 0`, then `m_j = a/(a + cj)` and the sum diverges;
* `q = (k/2) ∑_{j=1}^n r_j` solves `L q = c₀ + ρ_L/2 − (k/2) ∑_{j=1}^n v^j` with `c₀ = (k/2) ∑ m_j − ρ_L/2 > 0`, so the
  drift of `Φ + q(v)` is `c₀ + (k/2) v^{n+1}/(1 − v) ≥ c₀`;
* **`exists_lyapunov`**: there are `λ > 0` and such a `q` (with bounds on `[0, 1]`) for which, at every `Z, Y > 0`,
  `λ (κ/2) (q'(v)/S − 1/Z)² ≤ k/Z² − ρ_L/(YZ) + (2/(YZ)) (a − bv) q'(v) + (κ/2) q''(v)/S²`, i.e. the Itô drift of
  `exp(−λ(log Z + s/3 + q(v)))` is `≤ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Finset

namespace InteractingSLE.ZhanGT4.A5Clear

/-! ### The Jacobi polynomials `r_j` -/

section Poly

variable (a b c : ℝ)

/-- The ratio `(a + c j)/(b + c j)`. -/
def ratio (j : ℕ) : ℝ := (a + c * j) / (b + c * j)

/-- The Beta moments: `m_0 = 1`, `m_{j+1} = m_j (a + cj)/(b + cj)`. -/
def mom : ℕ → ℝ
  | 0 => 1
  | j + 1 => mom j * ratio a b c j

/-- The polynomial `r_j` with `L r_j = m_j − v^j`. -/
def rP : ℕ → ℝ → ℝ
  | 0, _ => 0
  | j + 1, v => ratio a b c j * rP j v + v ^ (j + 1) / ((j + 1) * (b + c * j))

/-- The derivative of `r_j`. -/
def rP1 : ℕ → ℝ → ℝ
  | 0, _ => 0
  | j + 1, v => ratio a b c j * rP1 j v + v ^ j / (b + c * j)

/-- The second derivative of `r_j`. -/
def rP2 : ℕ → ℝ → ℝ
  | 0, _ => 0
  | j + 1, v => ratio a b c j * rP2 j v + j * v ^ (j - 1) / (b + c * j)

theorem hasDerivAt_rP (j : ℕ) (v : ℝ) : HasDerivAt (rP a b c j) (rP1 a b c j v) v := by
  induction j generalizing v with
  | zero => exact hasDerivAt_const v (0 : ℝ)
  | succ j ih =>
    have h1 := (ih v).const_mul (ratio a b c j)
    have h2 := (hasDerivAt_pow (j + 1) v).div_const (((j : ℝ) + 1) * (b + c * j))
    have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
    have e : ((↑(j + 1) : ℝ) * v ^ (j + 1 - 1)) / (((j : ℝ) + 1) * (b + c * j)) = v ^ j / (b + c * j) := by
      rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_div_mul_left _ _ hne]
    rw [e] at h2
    exact h1.add h2

theorem hasDerivAt_rP1 (j : ℕ) (v : ℝ) : HasDerivAt (rP1 a b c j) (rP2 a b c j v) v := by
  induction j generalizing v with
  | zero => exact hasDerivAt_const v (0 : ℝ)
  | succ j ih =>
    have h1 := (ih v).const_mul (ratio a b c j)
    have h2 := (hasDerivAt_pow j v).div_const (b + c * j)
    exact h1.add h2

theorem contDiff_rP {n : WithTop ℕ∞} (j : ℕ) : ContDiff ℝ n (rP a b c j) := by
  induction j with
  | zero => exact contDiff_const
  | succ j ih =>
    have h : rP a b c (j + 1) = fun v => ratio a b c j * rP a b c j v +
        v ^ (j + 1) / ((j + 1) * (b + c * j)) := rfl
    rw [h]
    exact (contDiff_const.mul ih).add ((contDiff_id.pow _).div_const _)

theorem continuous_rP1 (j : ℕ) : Continuous (rP1 a b c j) := by
  induction j with
  | zero => exact continuous_const
  | succ j ih =>
    have h : rP1 a b c (j + 1) = fun v => ratio a b c j * rP1 a b c j v + v ^ j / (b + c * j) := rfl
    rw [h]
    exact (continuous_const.mul ih).add ((continuous_id.pow _).div_const _)

/-- **The Jacobi generator of `r_j`**: `(a − bv) r_j' + c v (1 − v) r_j'' = m_j − v^j`. -/
theorem gen_rP (hbc : ∀ j : ℕ, b + c * j ≠ 0) (j : ℕ) (v : ℝ) :
    (a - b * v) * rP1 a b c j v + c * v * (1 - v) * rP2 a b c j v = mom a b c j - v ^ j := by
  induction j with
  | zero => simp [rP1, rP2, mom]
  | succ j ih =>
    have hb := hbc j
    have key : (a - b * v) * (v ^ j / (b + c * j)) + c * v * (1 - v) * (j * v ^ (j - 1) / (b + c * j)) =
        ratio a b c j * v ^ j - v ^ (j + 1) := by
      rw [ratio]
      rcases j with _ | j
      · field_simp; ring
      · simp only [Nat.add_sub_cancel]
        field_simp
        ring
    simp only [rP1, rP2, mom]
    have e : (a - b * v) * (ratio a b c j * rP1 a b c j v + v ^ j / (b + c * j)) +
        c * v * (1 - v) * (ratio a b c j * rP2 a b c j v + j * v ^ (j - 1) / (b + c * j)) =
        ratio a b c j * ((a - b * v) * rP1 a b c j v + c * v * (1 - v) * rP2 a b c j v) +
          ((a - b * v) * (v ^ j / (b + c * j)) +
            c * v * (1 - v) * (j * v ^ (j - 1) / (b + c * j))) := by ring
    rw [e, ih, key]
    ring

end Poly

/-! ### The Beta moments: telescoping and divergence -/

section Moments

variable {a b c : ℝ}

theorem ratio_pos (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (j : ℕ) : 0 < ratio a b c j := by
  unfold ratio
  have h1 : 0 < a + c * j := by positivity
  exact div_pos h1 (by linarith)

theorem mom_pos (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (j : ℕ) : 0 < mom a b c j := by
  induction j with
  | zero => exact one_pos
  | succ j ih => exact mul_pos ih (ratio_pos ha hc hab j)

/-- `x_j = m_j (a + c j)`. -/
def xJ (a b c : ℝ) (j : ℕ) : ℝ := mom a b c j * (a + c * j)

/-- **Telescoping**: `(b − a − c) m_{j+1} = x_j − x_{j+1}`. -/
theorem mul_mom_succ_eq (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (j : ℕ) :
    (b - a - c) * mom a b c (j + 1) = xJ a b c j - xJ a b c (j + 1) := by
  have hb : 0 < b + c * j := by
    have : 0 ≤ c * (j : ℝ) := by positivity
    linarith
  simp only [xJ, mom, ratio]
  push_cast
  field_simp
  ring

theorem sum_mom_eq (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (n : ℕ) :
    (b - a - c) * ∑ j ∈ range n, mom a b c (j + 1) = a - xJ a b c n := by
  induction n with
  | zero => simp [xJ, mom]
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, mul_mom_succ_eq ha hc hab]
    ring

theorem xJ_succ (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (j : ℕ) :
    xJ a b c (j + 1) = xJ a b c j * (1 - (b - a - c) / (b + c * j)) := by
  have hb : 0 < b + c * j := by
    have : 0 ≤ c * (j : ℝ) := by positivity
    linarith
  simp only [xJ, mom, ratio]
  push_cast
  field_simp
  ring

theorem xJ_le_exp (ha : 0 < a) (hc : 0 < c) (hd : 0 ≤ b - a - c) (n : ℕ) :
    xJ a b c n ≤ a * Real.exp (-((b - a - c) * ∑ i ∈ range n, 1 / (b + c * i))) := by
  have hab : a ≤ b := by linarith
  induction n with
  | zero => simp [xJ, mom]
  | succ n ih =>
    have hb : 0 < b + c * n := by
      have : 0 ≤ c * (n : ℝ) := by positivity
      linarith
    have hf0 : 0 ≤ 1 - (b - a - c) / (b + c * n) := by
      rw [sub_nonneg, div_le_one hb]
      have : 0 ≤ c * n := by positivity
      linarith
    have hf1 : 1 - (b - a - c) / (b + c * n) ≤ Real.exp (-((b - a - c) / (b + c * n))) := by
      have := Real.add_one_le_exp (-((b - a - c) / (b + c * n)))
      linarith
    have hx0 : 0 ≤ xJ a b c n := by
      have := mom_pos ha hc hab n
      unfold xJ
      positivity
    rw [xJ_succ ha hc hab, sum_range_succ, mul_add, neg_add, Real.exp_add, ← mul_assoc]
    calc xJ a b c n * (1 - (b - a - c) / (b + c * n))
        ≤ (a * Real.exp (-((b - a - c) * ∑ i ∈ range n, 1 / (b + c * i)))) *
            Real.exp (-((b - a - c) / (b + c * n))) :=
          mul_le_mul ih hf1 hf0 (by positivity)
      _ = a * Real.exp (-((b - a - c) * ∑ i ∈ range n, 1 / (b + c * i))) *
            Real.exp (-((b - a - c) * (1 / (b + c * n)))) := by rw [mul_one_div]

theorem harmonic_le_sum (hb : 0 < b) (hc : 0 < c) (n : ℕ) :
    (1 / (b + c)) * ∑ i ∈ range n, (1 / ((i : ℝ) + 1)) ≤ ∑ i ∈ range n, 1 / (b + c * i) := by
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  have h1 : 0 < b + c * i := by
    have : 0 ≤ c * (i : ℝ) := by positivity
    linarith
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) h1, one_mul]
  have : 0 ≤ (b * i + c : ℝ) := by positivity
  nlinarith

/-- **Divergence of the corrector mean**: for `k > 2(b − a − c) ≥ 0` and `T < 2a`, some `n` has
`T < k ∑_{j=1}^n m_j`. -/
theorem exists_sum_mom_gt (ha : 0 < a) (hc : 0 < c) (hd : 0 ≤ b - a - c) {k T : ℝ}
    (hk : 2 * (b - a - c) < k) (hT : T < 2 * a) :
    ∃ n : ℕ, T < k * ∑ j ∈ range n, mom a b c (j + 1) := by
  have hab : a ≤ b := by linarith
  have hb : 0 < b := by linarith
  have hk0 : 0 < k := by linarith
  have hH := Real.tendsto_sum_range_one_div_nat_succ_atTop
  rcases hd.lt_or_eq with hd | hd
  · -- `d > 0`: `x_n → 0`
    set d := b - a - c with hd_def
    have hε : 0 < a - d * T / k := by
      rcases le_or_gt T 0 with hT0 | hT0
      · have : d * T / k ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hd.le hT0) hk0.le
        linarith
      · have h1 : d * T / k < T / 2 := by
          rw [div_lt_div_iff₀ hk0 two_pos]
          nlinarith
        linarith
    -- choose `n` with the harmonic sum large
    set M := (b + c) / d * (Real.log a - Real.log (a - d * T / k) + 1) with hM
    obtain ⟨n, hn⟩ := (hH.eventually_gt_atTop M).exists
    refine ⟨n, ?_⟩
    have hsum := sum_mom_eq ha hc hab n
    have hx := xJ_le_exp ha hc hd.le n
    have hlow := harmonic_le_sum hb hc n
    have hexp : a * Real.exp (-(d * ∑ i ∈ range n, 1 / (b + c * i))) < a - d * T / k := by
      have h1 : Real.log a - Real.log (a - d * T / k) < d * ∑ i ∈ range n, 1 / (b + c * i) := by
        have h2 : d * (1 / (b + c) * ∑ i ∈ range n, 1 / ((i : ℝ) + 1)) ≤
            d * ∑ i ∈ range n, 1 / (b + c * i) := mul_le_mul_of_nonneg_left hlow hd.le
        have h3 : Real.log a - Real.log (a - d * T / k) + 1 ≤
            d * (1 / (b + c) * ∑ i ∈ range n, 1 / ((i : ℝ) + 1)) := by
          have hbc : 0 < b + c := by linarith
          have e : d * (1 / (b + c) * ∑ i ∈ range n, 1 / ((i : ℝ) + 1)) =
              (∑ i ∈ range n, 1 / ((i : ℝ) + 1)) / ((b + c) / d) := by field_simp
          rw [e, le_div_iff₀ (by positivity), mul_comm]
          exact hn.le
        linarith
      have h4 : Real.exp (-(d * ∑ i ∈ range n, 1 / (b + c * i))) <
          Real.exp (-(Real.log a - Real.log (a - d * T / k))) := Real.exp_lt_exp.2 (by linarith)
      rw [neg_sub, Real.exp_sub, Real.exp_log hε, Real.exp_log ha] at h4
      calc a * Real.exp (-(d * ∑ i ∈ range n, 1 / (b + c * i)))
          < a * ((a - d * T / k) / a) := mul_lt_mul_of_pos_left h4 ha
        _ = a - d * T / k := by field_simp
    have hxn : xJ a b c n < a - d * T / k := hx.trans_lt hexp
    have hS : d * T / k < d * ∑ j ∈ range n, mom a b c (j + 1) := by rw [hsum]; linarith
    rw [mul_div_assoc] at hS
    have hS' := lt_of_mul_lt_mul_left hS hd.le
    rw [div_lt_iff₀ hk0] at hS'
    linarith
  · -- `d = 0`: `m_j = a/(a + cj)` and the sum diverges
    have hxa : ∀ n, xJ a b c n = a := fun n => by
      have := sum_mom_eq ha hc hab n
      rw [← hd, zero_mul] at this
      linarith
    have hmom : ∀ j : ℕ, (a / (a + c)) * (1 / ((j : ℝ) + 1)) ≤ mom a b c (j + 1) := by
      intro j
      have h := hxa (j + 1)
      have h1 : 0 < a + c * ((j : ℝ) + 1) := by positivity
      have hm : mom a b c (j + 1) = a / (a + c * ((j : ℝ) + 1)) := by
        unfold xJ at h
        push_cast at h
        field_simp
        linarith
      rw [hm, div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) h1]
      have : 0 ≤ a * j := by positivity
      nlinarith
    obtain ⟨n, hn⟩ := (hH.eventually_gt_atTop (T / k * ((a + c) / a))).exists
    refine ⟨n, ?_⟩
    have hsum : (a / (a + c)) * ∑ i ∈ range n, (1 / ((i : ℝ) + 1)) ≤
        ∑ j ∈ range n, mom a b c (j + 1) := by
      rw [mul_sum]; exact sum_le_sum fun j _ => hmom j
    have hac : 0 < a / (a + c) := by positivity
    have h1 : T / k < (a / (a + c)) * ∑ i ∈ range n, (1 / ((i : ℝ) + 1)) := by
      have := mul_lt_mul_of_pos_left hn hac
      have e : a / (a + c) * (T / k * ((a + c) / a)) = T / k := by field_simp
      rwa [e] at this
    rw [div_lt_iff₀ hk0] at h1
    nlinarith

end Moments

/-! ### The corrector `q` -/

section Corrector

variable (a b c : ℝ)

/-- The corrector `q = K ∑_{j=1}^n r_j`. -/
def qP (K : ℝ) (n : ℕ) (v : ℝ) : ℝ := K * ∑ j ∈ range n, rP a b c (j + 1) v

/-- The derivative of the corrector. -/
def qP1 (K : ℝ) (n : ℕ) (v : ℝ) : ℝ := K * ∑ j ∈ range n, rP1 a b c (j + 1) v

/-- The second derivative of the corrector. -/
def qP2 (K : ℝ) (n : ℕ) (v : ℝ) : ℝ := K * ∑ j ∈ range n, rP2 a b c (j + 1) v

theorem hasDerivAt_qP (K : ℝ) (n : ℕ) (v : ℝ) : HasDerivAt (qP a b c K n) (qP1 a b c K n v) v := by
  have h := (HasDerivAt.sum (u := range n) (A := fun j => rP a b c (j + 1))
    (A' := fun j => rP1 a b c (j + 1) v) fun j _ => hasDerivAt_rP a b c (j + 1) v).const_mul K
  have e : qP a b c K n = fun y => K * (∑ i ∈ range n, rP a b c (i + 1)) y := by
    funext y; simp only [qP, Finset.sum_apply]
  rw [e]; exact h

theorem hasDerivAt_qP1 (K : ℝ) (n : ℕ) (v : ℝ) : HasDerivAt (qP1 a b c K n) (qP2 a b c K n v) v := by
  have h := (HasDerivAt.sum (u := range n) (A := fun j => rP1 a b c (j + 1))
    (A' := fun j => rP2 a b c (j + 1) v) fun j _ => hasDerivAt_rP1 a b c (j + 1) v).const_mul K
  have e : qP1 a b c K n = fun y => K * (∑ i ∈ range n, rP1 a b c (i + 1)) y := by
    funext y; simp only [qP1, Finset.sum_apply]
  rw [e]; exact h

theorem contDiff_qP {m : WithTop ℕ∞} (K : ℝ) (n : ℕ) : ContDiff ℝ m (qP a b c K n) := by
  have h : qP a b c K n = fun v => K * ∑ j ∈ range n, rP a b c (j + 1) v := rfl
  rw [h]
  exact contDiff_const.mul (ContDiff.sum fun j _ => contDiff_rP a b c (j + 1))

theorem continuous_qP1 (K : ℝ) (n : ℕ) : Continuous (qP1 a b c K n) := by
  have h : qP1 a b c K n = fun v => K * ∑ j ∈ range n, rP1 a b c (j + 1) v := rfl
  rw [h]
  exact continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_rP1 a b c (j + 1))

theorem gen_qP (hbc : ∀ j : ℕ, b + c * j ≠ 0) (K : ℝ) (n : ℕ) (v : ℝ) :
    (a - b * v) * qP1 a b c K n v + c * v * (1 - v) * qP2 a b c K n v =
      K * (∑ j ∈ range n, mom a b c (j + 1) - ∑ j ∈ range n, v ^ (j + 1)) := by
  have h : ∀ j ∈ range n, (a - b * v) * (K * rP1 a b c (j + 1) v) +
      c * v * (1 - v) * (K * rP2 a b c (j + 1) v) = K * (mom a b c (j + 1) - v ^ (j + 1)) :=
    fun j _ => by rw [← gen_rP a b c hbc]; ring
  simp only [qP1, qP2, mul_sum]
  rw [← sum_add_distrib, sum_congr rfl h, ← mul_sum, sum_sub_distrib]

end Corrector

/-! ### The drift inequality -/

/-- `1/(2m) ≤ (1 − v) + v^m` on `[0, 1]`, `m ≥ 1`. -/
theorem one_div_le_sub_add_pow {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    1 / (2 * m) ≤ (1 - v) + v ^ m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : 0 ≤ v ^ m := pow_nonneg hv0 m
  by_cases h : 1 / (2 * m) ≤ 1 - v
  · linarith
  · replace h := not_le.1 h
    have hb := one_add_mul_le_pow (a := v - 1) (by linarith) m
    rw [add_sub_cancel] at hb
    have h1 : (m : ℝ) * (1 - v) < 1 / 2 := by
      have : (1 - v) * (2 * m) < 1 := by rwa [lt_div_iff₀ (by positivity)] at h
      nlinarith
    have h2 : 1 / (2 * (m : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) two_pos]; linarith
    nlinarith

/-- The Itô drift of `log Z + s/3 + q(v)` along the separated two-force law, with `v = Y/(Y + Z)`. -/
def lyapDrift (κ ρL ρR : ℝ) (q1 q2 : ℝ → ℝ) (Z Y : ℝ) : ℝ :=
  (2 + ρR - κ / 2 + 1 / 3) / Z ^ 2 - ρL / (Y * Z) +
    2 / (Y * Z) * ((2 + ρL) / 2 - (4 + ρL + ρR) / 2 * (Y / (Y + Z))) * q1 (Y / (Y + Z)) +
      κ / 2 * q2 (Y / (Y + Z)) / (Y + Z) ^ 2

/-- The algebraic core of the drift identity, in the variables `v = Y/S` and `S = Y + Z`. -/
theorem drift_core {k ρL c0 K Sm G v S : ℝ} {n : ℕ} (hS : 0 < S) (hv0 : 0 < v) (hv1 : v < 1)
    (hK : K = k / 2) (hc0 : c0 = K * Sm - ρL / 2) (hG : G * (1 - v) = v - v ^ (n + 1)) :
    k / ((1 - v) * S) ^ 2 - ρL / ((v * S) * ((1 - v) * S)) +
        2 / ((v * S) * ((1 - v) * S)) * (K * (Sm - G)) =
      2 * c0 / ((v * S) * ((1 - v) * S)) + k * v ^ (n + 1) * S / ((v * S) * ((1 - v) * S) ^ 2) := by
  have h1v : 1 - v ≠ 0 := by linarith
  have hG' : G = (v - v ^ (n + 1)) / (1 - v) := by rw [← hG]; field_simp
  subst hK hc0 hG'
  have hv : v ≠ 0 := hv0.ne'
  have hS' : S ≠ 0 := hS.ne'
  field_simp
  ring

/-- **The Lyapunov corrector** (added here; B.5 records that the source has no proof of (B.3)). For `κ > 0` and weights
`ρ_L, ρ_R ≥ κ/2 − 2` there are a polynomial `q` (with derivatives `q1`, `q2`, bounded by `Q` on `[0, 1]`) and `λ > 0`
such that at every `Z, Y > 0`, with `v = Y/(Y + Z)`,
`λ (κ/2) (q1(v)/(Y + Z) − 1/Z)² ≤ lyapDrift κ ρ_L ρ_R q1 q2 Z Y`. -/
theorem exists_lyapunov {κ ρL ρR : ℝ} (hκ : 0 < κ) (hL : κ / 2 - 2 ≤ ρL) (hR : κ / 2 - 2 ≤ ρR) :
    ∃ (q q1 q2 : ℝ → ℝ) (lam Q : ℝ), 0 < lam ∧ 0 ≤ Q ∧ (∀ m : ℕ, ContDiff ℝ m q) ∧
      (∀ v, HasDerivAt q (q1 v) v) ∧ (∀ v, HasDerivAt q1 (q2 v) v) ∧
      (∀ v ∈ Icc (0 : ℝ) 1, |q v| ≤ Q) ∧
      ∀ Z Y : ℝ, 0 < Z → 0 < Y →
        lam * (κ / 2) * (q1 (Y / (Y + Z)) / (Y + Z) - 1 / Z) ^ 2 ≤ lyapDrift κ ρL ρR q1 q2 Z Y := by
  set a : ℝ := (2 + ρL) / 2 with ha_def
  set b : ℝ := (4 + ρL + ρR) / 2 with hb_def
  set c : ℝ := κ / 4 with hc_def
  set k : ℝ := 2 + ρR - κ / 2 + 1 / 3 with hk_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hc : 0 < c := by positivity
  have hd : 0 ≤ b - a - c := by rw [ha_def, hb_def, hc_def]; linarith
  have hk : 2 * (b - a - c) < k := by rw [ha_def, hb_def, hc_def, hk_def]; linarith
  have hT : ρL < 2 * a := by rw [ha_def]; linarith
  have hk0 : 0 < k := by linarith
  obtain ⟨n, hn⟩ := exists_sum_mom_gt ha hc hd hk hT
  have hbc : ∀ j : ℕ, b + c * j ≠ 0 := fun j => by
    have : 0 ≤ c * (j : ℝ) := by positivity
    linarith
  set K : ℝ := k / 2 with hK
  set Sm : ℝ := ∑ j ∈ range n, mom a b c (j + 1) with hSm
  set c0 : ℝ := K * Sm - ρL / 2 with hc0_def
  have hc0 : 0 < c0 := by rw [hc0_def, hK]; linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_qP a b c (m := 0) K n).continuous.continuousOn
  obtain ⟨C1, hC1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_qP1 a b c K n).continuousOn
  set Q1 : ℝ := max C1 0 with hQ1
  have hQ10 : 0 ≤ Q1 := le_max_right _ _
  set m0 : ℝ := min c0 (k / 2) with hm0
  have hm00 : 0 < m0 := lt_min hc0 (by linarith)
  set lam : ℝ := 2 * m0 / (((n : ℝ) + 1) * κ * (Q1 + 1) ^ 2) with hlam
  have hlam0 : 0 < lam := by positivity
  refine ⟨qP a b c K n, qP1 a b c K n, qP2 a b c K n, lam, max C 0, hlam0, le_max_right _ _,
    fun m => contDiff_qP a b c K n, hasDerivAt_qP a b c K n, hasDerivAt_qP1 a b c K n,
    fun v hv => by rw [← Real.norm_eq_abs]; exact (hC v hv).trans (le_max_left _ _),
    fun Z Y hZ hY => ?_⟩
  obtain ⟨v, S, rfl, rfl, hS, hv0, hv1⟩ : ∃ v S : ℝ, Y = v * S ∧ Z = (1 - v) * S ∧ 0 < S ∧ 0 < v ∧ v < 1 :=
    ⟨Y / (Y + Z), Y + Z, by field_simp, by field_simp; ring, by linarith, by positivity,
      by rw [div_lt_one (by linarith)]; linarith⟩
  have hsum : v * S + (1 - v) * S = S := by ring
  have hvv : v * S / S = v := by field_simp
  have h1v : 0 < 1 - v := by linarith
  have hG : (∑ j ∈ range n, v ^ (j + 1)) * (1 - v) = v - v ^ (n + 1) := by
    have h := geom_sum_mul_neg v n
    have e : ∑ j ∈ range n, v ^ (j + 1) = v * ∑ j ∈ range n, v ^ j := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [e, mul_assoc, h]; ring
  have hgen := gen_qP a b c hbc K n v
  unfold lyapDrift
  rw [hsum, hvv]
  have e1 : k / ((1 - v) * S) ^ 2 - ρL / (v * S * ((1 - v) * S)) +
      2 / (v * S * ((1 - v) * S)) * (a - b * v) * qP1 a b c K n v + κ / 2 * qP2 a b c K n v / S ^ 2 =
      k / ((1 - v) * S) ^ 2 - ρL / (v * S * ((1 - v) * S)) +
        2 / (v * S * ((1 - v) * S)) *
          ((a - b * v) * qP1 a b c K n v + c * v * (1 - v) * qP2 a b c K n v) := by
    rw [hc_def]; field_simp; ring
  rw [e1, hgen, drift_core hS hv0 hv1 rfl rfl hG]
  -- the final comparison
  have hq1 : |qP1 a b c K n v| ≤ Q1 := by
    rw [← Real.norm_eq_abs]; exact (hC1 v ⟨hv0.le, hv1.le⟩).trans (le_max_left _ _)
  have hsq : (qP1 a b c K n v * (1 - v) - 1) ^ 2 ≤ (Q1 + 1) ^ 2 := by
    have h1 : |qP1 a b c K n v * (1 - v) - 1| ≤ Q1 + 1 := by
      calc |qP1 a b c K n v * (1 - v) - 1| ≤ |qP1 a b c K n v * (1 - v)| + |(1 : ℝ)| := abs_sub _ _
        _ = |qP1 a b c K n v| * (1 - v) + 1 := by rw [abs_mul, abs_of_pos h1v, abs_one]
        _ ≤ Q1 * 1 + 1 := by gcongr; linarith
        _ = Q1 + 1 := by ring
    exact sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  have hB := one_div_le_sub_add_pow hv0.le hv1.le (m := n + 1) (by omega)
  push_cast at hB
  have key : lam * (κ / 2) * (qP1 a b c K n v * (1 - v) - 1) ^ 2 * v ≤ 2 * c0 * (1 - v) + k * v ^ (n + 1) := by
    have hpow := pow_nonneg hv0.le (n + 1)
    calc lam * (κ / 2) * (qP1 a b c K n v * (1 - v) - 1) ^ 2 * v
        ≤ lam * (κ / 2) * (Q1 + 1) ^ 2 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq (by positivity)) hv1.le hv0.le (by positivity)
      _ = 2 * m0 * (1 / (2 * ((n : ℝ) + 1))) := by rw [hlam]; field_simp
      _ ≤ 2 * m0 * ((1 - v) + v ^ (n + 1)) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ 2 * c0 * (1 - v) + k * v ^ (n + 1) := by
          have h1 : m0 ≤ c0 := min_le_left _ _
          have h2 : m0 ≤ k / 2 := min_le_right _ _
          nlinarith
  have hL' : lam * (κ / 2) * (qP1 a b c K n v / S - 1 / ((1 - v) * S)) ^ 2 =
      lam * (κ / 2) * (qP1 a b c K n v * (1 - v) - 1) ^ 2 * v / (v * ((1 - v) * S) ^ 2) := by
    field_simp
  have hR' : 2 * c0 / (v * S * ((1 - v) * S)) + k * v ^ (n + 1) * S / (v * S * ((1 - v) * S) ^ 2) =
      (2 * c0 * (1 - v) + k * v ^ (n + 1)) / (v * ((1 - v) * S) ^ 2) := by
    field_simp
  rw [hL', hR']
  exact div_le_div_of_nonneg_right key (by positivity)

end InteractingSLE.ZhanGT4.A5Clear
