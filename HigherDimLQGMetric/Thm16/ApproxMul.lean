import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Almost multiplicative positive functions are comparable to a real power. -/

set_option autoImplicit false
noncomputable section

open Filter Set Topology

namespace HigherDimLQGMetric

private theorem quasi_add_lower (f : ℝ → ℝ) {k : ℝ}
    (hlo : ∀ x y, f x + f y - k ≤ f (x + y)) (t : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * f t - (n : ℝ) * k ≤ f ((n + 1 : ℕ) * t) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hs := hlo (((n + 1 : ℕ) : ℝ) * t) t
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hs ih ⊢
      linarith only [ih, hs]

private theorem quasi_add_subadditive (f : ℝ → ℝ) {k : ℝ}
    (h : ∀ x y, f (x + y) ≤ f x + f y + k) (t : ℝ) :
    Subadditive (fun n : ℕ => f (n * t) + k) := by
  intro m n
  have hs := h (m * t) (n * t)
  simpa only [Nat.cast_add, add_mul] using (show
    f (m * t + n * t) + k ≤ (f (m * t) + k) + (f (n * t) + k) by linarith)

private theorem quasi_add_bddBelow (f : ℝ → ℝ) {k : ℝ} (hk : 0 ≤ k)
    (hlo : ∀ x y, f x + f y - k ≤ f (x + y)) (t : ℝ) :
    BddBelow (range fun n : ℕ => (f (n * t) + k) / n) := by
  refine ⟨min 0 (f t - k), ?_⟩
  rintro x ⟨n, rfl⟩
  cases n with
  | zero => simp
  | succ n =>
      have hp : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      have hm := quasi_add_lower f hlo t n
      apply (min_le_right 0 (f t - k)).trans
      apply (le_div_iff₀ hp).2
      push_cast at hm ⊢
      nlinarith only [hm, hk]

private theorem quasi_add_linear (f : ℝ → ℝ) {k δ M : ℝ} (hk : 0 ≤ k)
    (hlo : ∀ x y, f x + f y - k ≤ f (x + y))
    (hup : ∀ x y, f (x + y) ≤ f x + f y + k)
    (hδ : 0 < δ) (hloc : ∀ t ∈ Icc (-δ) δ, |f t| ≤ M) :
    ∃ a : ℝ, ∀ t : ℝ, |f t - a * t| ≤ k := by
  let A : ℝ → ℝ := fun t => (quasi_add_subadditive f hup t).lim
  have hlim (t : ℝ) : Tendsto (fun n : ℕ => (f (n * t) + k) / n) atTop (𝓝 (A t)) :=
    (quasi_add_subadditive f hup t).tendsto_lim (quasi_add_bddBelow f hk hlo t)
  have hlimf (t : ℝ) : Tendsto (fun n : ℕ => f (n * t) / n) atTop (𝓝 (A t)) := by
    simpa only [add_div, add_sub_cancel_right, sub_zero] using
      (hlim t).sub (tendsto_const_div_atTop_nhds_zero_nat k)
  have hAbounds (t : ℝ) : f t - k ≤ A t ∧ A t ≤ f t + k := by
    constructor
    · apply ge_of_tendsto (hlim t)
      apply Filter.eventually_atTop.2
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have hp : (0 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
      have hm := quasi_add_lower f hlo t m
      apply (le_div_iff₀ hp).2
      push_cast at hm ⊢
      nlinarith only [hm, hk]
    · have hh := (quasi_add_subadditive f hup t).lim_le_div
        (quasi_add_bddBelow f hk hlo t) (n := 1) (by norm_num)
      simpa [A] using hh
  have hAadd (s t : ℝ) : A (s + t) = A s + A t := by
    have hplus : A (s + t) ≤ A s + A t := by
      have hev : (fun n : ℕ => f (n * (s + t)) / n) ≤ᶠ[atTop]
          (fun n => f (n * s) / n + f (n * t) / n + k / n) := by
        apply Filter.eventually_atTop.2
        refine ⟨1, fun n hn => ?_⟩
        have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hh := hup (n * s) (n * t)
        rw [← mul_add] at hh
        simpa only [add_div] using (div_le_div_of_nonneg_right hh hp.le)
      simpa only [add_zero] using
        (le_of_tendsto_of_tendsto (hlimf (s + t))
          (((hlimf s).add (hlimf t)).add (tendsto_const_div_atTop_nhds_zero_nat k)) hev)
    have hminus : A s + A t ≤ A (s + t) := by
      have hev : (fun n : ℕ => f (n * s) / n + f (n * t) / n - k / n) ≤ᶠ[atTop]
          (fun n => f (n * (s + t)) / n) := by
        apply Filter.eventually_atTop.2
        refine ⟨1, fun n hn => ?_⟩
        have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hh := hlo (n * s) (n * t)
        rw [← mul_add] at hh
        simpa only [add_div, sub_div] using (div_le_div_of_nonneg_right hh hp.le)
      simpa only [sub_zero] using
        (le_of_tendsto_of_tendsto
          (((hlimf s).add (hlimf t)).sub (tendsto_const_div_atTop_nhds_zero_nat k))
          (hlimf (s + t)) hev)
    exact le_antisymm hplus hminus
  let F : ℝ →+ ℝ := AddMonoidHom.mk' A hAadd
  have hFbound : Bornology.IsBounded (F '' Icc (-δ) δ) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M + k, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    have hb := hAbounds t
    have hf := hloc t ht
    change |A t| ≤ M + k
    rw [abs_le] at hf ⊢
    constructor <;> linarith only [hb.1, hb.2, hf.1, hf.2]
  have hFc : Continuous F :=
    F.continuous_of_isBounded_nhds_zero (Icc_mem_nhds_iff.mpr ⟨by linarith, hδ⟩) hFbound
  refine ⟨F 1, fun t => ?_⟩
  have hlin : F t = t * F 1 := by
    simpa [smul_eq_mul] using map_real_smul F hFc t 1
  have hb := hAbounds t
  change |f t - F 1 * t| ≤ k
  rw [mul_comm (F 1) t, ← hlin, abs_le]
  change f t - k ≤ F t ∧ F t ≤ f t + k at hb
  constructor <;> linarith only [hb.1, hb.2]

theorem powerLaw_of_approxMul {c : ℝ → ℝ} (hc : ∀ r, 0 < r → 0 < c r) {K : ℝ} (hK : 1 ≤ K)
    (hmul : ∀ r s, 0 < r → 0 < s → c r * c s ≤ K * c (r * s) ∧ c (r * s) ≤ K * (c r * c s))
    (hloc : ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Icc (1 / 2 : ℝ) 1, B⁻¹ ≤ c r ∧ c r ≤ B) :
    ∃ α B' : ℝ, 0 < B' ∧ ∀ r, 0 < r → B'⁻¹ * r ^ α ≤ c r ∧ c r ≤ B' * r ^ α := by
  obtain ⟨B,hB0,hB⟩ := hloc
  have hB1 : 1 ≤ B := by
    have hh := hB 1 (by norm_num : (1:ℝ) ∈ Icc (1/2:ℝ) 1)
    have hle : B⁻¹ ≤ B := hh.1.trans hh.2
    have hprod := mul_le_mul_of_nonneg_right hle hB0.le
    rw [inv_mul_cancel₀ hB0.ne'] at hprod
    nlinarith only [hprod, hB0]
  let k : ℝ := Real.log K
  have hk : 0 ≤ k := Real.log_nonneg hK
  let f : ℝ → ℝ := fun t => Real.log (c (Real.exp t))
  have hflo (s t : ℝ) : f s + f t - k ≤ f (s + t) := by
    let r := Real.exp s
    let u := Real.exp t
    have hr : 0 < r := Real.exp_pos s
    have hu : 0 < u := Real.exp_pos t
    have hc1 := hc r hr
    have hc2 := hc u hu
    have hc3 := hc (r*u) (mul_pos hr hu)
    have hh := (hmul r u hr hu).1
    have hl := Real.log_le_log (mul_pos hc1 hc2) hh
    rw [Real.log_mul hc1.ne' hc2.ne', Real.log_mul (by positivity : K ≠ 0) hc3.ne'] at hl
    dsimp [f,k]
    rw [Real.exp_add]
    linarith only [hl]
  have hfup (s t : ℝ) : f (s + t) ≤ f s + f t + k := by
    let r := Real.exp s
    let u := Real.exp t
    have hr : 0 < r := Real.exp_pos s
    have hu : 0 < u := Real.exp_pos t
    have hc1 := hc r hr
    have hc2 := hc u hu
    have hc3 := hc (r*u) (mul_pos hr hu)
    have hh := (hmul r u hr hu).2
    have hl := Real.log_le_log hc3 hh
    rw [Real.log_mul (by positivity : K ≠ 0) (mul_pos hc1 hc2).ne',
      Real.log_mul hc1.ne' hc2.ne'] at hl
    dsimp [f,k]
    rw [Real.exp_add]
    linarith only [hl]
  have hδ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hneg (t : ℝ) (ht : t ∈ Icc (-Real.log 2) 0) :
      -Real.log B ≤ f t ∧ f t ≤ Real.log B := by
    have he : Real.exp t ∈ Icc (1 / 2 : ℝ) 1 := by
      constructor
      · have hh := Real.exp_le_exp.mpr ht.1
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
        simpa only [one_div] using hh
      · simpa only [Real.exp_le_one_iff] using ht.2
    have hh := hB (Real.exp t) he
    constructor
    · have hlog := Real.log_le_log (inv_pos.mpr hB0) hh.1
      simpa [f, Real.log_inv] using hlog
    · exact Real.log_le_log (hc _ (Real.exp_pos t)) hh.2
  have hlocal : ∀ t ∈ Icc (-Real.log 2) (Real.log 2),
      |f t| ≤ 2 * Real.log B + k := by
    intro t ht
    by_cases htn : t ≤ 0
    · have hh := hneg t ⟨ht.1, htn⟩
      rw [abs_le]
      constructor <;> linarith only [hh.1, hh.2, hk, Real.log_nonneg hB1]
    · have hh := hneg (-t) ⟨by linarith [ht.2], by linarith⟩
      have h0 := hneg 0 ⟨by linarith [hδ], le_rfl⟩
      have hsumlo := hflo t (-t)
      have hsumup := hfup t (-t)
      simp only [add_neg_cancel] at hsumlo hsumup
      rw [abs_le]
      constructor <;> linarith only [hh.1, hh.2, h0.1, h0.2, hsumlo, hsumup]
  obtain ⟨α, hα⟩ := quasi_add_linear f hk hflo hfup hδ hlocal
  refine ⟨α, Real.exp k, Real.exp_pos k, fun r hr => ?_⟩
  have hh := hα (Real.log r)
  simp only [f, Real.exp_log hr] at hh
  rw [abs_le] at hh
  have hpow : r ^ α = Real.exp (α * Real.log r) := by
    rw [Real.rpow_def_of_pos hr, mul_comm]
  constructor
  · have hlo : α * Real.log r - k ≤ Real.log (c r) := by linarith only [hh.1]
    have he := Real.exp_le_exp.mpr hlo
    rw [Real.exp_sub, Real.exp_log (hc r hr)] at he
    simpa only [hpow, div_eq_mul_inv, mul_comm] using he
  · have hup : Real.log (c r) ≤ k + α * Real.log r := by linarith only [hh.2]
    have he := Real.exp_le_exp.mpr hup
    rw [Real.exp_add, Real.exp_log (hc r hr)] at he
    simpa only [hpow] using he

end HigherDimLQGMetric
