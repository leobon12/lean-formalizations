import SmallGammaGeodesics.Probes.Basic
import SmallGammaGeodesics.Probes.Decay
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Algebra.Order.Round

/-!
# The probe kernel and its derivatives on strips (GA2 D4.2)

* `probeH_eq_probeF`: `H_{j,a}(z) = F_j(z-a) - F_j(z+a)` with
  `F_j(w) = -ℓ_j ∑_{k=1}^{2^{j+1}} q(kℓ_j) cos(kπw)` (product to sum).
* `probeF_eq_probeG`: `F_j = G_{j,0}`, where `G_{j,d}(w) = -(ℓ_j/2) ∑_{|k| ≤ 2^{j+1}+2}
  q(kℓ_j) (iπk)^d e^{iπkw}` (symmetrization; `q` is even and vanishes near `0` and off `(-2,2)`).
* `iteratedDeriv_probeG`: `G_{j,0}^{(d)} = G_{j,d}`; `iteratedDeriv_probeH`:
  `H_{j,a}^{(d)}(z) = G_{j,d}(z-a) - G_{j,d}(z+a)`.
* `norm_probeG_le`: on `|Im w| ≤ Kℓ_j`,
  `‖G_{j,d}(w)‖ ≤ C_{d,K} ℓ_j^{-d} (ℓ_j / max(ℓ_j, dist(Re w, 2ℤ)))²`, from the decay lemma with
  `p = 2` applied to the multiplier `s ↦ e^{-π s t} q(s) (iπs)^d`, `t = Im w / ℓ_j ∈ [-K, K]`.
* `lemma41_envelope`: the envelope bound of Lemma 4.1 (GA2 (c)'s statement, with the junk-free
  `envelope`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset
open scoped Real

namespace SmallGammaGeodesics

/-! ### Product to sum and exponential form -/

/-- `F_j(w) = -ℓ_j ∑_{k=1}^{2^{j+1}} q(kℓ_j) cos(kπw)`. -/
def probeF (j : ℕ) (w : ℂ) : ℂ :=
  -(ell j : ℂ) * ∑ k ∈ Icc (1 : ℕ) (2 ^ (j + 1)),
    (probeQ ((k : ℝ) * ell j) : ℂ) * Complex.cos ((k : ℂ) * π * w)

/-- Product to sum: `H_{j,a}(z) = F_j(z-a) - F_j(z+a)`. -/
theorem probeH_eq_probeF (j : ℕ) (a : ℝ) (z : ℂ) :
    probeH j a z = probeF j (z - a) - probeF j (z + a) := by
  unfold probeH probeF
  rw [← mul_sub, ← sum_sub_distrib]
  have hℓ : (ell j : ℂ) ≠ 0 := by exact_mod_cast (ell_pos j).ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show -((2 / ell j : ℝ) : ℂ) = -(ell j : ℂ) * (2 / (ell j : ℂ) ^ 2) by
    push_cast; field_simp, mul_assoc]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : (k : ℂ) ≠ 0 := by
    have := (mem_Icc.mp hk).1
    exact_mod_cast (show k ≠ 0 by omega)
  rw [← mul_sub, Complex.cos_sub_cos]
  have h1 : ((k : ℂ) * π * (z - a) + (k : ℂ) * π * (z + a)) / 2 = (k : ℂ) * π * z := by ring
  have h2 : ((k : ℂ) * π * (z - a) - (k : ℂ) * π * (z + a)) / 2 = -((k : ℂ) * π * a) := by ring
  rw [h1, h2, Complex.sin_neg]
  unfold probeQ
  push_cast
  field_simp

/-- The exponential form `G_{j,d}(w) = -(ℓ_j/2) ∑_{|k| ≤ 2^{j+1}+2} q(kℓ_j) (iπk)^d e^{iπkw}`. -/
def probeG (j d : ℕ) (w : ℂ) : ℂ :=
  -((ell j / 2 : ℝ) : ℂ) * ∑ k ∈ Icc (-((2 ^ (j + 1) + 2 : ℕ) : ℤ)) ((2 ^ (j + 1) + 2 : ℕ) : ℤ),
    (probeQ ((k : ℝ) * ell j) : ℂ) * (Complex.I * π * k) ^ d * Complex.exp (Complex.I * π * k * w)

theorem probeQ_int_mul_ell_eq_zero {j : ℕ} {k : ℤ} (hk : 2 ^ (j + 1) ≤ |k|) :
    probeQ ((k : ℝ) * ell j) = 0 := by
  refine probeQ_eq_zero_of_le_abs ?_
  rw [abs_mul, abs_of_pos (ell_pos j)]
  have h1 : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ |(k : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hk
  have h2 : ell j * 2 ^ j = 1 := ell_mul_pow j
  push_cast at h1
  rw [pow_succ] at h1
  nlinarith [ell_pos j]

/-- `F_j = G_{j,0}`. -/
theorem probeF_eq_probeG (j : ℕ) (w : ℂ) : probeF j w = probeG j 0 w := by
  unfold probeF probeG
  rw [sum_Icc_int_eq]
  simp only [Int.cast_zero, zero_mul, probeQ_eq_zero_of_abs_le (show |(0 : ℝ)| ≤ 1 / 2 by simp),
    Complex.ofReal_zero, zero_mul, zero_add, pow_zero, mul_one]
  -- restrict the frequency range to `k ≤ 2^{j+1}`
  have hsub : Icc (1 : ℕ) (2 ^ (j + 1)) ⊆ Icc (1 : ℕ) (2 ^ (j + 1) + 2) := by
    intro k hk
    simp only [mem_Icc] at hk ⊢
    omega
  rw [← sum_subset hsub]
  · rw [mul_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    push_cast
    simp only [neg_mul, probeQ_neg]
    rw [Complex.cos]
    ring_nf
  · intro k hk hk'
    simp only [mem_Icc, not_and_or, not_le] at hk hk'
    have hq : probeQ ((k : ℝ) * ell j) = 0 := by
      have hkk : 2 ^ (j + 1) ≤ |(k : ℤ)| := by
        rw [Nat.abs_cast]
        exact_mod_cast (show 2 ^ (j + 1) ≤ k by omega)
      simpa using probeQ_int_mul_ell_eq_zero hkk
    push_cast
    simp only [neg_mul, probeQ_neg, hq]
    simp

theorem hasDerivAt_probeG (j d : ℕ) (w : ℂ) :
    HasDerivAt (probeG j d) (probeG j (d + 1) w) w := by
  unfold probeG
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun k _ => ?_)
  have h := ((((hasDerivAt_id w).const_mul (Complex.I * π * k)).cexp)).const_mul
    ((probeQ ((k : ℝ) * ell j) : ℂ) * (Complex.I * π * k) ^ d)
  refine (h.congr_deriv ?_)
  simp only [id]
  ring

/-- `G_{j,0}^{(d)} = G_{j,d}`. -/
theorem iteratedDeriv_probeG (j d : ℕ) : iteratedDeriv d (probeG j 0) = probeG j d := by
  induction d with
  | zero => rw [iteratedDeriv_zero]
  | succ d ih =>
    rw [iteratedDeriv_succ, ih]
    funext w
    exact (hasDerivAt_probeG j d w).deriv

theorem contDiff_probeG (j d : ℕ) {n : ℕ∞} : ContDiff ℂ n (probeG j d) := by
  unfold probeG
  refine contDiff_const.mul (ContDiff.sum fun k _ => ?_)
  exact contDiff_const.mul ((contDiff_const.mul contDiff_id).cexp)

theorem differentiable_probeG (j d : ℕ) : Differentiable ℂ (probeG j d) :=
  fun w => (hasDerivAt_probeG j d w).differentiableAt

/-- `H_{j,a}^{(d)}(z) = G_{j,d}(z-a) - G_{j,d}(z+a)`. -/
theorem iteratedDeriv_probeH (j : ℕ) (a : ℝ) (d : ℕ) (z : ℂ) :
    iteratedDeriv d (probeH j a) z = probeG j d (z - a) - probeG j d (z + a) := by
  have hfun : probeH j a = fun z => probeG j 0 (z - a) - probeG j 0 (z + a) := by
    funext z
    rw [probeH_eq_probeF, probeF_eq_probeG, probeF_eq_probeG]
  have h1 : ContDiff ℂ (d : ℕ∞) (fun z => probeG j 0 (z - a)) :=
    (contDiff_probeG j 0).comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℂ (d : ℕ∞) (fun z => probeG j 0 (z + a)) :=
    (contDiff_probeG j 0).comp (contDiff_id.add contDiff_const)
  rw [hfun, iteratedDeriv_fun_sub h1.contDiffAt h2.contDiffAt,
    iteratedDeriv_comp_sub_const d (probeG j 0) (a : ℂ),
    iteratedDeriv_comp_add_const d (probeG j 0) (a : ℂ), iteratedDeriv_probeG]

theorem differentiable_probeH (j : ℕ) (a : ℝ) : Differentiable ℂ (probeH j a) := by
  have hfun : probeH j a = fun z => probeG j 0 (z - a) - probeG j 0 (z + a) := by
    funext z
    rw [probeH_eq_probeF, probeF_eq_probeG, probeF_eq_probeG]
  rw [hfun]
  exact ((differentiable_probeG j 0).comp (differentiable_id.sub_const _)).sub
    ((differentiable_probeG j 0).comp (differentiable_id.add_const _))

/-! ### The multipliers `s ↦ e^{-π t s} q(s) (iπs)^d` -/

/-- `r_d(s) = q(s) (iπs)^d`, smooth with support in `[-2, 2]`. -/
def probeR (d : ℕ) (s : ℝ) : ℂ := (probeQ s : ℂ) * (Complex.I * π * s) ^ d

/-- The multiplier `m_{d,t}(s) = e^{-π t s} q(s) (iπs)^d`. -/
def probeMult (d : ℕ) (t s : ℝ) : ℂ := Real.exp (-(π * t) * s) • probeR d s

theorem contDiff_probeR (d : ℕ) {n : ℕ∞} : ContDiff ℝ n (probeR d) := by
  unfold probeR
  exact contDiff_probeQ_complex.mul
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).pow d)

theorem probeR_eq_zero {d : ℕ} {s : ℝ} (hs : 2 ≤ |s|) : probeR d s = 0 := by
  unfold probeR
  rw [probeQ_eq_zero_of_le_abs hs]
  simp

theorem contDiff_probeMult (d : ℕ) (t : ℝ) {n : ℕ∞} : ContDiff ℝ n (probeMult d t) := by
  unfold probeMult
  exact (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).smul (contDiff_probeR d)

theorem probeMult_eq_zero {d : ℕ} {t s : ℝ} (hs : 2 ≤ |s|) : probeMult d t s = 0 := by
  unfold probeMult
  rw [probeR_eq_zero hs, smul_zero]

/-- Uniform bound on the first three derivatives of `r_d`. -/
theorem exists_bound_probeR (d : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i ≤ 2, ∀ s, ‖iteratedDeriv i (probeR d) s‖ ≤ R := by
  have hc : HasCompactSupport (probeR d) := hasCompactSupport_of_abs fun s hs => probeR_eq_zero hs
  obtain ⟨R₀, hR₀⟩ := exists_bound_iteratedDeriv (contDiff_probeR d) hc 0
  obtain ⟨R₁, hR₁⟩ := exists_bound_iteratedDeriv (contDiff_probeR d) hc 1
  obtain ⟨R₂, hR₂⟩ := exists_bound_iteratedDeriv (contDiff_probeR d) hc 2
  have h0 : 0 ≤ R₀ := le_trans (norm_nonneg _) (hR₀ 0)
  have h1 : 0 ≤ R₁ := le_trans (norm_nonneg _) (hR₁ 0)
  have h2 : 0 ≤ R₂ := le_trans (norm_nonneg _) (hR₂ 0)
  refine ⟨R₀ + R₁ + R₂, by positivity, fun i hi s => ?_⟩
  interval_cases i
  · linarith [hR₀ s]
  · linarith [hR₁ s]
  · linarith [hR₂ s]

/-- Derivatives of `r_d` vanish off `[-2, 2]`. -/
theorem iteratedDeriv_probeR_eq_zero {d : ℕ} (i : ℕ) {s : ℝ} (hs : 2 < |s|) :
    iteratedDeriv i (probeR d) s = 0 := by
  refine iteratedDeriv_eq_zero_of_notMem_tsupport i ?_
  intro hmem
  have := tsupport_subset_of_abs (f := probeR d) (A := 2) (fun x hx => probeR_eq_zero hx) hmem
  rw [Set.mem_Icc] at this
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h] at hs
    linarith [this.2]
  · rw [abs_of_neg h] at hs
    linarith [this.1]

/-- `‖r_d^{(i)}(s)‖ e^{-π t s} ≤ R e^{2πK}` for `|t| ≤ K`. -/
theorem norm_iteratedDeriv_probeR_mul_exp_le {d : ℕ} {R K t : ℝ} (hK : 0 ≤ K)
    (hR : ∀ i ≤ 2, ∀ s, ‖iteratedDeriv i (probeR d) s‖ ≤ R) (ht : |t| ≤ K) {i : ℕ} (hi : i ≤ 2)
    (s : ℝ) : ‖iteratedDeriv i (probeR d) s‖ * Real.exp (-(π * t) * s) ≤
      R * Real.exp (2 * π * K) := by
  rcases le_or_gt |s| 2 with hs | hs
  · have hexp : Real.exp (-(π * t) * s) ≤ Real.exp (2 * π * K) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : -(π * t) * s ≤ |π * t| * |s| := by
        rw [← abs_mul]
        exact (neg_le_abs _).trans' (by rw [neg_mul])
      have h2 : |π * t| * |s| ≤ (π * K) * 2 := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        exact mul_le_mul (mul_le_mul_of_nonneg_left ht Real.pi_pos.le) hs (abs_nonneg _)
          (by positivity)
      linarith
    have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR 0 (by norm_num) 0)
    calc ‖iteratedDeriv i (probeR d) s‖ * Real.exp (-(π * t) * s)
        ≤ R * Real.exp (-(π * t) * s) :=
          mul_le_mul_of_nonneg_right (hR i hi s) (Real.exp_pos _).le
      _ ≤ R * Real.exp (2 * π * K) := mul_le_mul_of_nonneg_left hexp hR0
  · have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR 0 (by norm_num) 0)
    rw [iteratedDeriv_probeR_eq_zero i hs, norm_zero, zero_mul]
    positivity

theorem norm_probeMult_le {d : ℕ} {R K t : ℝ} (hK : 0 ≤ K)
    (hR : ∀ i ≤ 2, ∀ s, ‖iteratedDeriv i (probeR d) s‖ ≤ R) (ht : |t| ≤ K) (s : ℝ) :
    ‖probeMult d t s‖ ≤ R * Real.exp (2 * π * K) := by
  have := norm_iteratedDeriv_probeR_mul_exp_le hK hR ht (i := 0) (by norm_num) s
  rw [iteratedDeriv_zero] at this
  unfold probeMult
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact this

theorem norm_iteratedDeriv_two_probeMult_le {d : ℕ} {R K t : ℝ} (hK : 0 ≤ K)
    (hR : ∀ i ≤ 2, ∀ s, ‖iteratedDeriv i (probeR d) s‖ ≤ R) (ht : |t| ≤ K) (s : ℝ) :
    ‖iteratedDeriv 2 (probeMult d t) s‖ ≤ (1 + π * K) ^ 2 * (R * Real.exp (2 * π * K)) := by
  have hE : ContDiff ℝ 2 (fun s => Real.exp (-(π * t) * s)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hr : ContDiff ℝ 2 (probeR d) := contDiff_probeR d
  have hL := norm_iteratedFDeriv_smul_le hE hr s (n := 2) le_rfl
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hL
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul] at hL
  have hpt : ∀ i ≤ 2, ‖(-(π * t)) ^ i * Real.exp (-(π * t) * s)‖ *
      ‖iteratedDeriv (2 - i) (probeR d) s‖ ≤ (π * K) ^ i * (R * Real.exp (2 * π * K)) := by
    intro i hi
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_pow,
      abs_neg, abs_mul, abs_of_pos Real.pi_pos, mul_assoc]
    refine mul_le_mul (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left ht Real.pi_pos.le) i) ?_ (by positivity) (by positivity)
    rw [mul_comm]
    exact norm_iteratedDeriv_probeR_mul_exp_le hK hR ht (by omega) s
  unfold probeMult
  have hB : 0 ≤ R * Real.exp (2 * π * K) := by
    have := le_trans (norm_nonneg _) (hR 0 (by norm_num) 0)
    positivity
  calc _ ≤ _ := hL
    _ ≤ ∑ x ∈ range (2 + 1), ((Nat.choose 2 x : ℕ) : ℝ) * ((π * K) ^ x * (R * Real.exp (2 * π * K))) := by
        refine sum_le_sum fun x hx => ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hpt x (by simp only [mem_range] at hx; omega))
          (by positivity)
    _ = (1 + π * K) ^ 2 * (R * Real.exp (2 * π * K)) := by
        simp only [sum_range_succ, sum_range_zero]
        norm_num
        ring

/-! ### From the exponential form to the decay lemma -/

theorem exp_int_mul_pi_sub (k r : ℤ) (u : ℝ) :
    Complex.exp ((k : ℂ) * ((π * (u - 2 * r) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * π * k * u) := by
  have : (k : ℂ) * ((π * (u - 2 * r) : ℝ) : ℂ) * Complex.I =
      Complex.I * π * k * u + ((-(k * r) : ℤ) : ℂ) * (2 * π * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The `k`-th term of `G_{j,d}(u + iv)` as a term of a `trigSum`. -/
theorem probeG_term_eq (j d : ℕ) (u v : ℝ) (r k : ℤ) :
    (probeQ ((k : ℝ) * ell j) : ℂ) * (Complex.I * π * k) ^ d *
        Complex.exp (Complex.I * π * k * ((u : ℂ) + (v : ℂ) * Complex.I)) =
      ((ell j : ℂ)⁻¹) ^ d * (probeMult d (v / ell j) ((k : ℝ) / ((2 ^ j : ℕ) : ℝ)) *
        Complex.exp ((k : ℂ) * ((π * (u - 2 * r) : ℝ) : ℂ) * Complex.I)) := by
  have hℓ : ell j ≠ 0 := (ell_pos j).ne'
  have hℓc : (ell j : ℂ) ≠ 0 := by exact_mod_cast hℓ
  have hks : (k : ℝ) / ((2 ^ j : ℕ) : ℝ) = (k : ℝ) * ell j := by
    unfold ell
    push_cast
    ring
  rw [hks, exp_int_mul_pi_sub]
  unfold probeMult probeR
  rw [Complex.real_smul, Complex.ofReal_exp]
  have hexp : Complex.exp (Complex.I * π * k * ((u : ℂ) + (v : ℂ) * Complex.I)) =
      Complex.exp (((-(π * (v / ell j)) * ((k : ℝ) * ell j) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * π * k * u) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hexp]
  have hpow : ((ell j : ℂ)⁻¹) ^ d * (Complex.I * π * ((k : ℝ) * ell j : ℝ)) ^ d =
      (Complex.I * π * k) ^ d := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp
  rw [← hpow]
  push_cast
  ring

/-- `G_{j,d}(u + iv) = -(ℓ_j/2) ℓ_j^{-d} S(θ)`, with `S` the trigonometric sum of the multiplier
`m_{d, v/ℓ_j}` and `θ = π(u - 2r)` for any integer `r`. -/
theorem probeG_eq_trigSum (j d : ℕ) (u v : ℝ) (r : ℤ) :
    probeG j d ((u : ℂ) + (v : ℂ) * Complex.I) =
      -((ell j / 2 : ℝ) : ℂ) * (((ell j : ℂ)⁻¹) ^ d *
        trigSum (2 ^ j) (2 ^ (j + 1) + 2) (probeMult d (v / ell j)) (π * (u - 2 * r))) := by
  unfold probeG trigSum
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [probeG_term_eq j d u v r k]

/-- Real-variable bookkeeping for the decay bound. -/
theorem decay_to_envelope {n ℓ S δ d₀ M₀ M₂ : ℝ} (hnr : 1 ≤ n) (hℓ : ℓ * n = 1)
    (hS0 : 0 ≤ S) (hd₀ : 0 ≤ d₀) (hδ : d₀ ≤ δ) (hM₀ : 0 ≤ M₀) (hM₂ : 0 ≤ M₂)
    (h1 : S ≤ (2 * (2 * n) + 1) * M₀)
    (h2 : (2 * δ) ^ 2 * S ≤ (2 * (2 * n) + 2 + 1) * M₂ / n ^ 2) :
    ℓ / 2 * S ≤ (5 * M₀ + 7 * M₂) / 2 * (ℓ / max ℓ d₀) ^ 2 := by
  have hℓpos : 0 < ℓ := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hℓ' : ℓ = n⁻¹ := by field_simp; linarith
  rcases le_or_gt d₀ ℓ with hdl | hdl
  · rw [max_eq_left hdl, div_self hℓpos.ne', one_pow, mul_one]
    have : ℓ * (2 * (2 * n) + 1) ≤ 5 := by nlinarith
    nlinarith
  · rw [max_eq_right hdl.le]
    have hδpos : 0 < δ := lt_of_lt_of_le hℓpos (hdl.le.trans hδ)
    have hd₀pos : 0 < d₀ := lt_trans hℓpos hdl
    -- from h2: S ≤ 7 M₂ ℓ / (4 δ²)
    have hS : S ≤ 7 * M₂ * ℓ / (4 * δ ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : (2 * (2 * (n : ℝ)) + 2 + 1) * M₂ / (n : ℝ) ^ 2 ≤ 7 * M₂ * ℓ := by
        rw [div_le_iff₀ (by positivity), hℓ']
        field_simp
        nlinarith
      nlinarith
    have hδd : ℓ ^ 2 / δ ^ 2 ≤ ℓ ^ 2 / d₀ ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hd₀ hδ 2)
    rw [div_pow]
    calc ℓ / 2 * S ≤ ℓ / 2 * (7 * M₂ * ℓ / (4 * δ ^ 2)) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 7 * M₂ / 8 * (ℓ ^ 2 / δ ^ 2) := by field_simp; ring
      _ ≤ 7 * M₂ / 8 * (ℓ ^ 2 / d₀ ^ 2) := mul_le_mul_of_nonneg_left hδd (by positivity)
      _ ≤ (5 * M₀ + 7 * M₂) / 2 * (ℓ ^ 2 / d₀ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith

/-- **Envelope bound for `G_{j,d}`**: on `|Im w| ≤ Kℓ_j`,
`‖G_{j,d}(w)‖ ≤ C ℓ_j^{-d} (ℓ_j / max(ℓ_j, dist(Re w, 2ℤ)))²`. -/
theorem norm_probeG_le (K : ℝ) (hK : 0 < K) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (w : ℂ), |w.im| ≤ K * ell j →
      ‖probeG j d w‖ ≤ C * (ell j)⁻¹ ^ d *
        (ell j / max (ell j) (Metric.infDist w.re (Set.range fun m : ℤ => (2 * m : ℝ)))) ^ 2 := by
  obtain ⟨R, hR0, hR⟩ := exists_bound_probeR d
  have hM₀0 : 0 ≤ R * Real.exp (2 * π * K) := by positivity
  have hM₂0 : 0 ≤ (1 + π * K) ^ 2 * (R * Real.exp (2 * π * K)) := by positivity
  refine ⟨(5 * (R * Real.exp (2 * π * K)) + 7 * ((1 + π * K) ^ 2 * (R * Real.exp (2 * π * K)))) / 2,
    by positivity, fun j w hw => ?_⟩
  have hℓ := ell_pos j
  have hta : |w.im / ell j| ≤ K := by
    rw [abs_div, abs_of_pos hℓ, div_le_iff₀ hℓ]
    exact hw
  obtain ⟨r, hr⟩ : ∃ r : ℤ, r = round (w.re / 2) := ⟨_, rfl⟩
  have hδ1 : |w.re - 2 * r| ≤ 1 := by
    have := abs_sub_round (w.re / 2)
    rw [← hr] at this
    have h2 : w.re - 2 * r = 2 * (w.re / 2 - r) := by ring
    rw [h2, abs_mul, abs_two]
    linarith
  have hd₀δ : Metric.infDist w.re (Set.range fun m : ℤ => (2 * m : ℝ)) ≤ |w.re - 2 * r| := by
    rw [← Real.dist_eq]
    exact Metric.infDist_le_dist_of_mem ⟨r, rfl⟩
  have hθ : |π * (w.re - 2 * r)| ≤ π := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hn : 0 < 2 ^ j := by positivity
  have hsupp : ∀ s : ℝ, ((2 ^ (j + 1) : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) < |s| →
      probeMult d (w.im / ell j) s = 0 := by
    intro s hs
    refine probeMult_eq_zero ?_
    have : ((2 ^ (j + 1) : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) = 2 := by
      push_cast
      rw [pow_succ]
      field_simp
    linarith
  have hdec := decay_lemma (p := 2) (R := 2 ^ (j + 1)) (N := 2 ^ (j + 1) + 2) hn le_rfl
    (contDiff_probeMult d (w.im / ell j)) hsupp (norm_probeMult_le hK.le hR hta)
    (norm_iteratedDeriv_two_probeMult_le hK.le hR hta) hθ
  set S := ‖trigSum (2 ^ j) (2 ^ (j + 1) + 2) (probeMult d (w.im / ell j)) (π * (w.re - 2 * r))‖
    with hS
  have hG : ‖probeG j d w‖ = ell j / 2 * (ell j)⁻¹ ^ d * S := by
    have hw' : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
    rw [hS]
    conv_lhs => rw [hw', probeG_eq_trigSum j d w.re w.im r]
    rw [norm_mul, norm_neg, norm_mul, norm_pow, norm_inv, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hℓ, abs_of_pos (half_pos hℓ)]
    ring
  rw [hG]
  have h1 := hdec.1
  have h2 := hdec.2
  have hθabs : 2 * |π * (w.re - 2 * r)| / π = 2 * |w.re - 2 * r| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hθabs] at h2
  push_cast at h1 h2
  have e : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
  rw [e] at h1 h2
  have hℓn : ell j * 2 ^ j = 1 := ell_mul_pow j
  have key := decay_to_envelope (n := (2 : ℝ) ^ j) (one_le_pow₀ (by norm_num)) hℓn
    (norm_nonneg _) Metric.infDist_nonneg hd₀δ hM₀0 hM₂0 h1 h2
  have hpow : 0 ≤ (ell j)⁻¹ ^ d := pow_nonneg (inv_nonneg.mpr hℓ.le) d
  calc ell j / 2 * (ell j)⁻¹ ^ d * S = (ell j)⁻¹ ^ d * (ell j / 2 * S) := by ring
    _ ≤ (ell j)⁻¹ ^ d * ((5 * (R * Real.exp (2 * π * K)) + 7 * ((1 + π * K) ^ 2 *
          (R * Real.exp (2 * π * K)))) / 2 * (ell j / max (ell j)
          (Metric.infDist w.re (Set.range fun m : ℤ => (2 * m : ℝ)))) ^ 2) :=
        mul_le_mul_of_nonneg_left key hpow
    _ = _ := by ring

/-- The envelope bound on strips for every real `a` (the constraint `a ∈ [0,1]` of Lemma 4.1 is
not needed): `‖H_{j,a}^{(k)}(z)‖ ≤ C ℓ_j^{-k} E_{j,a}(Re z)` for `k ≤ 4`, `|Im z| ≤ Kℓ_j`. -/
theorem norm_iteratedDeriv_probeH_le (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (a : ℝ), ∀ k ≤ 4, ∀ z : ℂ, |z.im| ≤ K * ell j →
      ‖iteratedDeriv k (probeH j a) z‖ ≤ C * (ell j)⁻¹ ^ k * envelope j a z.re := by
  have hall := fun d => norm_probeG_le K hK d
  choose C hC0 hC using hall
  refine ⟨∑ d ∈ range 5, C d, sum_nonneg fun d _ => hC0 d, fun j a k hk z hz => ?_⟩
  have hCk : C k ≤ ∑ d ∈ range 5, C d :=
    single_le_sum (fun d _ => hC0 d) (mem_range.mpr (by omega))
  rw [iteratedDeriv_probeH]
  have hm : ‖probeG j k (z - a)‖ ≤ C k * (ell j)⁻¹ ^ k * (ell j / max (ell j)
      (Metric.infDist (z.re - a) (Set.range fun m : ℤ => (2 * m : ℝ)))) ^ 2 := by
    have := hC k j (z - a) (by simpa using hz)
    simpa using this
  have hp : ‖probeG j k (z + a)‖ ≤ C k * (ell j)⁻¹ ^ k * (ell j / max (ell j)
      (Metric.infDist (z.re + a) (Set.range fun m : ℤ => (2 * m : ℝ)))) ^ 2 := by
    have := hC k j (z + a) (by simpa using hz)
    simpa using this
  have hE : 0 ≤ envelope j a z.re := by unfold envelope; positivity
  calc ‖probeG j k (z - a) - probeG j k (z + a)‖
      ≤ ‖probeG j k (z - a)‖ + ‖probeG j k (z + a)‖ := norm_sub_le _ _
    _ ≤ C k * (ell j)⁻¹ ^ k * envelope j a z.re := by
        unfold envelope
        linarith
    _ ≤ (∑ d ∈ range 5, C d) * (ell j)⁻¹ ^ k * envelope j a z.re := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCk
          (pow_nonneg (inv_nonneg.mpr (ell_pos j).le) k)) hE

/-- **Lemma 4.1, envelopes on strips** (GA2 (c)'s `lemma41_envelope`; `envelope` is the junk-free
envelope of the authorized correction): `‖H_{j,a}^{(k)}(z)‖ ≤ C ℓ_j^{-k} E_{j,a}(Re z)` for
`k ≤ 4` and `|Im z| ≤ Kℓ_j`. -/
theorem lemma41_envelope (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, ∀ j : ℕ, ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ k ≤ 4, ∀ z : ℂ, |z.im| ≤ K * ell j →
      ‖iteratedDeriv k (probeH j a) z‖ ≤ C * (ell j)⁻¹ ^ k * envelope j a z.re := by
  obtain ⟨C, _, hC⟩ := norm_iteratedDeriv_probeH_le K hK
  exact ⟨C, fun j a _ => hC j a⟩

end SmallGammaGeodesics
