import GaussianLQG.Uniform.Holder.Lp

/-!
# U12: one level of the chaining and the finest link, in `L^p`

Phase B, packet PB-U12 (ledger U12, Finding `fd:U12`: the exponent bookkeeping `1 − 4ξ − 2/q`;
ledger row U12 of §`subsec:ledger-cons`). With `L = log 2`, `D = 2 L K₀ / p + C_s`, `ξ ≤ 1/32` and
`p ≥ 16`:

* `level_real`, `level_bound`: for a family `J` of moved `2^{-K} R_{2,1}` with `|J| ≤ 4|A| 4^K` and
  a weight `2^{κ/2}`, `κ ≤ K ≤ n`,
  `E (λ_n^{-1} 2^{κ/2} Xdec)^p ≤ 4|A|² C₁ C_s^p e^{p(-(L/4) K + D √K)}`.
  The inputs are the exponential moment of the coarse field (`lintegral_exp_supQ_le`: the first
  `2ξ`), the moments `E L_{n−K}(R_{2,1})^p ≤ C₁ λ_{n−K}^p` (ledger U10), the scale relation
  `λ_{n−K} ≤ C_s 2^{2ξK} e^{C_s √K} λ_n` (ledger U11(a): the second `2ξ`) and the union over
  `≤ 4|A| 4^K` crossings (`2/p`): the exponent is `p L K (κ/(2K) − 1 + 4ξ + 2/p) ≤ −p L K / 4`;
* `link_real`, `link_bound` (ledger change (v)): the finest link
  `E (λ_n^{-1} e^{ξ sup_Q |φ_{0,n}|} 2^{-(n−1)/2})^p ≤ |A| e^{p(C_s/32 + L)} e^{p(-(L/4)n + D√n)}`,
  from `λ_n ≥ e^{-ξ(C_s + 2(n+1) L)}` (ledger U11(c)); the exponent is `1/2 − 4ξ ≥ 3/8`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform
namespace Holder

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-! ### Exponential forms -/

lemma sqrt_two_pow_eq (k : ℕ) : √2 ^ k = Real.exp (Real.log 2 * k / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num), ← Real.exp_nat_mul]
  congr 1; ring

lemma inv_two_pow_eq' (K : ℕ) : (2 : ℝ)⁻¹ ^ K = Real.exp (-(Real.log 2) * K) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num), inv_pow]

lemma four_rpow_eq (x : ℝ) : (4 : ℝ) ^ x = Real.exp (2 * Real.log 2 * x) := by
  rw [Real.rpow_def_of_pos (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring_nf

lemma four_pow_eq (K : ℕ) : (4 : ℝ) ^ K = Real.exp (2 * Real.log 2 * K) := by
  rw [← four_rpow_eq, Real.rpow_natCast]

lemma two_rpow_eq (x : ℝ) : (2 : ℝ) ^ x = Real.exp (Real.log 2 * x) :=
  Real.rpow_def_of_pos (by norm_num) x

lemma sqrt_exp_eq (x : ℝ) : √(Real.exp x) = Real.exp (x / 2) := by
  rw [show Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) by rw [← Real.exp_add]; ring_nf,
    Real.sqrt_mul_self (Real.exp_pos _).le]

/-! ### One level -/

/-- the real inequality of one level -/
lemma level_real {ξ K₀ Cs C₁ a₁ cd lam lamK : ℝ} {p K κ : ℕ} (hξ1 : ξ ≤ 1 / 32)
    (hp16 : 16 ≤ p) (hκ : κ ≤ K) (hCs : 0 < Cs) (hC₁ : 0 ≤ C₁) (ha₁ : 0 ≤ a₁)
    (hcd : cd ≤ 4 * a₁ * 4 ^ K) (hlam : 0 < lam) (hlamK0 : 0 ≤ lamK)
    (hlamK : lamK ≤ Cs * (2 : ℝ) ^ (2 * ξ * K) * Real.exp (Cs * √(K : ℝ)) * lam) :
    (lam⁻¹ * √2 ^ κ) ^ p * (a₁ * (4 : ℝ) ^ ((p : ℝ) * ξ * K + K₀ * √(K : ℝ))) *
        (cd * (((2 : ℝ)⁻¹ ^ K) ^ p * (C₁ * lamK ^ p))) ≤
      4 * a₁ ^ 2 * C₁ * Cs ^ p *
        Real.exp (p * (-(Real.log 2 / 4) * K + (2 * Real.log 2 * K₀ / p + Cs) * √(K : ℝ))) := by
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  have hp0 : (0 : ℝ) < p := by have : (16 : ℝ) ≤ p := by exact_mod_cast hp16
                               linarith
  set g := Cs * (2 : ℝ) ^ (2 * ξ * K) * Real.exp (Cs * √(K : ℝ)) * lam with hg
  have hg0 : 0 ≤ g := by positivity
  -- the monotone bound
  have h1 : (lam⁻¹ * √2 ^ κ) ^ p * (a₁ * (4 : ℝ) ^ ((p : ℝ) * ξ * K + K₀ * √(K : ℝ))) *
        (cd * (((2 : ℝ)⁻¹ ^ K) ^ p * (C₁ * lamK ^ p))) ≤
      (lam⁻¹ * √2 ^ κ) ^ p * (a₁ * (4 : ℝ) ^ ((p : ℝ) * ξ * K + K₀ * √(K : ℝ))) *
        ((4 * a₁ * 4 ^ K) * (((2 : ℝ)⁻¹ ^ K) ^ p * (C₁ * g ^ p))) := by
    gcongr
  refine h1.trans ?_
  -- the exponential form
  have hlam1 : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam.ne'
  have e1 : (lam⁻¹ * √2 ^ κ) ^ p * (a₁ * (4 : ℝ) ^ ((p : ℝ) * ξ * K + K₀ * √(K : ℝ))) *
      ((4 * a₁ * 4 ^ K) * (((2 : ℝ)⁻¹ ^ K) ^ p * (C₁ * g ^ p))) =
      4 * a₁ ^ 2 * C₁ * Cs ^ p * (lam⁻¹ * lam) ^ p *
        ((√2 ^ κ * (2 : ℝ) ^ (2 * ξ * K) * Real.exp (Cs * √(K : ℝ)) * (2 : ℝ)⁻¹ ^ K) ^ p *
          ((4 : ℝ) ^ ((p : ℝ) * ξ * K + K₀ * √(K : ℝ)) * 4 ^ K)) := by
    rw [hg]; ring
  rw [e1, hlam1, one_pow, mul_one, sqrt_two_pow_eq, two_rpow_eq, inv_two_pow_eq',
    four_rpow_eq, four_pow_eq]
  simp only [← Real.exp_add, ← Real.exp_nat_mul]
  gcongr
  -- the exponent: `p L K (κ/(2K) − 1 + 4ξ + 2/p) ≤ −p L K / 4`
  have hpK : (p : ℝ) * κ ≤ p * K := by
    have : (κ : ℝ) ≤ K := by exact_mod_cast hκ
    exact mul_le_mul_of_nonneg_left this hp0.le
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hpξK : (p : ℝ) * ξ * K ≤ p * K / 32 := by
    have := mul_le_mul_of_nonneg_left hξ1 (mul_nonneg hp0.le hK0)
    nlinarith
  have h2K : 2 * (K : ℝ) ≤ p * K / 8 := by
    have : (16 : ℝ) ≤ p := by exact_mod_cast hp16
    nlinarith
  have key : 0 ≤ L * (p * K - p * K / 4 - p * κ / 2 - 4 * (p * ξ * K) - 2 * K) :=
    mul_nonneg hL0.le (by linarith)
  have e2 : (p : ℝ) * (-(L / 4) * K + (2 * L * K₀ / p + Cs) * √(K : ℝ)) -
      (p * (L * κ / 2 + L * (2 * ξ * K) + Cs * √(K : ℝ) + -L * K) +
        (2 * L * ((p : ℝ) * ξ * K + K₀ * √(K : ℝ)) + 2 * L * K)) =
      L * (p * K - p * K / 4 - p * κ / 2 - 4 * (p * ξ * K) - 2 * K) := by
    field_simp
    ring
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **One level of the chaining in `L^p`** -/
theorem level_bound (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 32) {p : ℕ}
    (hp16 : 16 ≤ p) (hpξ : (p : ℝ) * ξ ≤ 3 / 2) {A : Finset ℂ} {Q : Set ℂ} (hQ : IsCompact Q)
    (hne : Q.Nonempty) {K₀ : ℝ}
    (hexp : ∀ (K : ℕ) (γ : ℝ), 0 ≤ γ → γ ≤ 3 / 2 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * supQ Q (fun z => phiMN W P 0 K z ω))) ∂P ≤
        ENNReal.ofReal (A.card * (4 : ℝ) ^ (γ * K + K₀ * √(K : ℝ))))
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hmom : ∀ m : ℕ, ∫⁻ ω, rectLen ξ (fun x => phiMN W P 0 m x ω) (rectAB 2 1) ^ p ∂P ≤
      ENNReal.ofReal (C₁ * lambdaN ξ W P m ^ p))
    {Cs : ℝ} (hCs : 0 < Cs) {n : ℕ} (hlam : ∀ m, 0 < lambdaN ξ W P m)
    (hsc : ∀ k : ℕ, k ≤ n → lambdaN ξ W P (n - k) ≤
      Cs * (2 : ℝ) ^ (2 * ξ * k) * Real.exp (Cs * √(k : ℝ)) * lambdaN ξ W P n)
    {K κ : ℕ} (hKn : K ≤ n) (hκ : κ ≤ K) {ι : Type*} (J : Finset ι) (j : ι → Circle × ℂ)
    (hJ : (J.card : ℝ) ≤ 4 * A.card * 4 ^ K) :
    ∫⁻ ω, (ENNReal.ofReal ((lambdaN ξ W P n)⁻¹ * √2 ^ κ) * Xdec ξ W P Q n p K J j ω) ^ p ∂P ≤
      ENNReal.ofReal (4 * A.card ^ 2 * C₁ * Cs ^ p *
        Real.exp (p * (-(Real.log 2 / 4) * K + (2 * Real.log 2 * K₀ / p + Cs) * √(K : ℝ)))) := by
  have hp0 : p ≠ 0 := by omega
  set lam := lambdaN ξ W P n
  have hw : 0 ≤ lam⁻¹ * √2 ^ κ := by have := hlam n; positivity
  simp_rw [mul_pow]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  have hX := lintegral_Xdec_pow_le (ξ := ξ) hW hQ hne hKn hp0 J j
    (hexp K ((p : ℝ) * ξ) (by positivity) hpξ) (hmom (n - K))
  have hlamK := hlam (n - K)
  calc ENNReal.ofReal (lam⁻¹ * √2 ^ κ) ^ p * ∫⁻ ω, Xdec ξ W P Q n p K J j ω ^ p ∂P
      ≤ ENNReal.ofReal (lam⁻¹ * √2 ^ κ) ^ p *
          (ENNReal.ofReal (A.card * (4 : ℝ) ^ ((p : ℝ) * ξ * K + K₀ * √(K : ℝ))) *
            ENNReal.ofReal (J.card * (((2 : ℝ)⁻¹ ^ K) ^ p *
              (C₁ * lambdaN ξ W P (n - K) ^ p)))) := by gcongr
    _ = ENNReal.ofReal ((lam⁻¹ * √2 ^ κ) ^ p *
          (A.card * (4 : ℝ) ^ ((p : ℝ) * ξ * K + K₀ * √(K : ℝ))) *
            (J.card * (((2 : ℝ)⁻¹ ^ K) ^ p * (C₁ * lambdaN ξ W P (n - K) ^ p)))) := by
        rw [← ENNReal.ofReal_pow hw, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (level_real hξ1 hp16 hκ hCs hC₁ (Nat.cast_nonneg _)
          hJ (hlam n) hlamK.le (hsc K hKn))

/-! ### The finest link -/

/-- the real inequality of the finest link -/
lemma link_real {ξ K₀ Cs a₁ lam : ℝ} {p n : ℕ} (hξ1 : ξ ≤ 1 / 32)
    (hp16 : 16 ≤ p) (hn : 1 ≤ n) (hCs : 0 < Cs) (ha₁ : 0 ≤ a₁) (hlam : 0 < lam)
    (hlow : Real.exp (-(ξ * (Cs + 2 * (n + 1) * Real.log 2))) ≤ lam) :
    (lam⁻¹ * √((2 : ℝ)⁻¹ ^ (n - 1))) ^ p * (a₁ * (4 : ℝ) ^ ((p : ℝ) * ξ * n + K₀ * √(n : ℝ))) ≤
      a₁ * Real.exp (p * (Cs / 32 + Real.log 2)) *
        Real.exp (p * (-(Real.log 2 / 4) * n + (2 * Real.log 2 * K₀ / p + Cs) * √(n : ℝ))) := by
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  have hp0 : (0 : ℝ) < p := by have : (16 : ℝ) ≤ p := by exact_mod_cast hp16
                               linarith
  have hinv : lam⁻¹ ≤ Real.exp (ξ * (Cs + 2 * (n + 1) * L)) := by
    rw [show Real.exp (ξ * (Cs + 2 * (n + 1) * L)) = (Real.exp (-(ξ * (Cs + 2 * (n + 1) * L))))⁻¹
      by rw [Real.exp_neg, inv_inv]]
    exact inv_anti₀ (Real.exp_pos _) hlow
  have hh : √((2 : ℝ)⁻¹ ^ (n - 1)) = Real.exp (-L * ((n - 1 : ℕ) : ℝ) / 2) := by
    rw [inv_two_pow_eq', sqrt_exp_eq]
  have hn1 : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub hn]; push_cast; ring
  have h1 : (lam⁻¹ * √((2 : ℝ)⁻¹ ^ (n - 1))) ^ p *
        (a₁ * (4 : ℝ) ^ ((p : ℝ) * ξ * n + K₀ * √(n : ℝ))) ≤
      (Real.exp (ξ * (Cs + 2 * (n + 1) * L)) * √((2 : ℝ)⁻¹ ^ (n - 1))) ^ p *
        (a₁ * (4 : ℝ) ^ ((p : ℝ) * ξ * n + K₀ * √(n : ℝ))) := by
    gcongr
  refine h1.trans ?_
  rw [hh, four_rpow_eq, mul_left_comm, mul_assoc a₁]
  simp only [← Real.exp_add, ← Real.exp_nat_mul]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) ha₁
  rw [hn1]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsn : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hξn : ξ * n ≤ n / 32 := by nlinarith
  have hξC : ξ * Cs ≤ Cs / 32 := by nlinarith
  have key : 0 ≤ (p : ℝ) * (Cs / 32 - ξ * Cs) + p * Cs * √(n : ℝ) +
      p * L * (1 / 2 + n / 4 - 4 * (ξ * n) - 2 * ξ) := by
    have h3 : 0 ≤ 1 / 2 + (n : ℝ) / 4 - 4 * (ξ * n) - 2 * ξ := by nlinarith
    have := mul_nonneg (mul_nonneg hp0.le hL0.le) h3
    have := mul_nonneg hp0.le (by linarith : (0 : ℝ) ≤ Cs / 32 - ξ * Cs)
    have := mul_nonneg (mul_nonneg hp0.le hCs.le) hsn
    linarith
  have e2 : (p : ℝ) * (Cs / 32 + L) +
      p * (-(L / 4) * n + (2 * L * K₀ / p + Cs) * √(n : ℝ)) -
      (p * (ξ * (Cs + 2 * (n + 1) * L) + -L * (n - 1) / 2) +
        2 * L * ((p : ℝ) * ξ * n + K₀ * √(n : ℝ))) =
      (p : ℝ) * (Cs / 32 - ξ * Cs) + p * Cs * √(n : ℝ) +
        p * L * (1 / 2 + n / 4 - 4 * (ξ * n) - 2 * ξ) := by
    field_simp
    ring
  linarith

/-- **The finest link in `L^p`** (ledger change (v)) -/
theorem link_bound {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 32) {p : ℕ}
    (hp16 : 16 ≤ p) (hpξ : (p : ℝ) * ξ ≤ 3 / 2) {A : Finset ℂ} {Q : Set ℂ} {K₀ : ℝ}
    (hexp : ∀ (K : ℕ) (γ : ℝ), 0 ≤ γ → γ ≤ 3 / 2 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * supQ Q (fun z => phiMN W P 0 K z ω))) ∂P ≤
        ENNReal.ofReal (A.card * (4 : ℝ) ^ (γ * K + K₀ * √(K : ℝ))))
    {Cs : ℝ} (hCs : 0 < Cs) {n : ℕ} (hn : 1 ≤ n) (hlam : 0 < lambdaN ξ W P n)
    (hlow : Real.exp (-(ξ * (Cs + 2 * (n + 1) * Real.log 2))) ≤ lambdaN ξ W P n) :
    ∫⁻ ω, ENNReal.ofReal ((lambdaN ξ W P n)⁻¹ * (Real.exp (ξ * supQ Q
        (fun z => phiMN W P 0 n z ω)) * √((2 : ℝ)⁻¹ ^ (n - 1)))) ^ p ∂P ≤
      ENNReal.ofReal (A.card * Real.exp (p * (Cs / 32 + Real.log 2)) *
        Real.exp (p * (-(Real.log 2 / 4) * n + (2 * Real.log 2 * K₀ / p + Cs) * √(n : ℝ)))) := by
  set lam := lambdaN ξ W P n
  have hw : 0 ≤ lam⁻¹ * √((2 : ℝ)⁻¹ ^ (n - 1)) := by positivity
  have hpt : ∀ ω, ENNReal.ofReal (lam⁻¹ * (Real.exp (ξ * supQ Q
      (fun z => phiMN W P 0 n z ω)) * √((2 : ℝ)⁻¹ ^ (n - 1)))) ^ p =
      ENNReal.ofReal ((lam⁻¹ * √((2 : ℝ)⁻¹ ^ (n - 1))) ^ p) *
        ENNReal.ofReal (Real.exp (((p : ℝ) * ξ) * supQ Q (fun z => phiMN W P 0 n z ω))) := by
    intro ω
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_assoc, Real.exp_nat_mul]
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal ((lam⁻¹ * √((2 : ℝ)⁻¹ ^ (n - 1))) ^ p) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (((p : ℝ) * ξ) *
          supQ Q (fun z => phiMN W P 0 n z ω))) ∂P
      ≤ ENNReal.ofReal ((lam⁻¹ * √((2 : ℝ)⁻¹ ^ (n - 1))) ^ p) *
          ENNReal.ofReal (A.card * (4 : ℝ) ^ ((p : ℝ) * ξ * n + K₀ * √(n : ℝ))) := by
        gcongr
        exact hexp n _ (by positivity) hpξ
    _ = ENNReal.ofReal ((lam⁻¹ * √((2 : ℝ)⁻¹ ^ (n - 1))) ^ p *
          (A.card * (4 : ℝ) ^ ((p : ℝ) * ξ * n + K₀ * √(n : ℝ)))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
        (link_real hξ1 hp16 hn hCs (Nat.cast_nonneg _) hlam hlow)

end Holder
end Uniform
end GaussianLQG
