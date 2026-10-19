import GaussianLQG.Uniform.Thm20.Defs
import GaussianLQG.Uniform.RSW.Law

/-!
# Lemma 24 and the `φ/ψ` comparison of DDDF Theorem 20, with explicit uniform constants

Phase B, packet PB-U9 (ledger U2, U9 and Finding `fd:opaque`). Three lemmas of `LQGMetric` have
explicit witnesses hidden behind an `∃` placed after `ξ` and the white noise:
`LambdaN_le_LambdaNPsi` (`LQGMetric/Papers/DDDF/T20.lean`, witness `e^{2|ξ|M}`),
`L24.psi_memLp_variance` and `dddf_lemma24` (`LQGMetric/Papers/DDDF/L24.lean`, witnesses
`2ξ² log 2 + 2M_L` and `√(2C)/p`), with `M_L = C₅(ξ²+1)/c₅` from Prop 5
(`L24.integral_sq_sub_le`, `LQGMetric/Papers/DDDF/L24Psi.lean`). Here their proofs are restated
with the witnesses in the statement (`…_of`), and the uniform versions take the Prop 5 constants
before the probability space (`dddf_prop5_XAB_W`, `exists_tail_XAB_unif_W`,
`GaussianLQG/Uniform/RSW/Law.lean`, law transfer, ledger Recipe B1) and evaluate the formulas at
`ξs` (ledger Recipe M):

* `LambdaN_le_LambdaNPsi_unif`: `Λ_n(φ,p) ≤ e^{2ξs M(p)} Λ_n(ψ,p/2)` for all `ξ ∈ (0, ξs]`, `n`
  and every white noise (DDDF (2.29), ledger U2);
* `psi_variance_unif`: `Var log L^{(k)}_{1,1}(ψ) ≤ C_V max(k,1)` (DDDF l. 1064–1065);
* `lemma24_unif`: `Λ_n(ψ,p) ≤ e^{C_t √n}` for `n ≥ 1` (DDDF Lemma 24, (5.56)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.DDDF.T20 LQGMetric.DDDF.L24

section Explicit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **`Λ_n(φ, p) ≤ e^{2|ξ|M} Λ_n(ψ, p/2)` from `P(X_{1,1} > M) ≤ p/2`** (the proof of
`LambdaN_le_LambdaNPsi`, `LQGMetric/Papers/DDDF/T20.lean`, DDDF l. 1212 and (2.29), with the Prop 5
quantity `M` as a parameter). -/
theorem LambdaN_le_LambdaNPsi_of (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {p : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 2) {M : ℝ} (hM0 : 0 ≤ M)
    (hε : P {ω | ENNReal.ofReal M <
      XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) 1 1} ≤
        ENNReal.ofReal (p / 2)) (n : ℕ) :
    LambdaN ξ W P n (ENNReal.ofReal p) ≤
      exp (|ξ| * M) ^ 2 * LambdaNPsi ξ Q W P n (ENNReal.ofReal (p / 2)) := by
  have := hW.isProbabilityMeasure
  have hq0 : 0 < p / 2 := by positivity
  set e := exp (|ξ| * M) with he
  have he0 : 0 < e := exp_pos _
  have hqq : ENNReal.ofReal (p / 2) + ENNReal.ofReal (p / 2) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_add hq0.le hq0.le]; congr 1; ring
  have hp1 : ENNReal.ofReal p < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  have hbar : 1 - ENNReal.ofReal p + ENNReal.ofReal (p / 2) = 1 - ENNReal.ofReal (p / 2) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp0.le, ← ENNReal.ofReal_add (by linarith)
      hq0.le, ← ENNReal.ofReal_sub _ hq0.le]
    congr 1; ring
  have hq1 : ENNReal.ofReal (p / 2) < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  have hq0' : 0 < ENNReal.ofReal (p / 2) := ENNReal.ofReal_pos.2 hq0
  have hp0' : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp0
  have hk : ∀ n, ellBarN ξ W P n (ENNReal.ofReal p) / ellN ξ W P n (ENNReal.ofReal p) ≤
      e ^ 2 * (ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (p / 2)) /
        ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (p / 2))) := by
    intro n
    have hvφ := isPhiVersion_phiMN hW (Nat.zero_le n)
    have hvψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
    -- `ℓ_n(ψ, p/2) ≤ e ℓ_n(φ, p)`
    have h1 := ellQ_psi_le_of_tail hW Q (ξ := ξ) zero_le_one zero_le_one hM0 hε hq0'
      (by rw [hqq]; exact hp1) n
    rw [hqq] at h1
    -- `ℓ̄_n(φ, p) ≤ e ℓ̄_n(ψ, p/2)`
    have h2 := ellQ_phi_le_of_tail hW Q (ξ := ξ) zero_le_one zero_le_one hM0 hε
      (p := 1 - ENNReal.ofReal p) (tsub_pos_of_lt hp1)
      (by rw [hbar]; exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0'.ne') n
    rw [hbar] at h2
    have hψ0 := ellQ_pos (P := P) (ξ := ξ) hvψ.cont hvψ.meas hq0' hq1
    have hψb : 0 ≤ ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (p / 2)) :=
      hψ0.le.trans (ellQ_le_ellBarQ hq0 (by linarith))
    set a := ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (p / 2))
    set b := ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (p / 2))
    have h2' : ellBarN ξ W P n (ENNReal.ofReal p) ≤ e * a := h2
    have h1' : e⁻¹ * b ≤ ellN ξ W P n (ENNReal.ofReal p) := by
      rw [inv_mul_le_iff₀ he0]; exact h1
    calc ellBarN ξ W P n (ENNReal.ofReal p) / ellN ξ W P n (ENNReal.ofReal p)
        ≤ (e * a) / (e⁻¹ * b) := div_le_div₀ (by positivity) h2' (by positivity) h1'
      _ = e ^ 2 * (a / b) := by field_simp
  refine Finset.sup'_le _ _ fun k hk' => (hk k).trans ?_
  exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun k =>
    ellBarQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) (ENNReal.ofReal (p / 2)) /
      ellQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) (ENNReal.ofReal (p / 2))) hk') (by positivity)

/-- **`E (log L^{(k)}(ψ) − log L^{(k)}(φ))² ≤ C(ξ²+1)/c`** from a Prop 5 tail with constants
`(C, c)` (the proof of `L24.integral_sq_sub_le`, `LQGMetric/Papers/DDDF/L24Psi.lean`). -/
theorem integral_sq_sub_le_of (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {C c : ℝ}
    (hC : 0 < C) (hc : 0 < c)
    (h5 : ∀ x : ℝ, 0 < x → P {ω | ENNReal.ofReal x ≤
      XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) 1 1} ≤
        ENNReal.ofReal (C * exp (-(c * x ^ 2)))) (k : ℕ) :
    Integrable (fun ω => (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2) P ∧
      ∫ ω, (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2 ∂P ≤
        C * (ξ ^ 2 + 1) / c := by
  set D := fun ω => (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2
  have hmψ : Measurable (logLenPsi ξ Q W P k) :=
    (measurable_lenObs (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).cont
      (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).meas _).log
  have hmφ : Measurable fun ω => Real.log (lenN ξ W P 1 1 k ω) :=
    (measurable_lenMN (ξ := ξ) hW 1 1 (Nat.zero_le k)).log
  have hDm : Measurable D := (hmψ.sub hmφ).pow_const 2
  have hb : 0 < c / (ξ ^ 2 + 1) := by positivity
  have h := integrable_integral_le_of_exp_tail (P := P) hDm (fun ω => sq_nonneg _)
    hC.le hb fun t ht => ?_
  · refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
    field_simp
  -- `{t ≤ D} ⊆ {√t/√(ξ²+1) ≤ X_{1,1}}`
  set x := √t / √(ξ ^ 2 + 1) with hx
  have hx0 : 0 < x := by positivity
  refine (measure_mono fun ω (hω : t ≤ D ω) => ?_).trans ((h5 x hx0).trans
    (ENNReal.ofReal_le_ofReal ?_))
  · show ENNReal.ofReal x ≤ _
    by_contra hcon
    push Not at hcon
    -- `X < x` so `|A − B| ≤ |ξ| x`
    obtain ⟨c', hc'0, hc'x, hc'⟩ : ∃ c', 0 ≤ c' ∧ c' < x ∧
        ¬ ENNReal.ofReal c' < XAB (fun n y => phiMN W P 0 n y ω)
          (fun n y => psiMN Q W P 0 n y ω) 1 1 := by
      obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hcon
      refine ⟨r, hr0, (ENNReal.ofReal_lt_ofReal_iff hx0).1 hr2, fun h => ?_⟩
      exact absurd (hr1.trans h) (lt_irrefl _)
    have hab := sq_sub_le hW Q ξ k ω hc'0 hc'
    have hD : D ω ≤ (|ξ| * c') ^ 2 := by
      show (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2 ≤ _
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    have hξ : |ξ| ≤ √(ξ ^ 2 + 1) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
    have hlt : |ξ| * c' < √t := by
      have h1 : |ξ| * c' ≤ √(ξ ^ 2 + 1) * c' := mul_le_mul_of_nonneg_right hξ hc'0
      have h2 : √(ξ ^ 2 + 1) * c' < √(ξ ^ 2 + 1) * x :=
        mul_lt_mul_of_pos_left hc'x (by positivity)
      have h3 : √(ξ ^ 2 + 1) * x = √t := by rw [hx]; field_simp
      linarith
    have : (|ξ| * c') ^ 2 < t := by
      have := pow_lt_pow_left₀ hlt (by positivity) two_ne_zero
      rwa [Real.sq_sqrt ht.le] at this
    linarith
  · rw [hx, div_pow, Real.sq_sqrt ht.le, Real.sq_sqrt (by positivity)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (le_of_eq ?_)) hC.le
    ring

/-- **`Var log L^{(k)}_{1,1}(ψ) ≤ (2ξ² log 2 + 2M) max(k, 1)`** (DDDF l. 1064–1065; the proof of
`L24.psi_memLp_variance`, `LQGMetric/Papers/DDDF/L24.lean`, with the Prop 5 bound `M` as a
parameter). -/
theorem psi_memLp_variance_of (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {M : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ k : ℕ,
      Integrable (fun ω => (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2) P ∧
      ∫ ω, (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2 ∂P ≤ M) (k : ℕ) :
    MemLp (logLenPsi ξ Q W P k) 2 P ∧
      Var[logLenPsi ξ Q W P k; P] ≤ (2 * ξ ^ 2 * Real.log 2 + 2 * M) * max (k : ℝ) 1 := by
  have := hW.isProbabilityMeasure
  have hmψ : Measurable (logLenPsi ξ Q W P k) :=
    (measurable_lenObs (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).cont
      (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).meas _).log
  obtain ⟨hB, hBv⟩ := dddf_lemma23_sharp hW ξ k
  obtain ⟨hA, hAv⟩ := variance_le_two_mul hmψ hB (hM k).1
  refine ⟨hA, hAv.trans ?_⟩
  have h1 : (1 : ℝ) ≤ max (k : ℝ) 1 := le_max_right _ _
  have h2 : (k : ℝ) ≤ max (k : ℝ) 1 := le_max_left _ _
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have e1 : 2 * (ξ ^ 2 * (k * Real.log 2)) ≤ 2 * ξ ^ 2 * Real.log 2 * max (k : ℝ) 1 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * ξ ^ 2 * Real.log 2)
    nlinarith
  have e2 : 2 * M ≤ 2 * M * max (k : ℝ) 1 := by nlinarith
  nlinarith [(hM k).2]

/-- **DDDF Lemma 24 with an explicit constant** (`Lem:Apriori`, (5.56); the proof of
`dddf_lemma24`, `LQGMetric/Papers/DDDF/L24.lean`): if `Var log L^{(k)}_{1,1}(ψ) ≤ C max(k,1)` for
all `k`, then `Λ_n(ψ, p) ≤ e^{(√(2C)/p) √n}` for `n ≥ 1`. -/
theorem lemma24_of (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {p : ℝ} (hp0 : 0 < p)
    (hp : p < 1 / 2) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k : ℕ, MemLp (logLenPsi ξ Q W P k) 2 P ∧
      Var[logLenPsi ξ Q W P k; P] ≤ C * max (k : ℝ) 1) (n : ℕ) (hn : 1 ≤ n) :
    LambdaNPsi ξ Q W P n (ENNReal.ofReal p) ≤ exp (√(2 * C) / p * √(n : ℝ)) := by
  have := hW.isProbabilityMeasure
  refine Finset.sup'_le _ _ fun k hk => ?_
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hv := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)
  refine (ratio_le_of_variance hv.cont hv.meas (hC k).1 hp0 hp).trans
    (Real.exp_le_exp.2 ?_)
  have hV : Var[fun ω => Real.log (lenObs ξ (psiMN Q W P 0 k) (rectAB 1 1) ω); P] ≤ C * n :=
    (hC k).2.trans (mul_le_mul_of_nonneg_left (max_le hkn hn1) hC0)
  rw [div_mul_eq_mul_div, ← Real.sqrt_mul (by positivity)]
  refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) hp0.le
  nlinarith

end Explicit

/-! ### Uniform versions (constants before the probability space and before `ξ`) -/

/-- **`Λ_n(φ, p) ≤ C_Λ Λ_n(ψ, p/2)`, uniform** (ledger U2, re-exposure of
`LambdaN_le_LambdaNPsi`): `C_Λ = e^{2 ξs M}` with `M = √(max(1, log(C/(p/2)))/c)` and `(C, c)`
the Prop 5 constants of `exists_tail_XAB_unif_W` (before the probability space). -/
theorem LambdaN_le_LambdaNPsi_unif (Q : PsiParams) (ξs : ℝ) {p : ℝ} (hp0 : 0 < p)
    (hp : p < 1 / 2) :
    ∃ CΛ : ℝ, 0 < CΛ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ n : ℕ,
        LambdaN ξ W P n (ENNReal.ofReal p) ≤
          CΛ * LambdaNPsi ξ Q W P n (ENNReal.ofReal (p / 2)) := by
  obtain ⟨C, c, hC, hc, htail⟩ := exists_tail_XAB_unif_W Q 1
  set M : ℝ := √(max 1 (Real.log (C / (p / 2))) / c) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  refine ⟨exp (ξs * M) ^ 2, by positivity, fun {Ω} _ {P} {W} hW ξ hξ n => ?_⟩
  have := hW.isProbabilityMeasure
  have hε := htail hW 1 1 le_rfl le_rfl (p / 2) (by positivity)
  refine (LambdaN_le_LambdaNPsi_of hW Q ξ hp0 hp hM0 hε n).trans
    (mul_le_mul_of_nonneg_right ?_ ?_)
  · rw [abs_of_pos hξ.1]
    exact pow_le_pow_left₀ (exp_pos _).le
      (exp_le_exp.2 (mul_le_mul_of_nonneg_right hξ.2 hM0)) 2
  · refine le_trans ?_ (Finset.le_sup' (fun k =>
      ellBarQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) (ENNReal.ofReal (p / 2)) /
        ellQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) (ENNReal.ofReal (p / 2)))
      (Finset.mem_range.2 (Nat.succ_pos n)))
    have hv := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le 0)
    have hq0 : 0 < p / 2 := by positivity
    have h0 := ellQ_pos (P := P) (ξ := ξ) hv.cont hv.meas (ENNReal.ofReal_pos.2 hq0)
      (by rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith))
    exact div_nonneg (h0.le.trans (ellQ_le_ellBarQ hq0 (by linarith))) h0.le

/-- **`Var log L^{(k)}_{1,1}(ψ) ≤ C_V max(k, 1)`, uniform** (DDDF l. 1064–1065; re-exposure of
`L24.psi_memLp_variance`): `C_V = 2ξs² log 2 + 2C₅(ξs²+1)/c₅`, `(C₅, c₅)` the Prop 5 constants of
`dddf_prop5_XAB_W` (before the probability space). -/
theorem psi_variance_unif (Q : PsiParams) (ξs : ℝ) :
    ∃ CV : ℝ, 0 ≤ CV ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ k : ℕ,
        MemLp (logLenPsi ξ Q W P k) 2 P ∧ Var[logLenPsi ξ Q W P k; P] ≤ CV * max (k : ℝ) 1 := by
  obtain ⟨C, c, hC, hc, h5⟩ := dddf_prop5_XAB_W Q 1 1
  refine ⟨2 * ξs ^ 2 * Real.log 2 + 2 * (C * (ξs ^ 2 + 1) / c), by positivity,
    fun {Ω} _ {P} {W} hW ξ hξ k => ?_⟩
  have hξ2 : ξ ^ 2 ≤ ξs ^ 2 := pow_le_pow_left₀ hξ.1.le hξ.2 2
  have hM : ∀ k : ℕ,
      Integrable (fun ω => (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2) P ∧
      ∫ ω, (logLenPsi ξ Q W P k ω - Real.log (lenN ξ W P 1 1 k ω)) ^ 2 ∂P ≤
        C * (ξs ^ 2 + 1) / c := fun k => by
    obtain ⟨h1, h2⟩ := integral_sq_sub_le_of hW Q ξ hC hc (h5 hW) k
    refine ⟨h1, h2.trans (div_le_div_of_nonneg_right ?_ hc.le)⟩
    exact mul_le_mul_of_nonneg_left (by linarith) hC.le
  obtain ⟨h1, h2⟩ := psi_memLp_variance_of hW Q ξ (by positivity) hM k
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))⟩
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have := mul_le_mul_of_nonneg_right hξ2 hl2
  nlinarith

/-- **DDDF Lemma 24, uniform** (`Lem:Apriori`, (5.56); re-exposure of `dddf_lemma24`):
`Λ_n(ψ, p) ≤ e^{C_t √n}` for `n ≥ 1`, all `ξ ∈ (0, ξs]` and every white noise, with
`C_t = √(2 C_V)/p` and `C_V` of `psi_variance_unif`. -/
theorem lemma24_unif (Q : PsiParams) (ξs : ℝ) {p : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ n : ℕ, 1 ≤ n →
        LambdaNPsi ξ Q W P n (ENNReal.ofReal p) ≤ exp (Ct * √(n : ℝ)) := by
  obtain ⟨CV, hCV0, hCV⟩ := psi_variance_unif Q ξs
  exact ⟨√(2 * CV) / p, by positivity, fun {Ω} _ {P} {W} hW ξ hξ n hn =>
    lemma24_of hW Q ξ hp0 hp hCV0 (hCV hW ξ hξ) n hn⟩

end Uniform
end GaussianLQG
