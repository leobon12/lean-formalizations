import GaussianLQG.Uniform.Thm20.Visited

/-!
# DDDF Theorem 20, Steps 1 and 5, with a data-free bound; Theorem 20 uniform in `ξ`

Phase B, packet PB-U9 (ledger U9 and Finding `fd:step5`).

`T20.t20_step5` (`LQGMetric/Papers/DDDF/T20Ind.lean`) returns `∃ K ∃ B` after the data with
`B = max(Λ_K, e^{C_p √(2C₁K)})`: the bound contains the value `Λ_K` of the sequence, which depends
on `ξ` and on the noise. Here:

* `t20_step5_of_fixK`: for any `K ≥ K₀`, `K ≥ 1` with (5.71)
  `e^{-C₂K}(e^{C_t√K} + e^{C_p√(2C₁K)})² ≤ C₁K`, the bound `B = e^{C_t√K} + e^{C_p√(2C₁K)}`,
  which dominates `Λ_K` by the a-priori bound (5.70) (proof of `t20_step5`, DDDF l. 1186–1210);
* `t20_step5_unif`: the ledger statement (U9): `K` (from `T20.t20_exists_K`, called once) and `B`
  are chosen before the data `r, V, Λ`;
* `thm20_psi_of_recursive_at`: Steps 1 and 5 (the proof of `dddf_thm20_psi_of_recursive`,
  `LQGMetric/Papers/DDDF/T20.lean`) with explicit constants;
* `thm20_unif_of`: DDDF Theorem 20 uniform in `ξ ∈ (0, ξs]` and in the white noise, for parameters
  `Q` of `ψ` with `PsiSmall Q`, from the uniform Step 4 (`T20Step4U`): Step 2–3 (`dddf_t20_step2`)
  with `C₁ = 2ξs² log 2 + 1` (ledger row `dddf_t20_recursive_of_step4`), Lemma 24 and the `φ/ψ`
  comparison with their uniform constants (`GaussianLQG/Uniform/Thm20/Apriori.lean`), and
  `t20_exists_K` called once at the uniform constants (Recipe E). The bound is
  `B = max(C_Λ B_ψ, max(B_ψ, max(2C₁K, C_V K)))`, `B_ψ = e^{C_t√K} + e^{C_p√(2C₁K)}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.DDDF.T20 LQGMetric.DDDF.L24

/-- **DDDF Theorem 20, Step 5, with the data-free bound** `B = e^{C_t√K} + e^{C_p√(2C₁K)}`
(`tightness.tex` l. 1186–1210; the proof of `T20.t20_step5`, `LQGMetric/Papers/DDDF/T20Ind.lean`,
with `max(Λ_K, e^{C_p√(2C₁K)})` replaced by its bound through (5.70)): for `K ≥ K₀`, `K ≥ 1`
satisfying (5.71), `Λ_n ≤ B` for all `n` and `V_n ≤ 2C₁K` for `n ≥ K`. -/
theorem t20_step5_of_fixK {r V Λ : ℕ → ℝ} {C₁ C₂ Cp Ct : ℝ} (hCp : 0 ≤ Cp) {K₀ K : ℕ}
    (hKK₀ : K₀ ≤ K) (hK1 : 1 ≤ K)
    (hfix : exp (-(C₂ * K)) * (exp (Ct * √(K : ℝ)) + exp (Cp * √(2 * C₁ * K))) ^ 2 ≤ C₁ * K)
    (hnonneg : ∀ n, 0 ≤ Λ n) (hmono : Monotone Λ)
    (hΛ : ∀ n, Λ (n + 1) ≤ max (Λ n) (r (n + 1)))
    (hr : ∀ n, r n ≤ exp (Cp * √(V n)))
    (hrec : ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
      V n ≤ C₁ * K + exp (-(C₂ * K)) * Λ (n - K) ^ 2)
    (happ : ∀ n : ℕ, 1 ≤ n → Λ n ≤ exp (Ct * √(n : ℝ))) :
    (∀ n, Λ n ≤ exp (Ct * √(K : ℝ)) + exp (Cp * √(2 * C₁ * K))) ∧
      ∀ n, K ≤ n → V n ≤ 2 * C₁ * K := by
  set e := exp (Cp * √(2 * C₁ * K)) with he
  set B := exp (Ct * √(K : ℝ)) + e with hB
  have he0 : 0 < e := exp_pos _
  -- (5.70) with `Λ_{n-K} ≤ B` gives `V_n ≤ 2 C₁ K` (DDDF l. 1205–1207)
  have hVle : ∀ n, K ≤ n → Λ (n - K) ≤ B → V n ≤ 2 * C₁ * K := by
    intro n hn hsub
    have h1 := hrec K hKK₀ n hn
    have h2 : Λ (n - K) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (hnonneg _) hsub 2
    have := mul_le_mul_of_nonneg_left h2 (exp_pos (-(C₂ * K))).le
    linarith
  -- (5.70): `Λ_K ≤ e^{C_t √K} ≤ B`
  have hΛK : Λ K ≤ B := (happ K hK1).trans (le_add_of_nonneg_right he0.le)
  have hall : ∀ n, Λ n ≤ B := by
    intro n
    induction n with
    | zero => exact (hmono (Nat.zero_le K)).trans hΛK
    | succ n ih =>
      rcases Nat.lt_or_ge (n + 1) (K + 1) with h | h
      · exact (hmono (Nat.lt_succ_iff.1 h)).trans hΛK
      · refine (hΛ n).trans (max_le ih ?_)
        have hV := hVle (n + 1) (by omega) ((hmono (by omega : n + 1 - K ≤ n)).trans ih)
        have hsqrt : √(V (n + 1)) ≤ √(2 * C₁ * K) := Real.sqrt_le_sqrt hV
        exact (hr (n + 1)).trans ((exp_le_exp.2 (mul_le_mul_of_nonneg_left hsqrt hCp)).trans
          (le_add_of_nonneg_left (exp_pos _).le))
  exact ⟨hall, fun n hn => hVle n hn (hall _)⟩

/-- **DDDF Theorem 20, Step 5, uniform** (ledger U9, `t20_step5_unif`; Finding `fd:step5`): for
`C₁, C₂ > 0`, `C_p ≥ 0`, `C_t` and `K₀`, the index `K` and the bound `B` are chosen before the data
`(r, V, Λ)`; `K` is `T20.t20_exists_K` at these constants and
`B = e^{C_t√K} + e^{C_p√(2C₁K)}` (`t20_step5_of_fixK`). -/
theorem t20_step5_unif {C₁ C₂ Cp Ct : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hCp : 0 ≤ Cp) (K₀ : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ B : ℝ, 0 < B ∧ ∀ {r V Λ : ℕ → ℝ}, (∀ n, 0 ≤ Λ n) → Monotone Λ →
      (∀ n, Λ (n + 1) ≤ max (Λ n) (r (n + 1))) → (∀ n, r n ≤ exp (Cp * √(V n))) →
      (∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n → V n ≤ C₁ * K + exp (-(C₂ * K)) * Λ (n - K) ^ 2) →
      (∀ n : ℕ, 1 ≤ n → Λ n ≤ exp (Ct * √(n : ℝ))) →
      (∀ n, Λ n ≤ B) ∧ ∀ n, K ≤ n → V n ≤ 2 * C₁ * K := by
  obtain ⟨K, hKK₀, hK1, hfix⟩ := T20.t20_exists_K (a := Ct) (b := Cp) hC₁ hC₂ K₀
  exact ⟨K, hK1, exp (Ct * √(K : ℝ)) + exp (Cp * √(2 * C₁ * K)), by positivity,
    fun hnonneg hmono hΛ hr hrec happ =>
      t20_step5_of_fixK hCp hKK₀ hK1 hfix hnonneg hmono hΛ hr hrec happ⟩

section Explicit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DDDF Theorem 20, Steps 1 and 5, with explicit constants** (`tightness.tex`
l. 1072–1076, 1176–1213; the proof of `dddf_thm20_psi_of_recursive`,
`LQGMetric/Papers/DDDF/T20.lean`, with `t20_step5_of_fixK` for Step 5): from the recursion (5.68)
with `(C₁, C₂, K₀)`, the variance bound `C_V max(k,1)`, Lemma 24 with `C_t` and an index `K ≥ K₀`
satisfying (5.71) with `C_p = √2/(p/2)`,
`Λ_n(ψ, p/2) ≤ e^{C_t√K} + e^{C_p√(2C₁K)}` and `Var log L^{(n)}_{1,1}(ψ) ≤ max(2C₁K, C_V K)`. -/
theorem thm20_psi_of_recursive_at (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {p : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 2) {C₁ C₂ : ℝ} {K₀ K : ℕ} (hKK₀ : K₀ ≤ K) (hK1 : 1 ≤ K)
    {Cv Ct : ℝ} (hCv0 : 0 ≤ Cv)
    (hCv : ∀ k : ℕ, MemLp (logLenPsi ξ Q W P k) 2 P ∧
      Var[logLenPsi ξ Q W P k; P] ≤ Cv * max (k : ℝ) 1)
    (hCt : ∀ n : ℕ, 1 ≤ n →
      LambdaNPsi ξ Q W P n (ENNReal.ofReal (p / 2)) ≤ exp (Ct * √(n : ℝ)))
    (hfix : exp (-(C₂ * K)) * (exp (Ct * √(K : ℝ)) + exp (√2 / (p / 2) * √(2 * C₁ * K))) ^ 2 ≤
      C₁ * K)
    (hrec : ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
      Var[logLenPsi ξ Q W P n; P] ≤
        C₁ * K + exp (-(C₂ * K)) * LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2) :
    (∀ n, LambdaNPsi ξ Q W P n (ENNReal.ofReal (p / 2)) ≤
        exp (Ct * √(K : ℝ)) + exp (√2 / (p / 2) * √(2 * C₁ * K))) ∧
      ∀ n, Var[logLenPsi ξ Q W P n; P] ≤ max (2 * C₁ * K) (Cv * K) := by
  have := hW.isProbabilityMeasure
  have hq0 : 0 < p / 2 := by positivity
  have hq : p / 2 < 1 / 2 := by linarith
  set q := ENNReal.ofReal (p / 2)
  set r : ℕ → ℝ := fun k =>
    ellBarQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) q / ellQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) q
  set V : ℕ → ℝ := fun n => Var[logLenPsi ξ Q W P n; P]
  have hΛdef : ∀ n, LambdaNPsi ξ Q W P n q =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one r := fun n => rfl
  -- Step 1 (5.56): `r_n ≤ e^{C_p √V_n}` with `C_p = √2 / (p/2)`
  have hr : ∀ n, r n ≤ exp (√2 / (p / 2) * √(V n)) := by
    intro n
    have hv := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
    refine (L24.ratio_le_of_variance hv.cont hv.meas (hCv n).1 hq0 hq).trans_eq ?_
    congr 1
    rw [Real.sqrt_mul (by norm_num)]
    have hVn : V n = Var[fun ω => Real.log (lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω); P] := rfl
    rw [hVn]
    ring
  have hnonneg : ∀ n, 0 ≤ LambdaNPsi ξ Q W P n q := by
    intro n
    have hv := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le 0)
    have h0 := ellQ_pos (P := P) (ξ := ξ) hv.cont hv.meas (ENNReal.ofReal_pos.2 hq0)
      (by rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith))
    refine le_trans ?_ (Finset.le_sup' r (Finset.mem_range.2 (Nat.succ_pos n)))
    exact div_nonneg (h0.le.trans (ellQ_le_ellBarQ hq0 hq)) h0.le
  obtain ⟨hB, hVK⟩ := t20_step5_of_fixK (r := r) (V := V)
    (Λ := fun n => LambdaNPsi ξ Q W P n q) (by positivity) hKK₀ hK1 hfix hnonneg
    (by simpa only [hΛdef] using monotone_sup'_range r)
    (fun n => by simp only [hΛdef]; rw [sup'_range_succ])
    hr hrec (fun n hn => hCt n hn)
  refine ⟨hB, fun n => ?_⟩
  rcases le_or_gt K n with h | h
  · exact (hVK n h).trans (le_max_left _ _)
  · refine ((hCv n).2.trans ?_).trans (le_max_right _ _)
    refine mul_le_mul_of_nonneg_left (max_le (by exact_mod_cast h.le) (by exact_mod_cast hK1))
      hCv0

end Explicit

/-- **DDDF Theorem 20, uniform in `ξ ∈ (0, ξs]` and in the white noise** (ledger U9, general
parameters `Q` of `ψ` with `PsiSmall Q`), from the uniform Step 4 (`T20Step4U`): `p₀`, and for
`p ≤ p₀` the bound `B`, are chosen before the probability space and before `ξ`, and
`Λ_n(φ, p) ≤ B`, `Λ_n(ψ, p/2) ≤ B`, `Var log L^{(n)}_{1,1}(ψ) ≤ B` for all `n`. -/
theorem thm20_unif_of (Q : PsiParams) (hQ : PsiSmall Q) {ξs : ℝ} (h4 : T20Step4U ξs Q) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ B : ℝ,
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ n : ℕ,
        LambdaN ξ W P n (ENNReal.ofReal p) ≤ B ∧
        LambdaNPsi ξ Q W P n (ENNReal.ofReal (p / 2)) ≤ B ∧
        Var[L24.logLenPsi ξ Q W P n; P] ≤ B := by
  obtain ⟨p₁, hp₁, h4⟩ := h4
  refine ⟨min p₁ (1 / 4), lt_min hp₁ (by norm_num), fun p hp hpp => ?_⟩
  have hp1 : p ≤ p₁ := hpp.trans (min_le_left _ _)
  have hp4 : p ≤ 1 / 4 := hpp.trans (min_le_right _ _)
  have hp2 : p < 1 / 2 := by linarith
  have hq0 : 0 < p / 2 := by positivity
  have hq : p / 2 < 1 / 2 := by linarith
  obtain ⟨C₂, hC₂, K₀, h4⟩ := h4 p hp hp1
  -- the uniform constants, before the probability space and before `ξ`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₁ : ℝ := 2 * (ξs ^ 2 * Real.log 2) + 1 with hC₁def
  have hC₁ : 0 < C₁ := by positivity
  obtain ⟨CV, hCV0, hCV⟩ := psi_variance_unif Q ξs
  obtain ⟨Ct, -, hCt⟩ := lemma24_unif Q ξs hq0 hq
  obtain ⟨CΛ, hCΛ, hΛ⟩ := LambdaN_le_LambdaNPsi_unif Q ξs hp hp2
  -- Step 5: `K` by `t20_exists_K`, once, at the uniform constants (Recipe E)
  obtain ⟨K, hKK₀, hK1, hfix⟩ := T20.t20_exists_K (a := Ct) (b := √2 / (p / 2)) hC₁ hC₂ K₀
  set Bψ : ℝ := exp (Ct * √(K : ℝ)) + exp (√2 / (p / 2) * √(2 * C₁ * K)) with hBψ
  refine ⟨max (CΛ * Bψ) (max Bψ (max (2 * C₁ * K) (CV * K))),
    fun {Ω} _ {P} {W} hW ξ hξ n => ?_⟩
  -- the recursion (5.68) at `ξ`, with `C₁ = 2ξs² log 2 + 1 ≥ 2ξ² log 2 + 1`
  have hrec : ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
      Var[logLenPsi ξ Q W P n; P] ≤
        C₁ * K + exp (-(C₂ * K)) * LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2 := by
    intro K hK n hn
    refine (dddf_t20_step2 hW Q hQ ξ hn).trans (add_le_add ?_ (h4 hW ξ hξ K hK n hn))
    have hK' : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hξ2 : ξ ^ 2 ≤ ξs ^ 2 := pow_le_pow_left₀ hξ.1.le hξ.2 2
    have h1 : ξ ^ 2 * Real.log 2 * K ≤ ξs ^ 2 * Real.log 2 * K :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hξ2 hl2.le) hK'
    have e1 : 2 * (ξ ^ 2 * (K * Real.log 2)) = 2 * (ξ ^ 2 * Real.log 2 * K) := by ring
    have e2 : C₁ * K = 2 * (ξs ^ 2 * Real.log 2 * K) + K := by rw [hC₁def]; ring
    rw [e1, e2]
    linarith
  obtain ⟨hBψ', hV⟩ := thm20_psi_of_recursive_at hW Q ξ hp hp2 hKK₀ hK1 hCV0 (hCV hW ξ hξ)
    (hCt hW ξ hξ) hfix hrec
  have hΛψ := hBψ' n
  refine ⟨?_, hΛψ.trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hV n).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  exact (hΛ hW ξ hξ n).trans ((mul_le_mul_of_nonneg_left hΛψ hCΛ.le).trans (le_max_left _ _))

end Uniform
end GaussianLQG
