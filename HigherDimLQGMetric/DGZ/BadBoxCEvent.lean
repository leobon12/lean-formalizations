import HigherDimLQGMetric.DGZ.BadBoxQ1

/-!
# DGZ Lemma 5.6: the event `𝒞(x,z)` is likely (packet L4a2)

Source: [2] Lemma 5.6 (TeX l. 2182–2260, p. 42–43); planning audit MA7 D-5.5–5.9 (Lemma 5.6:
"`P[𝒞(x,z)ᶜ] ≤ C2^{-a_j log a_j} + Ce^{-a_{j-1} log a_{j-1}} + 2^{-βλa_{j-1}}/2` by D-4.10
(rescaled), D-4.9 (rescaled …), and the small-box sup tail (L3b2) with [2]'s choice
`t = Qλ log 2 - δ > √(2β)λ log 2` … The `s_j` inequality (5.12) holds for `θ = θ(δ)` small and
`K ≥ C(δ, θ)`"), G19; blueprint Lemma `r2:lem:56` and Definition `r2:def:nice` (ruling M23).

`𝒞(x,z)` (`NiceCEvent p H j u w`, `x = s_j u`, `z = s_{j-1} w`) is the intersection of three events:

* **across**: `D_{n-a_j,n}(across B_{4s_j}(x) \ B_{2s_j}(x)) > 2^{-n+(ξQ-θ)a_j}`; by scaling
  (`prob_niceCEvent_across_eq`) its complement has the probability of
  `{D_{a_j}(across B₄(0) \ B₂(0)) ≤ 2^{-(1-ξQ+θ)a_j}}`, at most `C₁ e^{-a_j log a_j}` by L3c3's
  `superExpAcross_tail` (D-4.10 with `δ = θ`);
* **certificate**: `Cert_{j-1}(z)` fails with probability `≤ C₂ e^{-a_{j-1} log a_{j-1}}` (L4a1's
  `prob_not_niceCert_le`, from D-4.9);
* **supremum**: `h_{n-a_j,n-a_{j-1}} ≤ s_j*` on `B̄_{4R s_{j-1}}(z)`; `h_{n-a_j,n-a_{j-1}}` is a
  version of `H_{s_{j-1},s_j}`, `σ² = log(s_j/s_{j-1}) = (a_j - a_{j-1}) log 2 ≤ (λa_{j-1} + 1)
  log 2`, and L3b2's `exists_smallBox_gaussian_tail` (box radius `4R·s_{j-1}`, so G19 needs no
  covering) gives `2e^{-u²/(2σ²)} + 2e^{-w²/C₃}` for `s_j* = u + C₃ + w`.

The lower bound `s_j* ≥ (Qλ log 2 - δ₀) a_{j-1}` (`BadBox.supLevel_ge`, [2] (5.12)) holds when
`4(θ/ξ) log 2 ≤ δ₀/2` and `2/(ξ√K) ≤ δ₀/2`; with `σ := √(2β) λ log 2 < Qλ log 2` (`β < Q²/2`),
`δ₀ := (Qλ log 2 - σ)/2`, `τ := (Qλ log 2 - δ₀ + σ)/2 > σ`, `w := (δ₀/4) a_{j-1}` and
`u := s_j* - C₃ - w ≥ τ a_{j-1}`, each of the four terms is at most `2^{-βλa_{j-1}}/4` for
`a_{j-1} ≥ K⁴` large (`BadBoxArith`).

* `lemma56` (**target**): for `β ∈ (d, Q²/2)` there is `θ₀ > 0` such that for every `θ ∈ (0, θ₀]`
  there is `K₀` with `P[𝒞(x,z)ᶜ] ≤ 2^{-βλa_{j-1}}` for `K ≥ K₀`, all `n, k`, `2 ≤ j` with `a_j ≤ n`,
  all `x, z` and every dyadic realization (DGZ's sequence, `R ≥ 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## The lower bound on `s_j*` ([2] (5.12)) -/

namespace BadBox

theorem rpow_three_halves_eq {K : ℝ} (hK : 0 < K) : K ^ ((3 : ℝ) / 2) = K * √K := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hK, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-- **[2] (5.12)**: for DGZ's sequence (`0 ≤ λ ≤ 1/4`), `2 ≤ j`, `ξ > 0`, `Q, θ ≥ 0`: if
`4(θ/ξ) log 2 ≤ δ₀/2` and `2/(ξ√K) ≤ δ₀/2`, then `s_j* ≥ (Qλ log 2 - δ₀) a_{j-1}`. -/
theorem supLevel_ge (p : NiceParams) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam4 : lam ≤ 1 / 4)
    (hK : 1 ≤ p.K) (ha : p.a = dgzSeq lam p.K) (hξ : 0 < p.ξ) (hQ : 0 ≤ p.Q) (hθ : 0 ≤ p.θ)
    {j : ℕ} (hj : 2 ≤ j) {δ₀ : ℝ} (hθδ : 4 * (p.θ / p.ξ) * Real.log 2 ≤ δ₀ / 2)
    (hKδ : 2 / (p.ξ * √(p.K : ℝ)) ≤ δ₀ / 2) :
    (p.Q * lam * Real.log 2 - δ₀) * p.a (j - 1) ≤ p.supLevel j := by
  have hℓ : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hj1 : 1 ≤ j - 1 := by omega
  have hjj : j - 1 + 1 = j := by omega
  have hK0 : (0 : ℝ) < p.K := by exact_mod_cast (show 0 < p.K by omega)
  have hK1 : (1 : ℝ) ≤ p.K := by exact_mod_cast hK
  -- the exponents `N = a_{j-1}`, `A = a_j`
  have hgap : lam * (p.a (j - 1) : ℝ) ≤ (p.a j : ℝ) - p.a (j - 1) := by
    have h1 := dgzSeq_gap (K := p.K) hlam0 hj1
    rw [hjj] at h1
    have hle : dgzSeq lam p.K (j - 1) ≤ dgzSeq lam p.K j :=
      dgzSeq_monotone hlam0 hK (Nat.sub_le j 1)
    rw [Nat.cast_sub hle] at h1
    rw [ha]
    exact h1
  have hup : (p.a j : ℝ) ≤ (1 + lam) * p.a (j - 1) + 1 := by
    have h1 := dgzSeq_succ_le (K := p.K) hlam0 hj1
    rw [hjj] at h1
    rw [ha]
    exact h1
  have hN4 : (p.K : ℝ) ^ 4 ≤ p.a (j - 1) := by
    have : p.K ^ 4 ≤ p.a (j - 1) := by rw [ha]; exact pow_le_dgzSeq hlam0 hK hj1
    exact_mod_cast this
  set N : ℝ := ((p.a (j - 1) : ℕ) : ℝ) with hNdef
  set A : ℝ := ((p.a j : ℕ) : ℝ) with hAdef
  have hN1 : 1 ≤ N := (one_le_pow₀ hK1).trans hN4
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  -- (a) the main term
  have ha' : p.Q * lam * Real.log 2 * N ≤ p.Q * (A - N) * Real.log 2 := by
    have h1 := mul_le_mul_of_nonneg_left hgap hQ
    have h2 := mul_le_mul_of_nonneg_right h1 hℓ.le
    linarith
  -- (b) the `θ` term
  have hb' : p.θ / p.ξ * (A + N) * Real.log 2 ≤ 4 * (p.θ / p.ξ) * Real.log 2 * N := by
    have h1 : A + N ≤ 4 * N := by nlinarith
    have h2 : 0 ≤ p.θ / p.ξ := div_nonneg hθ hξ.le
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    have h4 := mul_le_mul_of_nonneg_right h3 hℓ.le
    linarith
  -- (c) the `K^{3/2} √a_j` term
  have hc' : (p.K : ℝ) ^ ((3 : ℝ) / 2) * √A / p.ξ ≤ 2 / (p.ξ * √(p.K : ℝ)) * N := by
    rw [rpow_three_halves_eq hK0]
    have hsK : 0 < √(p.K : ℝ) := Real.sqrt_pos.2 hK0
    have hsKK : √(p.K : ℝ) * √(p.K : ℝ) = p.K := Real.mul_self_sqrt hK0.le
    have hsqN : (p.K : ℝ) ^ 2 ≤ √N := by
      rw [Real.le_sqrt (by positivity) (by linarith)]
      calc ((p.K : ℝ) ^ 2) ^ 2 = (p.K : ℝ) ^ 4 := by ring
        _ ≤ N := hN4
    have hsA : √A ≤ 2 * √N := by
      have h1 : A ≤ 4 * N := by nlinarith
      calc √A ≤ √(4 * N) := Real.sqrt_le_sqrt h1
        _ = 2 * √N := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
    have hNN : √N * √N = N := Real.mul_self_sqrt (by linarith)
    have hsN0 : 0 ≤ √N := Real.sqrt_nonneg _
    have h1 : (p.K : ℝ) * √(p.K : ℝ) * √A ≤ 2 * N / √(p.K : ℝ) := by
      rw [le_div_iff₀ hsK]
      calc (p.K : ℝ) * √(p.K : ℝ) * √A * √(p.K : ℝ)
          = (p.K : ℝ) * (√(p.K : ℝ) * √(p.K : ℝ)) * √A := by ring
        _ = (p.K : ℝ) * p.K * √A := by rw [hsKK]
        _ ≤ (p.K : ℝ) * p.K * (2 * √N) := by gcongr
        _ = 2 * ((p.K : ℝ) ^ 2 * √N) := by ring
        _ ≤ 2 * (√N * √N) := by gcongr
        _ = 2 * N := by rw [hNN]
    calc (p.K : ℝ) * √(p.K : ℝ) * √A / p.ξ ≤ 2 * N / √(p.K : ℝ) / p.ξ :=
          div_le_div_of_nonneg_right h1 hξ.le
      _ = 2 / (p.ξ * √(p.K : ℝ)) * N := by field_simp
  have e : p.supLevel j = p.Q * (A - N) * Real.log 2 - p.θ / p.ξ * (A + N) * Real.log 2 -
      (p.K : ℝ) ^ ((3 : ℝ) / 2) * √A / p.ξ := rfl
  rw [e]
  have hN0 : 0 ≤ N := by linarith
  have h1 := mul_le_mul_of_nonneg_right hθδ hN0
  have h2 := mul_le_mul_of_nonneg_right hKδ hN0
  nlinarith

end BadBox

/-! ## The across term -/

/-- **The across term of `𝒞(x,z)` by scaling**: for a dyadic realization and `a_j ≤ n`,
`P[D_{n-a_j,n}(across B_{4s_j}(x) \ B_{2s_j}(x)) ≤ 2^{-n+(ξQ-θ)a_j}] =
P[D_{a_j}(across B₄(0) \ B₂(0)) ≤ 2^{-(1-ξQ+θ)a_j}]`. -/
theorem prob_niceCEvent_across_eq {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (p : NiceParams) {j : ℕ} (hjn : p.a j ≤ p.n) (u : Zd d) :
    P {ω | ¬ (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) <
        acrossDist p.ξ (fun z => H p.n z ω - H (p.n - p.a j) z ω) (latPt (p.s j) u)
          (4 * p.s j) (2 * p.s j)} =
      P {ω | acrossDist p.ξ (fun z => H (p.a j) z ω) 0 4 2 ≤
        (2 : ℝ) ^ (-(1 - p.ξ * p.Q + p.θ) * p.a j)} := by
  have hG := isBandVersion_sub_of_realization hκ hH (Nat.sub_le p.n (p.a j))
  have h := BadBox.measure_acrossDist_band_le_eq hκ hH (Nat.sub_le p.n (p.a j)) hG p.ξ
    (latPt (p.s j) u) 4 2 ((2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j))
  rw [Nat.sub_sub_self hjn] at h
  have ht : (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) / (2 : ℝ)⁻¹ ^ (p.n - p.a j) =
      (2 : ℝ) ^ (-(1 - p.ξ * p.Q + p.θ) * p.a j) := by
    rw [two_rpow_div_inv_two_pow, Nat.cast_sub hjn]
    congr 1
    ring
  rw [ht] at h
  have hset : {ω | ¬ (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) <
        acrossDist p.ξ (fun z => H p.n z ω - H (p.n - p.a j) z ω) (latPt (p.s j) u)
          (4 * p.s j) (2 * p.s j)} =
      {ω | acrossDist p.ξ (fun z => H p.n z ω - H (p.n - p.a j) z ω) (latPt (p.s j) u)
          (4 * (2 : ℝ)⁻¹ ^ (p.n - p.a j)) (2 * (2 : ℝ)⁻¹ ^ (p.n - p.a j)) ≤
        (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j)} := by
    ext ω
    simp only [mem_ofPred_eq, not_lt]
    rfl
  rw [hset, h]

/-! ## Lemma 5.6 -/

/-- **DGZ Lemma 5.6** (target `lemma56`; MA7 D-5.5–5.9, G19; blueprint `r2:lem:56`): for
`β ∈ (d, Q²/2)` and `R ≥ 1` there is `θ₀ > 0` such that for every `θ ∈ (0, θ₀]` there is `K₀` with
`P[𝒞(x,z)ᶜ] ≤ 2^{-βλa_{j-1}}` for every dyadic realization, all parameters with `ξ, Q, θ, R` fixed,
`K ≥ K₀` and DGZ's sequence, all `n, k`, `2 ≤ j` with `a_j ≤ n`, and all `x = s_j u`,
`z = s_{j-1} w`. -/
theorem lemma56 {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) {β : ℝ} (hβd : (d : ℝ) < β)
    (hβQ : β < Q ^ 2 / 2) {R : ℕ} (hR : 1 ≤ R) :
    ∃ θ₀ > 0, ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ → ∃ K₀ : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = Q → p.θ = θ → p.R = R → K₀ ≤ p.K →
          p.a = dgzSeq (dgzLambda d Q) p.K → ∀ j : ℕ, 2 ≤ j → p.a j ≤ p.n → ∀ u w : Zd d,
            P {ω | ¬ NiceCEvent p (fun q z => H q z ω) j u w} ≤
              ENNReal.ofReal ((2 : ℝ) ^ (-(β * dgzLambda d Q * p.a (j - 1)))) := by
  have hd2 := h.dim
  have hκ := h.kernel
  have hξ := h.xi_pos
  have hQ0 : 0 < Q := lt_of_le_of_lt (Real.sqrt_nonneg _) h.subcritical
  have hα := dgzAlpha_pos h.subcritical
  have hlam : 0 < dgzLambda d Q := dgzLambda_pos hα
  have hlam4 : dgzLambda d Q ≤ 1 / 4 := dgzLambda_le_quarter hα
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hβ0 : 0 < β := hd0.trans hβd
  have hℓ : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the constants of the proof
  set lam := dgzLambda d Q with hlamdef
  set σ := √(2 * β) * lam * Real.log 2 with hσ
  set t₀ := Q * lam * Real.log 2 with ht₀
  have hsβ : √(2 * β) < Q := by
    rw [Real.sqrt_lt' hQ0]
    linarith
  have hσt₀ : σ < t₀ := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hsβ hlam) hℓ
  have hσ0 : 0 ≤ σ := by positivity
  set δ₀ := (t₀ - σ) / 2 with hδ₀
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀]; linarith
  set τ := (t₀ - δ₀ + σ) / 2 with hτ
  have hστ : σ < τ := by rw [hτ]; linarith
  set ε' := δ₀ / 4 with hε'
  have hε'pos : 0 < ε' := by positivity
  set b := β * lam * Real.log 2 with hb
  have hb0 : 0 ≤ b := by positivity
  have hσb : σ ^ 2 = 2 * lam * Real.log 2 * b := by
    rw [hσ, hb, mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
    ring
  refine ⟨ξ * δ₀ / (8 * Real.log 2), by positivity, fun θ hθ hθθ₀ => ?_⟩
  -- the three probability inputs
  obtain ⟨C₁, hC₁, hacr⟩ := superExpAcross_tail h hθ (r₁ := 4) (r₂ := 2) (by norm_num)
    (by norm_num)
  obtain ⟨C₂, hC₂, hcert⟩ := prob_not_niceCert_le h hθ hR
  obtain ⟨C₃, hC₃, hsb⟩ := exists_smallBox_gaussian_tail.{0} hκ (R := 4 * R) (by positivity)
  -- the thresholds
  obtain ⟨N₁, hN₁⟩ := BadBox.exists_mul_exp_neg_mul_log_le C₁ b hC₁.le
  obtain ⟨N₂, hN₂⟩ := BadBox.exists_mul_exp_neg_mul_log_le C₂ b hC₂.le
  obtain ⟨N₃, hN₃⟩ := BadBox.exists_gauss_le hσ0 hστ hlam hb0 hσb
  obtain ⟨N₄, hN₄⟩ := BadBox.exists_two_exp_neg_sq_div_le b hε'pos hC₃
  set Kδ : ℕ := ⌈(4 / (ξ * δ₀)) ^ 2⌉₊ with hKδdef
  set NC : ℕ := ⌈C₃ / ε'⌉₊ with hNCdef
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max Kδ NC) 8),
    fun Ω _ P W H hH p hpξ hpQ hpθ hpR hK ha j hj hjn u w => ?_⟩
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  have hK8 : 8 ≤ p.K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hK1 : 1 ≤ p.K := by omega
  have hmono : Monotone p.a := by rw [ha]; exact dgzSeq_monotone hlam.le hK1
  have hj1 : 1 ≤ j - 1 := by omega
  have hjj : j - 1 + 1 = j := by omega
  have haj : p.a (j - 1) ≤ p.a j := hmono (Nat.sub_le j 1)
  have hj1n : p.a (j - 1) ≤ p.n := haj.trans hjn
  -- `N = a_{j-1} ≥ K⁴ ≥ K`
  have hNK : p.K ≤ p.a (j - 1) := by
    have h1 : p.K ^ 4 ≤ p.a (j - 1) := by rw [ha]; exact pow_le_dgzSeq hlam.le hK1 hj1
    have h2 : p.K ≤ p.K ^ 4 := Nat.le_self_pow (by norm_num) _
    omega
  have hKN : ∀ M : ℕ, M ≤ p.K → M ≤ p.a (j - 1) := fun M hM => hM.trans hNK
  have hN₁' := hKN N₁ ((le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hK)))
  have hN₂' := hKN N₂ ((le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hK)))
  have hN₃' := hKN N₃ ((le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_left _ _).trans hK)))
  have hN₄' := hKN N₄ ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_left _ _).trans hK)))
  have hKδ' : Kδ ≤ p.K := (le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hK))
  have hNC' := hKN NC ((le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hK)))
  -- the lower bound on `s_j*`
  have hθδ : 4 * (p.θ / p.ξ) * Real.log 2 ≤ δ₀ / 2 := by
    rw [hpθ, hpξ]
    have h1 : θ / ξ ≤ δ₀ / (8 * Real.log 2) := by
      rw [div_le_iff₀ hξ]
      calc θ ≤ ξ * δ₀ / (8 * Real.log 2) := hθθ₀
        _ = δ₀ / (8 * Real.log 2) * ξ := by ring
    calc 4 * (θ / ξ) * Real.log 2 ≤ 4 * (δ₀ / (8 * Real.log 2)) * Real.log 2 := by gcongr
      _ = δ₀ / 2 := by field_simp; ring
  have hKδ2 : 2 / (p.ξ * √(p.K : ℝ)) ≤ δ₀ / 2 := by
    rw [hpξ]
    have hKr : (4 / (ξ * δ₀)) ^ 2 ≤ (p.K : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hKδ')
    have hsK : 4 / (ξ * δ₀) ≤ √(p.K : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      exact hKr
    have hsK0 : 0 < √(p.K : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < p.K by omega))
    rw [div_le_iff₀ (by positivity)]
    calc (2 : ℝ) = δ₀ / 2 * (ξ * (4 / (ξ * δ₀))) := by field_simp; ring
      _ ≤ δ₀ / 2 * (ξ * √(p.K : ℝ)) := by gcongr
  have hsup := BadBox.supLevel_ge p hlam.le hlam4 hK1 ha (by rw [hpξ]; exact hξ)
    (by rw [hpQ]; exact hQ0.le) (by rw [hpθ]; exact hθ.le) hj hθδ hKδ2
  rw [hpQ] at hsup
  -- notation
  set N : ℝ := ((p.a (j - 1) : ℕ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hNdef]
    exact_mod_cast (show 1 ≤ p.a (j - 1) by omega)
  -- the event split
  have hsplit : {ω | ¬ NiceCEvent p (fun q z => H q z ω) j u w} ⊆
      ({ω | ¬ (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) <
          acrossDist p.ξ (fun z => H p.n z ω - H (p.n - p.a j) z ω) (latPt (p.s j) u)
            (4 * p.s j) (2 * p.s j)} ∪
        {ω | ¬ NiceCert p (fun q z => H q z ω) (j - 1) (latPt (p.s (j - 1)) w)}) ∪
      {ω | ∃ z ∈ cbox (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1)),
        p.supLevel j < H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, NiceCEvent] at hω
    simp only [mem_union, mem_ofPred_eq]
    by_cases h1 : (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) <
        acrossDist p.ξ (fun z => H p.n z ω - H (p.n - p.a j) z ω) (latPt (p.s j) u)
          (4 * p.s j) (2 * p.s j)
    · by_cases h2 : NiceCert p (fun q z => H q z ω) (j - 1) (latPt (p.s (j - 1)) w)
      · right
        by_contra h3
        push Not at h3
        exact hω ⟨h1, h2, h3⟩
      · exact Or.inl (Or.inr h2)
    · exact Or.inl (Or.inl h1)
  -- (i) across
  have hP1 : P {ω | ¬ (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) <
      acrossDist p.ξ (fun z => H p.n z ω - H (p.n - p.a j) z ω) (latPt (p.s j) u)
        (4 * p.s j) (2 * p.s j)} ≤ ENNReal.ofReal (Real.exp (-(b * N)) / 4) := by
    rw [prob_niceCEvent_across_eq hκ hH p hjn u, hpξ, hpQ, hpθ]
    exact (hacr Ω P W H hH (p.a j)).trans (ENNReal.ofReal_le_ofReal (hN₁ _ _ hN₁' haj))
  -- (ii) certificate
  have hP2 : P {ω | ¬ NiceCert p (fun q z => H q z ω) (j - 1) (latPt (p.s (j - 1)) w)} ≤
      ENNReal.ofReal (Real.exp (-(b * N)) / 4) := by
    have hss : superScale (p.a (j - 1)) ≤ p.a (j - 1) :=
      superScale_le_self ((hKN 8 hK8))
    refine (hcert Ω P W H hH p hpξ hpQ hpθ hpR (j - 1) hj1n hss _).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact hN₂ _ _ hN₂' le_rfl
  -- (iii) supremum
  have hP3 : P {ω | ∃ z ∈ cbox (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1)),
      p.supLevel j < H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω} ≤
      ENNReal.ofReal (Real.exp (-(b * N)) / 4 + Real.exp (-(b * N)) / 4) := by
    have hX := isBandVersion_sub_of_realization hκ hH (Nat.sub_le_sub_left haj p.n)
    have hab : p.s (j - 1) ≤ p.s j := p.s_le_s hmono (Nat.sub_le j 1)
    -- `σ² = log(s_j/s_{j-1}) = D log 2`
    set D : ℝ := (((p.a j - p.a (j - 1)) : ℕ) : ℝ) with hDdef
    have hlogD : Real.log (p.s j / p.s (j - 1)) = D * Real.log 2 := by
      have e1 := BadBox.s_div_s_eq p haj hjn
      have e2 : p.s j / p.s (j - 1) = (2 : ℝ) ^ (p.a j - p.a (j - 1)) := by
        rw [← inv_div, e1, inv_pow, inv_inv]
      rw [e2, Real.log_pow]
    have hDN : D ≤ lam * N + 1 := by
      have h1 := dgzSeq_succ_le (K := p.K) hlam.le hj1
      rw [hjj, ← ha] at h1
      rw [hDdef, Nat.cast_sub haj]
      linarith
    have hD0 : 0 < D := by
      have h1 := dgzSeq_gap (K := p.K) hlam.le hj1
      rw [hjj, ← ha] at h1
      have : 0 < lam * N := by positivity
      rw [hDdef]
      linarith
    set uu : ℝ := p.supLevel j - C₃ - ε' * N with huu
    have hτu : τ * N ≤ uu := by
      have hNC'' : C₃ / ε' ≤ N := (Nat.le_ceil _).trans (by rw [hNdef]; exact_mod_cast hNC')
      have hC3 : C₃ ≤ ε' * N := by
        rw [div_le_iff₀ hε'pos] at hNC''
        linarith
      have e : (t₀ - δ₀) - τ - ε' = ε' := by rw [hτ, hε', hδ₀]; ring
      have : (Q * lam * Real.log 2 - δ₀) * N - C₃ - ε' * N ≥ τ * N := by
        have h1 : (t₀ - δ₀) * N - ε' * N - τ * N = ε' * N := by
          linear_combination N * e
        rw [ht₀] at h1
        linarith
      rw [huu]
      linarith
    have huu0 : 0 ≤ uu := le_trans (mul_nonneg (hσ0.trans hστ.le) (by linarith)) hτu
    have hw0 : 0 ≤ ε' * N := by positivity
    have hb3 := hsb hW (a := p.s (j - 1)) (b := p.s j) (p.s_pos _) hab hX
      (latPt (p.s (j - 1)) w) huu0 hw0
    rw [hlogD] at hb3
    refine (measure_mono fun ω hω => ?_).trans (hb3.trans (ENNReal.ofReal_le_ofReal ?_))
    · simp only [mem_ofPred_eq] at hω ⊢
      obtain ⟨z, hz, hlt⟩ := hω
      refine ⟨z, ?_, ?_⟩
      · rw [hpR] at hz
        exact hz
      · have e : uu + C₃ + ε' * N = p.supLevel j := by rw [huu]; ring
        rw [e]
        exact lt_of_lt_of_le hlt (le_abs_self _)
    · have g1 := hN₃ (p.a (j - 1)) D uu hN₃' hD0 hDN hτu
      have g2 := hN₄ (p.a (j - 1)) hN₄'
      exact add_le_add g1 g2
  -- combine
  have hfinal : Real.exp (-(b * N)) = (2 : ℝ) ^ (-(β * dgzLambda d Q * p.a (j - 1))) := by
    rw [Real.rpow_def_of_pos two_pos, hb, hNdef, ← hlamdef]
    congr 1
    ring
  calc P {ω | ¬ NiceCEvent p (fun q z => H q z ω) j u w}
      ≤ P (({ω | ¬ (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) <
          acrossDist p.ξ (fun z => H p.n z ω - H (p.n - p.a j) z ω) (latPt (p.s j) u)
            (4 * p.s j) (2 * p.s j)} ∪
        {ω | ¬ NiceCert p (fun q z => H q z ω) (j - 1) (latPt (p.s (j - 1)) w)}) ∪
      {ω | ∃ z ∈ cbox (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1)),
        p.supLevel j < H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω}) := measure_mono hsplit
    _ ≤ (ENNReal.ofReal (Real.exp (-(b * N)) / 4) + ENNReal.ofReal (Real.exp (-(b * N)) / 4)) +
        ENNReal.ofReal (Real.exp (-(b * N)) / 4 + Real.exp (-(b * N)) / 4) :=
      (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hP1 hP2))
        hP3)
    _ = ENNReal.ofReal (Real.exp (-(b * N))) := by
        have hx : 0 ≤ Real.exp (-(b * N)) / 4 := by positivity
        rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-(β * dgzLambda d Q * p.a (j - 1)))) := by rw [hfinal]

end DGZ

end HigherDimLQGMetric
