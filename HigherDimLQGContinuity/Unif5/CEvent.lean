import HigherDimLQGContinuity.Unif5.Q1
import HigherDimLQGContinuity.Unif5.Cert
import HigherDimLQGContinuity.Unif4.SuperExpAcross
import HigherDimLQGMetric.DGZ.BadBoxCEvent

/-!
# Uniform DGZ Lemma 5.6 via (A.8) (packet U2)

Blueprint Part D, `d:lem-u56` (equation (D.3) = [C] (A.8)); NA3 Details (c) R4 (a new proof), §2.5, §2.15 row 11.
Replaces `HigherDimLQGMetric.DGZ.lemma56` (`DGZ/BadBoxCEvent.lean`), whose `θ₀(β)` and `K₀` depend on `(ξ, Q)` through
the lower bound `s_j* ≥ (Qλ log 2 - δ₀) a_{j-1}` of [1] (5.12) (it needs `4(θ/ξ) log 2 ≤ δ₀/2` and `2/(ξ√K) ≤ δ₀/2`).

`𝒞(x,z)` (`DGZ.NiceCEvent p H j u w`, reused verbatim, as are `DGZ.NiceParams.supLevel` and `tStar`) is the
intersection of three events; write `u = a_{j-1}`, `v = a_j`, `λu ≤ v - u ≤ λu + 1`.

* **Across**: by scaling (`DGZ.prob_niceCEvent_across_eq`) and the uniform Lemma 4.10 (`superExpAcross_unif`,
  `δ = θ`, radii `(4, 2)`) it fails with probability `≤ C₁ e^{-v log v}`.
* **Certificate**: `prob_not_niceCert_le_unif` gives `≤ C₂ e^{-u log u}`.
* **Supremum** ((A.8), the new step): multiplied by `ξ > 0` the condition `H ≤ s_j*`, `H = h_{n-v,n-u}` on
  `B̄_{4R s_{j-1}}(z)`, reads `ξ H ≤ ϕ(v-u) log 2 - θ(v+u) log 2 - K^{3/2} √v`. The deterministic lemma
  `u2_supLevel_ge` shows `s_j* ≥ Q̄ λ log 2 · u` whenever `ϕ - ξQ̄ ≥ ν`, `θ(3+λ) ≤ νλ/8` and
  `2/√K ≤ νλ log 2/4` (the margin is `≥ (5/8) νλ u log 2 ≥ 0`, uniformly in `ξ`). So the supremum event fails only if
  `H > Q̄ λ u log 2 - δ₀ u`, a `ξ`-free event, and the small-box Gaussian tail (`DGZ.exists_smallBox_gaussian_tail`,
  box radius `4R` in units of `s_{j-1}`, variance `(v-u) log 2 ≤ (λu+1) log 2`) bounds it by `2^{-βλu}/2` for
  `u ≥ u₀`, because `Q̄ > √(2β)`.

Main statements:
* `u2_supLevel_ge`: the deterministic (A.8) bound (any `λ ∈ [0, 1/4]`, any `Q̄ ≥ 0`).
* `lemma56_unif_gen`: the uniform Lemma 5.6 for any `λ ∈ (0, 1/4]`, `β ≥ 0`, `Q̄ > √(2β)`, `ν > 0` and
  `θ ∈ (0, νλ/(8(3+λ))]`, over the `ξ` with `UHyp d κ b μ ξ` and `ϕ(ξ) - ξQ̄ ≥ ν`.
* `lemma56_unif` (**target**, `d:lem-u56`): the constants of (A.7): `λ = uLambda`, `β = uBeta`, `Q̄ = uQbar`,
  `ν = uNu`, every `θ ∈ (0, uTheta]`, all `ξ ∈ S(b, μ)` (`UHyp.uNu_le` gives `ϕ - ξQ̄ ≥ ν`):
  `P[𝒞(x,z)ᶜ] ≤ 2^{-βλ a_{j-1}}` for `K ≥ K₀(d, κ, b, μ, R, θ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## The deterministic part of (A.8) -/

/-- **(A.8), deterministic part** (`d:lem-u56`, *Supremum*; NA3 R4): for DGZ's sequence with `0 ≤ λ ≤ 1/4`,
`K ≥ 1`, `2 ≤ j`, `ξ > 0`, `θ ≥ 0`, `Q̄ ≥ 0` and `ν ≥ 0`: if `ν ≤ ξQ - ξQ̄`, `θ(3 + λ) ≤ νλ/8` and
`2/√K ≤ νλ log 2/4`, then `s_j* ≥ Q̄ λ log 2 · a_{j-1}`.

Proof: with `N = a_{j-1}`, `A = a_j`, `ϕ = ξQ`, `ξ s_j* = ϕ(A - N) log 2 - θ(A + N) log 2 - K^{3/2} √A`, and
`ϕ(A - N) ≥ ϕλN`, `A + N ≤ (3+λ)N`, `K^{3/2} √A ≤ (2/√K) N` (`A ≤ 4N`, `N ≥ K⁴`), so
`ξ s_j* ≥ λN log 2 · (ϕ - ν/8 - ν/4) ≥ ξ Q̄ λ N log 2`; divide by `ξ`. -/
theorem u2_supLevel_ge (p : NiceParams) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam4 : lam ≤ 1 / 4)
    (hK : 1 ≤ p.K) (ha : p.a = dgzSeq lam p.K) (hξ : 0 < p.ξ) (hθ : 0 ≤ p.θ) {Qb ν : ℝ}
    (hQb : 0 ≤ Qb) (hν0 : 0 ≤ ν) (hν : ν ≤ p.ξ * p.Q - p.ξ * Qb)
    (hθν : p.θ * (3 + lam) ≤ ν * lam / 8) (hKν : 2 / √(p.K : ℝ) ≤ ν * lam * Real.log 2 / 4)
    {j : ℕ} (hj : 2 ≤ j) :
    Qb * lam * Real.log 2 * p.a (j - 1) ≤ p.supLevel j := by
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
  -- `ϕ = ξQ ≥ ξQ̄ + ν ≥ 0`
  have hQb' : 0 ≤ p.ξ * Qb := mul_nonneg hξ.le hQb
  have hϕ : 0 ≤ p.ξ * p.Q := by linarith
  -- (a) the main term
  have ha' : p.ξ * p.Q * (lam * N) * Real.log 2 ≤ p.ξ * p.Q * (A - N) * Real.log 2 := by
    have h1 := mul_le_mul_of_nonneg_left hgap hϕ
    exact mul_le_mul_of_nonneg_right h1 hℓ.le
  -- (b) the `θ` term
  have hb' : p.θ * (A + N) * Real.log 2 ≤ p.θ * (3 + lam) * (N * Real.log 2) := by
    have h1 : A + N ≤ (3 + lam) * N := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h1 hθ
    have h4 := mul_le_mul_of_nonneg_right h3 hℓ.le
    calc p.θ * (A + N) * Real.log 2 ≤ p.θ * ((3 + lam) * N) * Real.log 2 := h4
      _ = p.θ * (3 + lam) * (N * Real.log 2) := by ring
  -- (c) the `K^{3/2} √a_j` term
  have hc' : (p.K : ℝ) ^ ((3 : ℝ) / 2) * √A ≤ 2 / √(p.K : ℝ) * N := by
    rw [BadBox.rpow_three_halves_eq hK0]
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
    calc (p.K : ℝ) * √(p.K : ℝ) * √A ≤ 2 * N / √(p.K : ℝ) := h1
      _ = 2 / √(p.K : ℝ) * N := by ring
  -- `ξ s_j*`
  have e : p.ξ * p.supLevel j = p.ξ * p.Q * (A - N) * Real.log 2 - p.θ * (A + N) * Real.log 2 -
      (p.K : ℝ) ^ ((3 : ℝ) / 2) * √A := by
    have e0 : p.supLevel j = p.Q * (A - N) * Real.log 2 - p.θ / p.ξ * (A + N) * Real.log 2 -
        (p.K : ℝ) ^ ((3 : ℝ) / 2) * √A / p.ξ := rfl
    rw [e0]
    field_simp
  -- combine
  have hX0 : 0 ≤ lam * N * Real.log 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hθν (by positivity : (0 : ℝ) ≤ N * Real.log 2)
  have h2 := mul_le_mul_of_nonneg_right hKν (by positivity : (0 : ℝ) ≤ N)
  have h3 : (p.ξ * Qb + ν) * (lam * N * Real.log 2) ≤ p.ξ * p.Q * (lam * N * Real.log 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hX0
  have h4 : 0 ≤ ν * (lam * N * Real.log 2) := mul_nonneg hν0 hX0
  refine le_of_mul_le_mul_left ?_ hξ
  rw [e]
  have e1 : p.ξ * (Qb * lam * Real.log 2 * N) = p.ξ * Qb * (lam * N * Real.log 2) := by ring
  have e2 : ν * lam / 8 * (N * Real.log 2) = ν * (lam * N * Real.log 2) / 8 := by ring
  have e3 : ν * lam * Real.log 2 / 4 * N = ν * (lam * N * Real.log 2) / 4 := by ring
  have e4 : p.ξ * p.Q * (lam * N) * Real.log 2 = p.ξ * p.Q * (lam * N * Real.log 2) := by ring
  rw [e2] at h1
  rw [e3] at h2
  rw [e4] at ha'
  rw [e1]
  linarith

/-! ## Lemma 5.6 -/

/-- **Uniform DGZ Lemma 5.6 for general constants** (the proof of `d:lem-u56`, NA3 R4). Let `d ≥ 2`, `κ` admissible,
`b, μ > 0`, `R ≥ 1`, `0 < λ ≤ 1/4`, `β ≥ 0`, `Q̄ > √(2β)`, `ν > 0` and `0 < θ` with `θ(3 + λ) ≤ νλ/8`. There is
`K₀` (depending only on `d, κ, b, μ, R, λ, β, Q̄, ν, θ`) such that `P[𝒞(x,z)ᶜ] ≤ 2^{-βλ a_{j-1}}` for every `ξ` with
`UHyp d κ b μ ξ` and `ξQ(ξ) - ξQ̄ ≥ ν`, every dyadic realization, all parameters with `p.ξ = ξ`, `p.Q = Q(ξ)`,
`p.θ = θ`, `p.R = R`, `K ≥ K₀` and the sequence `dgzSeq λ K`, all `n, k`, `2 ≤ j` with `a_j ≤ n` and all
`x = s_j u`, `z = s_{j-1} w`. -/
theorem lemma56_unif_gen (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {R : ℕ} (hR : 1 ≤ R) {lam β Qb ν : ℝ} (hlam : 0 < lam) (hlam4 : lam ≤ 1 / 4)
    (hβ : 0 ≤ β) (hβQ : √(2 * β) < Qb) (hν : 0 < ν) {θ : ℝ} (hθ : 0 < θ)
    (hθν : θ * (3 + lam) ≤ ν * lam / 8) :
    ∃ K₀ : ℕ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ν ≤ ξ * distExp d ξ - ξ * Qb →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.R = R → K₀ ≤ p.K →
          p.a = dgzSeq lam p.K → ∀ j : ℕ, 2 ≤ j → p.a j ≤ p.n → ∀ u w : Zd d,
            P {ω | ¬ NiceCEvent p (fun q z => H q z ω) j u w} ≤
              ENNReal.ofReal ((2 : ℝ) ^ (-(β * lam * p.a (j - 1)))) := by
  have hℓ : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hQb0 : 0 ≤ Qb := (Real.sqrt_nonneg _).trans hβQ.le
  -- the constants of the proof (all `ξ`-free)
  set σ := √(2 * β) * lam * Real.log 2 with hσ
  set t₀ := Qb * lam * Real.log 2 with ht₀
  have hσt₀ : σ < t₀ := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hβQ hlam) hℓ
  have hσ0 : 0 ≤ σ := by positivity
  set δ₀ := (t₀ - σ) / 2 with hδ₀
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀]; linarith
  set τ := (t₀ - δ₀ + σ) / 2 with hτ
  have hστ : σ < τ := by rw [hτ]; linarith
  set ε' := δ₀ / 4 with hε'
  have hε'pos : 0 < ε' := by positivity
  set bb := β * lam * Real.log 2 with hbb
  have hbb0 : 0 ≤ bb := by positivity
  have hσb : σ ^ 2 = 2 * lam * Real.log 2 * bb := by
    rw [hσ, hbb, mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
    ring
  -- the three probability inputs (uniform in `ξ`)
  obtain ⟨C₁, hC₁, hacr⟩ := superExpAcross_unif hd hκ hb hμ hθ (r₁ := 4) (r₂ := 2) (by norm_num)
    (by norm_num)
  obtain ⟨C₂, hC₂, hcert⟩ := prob_not_niceCert_le_unif hd hκ hb hμ hθ hR
  obtain ⟨C₃, hC₃, hsb⟩ := exists_smallBox_gaussian_tail.{0} hκ (R := 4 * R) (by positivity)
  -- the thresholds
  obtain ⟨N₁, hN₁⟩ := BadBox.exists_mul_exp_neg_mul_log_le C₁ bb hC₁.le
  obtain ⟨N₂, hN₂⟩ := BadBox.exists_mul_exp_neg_mul_log_le C₂ bb hC₂.le
  obtain ⟨N₃, hN₃⟩ := BadBox.exists_gauss_le hσ0 hστ hlam hbb0 hσb
  obtain ⟨N₄, hN₄⟩ := BadBox.exists_two_exp_neg_sq_div_le bb hε'pos hC₃
  set Kν : ℕ := ⌈(8 / (ν * lam * Real.log 2)) ^ 2⌉₊ with hKνdef
  set NC : ℕ := ⌈C₃ / ε'⌉₊ with hNCdef
  refine ⟨max (max (max N₁ N₂) (max N₃ N₄)) (max (max Kν NC) 8),
    fun ξ hξh hνξ Ω _ P W H hH p hpξ hpQ hpθ hpR hK ha j hj hjn u w => ?_⟩
  have hξ : 0 < ξ := hξh.base.xi_pos
  have hκ' := hκ
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
  have hKν' : Kν ≤ p.K := (le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hK))
  have hNC' := hKN NC ((le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hK)))
  -- (A.8): `s_j* ≥ Q̄ λ log 2 · a_{j-1}`
  have hKν2 : 2 / √(p.K : ℝ) ≤ ν * lam * Real.log 2 / 4 := by
    have hνl : 0 < ν * lam * Real.log 2 := by positivity
    have hKr : (8 / (ν * lam * Real.log 2)) ^ 2 ≤ (p.K : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hKν')
    have hsK : 8 / (ν * lam * Real.log 2) ≤ √(p.K : ℝ) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      exact hKr
    have hsK0 : 0 < √(p.K : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < p.K by omega))
    rw [div_le_iff₀ hsK0]
    have e8 : ν * lam * Real.log 2 / 4 * (8 / (ν * lam * Real.log 2)) = 2 := by
      field_simp
      ring
    calc (2 : ℝ) = ν * lam * Real.log 2 / 4 * (8 / (ν * lam * Real.log 2)) := e8.symm
      _ ≤ ν * lam * Real.log 2 / 4 * √(p.K : ℝ) := by gcongr
  have hsup := u2_supLevel_ge p hlam.le hlam4 hK1 ha (by rw [hpξ]; exact hξ)
    (by rw [hpθ]; exact hθ.le) hQb0 hν.le (by rw [hpξ, hpQ]; exact hνξ)
    (by rw [hpθ]; exact hθν) hKν2 hj
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
        (4 * p.s j) (2 * p.s j)} ≤ ENNReal.ofReal (Real.exp (-(bb * N)) / 4) := by
    rw [prob_niceCEvent_across_eq hκ hH p hjn u, hpξ, hpQ, hpθ]
    exact (hacr ξ hξh Ω P W H hH (p.a j)).trans
      (ENNReal.ofReal_le_ofReal (hN₁ _ _ hN₁' haj))
  -- (ii) certificate
  have hP2 : P {ω | ¬ NiceCert p (fun q z => H q z ω) (j - 1) (latPt (p.s (j - 1)) w)} ≤
      ENNReal.ofReal (Real.exp (-(bb * N)) / 4) := by
    have hss : superScale (p.a (j - 1)) ≤ p.a (j - 1) :=
      superScale_le_self ((hKN 8 hK8))
    refine (hcert ξ hξh Ω P W H hH p hpξ hpQ hpθ hpR (j - 1) hj1n hss _).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact hN₂ _ _ hN₂' le_rfl
  -- (iii) supremum: the `ξ`-free threshold `Q̄λ log 2 · a_{j-1}` of (A.8)
  have hP3 : P {ω | ∃ z ∈ cbox (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1)),
      p.supLevel j < H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω} ≤
      ENNReal.ofReal (Real.exp (-(bb * N)) / 4 + Real.exp (-(bb * N)) / 4) := by
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
      have hδN : 0 ≤ δ₀ * N := by positivity
      have : (t₀ - δ₀) * N - C₃ - ε' * N ≥ τ * N := by
        have h1 : (t₀ - δ₀) * N - ε' * N - τ * N = ε' * N := by
          linear_combination N * e
        linarith
      have h2 : (t₀ - δ₀) * N ≤ p.supLevel j := by
        have : t₀ * N ≤ p.supLevel j := hsup
        nlinarith
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
  have hfinal : Real.exp (-(bb * N)) = (2 : ℝ) ^ (-(β * lam * p.a (j - 1))) := by
    rw [Real.rpow_def_of_pos two_pos, hbb, hNdef]
    congr 1
    ring
  calc P {ω | ¬ NiceCEvent p (fun q z => H q z ω) j u w}
      ≤ P (({ω | ¬ (2 : ℝ) ^ (-(p.n : ℝ) + (p.ξ * p.Q - p.θ) * p.a j) <
          acrossDist p.ξ (fun z => H p.n z ω - H (p.n - p.a j) z ω) (latPt (p.s j) u)
            (4 * p.s j) (2 * p.s j)} ∪
        {ω | ¬ NiceCert p (fun q z => H q z ω) (j - 1) (latPt (p.s (j - 1)) w)}) ∪
      {ω | ∃ z ∈ cbox (latPt (p.s (j - 1)) w) (4 * p.R * p.s (j - 1)),
        p.supLevel j < H (p.n - p.a (j - 1)) z ω - H (p.n - p.a j) z ω}) := measure_mono hsplit
    _ ≤ (ENNReal.ofReal (Real.exp (-(bb * N)) / 4) + ENNReal.ofReal (Real.exp (-(bb * N)) / 4)) +
        ENNReal.ofReal (Real.exp (-(bb * N)) / 4 + Real.exp (-(bb * N)) / 4) :=
      (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans (add_le_add hP1 hP2))
        hP3)
    _ = ENNReal.ofReal (Real.exp (-(bb * N))) := by
        have hx : 0 ≤ Real.exp (-(bb * N)) / 4 := by positivity
        rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-(β * lam * p.a (j - 1)))) := by rw [hfinal]

/-- `θ ≤ θ_U = νλ/(8(3+λ))` gives `θ(3 + λ) ≤ νλ/8` for the constants of (A.7). -/
theorem u2_theta_mul_le {b μ θ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hθ : θ ≤ uTheta d b μ) :
    θ * (3 + uLambda d b μ) ≤ uNu d b μ * uLambda d b μ / 8 := by
  have hl : 0 < 3 + uLambda d b μ := by linarith [uLambda_pos (d := d) hb hμ]
  calc θ * (3 + uLambda d b μ) ≤ uTheta d b μ * (3 + uLambda d b μ) :=
        mul_le_mul_of_nonneg_right hθ hl.le
    _ = uNu d b μ * uLambda d b μ / 8 := by
        unfold uTheta
        field_simp

/-- **Uniform DGZ Lemma 5.6 via (A.8)** (target `lemma56_unif`; blueprint `d:lem-u56`; NA3 R4; replaces
`DGZ.lemma56`). Let `d ≥ 2`, `κ` admissible, `b, μ > 0` and `R ≥ 1`; let `λ, β, Q̄, ν, θ_U` be the constants of (A.7)
(`uLambda`, `uBeta`, `uQbar`, `uNu`, `uTheta`). For every `θ ∈ (0, θ_U]` there is `K₀` (depending only on
`d, κ, b, μ, R, θ`) such that `P[𝒞(x,z)ᶜ] ≤ 2^{-βλ a_{j-1}}` for every `ξ ∈ S(b, μ)` (`UHyp d κ b μ ξ`), every dyadic
realization, all parameters with `p.ξ = ξ`, `p.Q = Q(ξ)`, `p.θ = θ`, `p.R = R`, `K ≥ K₀` and the uniform sequence
`dgzSeq λ K`, all `n, k`, `2 ≤ j` with `a_j ≤ n`, and all `x = s_j u`, `z = s_{j-1} w`. -/
theorem lemma56_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {R : ℕ} (hR : 1 ≤ R) :
    ∀ θ : ℝ, 0 < θ → θ ≤ uTheta d b μ → ∃ K₀ : ℕ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.R = R → K₀ ≤ p.K →
          p.a = dgzSeq (uLambda d b μ) p.K → ∀ j : ℕ, 2 ≤ j → p.a j ≤ p.n → ∀ u w : Zd d,
            P {ω | ¬ NiceCEvent p (fun q z => H q z ω) j u w} ≤
              ENNReal.ofReal ((2 : ℝ) ^ (-(uBeta d b μ * uLambda d b μ * p.a (j - 1)))) := by
  intro θ hθ hθθ
  obtain ⟨K₀, hK₀⟩ := lemma56_unif_gen hd hκ hb hμ hR (uLambda_pos hb hμ) (uLambda_le_quarter hb hμ)
    (uBeta_pos hb hμ).le (sqrt_two_uBeta_lt_uQbar hb hμ) (uNu_pos hb hμ) hθ
    (u2_theta_mul_le hb hμ hθθ)
  exact ⟨K₀, fun ξ hξh => hK₀ ξ hξh (hξh.uNu_le hμ)⟩

end HigherDimLQGContinuity
