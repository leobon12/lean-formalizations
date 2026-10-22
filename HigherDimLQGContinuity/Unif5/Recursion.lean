import HigherDimLQGContinuity.Unif5.CEvent
import HigherDimLQGMetric.DGZ.BadBoxRecursion

/-!
# Uniform DGZ Lemmas 5.7 and 5.8: the recursion (A.9) (packet U2)

Blueprint Part D, `d:lem-u57` (a), (b) (= [C] (A.9)); NA3 §2.5, §2.15 rows 12–13; [8]-bp `r2:lem:57`, `r2:lem:58`.
Port of `HigherDimLQGMetric.DGZ.lemma57` and `DGZ.q_le` (`DGZ/BadBoxRecursion.lean`, MA7 D-5.5–5.9).

* `lemma57_unif_gen` / `lemma57_unif` (**target**, (A.9)):
  `q_j ≤ C (e^{-K a_j} + 2^{2dλa_{j-1}} q_{j-1}² + 2^{(d-β)λa_{j-1}} q_{j-1})` for `2 ≤ j`, `a_j ≤ n`, where
  `C = 1 + 16^d + 4^d (2R)^d` depends only on `(d, R)` (it counts boxes). The proof of `DGZ.lemma57` is repeated with
  the uniform Lemma 5.6 (`lemma56_unif_gen`); its other inputs are `ξ`-free and reused verbatim: the union bound
  `DGZ.BadBox.prob_bad_add_two_le` (deterministic case split + independence), the oscillation bound
  `DGZ.prob_not_niceOscCond_le` (any `λ ∈ [0, 1/4]`), the scale separation `DGZ.dgz_gap_of_le`,
  `DGZ.BadBox.exists_le_two_rpow` and the box count `DGZ.BadBox.card_subBoxes_le`.
* `q_le_unif_gen` / `q_le_unif` (**target**, Lemma 5.8): `q_j ≤ 2^{-α a_j}` for `1 ≤ j` with `a_j ≤ n`, by induction:
  the base `q₁ ≤ 2^{-αK⁴}` is `q1_le_unif` (choose `L` after `K`), and the step is (A.9) with the arithmetic
  `DGZ.BadBox.q_step_arith` at `β' = d + 3α/2` (it uses `(2d + α)λ < α`); the uniform `β = d + 2α ≥ β'` enters through
  `2^{(d-β)λN} ≤ 2^{(d-β')λN}`.

The general forms (`*_gen`) take `λ`, `β`, `Q̄`, `ν` (and `α`) as parameters with the inequalities that the proof uses,
over the `ξ` with `UHyp d κ b μ ξ` and `ξQ(ξ) - ξQ̄ ≥ ν`; the targets are their instances at the constants of (A.7)
(`uLambda`, `uBeta`, `uQbar`, `uNu`, `uAlpha`, `θ ≤ uTheta`). Every constant depends only on `(d, κ, b, μ)` and the
displayed parameters, never on `ξ`.
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

/-! ## Lemma 5.7 -/

/-- **Uniform DGZ Lemma 5.7 for general constants** ((A.9); port of `DGZ.lemma57`). Let `d ≥ 2`, `κ` admissible with
support radius `ρ`, `b, μ > 0`, `R ≥ 2ρ + 10`, `0 < λ ≤ 1/4`, `β ≥ 0`, `Q̄ > √(2β)` and `ν > 0`. There is
`C = 1 + 16^d + 4^d (2R)^d > 0` such that for every `θ > 0` with `θ(3 + λ) ≤ νλ/8` there is `K₀` with
`q_j ≤ C (e^{-K a_j} + 2^{2dλa_{j-1}} q_{j-1}² + 2^{(d-β)λa_{j-1}} q_{j-1})` for every `ξ` with `UHyp d κ b μ ξ` and
`ξQ(ξ) - ξQ̄ ≥ ν`, every dyadic realization, the sequence `dgzSeq λ K` with `K ≥ K₀`, all `n, k`, `2 ≤ j` with
`a_j ≤ n` and all boxes. -/
theorem lemma57_unif_gen (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ} (hR : 2 * ρ + 10 ≤ (R : ℝ))
    {lam β Qb ν : ℝ} (hlam : 0 < lam) (hlam4 : lam ≤ 1 / 4) (hβ : 0 ≤ β) (hβQ : √(2 * β) < Qb)
    (hν : 0 < ν) :
    ∃ C > 0, ∀ θ : ℝ, 0 < θ → θ * (3 + lam) ≤ ν * lam / 8 → ∃ K₀ : ℕ,
      ∀ ξ : ℝ, UHyp d κ b μ ξ → ν ≤ ξ * distExp d ξ - ξ * Qb →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.R = R → K₀ ≤ p.K →
          p.a = dgzSeq lam p.K → ∀ j : ℕ, 2 ≤ j → p.a j ≤ p.n → ∀ u u' : Zd d,
            P {ω | ¬ NiceBox p (fun q z => H q z ω) j u} ≤
              ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(p.K * p.a j : ℝ))) +
                ENNReal.ofReal ((2 : ℝ) ^ (2 * d * lam * p.a (j - 1))) *
                  P {ω | ¬ NiceBox p (fun q z => H q z ω) (j - 1) u'} ^ 2 +
                ENNReal.ofReal ((2 : ℝ) ^ ((d - β) * lam * p.a (j - 1))) *
                  P {ω | ¬ NiceBox p (fun q z => H q z ω) (j - 1) u'}) := by
  have hρ0 : 0 < ρ := hκ.radius_pos hρ
  have hR1 : 1 ≤ R := by exact_mod_cast (show (1 : ℝ) ≤ R by linarith)
  set C : ℝ := 1 + 16 ^ d + 4 ^ d * (2 * R) ^ d with hC
  have hC1 : 1 ≤ C := by
    rw [hC]
    have : (0 : ℝ) ≤ 16 ^ d + 4 ^ d * (2 * R) ^ d := by positivity
    linarith
  have hC0 : 0 ≤ C := by linarith
  refine ⟨C, by linarith, fun θ hθ hθν => ?_⟩
  obtain ⟨K₁, hK₁⟩ := lemma56_unif_gen hd hκ hb hμ hR1 hlam hlam4 hβ hβQ hν hθ hθν
  obtain ⟨K₂, hK₂⟩ := prob_not_niceOscCond_le (d := d) hκ hlam.le hlam4
  obtain ⟨K₃, hK₃⟩ := BadBox.exists_le_two_rpow (2 * ρ + R + 4) hlam
  refine ⟨max (max K₁ K₂) (max K₃ 2),
    fun ξ hξh hνξ Ω _ P W H hH p hpξ hpQ hpθ hpR hK ha j hj hjn u u' => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
  rw [show j + 2 - 1 = j + 1 from rfl]
  have hK1' : K₁ ≤ p.K := (le_max_left _ _).trans ((le_max_left _ _).trans hK)
  have hK2' : K₂ ≤ p.K := (le_max_right _ _).trans ((le_max_left _ _).trans hK)
  have hK3' : K₃ ≤ p.K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hK2 : 2 ≤ p.K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hK1 : 1 ≤ p.K := by omega
  have hmono : Monotone p.a := by rw [ha]; exact dgzSeq_monotone hlam.le hK1
  have hRp : 2 * ρ + 10 ≤ (p.R : ℝ) := by rw [hpR]; exact hR
  have hN4 : p.K ^ 4 ≤ p.a (j + 1) := by rw [ha]; exact pow_le_dgzSeq hlam.le hK1 (by omega)
  have hsS : superScale (p.a (j + 1)) ≤ p.a (j + 1) := by
    refine superScale_le_self ?_
    have : 2 ^ 4 ≤ p.K ^ 4 := Nat.pow_le_pow_left hK2 4
    omega
  have hgap : ∀ i, 2 ≤ i → i ≤ j + 2 → (2 * ρ + p.R + 4) * p.s (i - 1) ≤ p.s i :=
    dgz_gap_of_le p hlam.le hK1 ha (by rw [hpR]; exact hK₃ p.K hK3') hjn
  have hA := hK₂ Ω P W H hH p hK2' ha (j + 2) le_add_self hjn u
  have hCw : ∀ w : Zd d, P {ω | ¬ NiceCEvent p (fun q z => H q z ω) (j + 2) u w} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(β * lam * p.a (j + 1)))) := fun w =>
    hK₁ ξ hξh hνξ Ω P W H hH p hpξ hpQ hpθ hpR hK1' ha (j + 2) le_add_self hjn u w
  have key := BadBox.prob_bad_add_two_le hκ hH hρ p hmono hRp hjn hsS hgap u u' hA hCw
  refine key.trans ?_
  -- the coefficients
  set N : ℕ := p.a (j + 1) with hNdef
  set A : ℕ := p.a (j + 2) with hAdef
  have hNA : N ≤ A := hmono (Nat.le_succ _)
  have hup : (A : ℝ) ≤ (1 + lam) * N + 1 := by
    have h1 := dgzSeq_succ_le (K := p.K) hlam.le (i := j + 1) (by omega)
    rw [← ha] at h1
    exact h1
  have hS := BadBox.card_subBoxes_le (d := d) hNA hup
  set S : ℕ := (2 * 2 ^ (A - N) - 1) ^ d with hSdef
  set x : ℝ := (2 : ℝ) ^ ((d : ℝ) * lam * N) with hx
  have hx0 : 0 ≤ x := by positivity
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hcR : ((((2 * p.R - 1) ^ d : ℕ)) : ℝ) ≤ (2 * R) ^ d := by
    rw [hpR]
    have : (2 * R - 1) ^ d ≤ (2 * R) ^ d := Nat.pow_le_pow_left (Nat.sub_le _ _) d
    exact_mod_cast this
  rw [mul_add, mul_add]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- (a′)
    calc ENNReal.ofReal (Real.exp (-(p.K * A : ℝ))) =
          1 * ENNReal.ofReal (Real.exp (-(p.K * A : ℝ))) := (one_mul _).symm
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-(p.K * A : ℝ))) := by
          refine mul_le_mul' ?_ le_rfl
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hC1
  · -- `ℬ₁`
    rw [← mul_assoc, ← ENNReal.ofReal_mul hC0]
    refine mul_le_mul' ?_ le_rfl
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (2 : ℝ) ^ (2 * d * lam * N) = x * x := by
      rw [hx, ← Real.rpow_add two_pos]
      congr 1
      ring
    rw [e]
    push_cast
    have h16 : (4 : ℝ) ^ d * 4 ^ d ≤ C := by
      rw [hC, ← mul_pow]
      norm_num
      have : (0 : ℝ) ≤ 4 ^ d * (2 * R) ^ d := by positivity
      linarith
    calc (S : ℝ) * S ≤ (4 ^ d * x) * (4 ^ d * x) := mul_le_mul hS hS hS0 (by positivity)
      _ = (4 ^ d * 4 ^ d) * (x * x) := by ring
      _ ≤ C * (x * x) := mul_le_mul_of_nonneg_right h16 (by positivity)
  · -- `ℬ₂`
    have e : (S : ℝ≥0∞) * (ENNReal.ofReal ((2 : ℝ) ^ (-(β * lam * N))) *
        ((((2 * p.R - 1) ^ d : ℕ) : ℝ≥0∞) * P {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) u'})) =
        ENNReal.ofReal ((S : ℝ) * (((2 * p.R - 1) ^ d : ℕ) : ℝ) * (2 : ℝ) ^ (-(β * lam * N))) *
          P {ω | ¬ NiceBox p (fun q z => H q z ω) (j + 1) u'} := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      ring
    rw [e, ← mul_assoc, ← ENNReal.ofReal_mul hC0]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have e2 : (2 : ℝ) ^ (((d : ℝ) - β) * lam * N) = x * (2 : ℝ) ^ (-(β * lam * N)) := by
      rw [hx, ← Real.rpow_add two_pos]
      congr 1
      ring
    rw [e2]
    have hy0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(β * lam * N)) := by positivity
    have h4 : (4 : ℝ) ^ d * (2 * R) ^ d ≤ C := by
      rw [hC]
      have : (0 : ℝ) ≤ 16 ^ d := by positivity
      linarith
    calc (S : ℝ) * (((2 * p.R - 1) ^ d : ℕ) : ℝ) * (2 : ℝ) ^ (-(β * lam * N))
        ≤ (4 ^ d * x) * (2 * R) ^ d * (2 : ℝ) ^ (-(β * lam * N)) := by gcongr
      _ = (4 ^ d * (2 * R) ^ d) * (x * (2 : ℝ) ^ (-(β * lam * N))) := by ring
      _ ≤ C * (x * (2 : ℝ) ^ (-(β * lam * N))) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)

/-- **Uniform DGZ Lemma 5.7** (target `lemma57_unif`; (A.9), blueprint `d:lem-u57`(a); port of `DGZ.lemma57`). Let
`d ≥ 2`, `κ` admissible with support radius `ρ`, `b, μ > 0` and `R ≥ 2ρ + 10`; `λ = uLambda`, `β = uBeta`. There is
`C = 1 + 16^d + 4^d (2R)^d > 0` (depending only on `d, R`) such that for every `θ ∈ (0, uTheta]` there is `K₀`
(depending only on `d, κ, b, μ, R, θ`) with
`q_j ≤ C (e^{-K a_j} + 2^{2dλa_{j-1}} q_{j-1}² + 2^{(d-β)λa_{j-1}} q_{j-1})` for every `ξ ∈ S(b, μ)`, every dyadic
realization, the uniform parameters with `K ≥ K₀` (`p.ξ = ξ`, `p.Q = Q(ξ)`, `p.θ = θ`, `p.R = R`,
`a = dgzSeq λ K`), all `n, k`, `2 ≤ j` with `a_j ≤ n` and all boxes, where `q_j = P[B_{s_j}(s_j u) is bad]` and
`q_{j-1} = P[B_{s_{j-1}}(s_{j-1} u') is bad]`. -/
theorem lemma57_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ} (hR : 2 * ρ + 10 ≤ (R : ℝ)) :
    ∃ C > 0, ∀ θ : ℝ, 0 < θ → θ ≤ uTheta d b μ → ∃ K₀ : ℕ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.R = R → K₀ ≤ p.K →
          p.a = dgzSeq (uLambda d b μ) p.K → ∀ j : ℕ, 2 ≤ j → p.a j ≤ p.n → ∀ u u' : Zd d,
            P {ω | ¬ NiceBox p (fun q z => H q z ω) j u} ≤
              ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(p.K * p.a j : ℝ))) +
                ENNReal.ofReal ((2 : ℝ) ^ (2 * d * uLambda d b μ * p.a (j - 1))) *
                  P {ω | ¬ NiceBox p (fun q z => H q z ω) (j - 1) u'} ^ 2 +
                ENNReal.ofReal ((2 : ℝ) ^ ((d - uBeta d b μ) * uLambda d b μ * p.a (j - 1))) *
                  P {ω | ¬ NiceBox p (fun q z => H q z ω) (j - 1) u'}) := by
  obtain ⟨C, hC, h57⟩ := lemma57_unif_gen hd hκ hb hμ hρ hR (uLambda_pos hb hμ)
    (uLambda_le_quarter hb hμ) (uBeta_pos hb hμ).le (sqrt_two_uBeta_lt_uQbar hb hμ) (uNu_pos hb hμ)
  refine ⟨C, hC, fun θ hθ hθθ => ?_⟩
  obtain ⟨K₀, hK₀⟩ := h57 θ hθ (u2_theta_mul_le hb hμ hθθ)
  exact ⟨K₀, fun ξ hξh => hK₀ ξ hξh (hξh.uNu_le hμ)⟩

/-! ## Lemma 5.8 -/

/-- **Uniform DGZ Lemma 5.8 for general constants** (port of `DGZ.q_le`). Let `d ≥ 2`, `κ` admissible with support
radius `ρ`, `b, μ > 0`, `R ≥ 2ρ + 10`, `α > 0`, `λ = α/(4(α + d))`, `β ≥ d + 3α/2`, `Q̄ > √(2β)` and `ν > 0`. For every
`θ > 0` with `θ(3 + λ) ≤ νλ/8` there is `K₀` such that for every `K ≥ K₀` and `ε > 0` there is `L₀` with
`q_j ≤ 2^{-α a_j}` for every `ξ` with `UHyp d κ b μ ξ` and `ξQ(ξ) - ξQ̄ ≥ ν`, every dyadic realization, the parameters
with these `θ, K, ε, R`, `L ≥ L₀` and `a = dgzSeq λ K`, all `n, k`, `1 ≤ j` with `a_j ≤ n` and all boxes. -/
theorem q_le_unif_gen (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ} (hR : 2 * ρ + 10 ≤ (R : ℝ))
    {α lam β Qb ν : ℝ} (hα : 0 < α) (hlam : lam = α / (4 * (α + d))) (hβ : d + 3 * α / 2 ≤ β)
    (hβQ : √(2 * β) < Qb) (hν : 0 < ν) :
    ∀ θ : ℝ, 0 < θ → θ * (3 + lam) ≤ ν * lam / 8 → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ν ≤ ξ * distExp d ξ - ξ * Qb →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
          ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.ε = ε → p.R = R →
            p.K = K → L₀ ≤ p.L → p.a = dgzSeq lam K → ∀ j : ℕ, 1 ≤ j → p.a j ≤ p.n →
              ∀ u : Zd d, P {ω | ¬ NiceBox p (fun q z => H q z ω) j u} ≤
                ENNReal.ofReal ((2 : ℝ) ^ (-(α * p.a j))) := by
  intro θ hθ hθν
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlam0 : 0 < lam := by rw [hlam]; exact u0_lambda_pos hα
  have hlam4 : lam ≤ 1 / 4 := by rw [hlam]; exact u2_lambda_le_quarter hα
  have hg : (2 * d + α) * lam < α := by rw [hlam]; exact u0_two_mul_add_mul_lambda_lt hα
  have hβ0 : 0 ≤ β := by linarith
  set β' : ℝ := d + 3 * α / 2 with hβ'
  obtain ⟨C, hC, h57⟩ := lemma57_unif_gen hd hκ hb hμ hρ hR hlam0 hlam4 hβ0 hβQ hν
  obtain ⟨K₁, hK₁⟩ := h57 θ hθ hθν
  obtain ⟨K₂, hK₂⟩ := BadBox.q_step_arith d hα hlam0 hg hβ' hC
  refine ⟨max K₁ (max K₂ 1), fun K hK ε hε => ?_⟩
  obtain ⟨L₀, hL₀⟩ := q1_le_unif hd hκ hb hμ hε (K ^ 4)
    (η := (2 : ℝ) ^ (-(α * ((K ^ 4 : ℕ) : ℝ)))) (by positivity)
  refine ⟨L₀, fun ξ hξh hνξ Ω _ P W H hH p hpξ hpQ hpθ hpε hpR hpK hL ha j hj hjn u => ?_⟩
  have hK1 : 1 ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hK₁' : K₁ ≤ p.K := by rw [hpK]; exact (le_max_left _ _).trans hK
  have hK₂' : K₂ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have ha' : p.a = dgzSeq lam p.K := by rw [hpK]; exact ha
  have hmono : Monotone p.a := by rw [ha]; exact dgzSeq_monotone hlam0.le hK1
  induction j, hj using Nat.le_induction generalizing u with
  | base =>
      have ha0 : p.a 0 = 0 := by rw [ha]; rfl
      have ha1 : p.a 1 = K ^ 4 := by rw [ha]; rfl
      refine (hL₀ ξ hξh Ω P W H hH p hpξ hpQ hpε ha0 ha1.le hL u).trans (le_of_eq ?_)
      rw [ha1]
  | succ j hj ih =>
      have hjn' : p.a j ≤ p.n := (hmono (Nat.le_succ j)).trans hjn
      have hstep := hK₁ ξ hξh hνξ Ω P W H hH p hpξ hpQ hpθ hpR hK₁' ha' (j + 1) (by omega) hjn u 0
      rw [Nat.add_sub_cancel, hpK] at hstep
      have hq := ih hjn' 0
      refine hstep.trans ?_
      have hN4 : K ^ 4 ≤ p.a j := by rw [ha]; exact pow_le_dgzSeq hlam0.le hK1 hj
      have hNA : p.a j ≤ p.a (j + 1) := hmono (Nat.le_succ j)
      have hA : (p.a (j + 1) : ℝ) ≤ (1 + lam) * p.a j + 1 := by
        rw [ha]
        exact dgzSeq_succ_le hlam0.le hj
      have harith := hK₂ K (p.a j) (p.a (j + 1)) hK₂' hN4 hNA hA
      set y : ℝ := (2 : ℝ) ^ (-(α * p.a j)) with hy
      have hy0 : 0 ≤ y := by positivity
      have hC0 : 0 ≤ C := hC.le
      have he0 : 0 ≤ Real.exp (-(K * p.a (j + 1) : ℝ)) := (Real.exp_pos _).le
      have hx₂0 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * d * lam * p.a j) := by positivity
      have hx₃0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((d - β') * lam * p.a j) := by positivity
      -- `β ≥ β' = d + 3α/2`
      have hββ : ENNReal.ofReal ((2 : ℝ) ^ ((d - β) * lam * p.a j)) ≤
          ENNReal.ofReal ((2 : ℝ) ^ ((d - β') * lam * p.a j)) := by
        refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
        have h0 : (0 : ℝ) ≤ lam * p.a j := by positivity
        have h1 : (d : ℝ) - β ≤ d - β' := by linarith
        calc ((d : ℝ) - β) * lam * p.a j = ((d : ℝ) - β) * (lam * p.a j) := by ring
          _ ≤ ((d : ℝ) - β') * (lam * p.a j) := mul_le_mul_of_nonneg_right h1 h0
          _ = ((d : ℝ) - β') * lam * p.a j := by ring
      have hq2 : P {ω | ¬ NiceBox p (fun q z => H q z ω) j 0} ^ 2 ≤ ENNReal.ofReal y ^ 2 := by
        gcongr
      calc ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(K * p.a (j + 1) : ℝ))) +
            ENNReal.ofReal ((2 : ℝ) ^ (2 * d * lam * p.a j)) *
              P {ω | ¬ NiceBox p (fun q z => H q z ω) j 0} ^ 2 +
            ENNReal.ofReal ((2 : ℝ) ^ ((d - β) * lam * p.a j)) *
              P {ω | ¬ NiceBox p (fun q z => H q z ω) j 0})
          ≤ ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-(K * p.a (j + 1) : ℝ))) +
            ENNReal.ofReal ((2 : ℝ) ^ (2 * d * lam * p.a j)) * ENNReal.ofReal y ^ 2 +
            ENNReal.ofReal ((2 : ℝ) ^ ((d - β') * lam * p.a j)) * ENNReal.ofReal y) := by
            refine mul_le_mul' le_rfl (add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hq2))
              (mul_le_mul' hββ hq))
        _ = ENNReal.ofReal (C * (Real.exp (-(K * p.a (j + 1) : ℝ)) +
            (2 : ℝ) ^ (2 * d * lam * p.a j) * y ^ 2 +
            (2 : ℝ) ^ ((d - β') * lam * p.a j) * y)) := by
            rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add he0 (by positivity), ENNReal.ofReal_mul hx₂0,
              ENNReal.ofReal_mul hx₃0, ENNReal.ofReal_pow hy0]
        _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(α * p.a (j + 1)))) := ENNReal.ofReal_le_ofReal harith

/-- **Uniform DGZ Lemma 5.8** (target `q_le_unif`; blueprint `d:lem-u57`(b); port of `DGZ.q_le`). Let `d ≥ 2`, `κ`
admissible with support radius `ρ`, `b, μ > 0` and `R ≥ 2ρ + 10`; `α = uAlpha`, `λ = uLambda`. For every
`θ ∈ (0, uTheta]` there is `K₀` such that for every `K ≥ K₀` and `ε > 0` there is `L₀` (all depending only on
`d, κ, b, μ, R` and the displayed parameters) with `q_j ≤ 2^{-α a_j}` for every `ξ ∈ S(b, μ)`, every dyadic
realization, the uniform parameters with these `θ, K, ε, R` and `L ≥ L₀` (`p.ξ = ξ`, `p.Q = Q(ξ)`,
`a = dgzSeq λ K`), all `n, k`, `1 ≤ j` with `a_j ≤ n` and all boxes. -/
theorem q_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ} (hR : 2 * ρ + 10 ≤ (R : ℝ)) :
    ∀ θ : ℝ, 0 < θ → θ ≤ uTheta d b μ → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ ε : ℝ, 0 < ε →
      ∃ L₀ : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
          ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.ε = ε → p.R = R →
            p.K = K → L₀ ≤ p.L → p.a = dgzSeq (uLambda d b μ) K → ∀ j : ℕ, 1 ≤ j → p.a j ≤ p.n →
              ∀ u : Zd d, P {ω | ¬ NiceBox p (fun q z => H q z ω) j u} ≤
                ENNReal.ofReal ((2 : ℝ) ^ (-(uAlpha d b μ * p.a j))) := by
  intro θ hθ hθθ
  have hα := uAlpha_pos (d := d) hb hμ
  have hβ : (d : ℝ) + 3 * uAlpha d b μ / 2 ≤ uBeta d b μ := by
    rw [uBeta_eq]
    linarith
  obtain ⟨K₀, hK₀⟩ := q_le_unif_gen hd hκ hb hμ hρ hR hα rfl hβ (sqrt_two_uBeta_lt_uQbar hb hμ)
    (uNu_pos hb hμ) θ hθ (u2_theta_mul_le hb hμ hθθ)
  refine ⟨K₀, fun K hK ε hε => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hK₀ K hK ε hε
  exact ⟨L₀, fun ξ hξh => hL₀ ξ hξh (hξh.uNu_le hμ)⟩

end HigherDimLQGContinuity
