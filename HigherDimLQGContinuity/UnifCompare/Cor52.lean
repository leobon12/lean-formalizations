import HigherDimLQGContinuity.UnifCompare.Prop51
import HigherDimLQGMetric.DGZ.CompareCor52

/-!
# Uniform DGZ Corollary 5.2, right inequality: the interface `UCor52Shape` (packet U3)

Blueprint Part D, `d:prop-u52`(b), (D.4) (NA3 §2.2, §2.6, ROUTE-1; [8]-bp `r2:cor:52`). Port of
`HigherDimLQGMetric.DGZ.cor52Shape` (`DGZ/CompareCor52.lean`, MA7 D-5.2; ruling M23 (iii) of the previous campaign).

**Statement** (`uCor52 : UCor52Shape d κ`, interface I6 of `Core/Interfaces.lean`, exactly). For `d ≥ 2`, `κ`
admissible, `b, μ > 0`, `ε > 0` and `0 < q < q' < 1` there is `C > 0` (depending only on `d, κ, b, μ, ε, q, q'`)
such that for every `ξ ∈ S(b, μ)`, every dyadic realization and all `0 ≤ k ≤ n`:
`a^ξ_{n-k}(q) ≤ C 2^{(1-ϕ(ξ)+ε)k} a^ξ_n(q')`, `ϕ(ξ) = ξQ(ξ)`.

**Proof** (the three-case split of the sealed proof; every constant before `ξ`). Let `c, N` be the constants of the
uniform Proposition 5.1 (`prop51_unif`), `N₁ ≥ N` with `2^{-cN₁} ≤ q' - q`, and `η = εc/(2(1+c))`.
* `k = 0`: monotonicity of the lower quantile, `C ≥ 1`.
* `k ≥ 1`, `k ≤ c(n-k)`, `n - k ≥ N₁`: `prop51_unif` at `(n-k, k)` gives `a^ξ_{n-k}(q) ≤ c⁻¹ 2^{(1-ϕ+ε)k} a^ξ_n(q')`.
* otherwise (`k > c(n-k)` or `n - k < N₁`): U1's uniform quantile bounds `exists_aQ_le_unif`, `exists_le_aQ_unif`
  (from U-EXP, interface I4, proved by U0's `uExpRate`/`uExp_aQ_bounds`) give
  `a^ξ_{n-k}(q) ≤ A 2^{-(1-ϕ-η)(n-k)}` and `a^ξ_n(q') ≥ c' 2^{-(1-ϕ+η)n}` with `A, c'` independent of `ξ ∈ (0, b]`;
  the ratio is `≤ (A/c') 2^E`, `E = 2ηn - (ε+η)k ≤ 2ηN₁`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- **U-Cor 5.2** ((A.2) upper half, uniformly in `ξ ∈ S(b, μ)`; Part D `d:prop-u52`(b), (D.4); port of
`DGZ.cor52Shape`): the interface `UCor52Shape d κ` (I6) holds for `d ≥ 2` and every admissible kernel `κ`. -/
theorem uCor52 (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) : UCor52Shape d κ := by
  intro b μ hb hμ ε hε q q' hq0 hqq' hq'1
  have hq1 : q < 1 := hqq'.trans hq'1
  have hq'0 : 0 < q' := hq0.trans hqq'
  obtain ⟨c, hc, N, hP51⟩ := prop51_unif hd hκ hb hμ hε
  have hq'top : q' ≠ ⊤ := ne_top_of_lt hq'1
  have hgap : 0 < (q' - q).toReal :=
    ENNReal.toReal_pos (tsub_pos_of_lt hqq').ne' (ne_top_of_le_ne_top hq'top tsub_le_self)
  obtain ⟨N₁', hN₁'⟩ := cmp_exists_two_rpow_le hc hgap
  set N₁ : ℕ := max N N₁' with hN₁def
  set η : ℝ := ε * c / (2 * (1 + c)) with hηdef
  have hη : 0 < η := by positivity
  have hηc : 2 * η * (1 + c) = ε * c := by
    rw [hηdef]
    field_simp
  have hηε : η ≤ ε := by
    rw [hηdef, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨A, hA, haQ⟩ := exists_aQ_le_unif.{0} hd hκ hb hq0 hq1 hη
  obtain ⟨c', hc', hlaQ⟩ := exists_le_aQ_unif.{0} hd hκ hb hq'0 hq'1 hη
  set C₂ : ℝ := A / c' * (2 : ℝ) ^ (2 * η * N₁) with hC₂def
  have hC₂ : 0 < C₂ := by positivity
  refine ⟨max c⁻¹ (max C₂ 1), lt_of_lt_of_le (inv_pos.2 hc) (le_max_left _ _),
    fun ξ hU Ω _ P W H hH n k hkn => ?_⟩
  have hξ : 0 < ξ := hU.base.xi_pos
  have hξb : ξ ≤ b := hU.le_b
  set Q : ℝ := distExp d ξ with hQdef
  set C : ℝ := max c⁻¹ (max C₂ 1) with hCdef
  have hpos : 0 < aQ P H ξ n q' :=
    lt_of_lt_of_le (by positivity) (hlaQ ξ hξ hξb Ω P W H hH n)
  have hX : 0 < (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) := Real.rpow_pos_of_pos two_pos _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`
    have hC1 : 1 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
    simp only [Nat.sub_zero, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    calc aQ P H ξ n q ≤ aQ P H ξ n q' := cmp_aQ_mono hH ξ n hq0 hqq'.le hq'1
      _ ≤ C * aQ P H ξ n q' := le_mul_of_one_le_left hpos.le hC1
  by_cases hcase : (k : ℝ) ≤ c * ((n - k : ℕ) : ℝ) ∧ N₁ ≤ n - k
  · -- Proposition 5.1 at `(n - k, k)`
    obtain ⟨hkc, hN₁⟩ := hcase
    have hP := hP51 ξ hU Ω P W H hH (n - k) k ((le_max_left _ _).trans hN₁) hk hkc
    rw [Nat.sub_add_cancel hkn] at hP
    have hsmall : ENNReal.ofReal ((2 : ℝ) ^ (-(c * ((n - k : ℕ) : ℝ)))) ≤ q' - q := by
      rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top hq'top tsub_le_self)]
      exact ENNReal.ofReal_le_ofReal (hN₁' _ ((le_max_right _ _).trans hN₁))
    set a : ℝ := aQ P H ξ n q' with hadef
    set X : ℝ := c⁻¹ * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * a with hXdef
    have hqa : q' ≤ P {ω | lfppDistance d ξ (fun z => H n z ω) ≤ a} :=
      (cmp_le_prob_iff_aQ_le hH ξ n hq'0 hq'1 a).2 le_rfl
    have hinc : {ω | lfppDistance d ξ (fun z => H n z ω) ≤ a} ⊆
        {ω | lfppDistance d ξ (fun z => H (n - k) z ω) ≤ X} ∪
        {ω | lfppDistance d ξ (fun z => H n z ω) ≤
          c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * lfppDistance d ξ (fun z => H (n - k) z ω)} := by
      intro ω hω
      by_contra hcon
      simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hcon hω
      obtain ⟨h1, h2⟩ := hcon
      have hY : 0 < c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) :=
        mul_pos hc (Real.rpow_pos_of_pos two_pos _)
      have hYX : c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * X = a := by
        rw [hXdef]
        have e : (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) = 1 := by
          rw [← Real.rpow_add two_pos,
            show -(1 - ξ * Q + ε) * (k : ℝ) + (1 - ξ * Q + ε) * k = 0 by ring, Real.rpow_zero]
        calc c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * (c⁻¹ * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * a)
            = (c * c⁻¹) * ((2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k)) *
                a := by ring
          _ = a := by rw [mul_inv_cancel₀ hc.ne', e, one_mul, one_mul]
      have := mul_lt_mul_of_pos_left h1 hY
      linarith
    have hsum : q' ≤ P {ω | lfppDistance d ξ (fun z => H (n - k) z ω) ≤ X} + (q' - q) :=
      hqa.trans ((measure_mono hinc).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl (hP.trans hsmall))))
    have hq : q ≤ P {ω | lfppDistance d ξ (fun z => H (n - k) z ω) ≤ X} := by
      have := tsub_le_iff_right.2 hsum
      rwa [ENNReal.sub_sub_cancel hq'top hqq'.le] at this
    have hle := (cmp_le_prob_iff_aQ_le hH ξ (n - k) hq0 hq1 X).1 hq
    calc aQ P H ξ (n - k) q ≤ X := hle
      _ = c⁻¹ * ((2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * a) := by rw [hXdef, mul_assoc]
      _ ≤ C * ((2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * a) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = C * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * a := by ring
  · -- the quantile asymptotics
    have h1 := haQ ξ hξ hξb Ω P W H hH (n - k)
    have h2 := hlaQ ξ hξ hξb Ω P W H hH n
    have hnk : ((n - k : ℕ) : ℝ) = n - k := Nat.cast_sub hkn
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    set E : ℝ := 2 * η * n - (ε + η) * k with hEdef
    have hE : E ≤ 2 * η * N₁ := by
      rw [not_and_or, not_le, not_le] at hcase
      rcases hcase with hlt | hlt
      · -- `k > c (n - k)`: `E < 0`
        rw [hnk] at hlt
        have hN₁0 : (0 : ℝ) ≤ 2 * η * N₁ := by positivity
        have e1 : 2 * η * (1 + c) * k = ε * c * k := by rw [hηc]
        have e2 : 2 * η * (c * (n - k)) < 2 * η * k := mul_lt_mul_of_pos_left hlt (by positivity)
        have e3 : 0 ≤ η * c * k := by positivity
        have hcE : c * E ≤ c * 0 := by
          rw [hEdef]
          linarith
        have : E ≤ 0 := le_of_mul_le_mul_left hcE hc
        linarith
      · -- `n - k < N₁`
        have hlt' : ((n - k : ℕ) : ℝ) < N₁ := by exact_mod_cast hlt
        rw [hnk] at hlt'
        rw [hEdef]
        nlinarith
    have hsplit : (2 : ℝ) ^ (-(1 - ξ * Q - η) * ((n - k : ℕ) : ℝ)) =
        (2 : ℝ) ^ E * ((2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)) := by
      rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos, hnk, hEdef]
      ring_nf
    have hEle : (2 : ℝ) ^ E ≤ (2 : ℝ) ^ (2 * η * N₁) :=
      Real.rpow_le_rpow_of_exponent_le one_le_two hE
    calc aQ P H ξ (n - k) q ≤ A * (2 : ℝ) ^ (-(1 - ξ * Q - η) * ((n - k : ℕ) : ℝ)) := h1
      _ = A / c' * (2 : ℝ) ^ E * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) *
            (c' * (2 : ℝ) ^ (-(1 - ξ * Q + η) * n)) := by
          rw [hsplit]
          field_simp
      _ ≤ A / c' * (2 : ℝ) ^ (2 * η * N₁) * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) *
            aQ P H ξ n q' := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEle
            (by positivity)) hX.le) h2 (by positivity) (by positivity)
      _ ≤ C * (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) * aQ P H ξ n q' := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hX.le) hpos.le
          exact (le_max_left _ _).trans (le_max_right _ _)

end HigherDimLQGContinuity
