import HigherDimLQGMetric.ShellDec.Finite

/-!
# Uniform annular coordinate bound

The geometric covariance constants are chosen before the law of the LGF. This
quantifier order is needed by `ShellDecouplingFun0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

theorem shellUniformCoordinateBound {d : ℕ} (hd : 1 ≤ d)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
        {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P),
      ∀ (q : ℝ) (_hq : 0 < q) (_hq1 : q < 1)
        (k₀ : ℕ) (_hk₀ : 1 ≤ k₀) (_hqk : q ^ k₀ ≤ ε₀)
        (ρ : ℕ → ℝ) (_hpos : ∀ i, 0 < ρ i)
        (_hstep : ∀ i, ρ (i + 1) ≤ q * ρ i)
        (n : ℕ) (m : Fin n → ℕ)
        (X : ∀ i : Fin n, Fin (m i) → Lp ℝ 2 P)
        (_hX : ∀ (i : Fin n) (k : Fin (m i)), X i k ∈ annularBlock hh a b (ρ i))
        (_horth : ∀ i, Orthonormal ℝ (X i))
        (w : ∀ i : Fin n, Fin (m i) → ℝ),
        ‖∑ i : Fin n, ∑ k : Fin (m i), w i k • X i k‖ ^ 2 ≤
          ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)) *
            ∑ i : Fin n, ∑ k : Fin (m i), (w i k) ^ 2 := by
  obtain ⟨C, ε₀, hC, hε₀, hdecay⟩ := logCov_decay hd ha hab
  refine ⟨C, ε₀, hC, hε₀, ?_⟩
  intro Ω _ P h hh q hq hq1 k₀ hk₀ hqk ρ hpos hstep n m X hX horth w
  have hblock : ∀ r r' : ℝ, 0 < r' → r' ≤ ε₀ * r →
      ∀ U ∈ annularBlock hh a b r, ∀ V ∈ annularBlock hh a b r',
        |inner ℝ U V| ≤ C * (r' / r) * (‖U‖ * ‖V‖) := by
    intro r r' hr' hrr U hU V hV
    apply inner_abs_le_of_mem_closure (s := annularPairings hh a b r)
      (t := annularPairings hh a b r') (C := C * (r' / r)) ?_ U hU V hV
    intro U hU V hV
    rcases hU with ⟨φ, hφ, rfl⟩
    rcases hV with ⟨ψ, hψ, rfl⟩
    rw [lgfPairLp_inner_eq hh φ ψ, lgfPairLp_norm_eq hh φ,
      lgfPairLp_norm_eq hh ψ]
    exact hdecay r r' hr' hrr φ ψ hφ hψ
  have hcorr : ∀ (Y : Fin n → Lp ℝ 2 P)
      (_hY : ∀ i : Fin n, Y i ∈ annularBlock hh a b (ρ i))
      (i j : Fin n),
      |inner ℝ (Y i) (Y j)| ≤
        blockCorrCoeff C q k₀ (Nat.dist (i : ℕ) (j : ℕ)) *
          (‖Y i‖ * ‖Y j‖) := by
    intro Y hY i j
    by_cases hnear : Nat.dist (i : ℕ) (j : ℕ) < k₀
    · simp only [blockCorrCoeff, hnear, ite_true, one_mul]
      exact abs_real_inner_le_norm (Y i) (Y j)
    have hfar (i j : Fin n) (hij : (i : ℕ) ≤ (j : ℕ))
        (hk : k₀ ≤ Nat.dist (i : ℕ) (j : ℕ)) :
        |inner ℝ (Y i) (Y j)| ≤
          blockCorrCoeff C q k₀ (Nat.dist (i : ℕ) (j : ℕ)) *
            (‖Y i‖ * ‖Y j‖) := by
      have hdist : Nat.dist (i : ℕ) (j : ℕ) = (j : ℕ) - (i : ℕ) :=
        Nat.dist_eq_sub_of_le hij
      have hratio := shellRadius_ratio_le_pow ρ hq.le hpos hstep hij
      have hsep : ρ j ≤ ε₀ * ρ i := by
        have hpow : q ^ ((j : ℕ) - (i : ℕ)) ≤ q ^ k₀ :=
          pow_le_pow_of_le_one hq.le hq1.le (by simpa [hdist] using hk)
        calc
          ρ j ≤ q ^ ((j : ℕ) - (i : ℕ)) * ρ i :=
            (div_le_iff₀ (hpos i)).1 hratio
          _ ≤ q ^ k₀ * ρ i := mul_le_mul_of_nonneg_right hpow (hpos i).le
          _ ≤ ε₀ * ρ i := mul_le_mul_of_nonneg_right hqk (hpos i).le
      have h := hblock (ρ i) (ρ j) (hpos j) hsep (Y i) (hY i) (Y j) (hY j)
      rw [hdist] at hk ⊢
      simp [blockCorrCoeff, not_lt.mpr hk]
      calc
        |inner ℝ (Y i) (Y j)| ≤
          C * (ρ j / ρ i) * (‖Y i‖ * ‖Y j‖) := h
        _ ≤ C * q ^ ((j : ℕ) - (i : ℕ)) * (‖Y i‖ * ‖Y j‖) := by gcongr
    by_cases hij : (i : ℕ) ≤ (j : ℕ)
    · exact hfar i j hij (not_lt.mp hnear)
    · have hji : (j : ℕ) ≤ (i : ℕ) := le_of_not_ge hij
      have hdist : Nat.dist (j : ℕ) (i : ℕ) = Nat.dist (i : ℕ) (j : ℕ) :=
        Nat.dist_comm _ _
      have h := hfar j i hji (by rw [hdist]; exact not_lt.mp hnear)
      simpa only [Nat.dist_comm, real_inner_comm, mul_comm] using h
  let Y : Fin n → Lp ℝ 2 P := fun i => ∑ k, w i k • X i k
  have hY (i : Fin n) : Y i ∈ annularBlock hh a b (ρ i) := by
    rw [annularBlock_eq_span_closure]
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    change X i k ∈ (annularBlockSubmodule hh a b (ρ i) : Set (Lp ℝ 2 P))
    rw [← annularBlock_eq_span_closure]
    exact hX i k
  exact blockCorrCoeff_coordinate_bound m X horth w hC.le hq.le hq1 hk₀
    (fun i j => hcorr Y hY i j)

end HigherDimLQGMetric
