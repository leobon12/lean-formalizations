import HigherDimLQGMetric.Gauss.BlockApp
import HigherDimLQGMetric.Gauss.GaussianHolder

/-!
# Finite Gaussian coordinates in annular blocks

This is the finite-coordinate part of the shell decoupling argument.  The
coordinate random variables are represented by their classes in `L²(P)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

theorem shellFiniteCoordinateHolder {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {a b : ℝ}
    {C ε₀ : ℝ} (hC : 0 ≤ C) (hbound :
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
            ∑ i : Fin n, ∑ k : Fin (m i), (w i k) ^ 2)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hqk : q ^ k₀ ≤ ε₀)
    (ρ : ℕ → ℝ) (hpos : ∀ i, 0 < ρ i)
    (hstep : ∀ i, ρ (i + 1) ≤ q * ρ i)
    (n : ℕ) (m : Fin n → ℕ)
    (X : ∀ i : Fin n, Fin (m i) → Lp ℝ 2 P)
    (hX : ∀ (i : Fin n) (k : Fin (m i)), X i k ∈ annularBlock hh a b (ρ i))
    (horth : ∀ i, Orthonormal ℝ (X i))
    (hgauss : IsGaussianProcess (fun p : Σ i : Fin n, Fin (m i) => (X p.1 p.2 : Ω → ℝ)) P)
    (hcent : ∀ i k, ∫ ω, (X i k : Ω → ℝ) ω ∂P = 0)
    (f : (i : Fin n) → (Fin (m i) → ℝ) → ℝ)
    (hfm : ∀ i, Measurable (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hf1 : ∀ i y, f i y ≤ 1) :
    ∫ ω, ∏ i, f i (fun k => (X i k : Ω → ℝ) ω) ∂P ≤
      ∏ i, (∫ ω, f i (fun k => (X i k : Ω → ℝ) ω) ^
        ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)) ∂P) ^
          ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q))⁻¹ := by
  let K : ℝ := (2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)
  have hK : 1 ≤ K := by
    have hk : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
    have hqpow : 0 ≤ q ^ k₀ := pow_nonneg hq.le _
    have hden : 0 < 1 - q := sub_pos.mpr hq1
    dsimp [K]
    have hterm : 0 ≤ 2 * C * q ^ k₀ / (1 - q) := by positivity
    linarith
  have horth' : ∀ i (k l : Fin (m i)),
      ∫ ω, (X i k : Ω → ℝ) ω * (X i l : Ω → ℝ) ω ∂P =
        if k = l then 1 else 0 := by
    intro i k l
    have hi := (orthonormal_iff_ite).mp (horth i) k l
    rw [MeasureTheory.L2.inner_def] at hi
    simpa [mul_comm] using hi
  have hT : ∀ w : (i : Fin n) → Fin (m i) → ℝ,
      ∫ ω, (∑ i, ∑ k, w i k * (X i k : Ω → ℝ) ω) ^ 2 ∂P ≤
        K * ∑ i, ∑ k, (w i k) ^ 2 := by
    intro w
    let Y : Lp ℝ 2 P := ∑ i : Fin n, ∑ k : Fin (m i), w i k • X i k
    have hYi (i : Fin n) :
        ((∑ k : Fin (m i), w i k • X i k : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
          fun ω => ∑ k, w i k * (X i k : Ω → ℝ) ω :=
      by
        have ha := (Lp.coeFn_finsetSum (Finset.univ : Finset (Fin (m i)))
          (fun k => w i k • X i k)).trans <|
            eventuallyEq_sum fun k _ => Lp.coeFn_smul (w i k) (X i k)
        filter_upwards [ha] with ω hω
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hω
    have hY : (Y : Ω → ℝ) =ᵐ[P]
        fun ω => ∑ i, ∑ k, w i k * (X i k : Ω → ℝ) ω := by
      have ha := (Lp.coeFn_finsetSum (Finset.univ : Finset (Fin n))
        (fun i => ∑ k : Fin (m i), w i k • X i k)).trans <|
          eventuallyEq_sum fun i _ => hYi i
      filter_upwards [ha] with ω hω
      simpa [Y, Finset.sum_apply] using hω
    have hnorm : ∫ ω, (Y : Ω → ℝ) ω ^ 2 ∂P = ‖Y‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      congr 1
      funext ω
      simp [Real.norm_eq_abs, sq_abs]
    calc
      _ = ∫ ω, (Y : Ω → ℝ) ω ^ 2 ∂P := integral_congr_ae (hY.fun_comp fun t => t ^ 2).symm
      _ = ‖Y‖ ^ 2 := hnorm
      _ ≤ K * ∑ i, ∑ k, (w i k) ^ 2 := hbound q hq hq1 k₀ hk₀ hqk ρ hpos hstep n m X hX horth w
  exact Gauss.gaussianHolder_prob (fun i k ω => (X i k : Ω → ℝ) ω)
    hgauss hcent horth' hK hT f hfm hf0 hf1

end HigherDimLQGMetric
