import HigherDimLQGMetric.ShellDec.Limit
import HigherDimLQGMetric.ShellDec.Prefix

/-!
# Gaussian Hölder for functions of countable annular coordinates
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

theorem shellCountableHolder {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {a b C ε₀ : ℝ} (hC : 0 ≤ C) (hbound :
      ∀ (q : ℝ) (_hq : 0 < q) (_hq1 : q < 1)
        (k₀ : ℕ) (_hk₀ : 1 ≤ k₀) (_hqk : q ^ k₀ ≤ ε₀)
        (ρ : ℕ → ℝ) (_hpos : ∀ i, 0 < ρ i)
        (_hstep : ∀ i, ρ (i + 1) ≤ q * ρ i)
        (n : ℕ) (m : Fin n → ℕ)
        (X : ∀ i : Fin n, Fin (m i) → Lp ℝ 2 P)
        (_hX : ∀ (i : Fin n) (k : Fin (m i)),
          X i k ∈ annularBlock hh a b (ρ i))
        (_horth : ∀ i, Orthonormal ℝ (X i))
        (w : ∀ i : Fin n, Fin (m i) → ℝ),
        ‖∑ i : Fin n, ∑ k : Fin (m i), w i k • X i k‖ ^ 2 ≤
          ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)) *
            ∑ i : Fin n, ∑ k : Fin (m i), (w i k) ^ 2)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) (hqk : q ^ k₀ ≤ ε₀)
    (ρ : ℕ → ℝ) (hpos : ∀ i, 0 < ρ i)
    (hstep : ∀ i, ρ (i + 1) ≤ q * ρ i)
    (n : ℕ)
    (Y : Fin n → ℕ → Ω → ℝ) (hYm : ∀ i k, Measurable (Y i k))
    (X : Fin n → ℕ → Lp ℝ 2 P)
    (hXY : ∀ i k, (X i k : Ω → ℝ) =ᵐ[P] Y i k)
    (hX : ∀ (i : Fin n) (k : ℕ), X i k ∈ annularBlock hh a b (ρ i))
    (F : Fin n → Ω → ℝ)
    (hFm : ∀ i, Measurable[MeasurableSpace.comap
      (fun ω (k : ℕ) => Y i k ω) MeasurableSpace.pi] (F i))
    (hF0 : ∀ i ω, 0 ≤ F i ω) (hF1 : ∀ i ω, F i ω ≤ 1) :
    ∫ ω, ∏ i, F i ω ∂P ≤
      ∏ i, (∫ ω, F i ω ^
        ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)) ∂P) ^
          ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q))⁻¹ := by
  classical
  obtain ⟨g, hgm, hgb, hlim⟩ : ∃ g : (i : Fin n) → (m : ℕ) → (Fin m → ℝ) → ℝ,
      (∀ i m, Measurable (g i m)) ∧
      (∀ i m v, 0 ≤ g i m v ∧ g i m v ≤ 1) ∧
      (∀ i, ∀ᵐ ω ∂P, Filter.Tendsto
        (fun m => g i m (fun k : Fin m => Y i k ω))
        Filter.atTop (nhds (F i ω))) := by
    choose g hgm hgb hlim using fun i =>
      shellBounded_martingale_factor (P := P) (Y i) (hYm i) (F i)
        (hFm i) (hF0 i) (hF1 i)
    exact ⟨g, hgm, hgb, hlim⟩
  let G : ℕ → Fin n → Ω → ℝ :=
    fun m i ω => g i m (fun k : Fin m => Y i k ω)
  have hGm : ∀ m i, Measurable (G m i) := by
    intro m i
    apply (hgm i m).comp
    exact measurable_pi_iff.2 fun k => hYm i k
  have hG0 : ∀ m i ω, 0 ≤ G m i ω := fun m i ω => (hgb i m _).1
  have hG1 : ∀ m i ω, G m i ω ≤ 1 := fun m i ω => (hgb i m _).2
  have hGa : ∀ m i, (fun ω => g i m (fun k : Fin m => (X i k : Ω → ℝ) ω))
      =ᵐ[P] G m i := by
    intro m i
    have hk : ∀ᵐ ω ∂P, ∀ k : Fin m,
        (X i k : Ω → ℝ) ω = Y i k ω :=
      ae_all_iff.2 fun k => hXY i k
    filter_upwards [hk] with ω hω
    congr 1
    funext k
    exact hω k
  have hfinite (m : ℕ) :
      ∫ ω, ∏ i, G m i ω ∂P ≤
        ∏ i, (∫ ω, G m i ω ^
          ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)) ∂P) ^
            ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q))⁻¹ := by
    have h := shellFiniteCylinderHolder hh hC hbound hq hq1 hk₀ hqk
      ρ hpos hstep n m X (fun i k => hX i k)
      (fun i => g i m) (fun i => hgm i m)
      (fun i v => (hgb i m v).1) (fun i v => (hgb i m v).2)
    have hl : (∫ ω, ∏ i, g i m (fun k => (X i k : Ω → ℝ) ω) ∂P) =
        ∫ ω, ∏ i, G m i ω ∂P := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 (hGa m)] with ω hω
      exact Finset.prod_congr rfl fun i _ => hω i
    rw [hl] at h
    convert h using 1
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    apply integral_congr_ae
    filter_upwards [hGa m i] with ω hω
    exact congrArg (fun x : ℝ => x ^ ((2 * k₀ - 1 : ℝ) +
      2 * C * q ^ k₀ / (1 - q))) hω.symm
  let K : ℝ := (2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)
  have hK : 1 ≤ K := by
    have hk : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
    have hterm : 0 ≤ 2 * C * q ^ k₀ / (1 - q) := by positivity
    dsimp [K]
    linarith
  exact shellHolder_ae_limit hK G F hGm hG0 hG1 hlim hfinite

end HigherDimLQGMetric
