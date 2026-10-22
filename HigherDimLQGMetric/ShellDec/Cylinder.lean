import HigherDimLQGMetric.ShellDec.Basis

/-!
# Gaussian Hölder for finite cylinders of shell pairings
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

theorem shellFiniteCylinderHolder {d : ℕ}
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
    (n m : ℕ) (X : Fin n → ℕ → Lp ℝ 2 P)
    (hX : ∀ (i : Fin n) (k : Fin m),
      X i k ∈ annularBlock hh a b (ρ i))
    (f : (i : Fin n) → (Fin m → ℝ) → ℝ)
    (hfm : ∀ i, Measurable (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hf1 : ∀ i y, f i y ≤ 1) :
    ∫ ω, ∏ i, f i (fun k => (X i k : Ω → ℝ) ω) ∂P ≤
      ∏ i, (∫ ω, f i (fun k => (X i k : Ω → ℝ) ω) ^
        ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)) ∂P) ^
          ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q))⁻¹ := by
  let dim : Fin n → ℕ := fun i => Module.finrank ℝ (shellFiniteSpan (X i) m)
  let B : (i : Fin n) → Fin (dim i) → Lp ℝ 2 P :=
    fun i j => shellBasisVec (X i) m j
  have hB : ∀ (i : Fin n) (j : Fin (dim i)),
      B i j ∈ annularBlock hh a b (ρ i) :=
    fun i j => shellBasisVec_mem_annularBlock hh (X i) m (hX i) j
  have horth : ∀ i, Orthonormal ℝ (B i) :=
    fun i => shellBasisVec_orthonormal (X i) m
  have hgauss : IsGaussianProcess
      (fun p : Σ i : Fin n, Fin (dim i) => (B p.1 p.2 : Ω → ℝ)) P :=
    shellBlock_gaussian hh (fun p : Σ i : Fin n, Fin (dim i) => B p.1 p.2)
      (fun p => ρ p.1) (fun p => hB p.1 p.2)
  have hcent : ∀ (i : Fin n) (j : Fin (dim i)),
      ∫ ω, (B i j : Ω → ℝ) ω ∂P = 0 :=
    fun i j => shellBlock_centered hh (hB i j)
  let T : (i : Fin n) → (Fin (dim i) → ℝ) → (Fin m → ℝ) :=
    fun i v k => ∑ j : Fin (dim i), shellBasisCoeff (X i) m k j * v j
  let g : (i : Fin n) → (Fin (dim i) → ℝ) → ℝ :=
    fun i v => f i (T i v)
  have hTm : ∀ i, Measurable (T i) := by
    intro i
    refine measurable_pi_iff.2 fun k => ?_
    exact Finset.measurable_sum _ fun j _ =>
      measurable_const.mul (measurable_pi_apply j)
  have hgm : ∀ i, Measurable (g i) :=
    fun i => (hfm i).comp (hTm i)
  have hg0 : ∀ i v, 0 ≤ g i v := fun i v => hf0 i _
  have hg1 : ∀ i v, g i v ≤ 1 := fun i v => hf1 i _
  have hae : ∀ i : Fin n,
      (fun ω => f i (fun k => (X i k : Ω → ℝ) ω)) =ᵐ[P]
      (fun ω => g i (fun j => (B i j : Ω → ℝ) ω)) := by
    intro i
    have hk : ∀ᵐ ω ∂P, ∀ k : Fin m,
        (X i k : Ω → ℝ) ω =
          ∑ j : Fin (dim i),
            shellBasisCoeff (X i) m k j * (B i j : Ω → ℝ) ω :=
      ae_all_iff.2 fun k => shellFiniteBasis_expand_ae (X i) m k
    filter_upwards [hk] with ω hω
    change f i (fun k => (X i k : Ω → ℝ) ω) =
      f i (T i (fun j => (B i j : Ω → ℝ) ω))
    congr 1
    funext k
    exact hω k
  have hmain := shellFiniteCoordinateHolder hh hC hbound hq hq1 hk₀ hqk
    ρ hpos hstep n dim B hB horth hgauss hcent g hgm hg0 hg1
  have hleft : (∫ ω, ∏ i, f i (fun k => (X i k : Ω → ℝ) ω) ∂P) =
      ∫ ω, ∏ i, g i (fun j => (B i j : Ω → ℝ) ω) ∂P := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.2 hae] with ω hω
    exact Finset.prod_congr rfl fun i _ => hω i
  rw [hleft]
  convert hmain using 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  apply integral_congr_ae
  filter_upwards [hae i] with ω hω
  exact congrArg (fun x : ℝ => x ^ ((2 * k₀ - 1 : ℝ) +
    2 * C * q ^ k₀ / (1 - q))) hω

end HigherDimLQGMetric
