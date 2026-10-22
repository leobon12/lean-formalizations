import HigherDimLQGMetric.Gauss.BlockShell
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem annularBlock_shell_schur {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ (q : ℝ) (_hq : 0 < q) (_hq1 : q < 1)
        (k₀ : ℕ) (_hk₀ : 1 ≤ k₀) (_hqk : q^k₀ ≤ ε₀)
        (ρ : ℕ → ℝ) (_hpos : ∀ i, 0 < ρ i)
        (_hstep : ∀ i, ρ (i+1) ≤ q*ρ i)
        (n : ℕ) (Y : Fin n → Lp ℝ 2 P)
        (_hY : ∀ i : Fin n, Y i ∈ annularBlock hh a b (ρ i)),
        ‖∑ i, Y i‖^2 ≤
          ((2*k₀ - 1 : ℝ) + 2*C*q^k₀/(1-q)) *
            ∑ i, ‖Y i‖^2 := by
  obtain ⟨C,ε₀,hC,hε₀,hcorr⟩ := annularBlock_shell_corr hd hh ha hab
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro q hq hq1 k₀ hk₀ hqk ρ hpos hstep n Y hY
  apply blockCorrCoeff_schur Y hC.le hq.le hq1 hk₀
  exact hcorr q hq hq1 k₀ hk₀ hqk ρ hpos hstep n Y hY

theorem annularBlock_shell_coordinate_bound {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ (q : ℝ) (_hq : 0 < q) (_hq1 : q < 1)
        (k₀ : ℕ) (_hk₀ : 1 ≤ k₀) (_hqk : q^k₀ ≤ ε₀)
        (ρ : ℕ → ℝ) (_hpos : ∀ i, 0 < ρ i)
        (_hstep : ∀ i, ρ (i+1) ≤ q*ρ i)
        (n : ℕ) (m : Fin n → ℕ)
        (X : ∀ i : Fin n, Fin (m i) → Lp ℝ 2 P)
        (_hX : ∀ (i : Fin n) (k : Fin (m i)), X i k ∈ annularBlock hh a b (ρ i))
        (_horth : ∀ i, Orthonormal ℝ (X i))
        (w : ∀ i : Fin n, Fin (m i) → ℝ),
        ‖∑ i : Fin n, ∑ k : Fin (m i), w i k • X i k‖^2 ≤
          ((2*k₀ - 1 : ℝ) + 2*C*q^k₀/(1-q)) *
            ∑ i : Fin n, ∑ k : Fin (m i), (w i k)^2 := by
  obtain ⟨C,ε₀,hC,hε₀,hcorr⟩ := annularBlock_shell_corr hd hh ha hab
  refine ⟨C,ε₀,hC,hε₀,?_⟩
  intro q hq hq1 k₀ hk₀ hqk ρ hpos hstep n m X hX horth w
  let Y : Fin n → Lp ℝ 2 P := fun i => ∑ k, w i k • X i k
  have hY (i : Fin n) : Y i ∈ annularBlock hh a b (ρ i) := by
    rw [annularBlock_eq_span_closure]
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    change X i k ∈ (annularBlockSubmodule hh a b (ρ i) : Set (Lp ℝ 2 P))
    rw [←annularBlock_eq_span_closure]
    exact hX i k
  have hpair := hcorr q hq hq1 k₀ hk₀ hqk ρ hpos hstep n Y hY
  exact blockCorrCoeff_coordinate_bound m X horth w hC.le hq.le hq1 hk₀
    (fun i j => hpair i j)
end HigherDimLQGMetric
