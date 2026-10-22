import HigherDimLQGMetric.Determ.ESBound

/-! Integrating the Efron–Stein bound over shifts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open LQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {dim : ℕ}

theorem determ_int_ES_le (ν : Measure (ContMetric dim)) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 ≤ C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : Rd dim, p.2.1 (z, w) ≤ C * p.1.1 (z, w)) {ε R : ℝ}
    {F : ContMetric dim → ℝ} (hFm : Measurable F)
    {Φ : (Fin dim → ℝ) × (determFixedBox (d := dim) ε R → ℕ → ℝ≥0∞) → ℝ} (hΦ : Measurable Φ)
    (K : Kernel ((Fin dim → ℝ) × (determFixedBox (d := dim) ε R → ℕ → ℝ≥0∞)) (ContMetric dim)) [IsMarkovKernel K]
    (hslice : ∀ᵐ θ ∂(determShiftLaw dim), (ν.map (determY ε θ (determFixedBox (d := dim) ε R))) ⊗ₘ
        (K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id)) =
      ν.map fun d => (determY ε θ (determFixedBox (d := dim) ε R) d, d))
    (hΦF : ∀ᵐ θ ∂(determShiftLaw dim), ∀ᵐ d ∂ν, F d = Φ (θ, determY ε θ (determFixedBox (d := dim) ε R) d))
    (hprod : ∀ᵐ θ ∂(volume : Measure (Fin dim → ℝ)), ν.map (determY ε θ (determFixedBox (d := dim) ε R)) =
      Measure.pi fun k : determFixedBox (d := dim) ε R => ν.map (determ_enc (determCube ε θ k))) :
    ∀ᵐ d ∂ν, ∀ Γ : ℝ, (∀ᵐ θ ∂(volume : Measure (Fin dim → ℝ)), θ ∈ determUnitShift dim → ∃ b : determFixedBox (d := dim) ε R → ℝ, (∀ k, 0 ≤ b k) ∧
          (∀ (k : determFixedBox (d := dim) ε R) (d'' : ContMetric dim), DetermCompat C ε θ (determFixedBox (d := dim) ε R) d d'' k.1 →
            max (F d'' - F d) 0 ^ 2 ≤ b k) ∧ ∑ k, b k ≤ Γ) →
      ∫⁻ θ, determES ε R F Φ ν θ d ∂(determShiftLaw dim) ≤ ENNReal.ofReal Γ := by
  filter_upwards [determ_ES_le ν hL hC hcopy hFm hΦ K hslice hΦF hprod] with d hd Γ hΓ
  have hθ : ∀ᵐ θ ∂(determShiftLaw dim), determES ε R F Φ ν θ d ≤ ENNReal.ofReal Γ := by
    filter_upwards [hd, ae_restrict_of_ae hΓ, ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ico)] with θ h1 h2 h3
    obtain ⟨b, hb0, hb, hsum⟩ := h2 h3
    calc determES ε R F Φ ν θ d ≤ ∑ k, ENNReal.ofReal (b k) := h1 b hb
      _ = ENNReal.ofReal (∑ k, b k) :=
          (ENNReal.ofReal_sum_of_nonneg fun k _ => hb0 k).symm
      _ ≤ ENNReal.ofReal Γ := ENNReal.ofReal_le_ofReal hsum
  calc ∫⁻ θ, determES ε R F Φ ν θ d ∂(determShiftLaw dim) ≤ ∫⁻ _, ENNReal.ofReal Γ ∂(determShiftLaw dim) := lintegral_mono_ae hθ
    _ = ENNReal.ofReal Γ := by rw [lintegral_const, measure_univ, mul_one]

end HigherDimLQGMetric
