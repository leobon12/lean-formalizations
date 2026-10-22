import HigherDimLQGContinuity.MomentsW1.CoarseMoment

/-! A shared coarse constant for the moment and almost-sure bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory HigherDimLFPP HigherDimLQGMetric.DGZ
open scoped ENNReal

universe u

theorem wnZR_tail_of_extended {d : ℕ} {κ : Rd d → ℝ} (CZ : ℝ)
    (htail : ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R v : ℝ, 1 ≤ R → 0 ≤ v →
          P {ω | ENNReal.ofReal v < wnZRext (d := d) R Q CZ H ω} ≤
            ENNReal.ofReal (K * Real.exp (-(Real.sqrt (2 * d) / 2) * v))) :
    ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R v : ℝ, 1 ≤ R → 0 ≤ v →
          P {ω | v < wnZR (d := d) R Q CZ H ω} ≤
            ENNReal.ofReal (K * Real.exp (-(Real.sqrt (2 * d) / 2) * v)) := by
  intro Q hQ
  obtain ⟨K,hK,hKtail⟩ := htail Q hQ
  refine ⟨K,hK,?_⟩
  intro Ω _ P W H hH R v hR hv
  have hsub : {ω | v < wnZR (d := d) R Q CZ H ω} ⊆
      {ω | ENNReal.ofReal v < wnZRext (d := d) R Q CZ H ω} := by
    intro ω hω
    by_contra hnot
    have hle : wnZRext (d := d) R Q CZ H ω ≤ ENNReal.ofReal v := le_of_not_gt hnot
    have hreal : wnZR (d := d) R Q CZ H ω ≤ v :=
      ENNReal.toReal_le_of_le_ofReal hv hle
    exact (not_lt_of_ge hreal) hω
  exact (measure_mono hsub).trans (hKtail (P := P) (W := W) (H := H) hH R v hR hv)

theorem wnZR_joint {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {l : ℝ} (hl : 0 < l)
    (hlcrit : l ≤ Real.sqrt (2 * d) / 4) :
    ∃ CZ : ℝ, 0 < CZ ∧ ∀ Q : ℝ, Real.sqrt (2 * d) < Q →
      ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ R : ℝ, 1 ≤ R →
          (∀ᵐ ω ∂P, wnZRext (d := d) R Q CZ H ω ≠ ⊤) ∧
          ∫⁻ ω, ENNReal.ofReal (Real.exp (l * wnZR (d := d) R Q CZ H ω)) ∂P ≤
            ENNReal.ofReal C := by
  obtain ⟨CZ,hCZ,htail⟩ := wnZRext_tail hd hκ
  let hreal := wnZR_tail_of_extended CZ htail
  let hfinite := wnZRext_finite_ae_of_tail hd CZ hCZ htail
  let hmoment := wnZR_expMoment_of_tail hd CZ hCZ hreal hl hlcrit
  refine ⟨CZ,hCZ,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hCm⟩ := hmoment Q hQ
  exact ⟨C,hC,fun hH R hR => ⟨hfinite Q hQ hH R hR,hCm hH R hR⟩⟩

end HigherDimLQGContinuity
