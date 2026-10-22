import HigherDimLQGMetric.DGZ.NondegLawTransfer

/-! Uniform small-shell nondegeneracy, transferred from a canonical realization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_smallShell_nondeg_uniform {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) :
    ∃ q₀ : ℝ≥0∞, 0 < q₀ ∧ q₀ < 1 ∧
      ∀ q : ℝ≥0∞, q₀ ≤ q → q < 1 →
      ∀ r : ℝ, 0 < r → r * (10 * Real.sqrt d) ≤ 1 →
      ∀ θ : ℝ≥0∞, 0 < θ → θ ≤ 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
            (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
            IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
              P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
                δ * aQ P H ξ n q} ≤ θ := by
  obtain ⟨q₀, hq₀0, hq₀1, hfixed⟩ := nd_smallShell_nondeg_fixed h
  refine ⟨q₀, hq₀0, hq₀1, ?_⟩
  intro q hq hq1 r hr hrd θ hθ0 hθ1
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise d
  obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization h.kernel hW₀
  obtain ⟨δ, hδ, N, hN⟩ := hfixed q hq hq1 r hr hrd
    (ℕ → ℝ) LQGDimension.ExistAsm.stdP W₀ H₀ hH₀ θ hθ0 hθ1
  refine ⟨δ, hδ, N, ?_⟩
  intro Ω _ P W H hH n hn
  rw [nd_across_bad_prob_eq_of_realizations h.kernel hH hH₀ ξ n q r δ]
  exact hN n hn

end HigherDimLQGMetric.DGZ
