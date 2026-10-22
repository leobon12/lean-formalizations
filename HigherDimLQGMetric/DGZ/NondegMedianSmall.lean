import HigherDimLQGMetric.DGZ.NondegGeneralGeom

/-! Uniform small-shell lower tail at the median normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_smallShell_median_uniform {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) :
    ∀ r : ℝ, 0 < r → r * (10 * Real.sqrt d) ≤ 1 →
      ∀ θ : ℝ≥0∞, 0 < θ → θ ≤ 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
          ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
            (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
            IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
              P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
                δ * aQ P H ξ n 2⁻¹} ≤ θ := by
  obtain ⟨q₀, hq₀0, hq₀1, hsmall⟩ := nd_smallShell_nondeg_uniform h
  let q := max q₀ 2⁻¹
  have hq0 : q₀ ≤ q := le_max_left _ _
  have hq1 : q < 1 := max_lt hq₀1 (by norm_num)
  intro r hr hrd θ hθ0 hθ1
  obtain ⟨δ, hδ, N, hN⟩ := hsmall q hq0 hq1 r hr hrd θ hθ0 hθ1
  refine ⟨δ, hδ, N, ?_⟩
  intro Ω _ P W H hH n hn
  have hmed : aQ P H ξ n 2⁻¹ ≤ aQ P H ξ n q :=
    tight_aQ_mono hH ξ n (by norm_num) (le_max_right _ _) hq1
  have hδmed : δ * aQ P H ξ n 2⁻¹ ≤ δ * aQ P H ξ n q :=
    mul_le_mul_of_nonneg_left hmed hδ.le
  calc
    P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
        δ * aQ P H ξ n 2⁻¹} ≤
      P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
        δ * aQ P H ξ n q} := measure_mono (fun _ hω => hω.trans hδmed)
    _ ≤ θ := hN Ω P W H hH n hn

end HigherDimLQGMetric.DGZ
