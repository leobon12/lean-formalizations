import HigherDimLQGMetric.DGZ.NondegMedianSmall

/-! Translation of the small-shell lower-tail estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_smallShell_median_center {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {r : ℝ} (hr : 0 < r)
    (hrd : r * (10 * Real.sqrt d) ≤ 1)
    {θ : ℝ≥0∞} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (c : Rd d) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
          P {ω | acrossDist ξ (fun z => H n z ω) c (2 * r) r ≤
            δ * aQ P H ξ n 2⁻¹} ≤ θ := by
  obtain ⟨δ, hδ, N, hN⟩ := nd_smallShell_median_uniform h r hr hrd θ hθ0 hθ1
  refine ⟨δ, hδ, N, ?_⟩
  intro c Ω _ P W H hH n hn
  have hH' := isDyadicRealization_translate_tight h.kernel hH c
  have hq : aQ P (fun k z ω => H k (c + z) ω) ξ n 2⁻¹ = aQ P H ξ n 2⁻¹ :=
    aQ_eq_of_isDyadicRealization hH' hH ξ n 2⁻¹
  have hc : ∀ ω, acrossDist ξ (fun z => H n z ω) c (2 * r) r =
      acrossDist ξ (fun z => H n (c + z) ω) 0 (2 * r) r := by
    intro ω
    have hh := acrossDist_smul_add c ξ (fun z => H n z ω) one_pos 0 (2 * r) r
    simpa only [smul_zero, add_zero, one_mul, one_smul] using hh
  simp_rw [hc, ← hq]
  exact hN Ω P _ _ hH' n hn

end HigherDimLQGMetric.DGZ
