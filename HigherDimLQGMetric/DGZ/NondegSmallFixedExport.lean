import HigherDimLQGMetric.DGZ.NondegSmallFixed

/-! Fixed-realization small-shell nondegeneracy at every sufficiently high quantile. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_smallShell_nondeg_fixed {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) :
    ∃ q₀ : ℝ≥0∞, 0 < q₀ ∧ q₀ < 1 ∧
      ∀ q : ℝ≥0∞, q₀ ≤ q → q < 1 →
      ∀ r : ℝ, 0 < r → r * (10 * Real.sqrt d) ≤ 1 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        ∀ _hH : IsDyadicRealization κ P W H,
        ∀ θ : ℝ≥0∞, 0 < θ → θ ≤ 1 →
          ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
              δ * aQ P H ξ n q} ≤ θ := by
  obtain ⟨qJ, hqJ0, hqJ1, hJ⟩ := nd_exists_joint_limit h
  obtain ⟨qZ, hqZ0, hqZ1, hZ⟩ := nd_zeroOne_limitLaw h
  obtain ⟨qC, hqC0, hqC1, hC⟩ := nondeg_cross_pos (cor52Shape d κ ξ Q) h
  let q₀ := max qJ (max qZ qC)
  have hq₀0 : 0 < q₀ := hqJ0.trans_le (le_max_left _ _)
  have hq₀1 : q₀ < 1 := max_lt hqJ1 (max_lt hqZ1 hqC1)
  refine ⟨q₀, hq₀0, hq₀1, ?_⟩
  intro q hq hq1 r hr hrd Ω _ P W H hH θ hθ0 hθ1
  have hqJ : qJ ≤ q := (le_max_left _ _).trans hq
  have hqZ : qZ ≤ q := (le_max_left qZ qC).trans
    ((le_max_right qJ (max qZ qC)).trans hq)
  have hqC : qC ≤ q := (le_max_right qZ qC).trans
    ((le_max_right qJ (max qZ qC)).trans hq)
  obtain ⟨c, hc, hcross⟩ := hC q hqC hq1 r hr hrd
  have hJoint (ns : ℕ → ℕ) := hJ q hqJ hq1 r Ω P W H hH ns
  have hZero (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
      (μ : ProbabilityMeasure (nd_Joint d r)) :=
    hZ q hqZ hq1 r r hr hr Ω P W H hH ns hns μ
  exact nd_smallShell_nondeg_fixed_of_limit_inputs h hH
    (hq₀0.trans_le hq) hq1 r r hJoint hZero c hc
    (hcross Ω P W H hH) θ hθ0 hθ1

end HigherDimLQGMetric.DGZ
