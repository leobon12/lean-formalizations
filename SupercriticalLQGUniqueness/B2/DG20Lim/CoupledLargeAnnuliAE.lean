import SupercriticalLQGUniqueness.B2.DG20Lim.CoupledLargeCircleTail
import SupercriticalLQGUniqueness.B2.DG20Lim.LargeEndpointProbability

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_arbitrarily_large_centered_annuli_of_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Ylim : Ω → (CoordJ → ℝ) × RatCoords)
    (htail : ∀ (T η : ℝ), 0 < T → 0 < η →
      ∃ R₀ : ℝ, 1 < R₀ ∧
        ∀ (r : ℚ) (hr : 1 < r), R₀ ≤ (r : ℝ) →
          P {ω | (Ylim ω).2.1
            (centeredInnerCircle 0 0 r (lt_trans zero_lt_one hr),
              centeredOuterCircle 0 0 r (lt_trans zero_lt_one hr)) <
            ENNReal.ofReal T} ≤ ENNReal.ofReal η) :
    ∀ᵐ ω ∂P, ∀ N : ℕ,
      ∃ r : {r : ℚ // 1 < r}, (N : ℝ) < (r : ℚ) ∧
        ENNReal.ofReal ((N : ℝ) + 1) ≤ (Ylim ω).2.1
          (centeredInnerCircle 0 0 r.1 (lt_trans zero_lt_one r.property),
            centeredOuterCircle 0 0 r.1 (lt_trans zero_lt_one r.property)) := by
  apply ae_all_iff.mpr
  intro N
  let f : Ω → {r : ℚ // 1 < r} → ℝ≥0∞ := fun ω r =>
    (Ylim ω).2.1
      (centeredInnerCircle 0 0 r.1 (lt_trans zero_lt_one r.property),
        centeredOuterCircle 0 0 r.1 (lt_trans zero_lt_one r.property))
  let valid : {r : ℚ // 1 < r} → Prop :=
    fun r => (N : ℝ) < (r : ℚ)
  apply ae_exists_large_endpoint_of_arbitrarily_small_bad_prob
    P f valid (ENNReal.ofReal ((N : ℝ) + 1))
  intro η hη
  obtain ⟨R₀, hR₀, hbound⟩ :=
    htail ((N : ℝ) + 1) η (by positivity) hη
  obtain ⟨r, hrlo, -⟩ := exists_rat_btwn
    (show max R₀ (N : ℝ) < max R₀ (N : ℝ) + 1 by linarith)
  have hr1 : (1 : ℚ) < r := by
    have hh : (1 : ℝ) < (r : ℝ) :=
      hR₀.trans_le ((le_max_left _ _).trans hrlo.le)
    exact_mod_cast hh
  let rr : {r : ℚ // 1 < r} := ⟨r, hr1⟩
  refine ⟨rr, ?_, ?_⟩
  · exact (le_max_right R₀ (N : ℝ)).trans_lt hrlo
  · simpa only [f, rr] using
      hbound r hr1 ((le_max_left _ _).trans hrlo.le)

end SupercriticalLQGUniqueness.B2.DG20Lim
