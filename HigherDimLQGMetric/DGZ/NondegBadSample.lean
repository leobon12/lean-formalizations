import HigherDimLQGMetric.DGZ.NondegBadLimit

/-! Transfer a prelimit small-crossing probability to the joint-law observable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_jointLaw_badCross_prob
    {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r δ : ℝ) (n : ℕ) {θ : ℝ≥0∞}
    (hbad : θ ≤ P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
      δ * aQ P H ξ n q}) :
    θ ≤ (nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid n :
      Measure (nd_Joint d rGrid))
      {s | nd_crossPhi 0 (2 * r) r s.1 ≤ δ} := by
  have hF : MeasurableSet
      {s : nd_Joint d rGrid | nd_crossPhi 0 (2 * r) r s.1 ≤ δ} :=
    (isClosed_le ((nd_continuous_crossPhi 0 (2 * r) r).comp continuous_fst)
      continuous_const).measurableSet
  change θ ≤ (P.map (nd_jointSample P H ξ q rGrid n))
    {s | nd_crossPhi 0 (2 * r) r s.1 ≤ δ}
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q rGrid n) hF]
  apply hbad.trans
  apply measure_mono
  intro ω hω
  have ha : 0 < aQ P H ξ n q :=
    tight_aQ_pos (by have := h.dim; omega : 0 < d) hH ξ n hq0 hq1
  change acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
    δ * aQ P H ξ n q at hω
  change nd_crossPhi 0 (2 * r) r
    (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q)) ≤ δ
  rw [nd_crossPhi_normMetricC ((hH.band n).continuous ω) ha]
  exact (inv_mul_le_iff₀ ha).2 (by simpa only [mul_comm] using hω)

end HigherDimLQGMetric.DGZ
