import HigherDimLQGMetric.DGZ.NondegZeroOne

/-! A uniform positive crossing probability forces a joint weak limit to have positive crossing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

def nd_crossGeCSet (rGrid r c : ℝ) : Set (nd_Joint d rGrid) :=
  {s | c ≤ nd_crossPhi 0 (2 * r) r s.1}

theorem nd_isClosed_crossGeCSet (rGrid r c : ℝ) :
    IsClosed (nd_crossGeCSet (d := d) rGrid r c) :=
  isClosed_le continuous_const
    ((nd_continuous_crossPhi 0 (2 * r) r).comp continuous_fst)

theorem nd_limit_positiveCross_prob
    {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r c : ℝ) (hc : 0 < c)
    (hcross : ∀ n : ℕ, ENNReal.ofReal c ≤
      P {ω | c * aQ P H ξ n q < acrossDist ξ (fun z => H n z ω) 0 (2 * r) r})
    (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ)) :
    ENNReal.ofReal c ≤
      (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) := by
  let F := nd_crossGeCSet (d := d) rGrid r c
  have hF : IsClosed F := nd_isClosed_crossGeCSet rGrid r c
  have hpre (n : ℕ) : ENNReal.ofReal c ≤
      (nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid n :
        Measure (nd_Joint d rGrid)) F := by
    have hX : Measurable (nd_jointSample P H ξ q rGrid n) :=
      nd_measurable_jointSample hH ξ q rGrid n
    change ENNReal.ofReal c ≤ (P.map (nd_jointSample P H ξ q rGrid n)) F
    rw [Measure.map_apply hX hF.measurableSet]
    apply (hcross n).trans
    apply measure_mono
    intro ω hω
    have ha : 0 < aQ P H ξ n q :=
      tight_aQ_pos (by have := h.dim; omega : 0 < d) hH ξ n hq0 hq1
    change c ≤ nd_crossPhi 0 (2 * r) r
      (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q))
    rw [nd_crossPhi_normMetricC ((hH.band n).continuous ω) ha]
    change c * aQ P H ξ n q < acrossDist ξ (fun z => H n z ω) 0 (2 * r) r at hω
    rw [mul_comm c] at hω
    exact ((lt_inv_mul_iff₀ ha).2 hω).le
  have hlimF : ENNReal.ofReal c ≤ (μ : Measure (nd_Joint d rGrid)) F :=
    LQGMetric.DFGPS.le_measure_of_isClosed hlim hF
      (Filter.Eventually.of_forall fun k => hpre (ns k))
  have hsub : F ⊆ nd_positiveCrossEvent rGrid r := by
    intro s hs
    exact hc.trans_le hs
  exact hlimF.trans (measure_mono hsub)

end HigherDimLQGMetric.DGZ
