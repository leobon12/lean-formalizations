import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteComponentBasic
import SupercriticalLQGUniqueness.B2.DG20Lim.CompleteFromPointwiseEscape

 

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.complete_finiteComponent_of_pointwise_escape
    (R : RData)
    (htri : ∀ x y z : ℂ,
      R.DfromR x z ≤ R.DfromR x y + R.DfromR y z)
    (hescape : ∀ u : ℂ, ∀ T : ℝ≥0∞, T ≠ ∞ →
      ∃ S : ℝ, ∀ v : ℂ, S ≤ dist v 0 → T ≤ R.DfromR u v)
    (u : ℂ) : CompleteSpace (FiniteComponent (R.toLSCMetric htri) u) := by
  let D := R.toLSCMetric htri
  apply EMetric.complete_of_cauchySeq_tendsto
  intro z hz
  have hc : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
        R.DfromR (z n).1 (z m).1 ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hz ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    have hh := hN n hn m hm
    exact le_of_lt hh
  obtain ⟨w, hw⟩ := R.exists_limit_of_pointwise_escape hescape
    (fun n => (z n).1) hc
  have htail : ∀ᶠ n in atTop, R.DfromR (z n).1 w < 1 :=
    hw.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  have hzw : R.DfromR (z N).1 w ≠ ∞ :=
    ne_top_of_lt ((hN N le_rfl).trans_le (by norm_num : (1 : ℝ≥0∞) ≤ ∞))
  have huz : R.DfromR u (z N).1 ≠ ∞ := ne_top_of_lt (z N).property
  have huw : R.DfromR u w ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨huz, hzw⟩)
      (htri u (z N).1 w)
  let wC : FiniteComponent D u := ⟨D.pt w, lt_top_iff_ne_top.mpr huw⟩
  refine ⟨wC, ?_⟩
  apply tendsto_iff_edist_tendsto_0.mpr
  exact hw

end SupercriticalLQGUniqueness.B2.DG20Lim
