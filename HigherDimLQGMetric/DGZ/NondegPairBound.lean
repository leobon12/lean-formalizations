import HigherDimLQGMetric.DGZ.NondegGoodFactor

/-! Each separated-code event has probability at most the square of the crossing probability. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_sepPairEvent_measure_le_square
    {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ)) (j : ℕ) :
    (μ : Measure (nd_Joint d rGrid)) (nd_sepPairEvent rGrid r j) ≤
      (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) *
        (μ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) := by
  classical
  let ν : Measure (nd_Joint d rGrid) := μ
  let Z := nd_positiveCrossEvent (d := d) rGrid r
  let A (i : nd_GoodIndex (d := d) rGrid r (2 * r) j) :=
    nd_goodCodeEvent rGrid r (2 * r) j i
  let B (i : nd_GoodIndex (d := d) rGrid (2 * r) r j) :=
    nd_goodCodeEvent rGrid (2 * r) r j i
  let sep (i : nd_GoodIndex (d := d) rGrid r (2 * r) j)
      (k : nd_GoodIndex (d := d) rGrid (2 * r) r j) :=
    nd_domainSeparated rGrid i.1 k.1
  have hd : 0 < d := by have := h.dim; omega
  have hpseudo := nd_ae_pseudoSet_of_tendsto h hH hq0 hq1 rGrid ns hlim
  have hA : (∑' i, ν (A i)) ≤ ν Z :=
    nd_tsum_goodCode_first_le_cross hd hrGrid hr j ν hpseudo
  have hB : (∑' i, ν (B i)) ≤ ν Z :=
    nd_tsum_goodCode_second_le_cross hd hrGrid hr j ν hpseudo
  have hfac (i : nd_GoodIndex (d := d) rGrid r (2 * r) j)
      (k : nd_GoodIndex (d := d) rGrid (2 * r) r j)
      (hsep : sep i k) :
      ν (A i ∩ B k) = ν (A i) * ν (B k) := by
    exact nd_goodCode_factor_of_separated h hH hq0 hq1
      rGrid r hrGrid hr ns hns hlim j i k hsep
  rw [nd_sepPairEvent_eq]
  exact nd_measure_pairUnion_le_mul ν A B sep hfac hA hB

end HigherDimLQGMetric.DGZ
