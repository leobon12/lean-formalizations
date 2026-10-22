import HigherDimLQGMetric.DGZ.NondegProkhorov
import LQGMetric.Papers.DFGPS.L2_5ProofLim
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Closed relations in the DGZ joint limit law

The first relation is `D̃(x,y) ≤ D̃_{0,U}(x,y)` on each cubical domain `U`. It follows from
domain monotonicity at every dyadic level and passes to weak limits as a closed relation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- The global candidate distance does not exceed the zero-coarse-scale internal distance. -/
def nd_globalLE (r : ℝ) (i : nd_DomainIndex d r) : Set (nd_Joint d r) :=
  {x | ∀ p : nd_domain r i × nd_domain r i,
    x.1 (p.1.1, p.2.1) ≤ x.2 (i, 0) p}

theorem nd_isClosed_globalLE (r : ℝ) (i : nd_DomainIndex d r) :
    IsClosed (nd_globalLE r i) := by
  have e : nd_globalLE r i = ⋂ p : nd_domain r i × nd_domain r i,
      {x : nd_Joint d r | x.1 (p.1.1, p.2.1) ≤ x.2 (i, 0) p} := by
    ext x
    simp [nd_globalLE]
  rw [e]
  exact isClosed_iInter fun p =>
    isClosed_le ((continuous_eval_const _).comp continuous_fst)
      ((continuous_eval_const p).comp ((continuous_apply (i, 0)).comp continuous_snd))

theorem nd_jointSample_mem_globalLE {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (n : ℕ)
    (i : nd_DomainIndex d r) :
    ∀ᵐ ω ∂P, nd_jointSample P H ξ q r n ω ∈ nd_globalLE r i := by
  have hzero := ae_forall_eq_zero_of_isBandVersion_self h.kernel hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  filter_upwards [hzero] with ω hω
  intro p
  have hφ : Continuous fun z => H n z ω := (hH.band n).continuous ω
  have hsub : (fun z => H n z ω - H 0 z ω) = (fun z => H n z ω) :=
    funext fun z => by rw [hω z, sub_zero]
  have hd0 : 0 < d := by have := h.dim; omega
  have ha : 0 ≤ (aQ P H ξ n q)⁻¹ :=
    inv_nonneg.2 (tight_aQ_pos hd0 hH ξ n hq0 hq1).le
  have hj : PcwJoined (nd_domain r i) p.1.1 p.2.1 :=
    pcwJoined_of_isPreconnected (nd_isOpen_domain r i)
      (nd_isConnected_domain r i).isPreconnected p.1.2 p.2.2
  change normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q) (p.1.1, p.2.1) ≤
    internalMetricC ξ (fun z => H n z ω - H 0 z ω)
      (nd_domain r i) (aQ P H ξ n q) p
  rw [hsub, normMetricC_apply hφ,
    internalMetricC_apply hφ (nd_isOpen_domain r i)
      (nd_isConnected_domain r i).isPreconnected]
  exact mul_le_mul_of_nonneg_left (lfppMetric_le_lfppDistOn hj) ha

/-- The global/internal domination relation passes to every joint weak limit. -/
theorem nd_ae_globalLE_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d r) :
    ∀ᵐ x ∂(μ : Measure (nd_Joint d r)), x ∈ nd_globalLE r i := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim (nd_isClosed_globalLE r i)
  intro k
  change (P.map (nd_jointSample P H ξ q r (ns k))) (nd_globalLE r i) = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q r (ns k))
    (nd_isClosed_globalLE r i).measurableSet]
  exact (measure_congr (eventuallyEqSet_univ.2
    (nd_jointSample_mem_globalLE h hH hq0 hq1 r (ns k) i))).trans
      (@IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure)

end HigherDimLQGMetric.DGZ
