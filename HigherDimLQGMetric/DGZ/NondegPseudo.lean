import HigherDimLQGMetric.DGZ.NondegCrossLimit

/-!
# Pseudometric properties of the whole-space joint limit coordinate

The elementary metric relations are closed in the topology of local uniform
convergence and hold at every prelimit level.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

def nd_pseudoSet (rGrid : ℝ) : Set (nd_Joint d rGrid) :=
  {s | (∀ x : Rd d, s.1 (x, x) = 0) ∧
    (∀ x y : Rd d, 0 ≤ s.1 (x, y)) ∧
    (∀ x y : Rd d, s.1 (x, y) = s.1 (y, x)) ∧
    ∀ x y z : Rd d, s.1 (x, z) ≤ s.1 (x, y) + s.1 (y, z)}

theorem nd_isClosed_pseudoSet (rGrid : ℝ) : IsClosed (nd_pseudoSet (d := d) rGrid) := by
  have e : nd_pseudoSet (d := d) rGrid =
      (⋂ x : Rd d, {s : nd_Joint d rGrid | s.1 (x, x) = 0}) ∩
      ((⋂ x : Rd d, ⋂ y : Rd d, {s : nd_Joint d rGrid | 0 ≤ s.1 (x, y)}) ∩
      ((⋂ x : Rd d, ⋂ y : Rd d, {s : nd_Joint d rGrid |
          s.1 (x, y) = s.1 (y, x)}) ∩
      (⋂ x : Rd d, ⋂ y : Rd d, ⋂ z : Rd d, {s : nd_Joint d rGrid |
          s.1 (x, z) ≤ s.1 (x, y) + s.1 (y, z)}))) := by
    ext s
    simp [nd_pseudoSet]
  rw [e]
  apply IsClosed.inter
  · exact isClosed_iInter fun x =>
      isClosed_eq ((continuous_eval_const (x, x)).comp continuous_fst) continuous_const
  apply IsClosed.inter
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const
        ((continuous_eval_const (x, y)).comp continuous_fst)
  apply IsClosed.inter
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq ((continuous_eval_const (x, y)).comp continuous_fst)
        ((continuous_eval_const (y, x)).comp continuous_fst)
  · exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_le ((continuous_eval_const (x, z)).comp continuous_fst)
        (((continuous_eval_const (x, y)).comp continuous_fst).add
          ((continuous_eval_const (y, z)).comp continuous_fst))

theorem nd_jointSample_mem_pseudoSet {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid : ℝ) (n : ℕ) (ω : Ω) :
    nd_jointSample P H ξ q rGrid n ω ∈ nd_pseudoSet rGrid := by
  have hφ : Continuous fun z => H n z ω := (hH.band n).continuous ω
  have ha : 0 ≤ (aQ P H ξ n q)⁻¹ :=
    inv_nonneg.2 (tight_aQ_pos (by have := h.dim; omega : 0 < d)
      hH ξ n hq0 hq1).le
  simp only [nd_pseudoSet, Set.mem_ofPred_eq, nd_jointSample]
  refine ⟨fun x => ?_, fun x y => ?_, fun x y => ?_, fun x y z => ?_⟩
  · rw [normMetricC_apply hφ, lfppMetric_self, mul_zero]
  · rw [normMetricC_apply hφ]
    exact mul_nonneg ha (lfppMetric_nonneg ξ _ x y)
  · rw [normMetricC_apply hφ, normMetricC_apply hφ, lfppMetric_comm]
  · rw [normMetricC_apply hφ, normMetricC_apply hφ, normMetricC_apply hφ, ← mul_add]
    exact mul_le_mul_of_nonneg_left (lfppMetric_triangle hφ x y z) ha

theorem nd_ae_pseudoSet_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ)) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)), s ∈ nd_pseudoSet rGrid := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim
    (nd_isClosed_pseudoSet rGrid)
  intro k
  change (P.map (nd_jointSample P H ξ q rGrid (ns k)))
    (nd_pseudoSet rGrid) = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q rGrid (ns k))
    (nd_isClosed_pseudoSet rGrid).measurableSet]
  have heq : (nd_jointSample P H ξ q rGrid (ns k)) ⁻¹' nd_pseudoSet rGrid =
      (Set.univ : Set Ω) := by
    ext ω
    simp [nd_jointSample_mem_pseudoSet h hH hq0 hq1 rGrid (ns k) ω]
  rw [heq]
  exact @IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure

end HigherDimLQGMetric.DGZ
