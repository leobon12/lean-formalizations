import HigherDimLQGMetric.DGZ.NondegConnectedAE

/-! The local candidate metrics have zero diagonal under every joint limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

def nd_localDiagSet (rGrid : ℝ) (i : nd_DomainIndex d rGrid) (m : ℕ) :
    Set (nd_Joint d rGrid) :=
  {s | ∀ x : nd_domain rGrid i, s.2 (i, m) (x, x) = 0}

theorem nd_isClosed_localDiagSet (rGrid : ℝ) (i : nd_DomainIndex d rGrid) (m : ℕ) :
    IsClosed (nd_localDiagSet rGrid i m) := by
  have heq : nd_localDiagSet rGrid i m = ⋂ x : nd_domain rGrid i,
      {s : nd_Joint d rGrid | s.2 (i, m) (x, x) = 0} := by
    ext s
    simp [nd_localDiagSet]
  rw [heq]
  exact isClosed_iInter fun x => isClosed_eq
    ((continuous_eval_const (x, x)).comp
      ((continuous_apply (i, m)).comp continuous_snd)) continuous_const

theorem nd_jointSample_mem_localDiagSet {κ : Rd d → ℝ} {ξ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (q : ℝ≥0∞)
    (rGrid : ℝ) (n : ℕ) (i : nd_DomainIndex d rGrid) (m : ℕ) (ω : Ω) :
    nd_jointSample P H ξ q rGrid n ω ∈ nd_localDiagSet rGrid i m := by
  intro x
  change internalMetricC ξ (fun z => H n z ω - H m z ω)
    (nd_domain rGrid i) (aQ P H ξ n q) (x, x) = 0
  have hnm : Continuous fun z => H n z ω - H m z ω :=
    ((hH.band n).continuous ω).sub ((hH.band m).continuous ω)
  rw [internalMetricC_apply hnm
    (nd_isOpen_domain rGrid i) (nd_isConnected_domain rGrid i).isPreconnected]
  simp only [lfppDistOn_self, mul_zero]

theorem nd_ae_localDiagSet_of_tendsto {κ : Rd d → ℝ} {ξ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (q : ℝ≥0∞)
    (rGrid : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d rGrid) (m : ℕ) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)), s ∈ nd_localDiagSet rGrid i m := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim
    (nd_isClosed_localDiagSet rGrid i m)
  intro k
  change (P.map (nd_jointSample P H ξ q rGrid (ns k)))
    (nd_localDiagSet rGrid i m) = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q rGrid (ns k))
    (nd_isClosed_localDiagSet rGrid i m).measurableSet]
  have heq : (nd_jointSample P H ξ q rGrid (ns k)) ⁻¹' nd_localDiagSet rGrid i m =
      (Set.univ : Set Ω) := by
    ext ω
    simp [nd_jointSample_mem_localDiagSet hH q rGrid (ns k) i m ω]
  rw [heq]
  exact @IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure

end HigherDimLQGMetric.DGZ
