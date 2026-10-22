import HigherDimLQGMetric.DGZ.NondegDomains
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The joint metric state space for DGZ Lemma 6.9

The first coordinate is the normalized whole-space metric. Each remaining coordinate is a
normalized internal distance on one connected bounded cubical domain, with the coarse field
`h_m` subtracted pointwise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

noncomputable instance (r : ℝ) (i : nd_DomainIndex d r) :
    LocallyCompactSpace (nd_domain r i : Set (Rd d)) :=
  (nd_isOpen_domain r i).locallyCompactSpace

noncomputable instance (r : ℝ) (i : nd_DomainIndex d r) :
    PolishSpace C(nd_domain r i × nd_domain r i, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _

noncomputable instance : PolishSpace C(Rd d × Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _

/-- Whole-space candidate metric and all local internal metric coordinates. -/
abbrev nd_Joint (d : ℕ) (r : ℝ) : Type :=
  C(Rd d × Rd d, ℝ) ×
    ∀ i : nd_DomainIndex d r × ℕ,
      C(nd_domain r i.1 × nd_domain r i.1, ℝ)

noncomputable instance (r : ℝ) : PolishSpace (nd_Joint d r) := by
  unfold nd_Joint
  infer_instance

noncomputable instance (r : ℝ) :
    TopologicalSpace.MetrizableSpace (ProbabilityMeasure (nd_Joint d r)) :=
  MeasureTheory.instMetrizableSpaceProbabilityMeasure _

noncomputable instance (r : ℝ) :
    FirstCountableTopology (ProbabilityMeasure (nd_Joint d r)) :=
  TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology

/-- The pointwise random state at dyadic level `n`, normalized by `a_n^{(q)}`. -/
def nd_jointSample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℕ → Rd d → Ω → ℝ) (ξ : ℝ) (q : ℝ≥0∞) (r : ℝ) (n : ℕ) (ω : Ω) :
    nd_Joint d r :=
  (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q),
    fun i => internalMetricC ξ (fun z => H n z ω - H i.2 z ω)
      (nd_domain r i.1) (aQ P H ξ n q))

theorem nd_measurable_jointSample {κ : Rd d → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H)
    (ξ : ℝ) (q : ℝ≥0∞) (r : ℝ) (n : ℕ) :
    Measurable (nd_jointSample P H ξ q r n) := by
  apply Measurable.prodMk
  · exact measurable_normMetricC (hH.band n).continuous (hH.band n).measurable ξ _
  · apply Measurable.of_eval
    intro i
    apply measurable_internalMetricC
    · intro ω
      exact (hH.band n).continuous ω |>.sub ((hH.band i.2).continuous ω)
    · intro z
      exact (hH.band n).measurable z |>.sub ((hH.band i.2).measurable z)
    · exact nd_isOpen_domain r i.1
    · exact (nd_isConnected_domain r i.1).isPreconnected

end HigherDimLQGMetric.DGZ
