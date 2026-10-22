import HigherDimLQGMetric.B3.Interfaces
import HigherDimLQGMetric.Weak.DetInternalTight
import LQGMetric.Prob.PolishContinuousMap
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Length of subsequential metric laws

This is the probabilistic part of [1] Lemma 3.1(1).  The deterministic
closure implication is the checked DL1 theorem in `Weak.DetInternalTight`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- A proper continuous metric in the compact-open closure of length metrics is a length metric. -/
theorem l6c_length_of_closure {d : ℕ} (D : C(Rd d × Rd d, ℝ))
    (hc : D ∈ closure {E : C(Rd d × Rd d, ℝ) | IsContLengthFn E})
    (hm : IsContinuousMetric D) (hp : IsProperFn D) : IsContLengthFn D := by
  obtain ⟨Dn, hDn, hlim⟩ := mem_closure_iff_seq_limit.mp hc
  apply l6c_lengthLimit d Dn D hDn hm hp
  intro R _
  have hK : IsCompact
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim) _ hK

/-- Closed supports survive closure of a family of probability laws. -/
theorem l6c_ae_mem_closed_of_closure {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
    {S : Set (ProbabilityMeasure E)} {μ : ProbabilityMeasure E}
    (hμ : μ ∈ closure S) {F : Set E} (hF : IsClosed F)
    (hS : ∀ ν ∈ S, (ν : Measure E) F = 1) :
    ∀ᵐ x ∂(μ : Measure E), x ∈ F := by
  obtain ⟨νs, hνs, hlim⟩ := mem_closure_iff_seq_limit.mp hμ
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF
  simp only [hS _ (hνs _), limsup_const] at hle
  have heq : (μ : Measure E) F = (μ : Measure E) univ := by
    rw [measure_univ]
    exact le_antisymm prob_le_one hle
  exact (ae_mem_iff_measure_eq hF.measurableSet.nullMeasurableSet).2 heq

/-- Lemma 3.1(1): proper continuous metric limits of a tight family of a.s. length metrics
remain length metrics. The tight-family closure hypothesis also supplies properness. -/
theorem l6c_lemma31_lengthLaw {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → C(Rd d × Rd d, ℝ)) (S : Set ι)
    (hT : TightFamily P X S)
    (hLen : ∀ i ∈ S, ∀ᵐ ω ∂P, IsContLengthFn (X i ω))
    (μ : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (hμ : μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X i)}) :
    ∀ᵐ D ∂(μ : Measure C(Rd d × Rd d, ℝ)), IsContLengthFn D := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let F : Set C(Rd d × Rd d, ℝ) := closure {D | IsContLengthFn D}
  have hF : IsClosed F := isClosed_closure
  have hpre : ∀ ν ∈ {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X i)},
      (ν : Measure C(Rd d × Rd d, ℝ)) F = 1 := by
    intro ν hν
    obtain ⟨i, hi, hν⟩ := hν
    rw [hν, Measure.map_apply_of_aemeasurable (hT.1 i hi) hF.measurableSet]
    have hae : ∀ᵐ ω ∂P, X i ω ∈ F :=
      (hLen i hi).mono fun ω hω => subset_closure hω
    exact (measure_congr (eventuallyEqSet_univ.2 hae)).trans measure_univ
  filter_upwards [l6c_ae_mem_closed_of_closure hμ hF hpre, hT.2.2 μ hμ]
    with D hD hgood
  exact l6c_length_of_closure D hD hgood.1 hgood.2

end HigherDimLQGMetric
