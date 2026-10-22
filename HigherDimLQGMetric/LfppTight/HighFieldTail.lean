import HigherDimLQGMetric.LfppTight.CoupledVec
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.Compact

/-! A continuous fixed high-band field has a tight supremum on each compact ball. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

def l6a_highNorm {d : ℕ} {Ω : Type*} (Ψ : Rd d → Ω → ℝ)
    (hΨc : ∀ ω, Continuous fun z => Ψ z ω) (R : ℝ) (ω : Ω) : ℝ := by
  letI : CompactSpace (closedBall (0 : Rd d) R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact ‖(⟨fun z : closedBall (0 : Rd d) R => Ψ z ω,
    (hΨc ω).comp continuous_subtype_val⟩ : C(closedBall (0 : Rd d) R, ℝ))‖

theorem l6a_abs_highField_le_norm {d : ℕ} {Ω : Type*} (Ψ : Rd d → Ω → ℝ)
    (hΨc : ∀ ω, Continuous fun z => Ψ z ω) (R : ℝ) (ω : Ω)
    {z : Rd d} (hz : z ∈ closedBall (0 : Rd d) R) :
    |Ψ z ω| ≤ l6a_highNorm Ψ hΨc R ω := by
  letI : CompactSpace (closedBall (0 : Rd d) R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  simpa [l6a_highNorm, Real.norm_eq_abs] using
    (ContinuousMap.norm_coe_le_norm
      (⟨fun z : closedBall (0 : Rd d) R => Ψ z ω,
        (hΨc ω).comp continuous_subtype_val⟩ : C(closedBall (0 : Rd d) R, ℝ)) ⟨z, hz⟩)

/-- The supremum of a continuous random field on a fixed compact ball has an
arbitrarily small upper tail.  No Gaussian estimate is needed because the
high-band field is independent of the cutoff. -/
theorem l6a_exists_highField_sup_tail {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Ψ : Rd d → Ω → ℝ) (hΨc : ∀ ω, Continuous fun z => Ψ z ω)
    (hΨm : ∀ z, Measurable (Ψ z))
    {R θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, 0 < M ∧
      P {ω | M < l6a_highNorm Ψ hΨc R ω} ≤ ENNReal.ofReal θ := by
  letI : CompactSpace (closedBall (0 : Rd d) R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let F : Ω → C(closedBall (0 : Rd d) R, ℝ) := fun ω =>
    ⟨fun z => Ψ z ω, (hΨc ω).comp continuous_subtype_val⟩
  have hFm : Measurable F := ContinuousMap.measurable_iff_eval.mpr fun z => hΨm z
  let N : Ω → ℝ := fun ω => ‖F ω‖
  have hNm : Measurable N := continuous_norm.measurable.comp hFm
  have ht : Tendsto (fun n : ℕ => P {ω | (n : ℝ) < N ω}) atTop (𝓝 0) := by
    have hm : Antitone fun n : ℕ => {ω | (n : ℝ) < N ω} := by
      intro m n hmn ω hω
      change (n : ℝ) < N ω at hω
      change (m : ℝ) < N ω
      exact lt_of_le_of_lt (by exact_mod_cast hmn) hω
    have hI : (⋂ n : ℕ, {ω | (n : ℝ) < N ω}) = ∅ := by
      ext ω
      simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      exact exists_nat_ge (N ω)
    have h := tendsto_measure_iInter_atTop (μ := P)
      (fun n : ℕ => (measurableSet_lt measurable_const hNm).nullMeasurableSet) hm
      ⟨0, measure_ne_top _ _⟩
    simp only [Function.comp_def] at h
    rwa [hI, measure_empty] at h
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds
    (show (0 : ℝ≥0∞) < ENNReal.ofReal θ by simp [hθ]))).exists
  refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
  change P {ω | (n : ℝ) + 1 < N ω} ≤ ENNReal.ofReal θ
  exact (measure_mono (by
    intro ω hω
    change (n : ℝ) + 1 < N ω at hω
    change (n : ℝ) < N ω
    linarith)).trans hn.le

end HigherDimLQGMetric
