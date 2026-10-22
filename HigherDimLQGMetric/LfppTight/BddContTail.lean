import HigherDimLQGMetric.LfppTight.PerturbCompare
import Mathlib.Topology.ContinuousMap.Compact

/-! Uniform bound in probability for a random bounded continuous perturbation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_exists_bddCont_tail {d : ℕ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → C(Rd d, ℝ)) (hf : Measurable f)
    (hfb : ∀ ω, ∃ M : ℝ, ∀ z, |f ω z| ≤ M)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, 0 < M ∧
      P {ω | ∃ z : Rd d, M < |f ω z|} ≤ ENNReal.ofReal θ := by
  let B : ℕ → Set Ω := fun n => {ω | ∃ z : Rd d, (n : ℝ) < |f ω z|}
  have hBm (n : ℕ) : MeasurableSet (B n) := by
    let U : Set C(Rd d, ℝ) := {F | ∃ z : Rd d, (n : ℝ) < |F z|}
    have hU : IsOpen U := by
      have heq : U = ⋃ z : Rd d, {F : C(Rd d, ℝ) | (n : ℝ) < |F z|} := by
        ext F
        simp [U]
      rw [heq]
      apply isOpen_iUnion
      intro z
      simpa only [Set.preimage, Set.mem_Ioi, Function.comp_apply, Set.mem_ofPred_eq] using
        (isOpen_Ioi.preimage
          (continuous_abs.comp (continuous_eval_const z)))
    change MeasurableSet (f ⁻¹' U)
    exact hf hU.measurableSet
  have hBa : Antitone B := by
    intro m n hmn ω hω
    obtain ⟨z, hz⟩ := hω
    exact ⟨z, lt_of_le_of_lt (by exact_mod_cast hmn) hz⟩
  have hBi : (⋂ n : ℕ, B n) = ∅ := by
    ext ω
    constructor
    · intro hω
      obtain ⟨M, hM⟩ := hfb ω
      obtain ⟨n, hn⟩ := exists_nat_gt M
      obtain ⟨z, hz⟩ := mem_iInter.mp hω n
      have hn' : M < (n : ℝ) := by exact_mod_cast hn
      linarith [hM z]
    · intro hω
      simp at hω
  have ht : Tendsto (fun n => P (B n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P)
      (fun n => (hBm n).nullMeasurableSet) hBa
      ⟨0, measure_ne_top _ _⟩
    simp only [Function.comp_def] at h
    rwa [hBi, measure_empty] at h
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds
    (show (0 : ℝ≥0∞) < ENNReal.ofReal θ by simp [hθ]))).exists
  refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
  have hsub : {ω | ∃ z : Rd d, (n : ℝ) + 1 < |f ω z|} ⊆ B n := by
    rintro ω ⟨z, hz⟩
    exact ⟨z, by linarith⟩
  exact (measure_mono hsub).trans hn.le

end HigherDimLQGMetric
