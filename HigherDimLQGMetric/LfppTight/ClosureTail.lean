import HigherDimLQGMetric.B3.Interfaces
import Mathlib.MeasureTheory.Measure.Portmanteau
import LQGMetric.Papers.DFGPS.L2_5ProofLim

/-! Closed-event portmanteau and a reusable positive-observable criterion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

theorem l6a_closed_prob_lower_of_closure {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
    (S : Set (ProbabilityMeasure E)) {F : Set E} (hF : IsClosed F)
    (q : ℝ≥0∞) (hpre : ∀ ν ∈ S, q ≤ (ν : Measure E) F)
    (μ : ProbabilityMeasure E) (hμ : μ ∈ closure S) :
    q ≤ (μ : Measure E) F := by
  obtain ⟨νs, hνs, hlim⟩ := mem_closure_iff_seq_limit.mp hμ
  have hlow : q ≤ limsup (fun n => (νs n : Measure E) F) atTop := by
    simpa only [limsup_const] using
    (limsup_le_limsup (f := atTop)
      (Filter.Eventually.of_forall fun n => hpre (νs n) (hνs n))
      (u := fun _ : ℕ => q))
  exact hlow.trans (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hF)

theorem l6a_ae_pos_of_uniform_lower_tail {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
    (S : Set (ProbabilityMeasure E)) (F : E → ℝ) (hF : Continuous F)
    (htail : ∀ θ : ℝ, 0 < θ → ∃ δ : ℝ, 0 < δ ∧
      ∀ ν ∈ S, (ν : Measure E) {x | F x < δ} ≤ ENNReal.ofReal θ)
    (μ : ProbabilityMeasure E) (hμ : μ ∈ closure S) :
    ∀ᵐ x ∂(μ : Measure E), 0 < F x := by
  rw [ae_iff]
  have hzero : (μ : Measure E) {x | ¬ 0 < F x} ≤ 0 := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨δ, hδ, hpre⟩ := htail (ε : ℝ) (by exact_mod_cast hε)
    let C : Set E := {x | δ ≤ F x}
    have hC : IsClosed C := isClosed_le continuous_const hF
    have hCcomp : Cᶜ = {x : E | F x < δ} := by ext x; simp [C]
    have hpreC (ν : ProbabilityMeasure E) (hν : ν ∈ S) :
        (1 : ℝ≥0∞) - ENNReal.ofReal (ε : ℝ) ≤ (ν : Measure E) C := by
      have hbad : (ν : Measure E) Cᶜ ≤ ENNReal.ofReal (ε : ℝ) := by
        rw [hCcomp]
        exact hpre ν hν
      rw [prob_compl_eq_one_sub hC.measurableSet] at hbad
      exact (tsub_le_iff_right.mpr (by
        simpa only [add_comm] using (tsub_le_iff_right.mp hbad)))
    have hμC := l6a_closed_prob_lower_of_closure S hC
      (1 - ENNReal.ofReal (ε : ℝ)) hpreC μ hμ
    have hbad : (μ : Measure E) Cᶜ ≤ ENNReal.ofReal (ε : ℝ) := by
      rw [prob_compl_eq_one_sub hC.measurableSet]
      exact tsub_le_iff_right.mpr (by
        simpa only [add_comm] using (tsub_le_iff_right.mp hμC))
    have hsub : {x : E | ¬ 0 < F x} ⊆ Cᶜ := by
      intro x hx
      change ¬ 0 < F x at hx
      change ¬ δ ≤ F x
      linarith
    simpa only [zero_add, ENNReal.ofReal_coe_nnreal] using
      (measure_mono hsub).trans hbad
  exact le_antisymm hzero bot_le

theorem l6a_ae_exists_closed_of_uniform_tail {E ι : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
    (S : Set (ProbabilityMeasure E)) (F : ι → Set E)
    (hF : ∀ k, IsClosed (F k))
    (htail : ∀ θ : ℝ, 0 < θ → ∃ k : ι,
      ∀ ν ∈ S, (ν : Measure E) (F k)ᶜ ≤ ENNReal.ofReal θ)
    (μ : ProbabilityMeasure E) (hμ : μ ∈ closure S) :
    ∀ᵐ x ∂(μ : Measure E), ∃ k, x ∈ F k := by
  rw [ae_iff]
  have hzero : (μ : Measure E) {x | ¬ ∃ k, x ∈ F k} ≤ 0 := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨k, hpre⟩ := htail (ε : ℝ) (by exact_mod_cast hε)
    have hpreC (ν : ProbabilityMeasure E) (hν : ν ∈ S) :
        (1 : ℝ≥0∞) - ENNReal.ofReal (ε : ℝ) ≤ (ν : Measure E) (F k) := by
      have hbad := hpre ν hν
      rw [prob_compl_eq_one_sub (hF k).measurableSet] at hbad
      exact tsub_le_iff_right.mpr (by
        simpa only [add_comm] using (tsub_le_iff_right.mp hbad))
    have hμF := l6a_closed_prob_lower_of_closure S (hF k)
      (1 - ENNReal.ofReal (ε : ℝ)) hpreC μ hμ
    have hbad : (μ : Measure E) (F k)ᶜ ≤ ENNReal.ofReal (ε : ℝ) := by
      rw [prob_compl_eq_one_sub (hF k).measurableSet]
      exact tsub_le_iff_right.mpr (by
        simpa only [add_comm] using (tsub_le_iff_right.mp hμF))
    have hsub : {x : E | ¬ ∃ k, x ∈ F k} ⊆ (F k)ᶜ := by
      intro x hx hmem
      exact hx ⟨k, hmem⟩
    simpa only [zero_add, ENNReal.ofReal_coe_nnreal] using
      (measure_mono hsub).trans hbad
  exact le_antisymm hzero bot_le

end HigherDimLQGMetric
