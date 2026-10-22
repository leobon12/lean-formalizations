import HigherDimLQGMetric.Events.WitnessMeas

/-! Universal measurability of quantified internal-distance inequalities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set LQGMetric
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  [MeasurableSpace β] [StandardBorelSpace β]

/-- A Borel relation universally quantified over a standard Borel parameter
remains universally measurable. -/
theorem uMeasurableSet_forall_mem (K : Set β) (hK : MeasurableSet K)
    {R : Set (α × β)} (hR : MeasurableSet R) :
    UMeasurableSet {a : α | ∀ b ∈ K, (a, b) ∈ R} := by
  let S : Set (α × β) := {p | p.2 ∈ K → p ∈ R}
  have hS : MeasurableSet S := by
    convert (hK.preimage measurable_snd).compl.union hR using 1
    ext p
    simp [S, imp_iff_not_or]
  simpa only [S, mem_ofPred_eq] using UMeasurableSet.setOf_forall hS

/-- A Borel two-point observable has universally measurable supremum
sublevel sets, even if its parameter dependence is only Borel. -/
theorem uMeasurableSet_iSup_le (K : Set β) (hK : MeasurableSet K)
    {f : α × β → ℝ≥0∞} (hf : Measurable f) {c : α → ℝ≥0∞}
    (hc : Measurable c) :
    UMeasurableSet {a : α | (⨆ b ∈ K, f (a, b)) ≤ c a} := by
  have hR : MeasurableSet {p : α × β | f p ≤ c p.1} :=
    measurableSet_le hf (hc.comp measurable_fst)
  convert uMeasurableSet_forall_mem K hK hR using 1
  ext a
  simp only [mem_ofPred_eq, iSup_le_iff]

/-- A Borel two-point observable has universally measurable infimum
strict superlevel sets. A countable rational margin handles the strict infimum. -/
theorem uMeasurableSet_lt_iInf (K : Set β) (hK : MeasurableSet K)
    {f : α × β → ℝ≥0∞} (hf : Measurable f) {c : α → ℝ≥0∞}
    (hc : Measurable c) :
    UMeasurableSet {a : α | c a < ⨅ b ∈ K, f (a, b)} := by
  have hq (q : ℚ) : UMeasurableSet
      {a : α | c a < (ENNReal.ofReal (q : ℝ)) ∧
        ∀ b ∈ K, ENNReal.ofReal (q : ℝ) ≤ f (a, b)} := by
    have hR : MeasurableSet {p : α × β |
        ENNReal.ofReal (q : ℝ) ≤ f p} := measurableSet_le measurable_const hf
    exact (UMeasurableSet.of_measurableSet
      (measurableSet_lt hc measurable_const)).inter
        (uMeasurableSet_forall_mem K hK hR)
  have he : {a : α | c a < ⨅ b ∈ K, f (a, b)} =
      ⋃ q : ℚ, {a : α | c a < ENNReal.ofReal (q : ℝ) ∧
        ∀ b ∈ K, ENNReal.ofReal (q : ℝ) ≤ f (a, b)} := by
    ext a
    constructor
    · intro ha
      obtain ⟨q, hq0, hcq, hqinf⟩ := ENNReal.lt_iff_exists_rat_btwn.1 ha
      refine mem_iUnion.mpr ⟨q, hcq, ?_⟩
      intro b hb
      exact hqinf.le.trans (iInf₂_le b hb)
    · intro ha
      obtain ⟨q, hcq, hqall⟩ := mem_iUnion.mp ha
      exact hcq.trans_le (le_iInf₂ hqall)
  rw [he]
  exact UMeasurableSet.iUnion hq

end HigherDimLQGMetric
