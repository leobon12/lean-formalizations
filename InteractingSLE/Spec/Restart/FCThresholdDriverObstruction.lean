/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCPlumbAssembly2Inputs
import Mathlib.Analysis.Real.Cardinality

/-!
# The exact branch-cover requirement of the threshold-driver record

The committed record requires an everywhere countable force-type cover. This
imposes an everywhere countable range on the left seed weight. Almost-sure word
identification alone does not impose that condition on null modifications.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Restart.FCPlumb

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The first left weight of the padded force word at seed zero. -/
def fcLeftSeedWeight (κ θ : ℝ) (c : BoundaryWord) : ℝ :=
  (flowPad κ θ (c, 0)).2.1 0

omit mΩ in
/-- A word of a fixed type has one of the finitely many left weights of that type. -/
theorem fcLeftSeedWeight_mem_range_of_mem_typeSet {κ θ : ℝ} {c : BoundaryWord}
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hc : c ∈ FCDet.typeSet κ θ nL nR ρL ρR) :
    fcLeftSeedWeight κ θ c ∈ Set.range ρL := by
  have hN : flowLineNL c.fn c.jumps 0 = nL := hc.1
  have hpos : 0 < nL := by rw [← hN, flowLineNL]; omega
  exact ⟨⟨0, hpos⟩, (hc.2.2.1 ⟨0, hpos⟩).symm⟩

/-- The committed record forces an everywhere countable seed-weight range on its
live set. The proof uses only its all-sample cover and word-type fields. -/
theorem FCThresholdDriverInputs.countable_leftSeedWeights
    {P : Measure Ω} {κ θ : ℝ} {M : Set Ω} {β : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (h : FCThresholdDriverInputs P κ θ M β Hc Γ U) :
    ((fun ω => fcLeftSeedWeight κ θ (β ω)) '' M).Countable := by
  apply (Set.countable_range (fun p : Σ i, Fin (h.nL i) => h.rhoL p.1 p.2)).mono
  rintro y ⟨ω, hω, rfl⟩
  obtain ⟨i, hi⟩ := h.cover ω hω
  obtain ⟨j, hj⟩ := fcLeftSeedWeight_mem_range_of_mem_typeSet (h.word_type i ω hi)
  exact ⟨⟨i, j⟩, hj⟩

/-- An uncountable seed-weight image obstructs the exact committed record,
independently of any clock or stochastic-law arguments. -/
theorem not_nonempty_thresholdInputs_of_uncountable_seedWeights
    {P : Measure Ω} {κ θ : ℝ} {M : Set Ω} {β : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hβ : ¬ ((fun ω => fcLeftSeedWeight κ θ (β ω)) '' M).Countable) :
    ¬ Nonempty (FCThresholdDriverInputs P κ θ M β Hc Γ U) := by
  rintro ⟨h⟩
  exact hβ h.countable_leftSeedWeights

omit mΩ in
/-- Constant boundary data chosen to give left seed weight `r` at angle zero. -/
def fcSeedWord (κ r : ℝ) : BoundaryWord :=
  (0, (fun _ => 0), fun _ => -(r + 1) * sleLambda κ)

omit mΩ in
theorem measurable_fcSeedWord (κ : ℝ) : Measurable (fcSeedWord κ) :=
  measurable_const.prodMk (measurable_const.prodMk
    (measurable_pi_iff.2 fun _ => ((measurable_id.add_const 1).neg).mul_const _))

omit mΩ in
theorem fcSeedWord_isSorted (κ r : ℝ) : (fcSeedWord κ r).IsSorted := by
  intro i j hij hj
  exact False.elim (Nat.not_lt_zero j hj)

omit mΩ in
theorem fcLeftSeedWeight_fcSeedWord {κ : ℝ} (hκ : 0 < κ) (r : ℝ) :
    fcLeftSeedWeight κ 0 (fcSeedWord κ r) = r := by
  have hLam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  have hfn : (fcSeedWord κ r).fn = fun _ => -(r + 1) * sleLambda κ := rfl
  have hJ : (fcSeedWord κ r).jumps = ∅ := by simp [fcSeedWord, BoundaryWord.jumps]
  have hlim (a : ℝ) : PiecewiseConstantBoundaryData.leftLim (fun _ => a) 0 = a :=
    tendsto_const_nhds.limUnder_eq
  simp [fcLeftSeedWeight, flowPad, hfn, hJ,
    flowLineNL, flowLineRhoL, PiecewiseConstantBoundaryData.jumpSet, hlim]
  field_simp [hLam]
  ring

omit mΩ in
/-- A measurable, everywhere sorted word may have uncountably many seed weights
on a null event, even though it equals one constant word almost surely. -/
theorem null_modification_can_have_uncountably_many_seedWeights {κ : ℝ} (hκ : 0 < κ) :
    Measurable (fcSeedWord κ) ∧ (∀ r, (fcSeedWord κ r).IsSorted) ∧
      fcSeedWord κ =ᵐ[Measure.dirac (0 : ℝ)] (fun _ => fcSeedWord κ 0) ∧
      Measure.dirac (0 : ℝ) ({0}ᶜ) = 0 ∧
      ¬ ((fun r => fcLeftSeedWeight κ 0 (fcSeedWord κ r)) '' ({0}ᶜ)).Countable := by
  refine ⟨measurable_fcSeedWord κ, fcSeedWord_isSorted κ, ?_, ?_, ?_⟩
  · exact (ae_dirac_iff (measurableSet_eq_fun (measurable_fcSeedWord κ) measurable_const)).2 rfl
  · simp
  · simp only [fcLeftSeedWeight_fcSeedWord hκ, image_id']
    intro hc
    apply Cardinal.not_countable_real
    simpa only [compl_union_self] using hc.union (Set.countable_singleton (0 : ℝ))

/-- For the preceding null modification the exact old record cannot exist, no
matter how its field, path, lifetime, filtration, or driver are chosen. -/
theorem no_thresholdInputs_for_null_seedWord {κ : ℝ} (hκ : 0 < κ)
    (Hc : ℝ → DistOn upperHalfPlaneOpens) (Γ : ℝ → ℝ≥0 → ℂ) (U : ℝ → ℝ≥0∞) :
    ¬ Nonempty (FCThresholdDriverInputs (Measure.dirac (0 : ℝ)) κ 0
      ({0}ᶜ) (fcSeedWord κ) Hc Γ U) :=
  not_nonempty_thresholdInputs_of_uncountable_seedWeights
    (null_modification_can_have_uncountably_many_seedWeights hκ).2.2.2.2

end InteractingSLE.Restart.FCPlumb
