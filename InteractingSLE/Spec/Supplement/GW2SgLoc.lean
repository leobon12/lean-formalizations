/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LcdStageLoc
import InteractingSLE.Spec.Supplement.WalkUnionMeanAE

/-!
# GW2's stage identity: the union of a retained marked local set with a staged program's explored set

Packet PROVE-GW2-RELDET, ruling R106, item (γ6) of the handoff. At stage `n` the physical set of K2's lines is the
inverted counterflow hull `retSet s W ζ` (marked by the counterflow record) together with the explored set of the
GW2 schedule run through the current partial piece — the explored set of a staged program (the schedule truncated
after piece `n` and capped at the current own time `t` is again a GW2 schedule program, a staged history by
`GW2Schedule.isStagedHistory_canonFam`).

PROVE-T14-SB2LCOND proved that the explored set of ANY staged program is a history-marked local set for its retained
past, in R58 form (`SB.Lcd.stageSet_markedLocal_of_thm12_thm13`: avoidance events in `aeSigma (pastSigma n) P`). Here,
following `WalkLaw.walkUnion_markedAE`:

* **`isHistoryAvoidanceLocal_union_stageSet`**: for any field-determined marked local set `A` (marks `ℋ`) of the
  centred field, `A ∪ stageSet n` is a marked local set for `ℋ ⊔ pastSigma n`, its avoidance events are events of
  `aeSigma (ℋ ⊔ pastSigma n) P`, the joint marks are field-determined, and `ℍ ∖ (A ∪ stageSet n)` is a.s. open when
  `ℍ ∖ A` is (through a measurable version of the explored set, `WalkLaw.exists_version_of_aeSigma`, and
  `WalkLaw.isHistoryAvoidanceLocal_union_of_det`).

The marks of the counterflow are joined AFTER the stage assembly: under a kernel that also conditions on the
counterflow the stage field is not a GFF on `ℍ`, so the counterflow is never put into the stage kernels.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4). Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A retained marked local set together with the explored set of a staged program is a marked local set** for
the joined marks (Theorems 1.2–1.3). -/
theorem isHistoryAvoidanceLocal_union_stageSet (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (n : ℕ)
    {A : Ω → Set ℂ} (hAo : ∀ᵐ ω ∂P, IsOpen (H \ A ω))
    (hAm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (A ω) U})
    (hℋd : ℋ ≤ aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hlocA : WholeField.IsHistoryAvoidanceLocal ℋ A (WholeField.centredField h u₀) P) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma (ℋ ⊔ pastSigma κ b jumps spec E n) P]
        {ω | Disjoint (A ω ∪ WalkLaw.stageSet κ b jumps spec E n ω) U}) ∧
    (∀ᵐ ω ∂P, IsOpen (H \ (A ω ∪ WalkLaw.stageSet κ b jumps spec E n ω))) ∧
    ℋ ⊔ pastSigma κ b jumps spec E n ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P ∧
    WholeField.IsHistoryAvoidanceLocal (ℋ ⊔ pastSigma κ b jumps spec E n)
      (fun ω => A ω ∪ WalkLaw.stageSet κ b jumps spec E n ω) (WholeField.centredField h u₀) P := by
  obtain ⟨hS, hoS, hlocS⟩ := SB.Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hE hreg hu₀ n
  have hR : StagedPiecesRegular κ b jumps P spec E := stagedPiecesRegular_of_regular h13 hκ hb hE hreg
  obtain ⟨f, hf, hp⟩ := StagedDet.exists_pastMap_eq_comp_field h12p h13 hκ hκ4 hb hh hE hR n
  have hdS := WalkLaw.pastSigma_le_aeSigma_centred hf hp u₀
  -- a measurable version of the explored set
  obtain ⟨S', -, hS'ae, hS'm⟩ := WalkLaw.exists_version_of_aeSigma
    (fun ω => WalkLaw.stageSet_subset_H (κ := κ) (b := b) (jumps := jumps) (spec := spec) (E := E) n ω) hoS hS
  have hlocS' := WalkLaw.isHistoryAvoidanceLocal_congr_ae (hS'ae.mono fun ω h => h.symm) hlocS
  have hU := WalkLaw.isHistoryAvoidanceLocal_union_of_det (WholeField.measurable_centredField hh.1 u₀) hAm hS'm
    hℋd hdS hlocA hlocS'
  refine ⟨fun U hU => ?_, ?_, sup_le hℋd hdS, WalkLaw.isHistoryAvoidanceLocal_congr_ae ?_ hU⟩
  · have e : {ω | Disjoint (A ω ∪ WalkLaw.stageSet κ b jumps spec E n ω) (U : Set ℂ)} =
        {ω | Disjoint (A ω) (U : Set ℂ)} ∩ {ω | Disjoint (WalkLaw.stageSet κ b jumps spec E n ω) (U : Set ℂ)} := by
      ext ω
      simp only [mem_ofPred_eq, disjoint_union_left, mem_inter_iff]
    rw [e]
    have h1 : MeasurableSet[aeSigma (ℋ ⊔ pastSigma κ b jumps spec E n) P] {ω | Disjoint (A ω) (U : Set ℂ)} :=
      ⟨_, (le_sup_left : ℋ ≤ ℋ ⊔ pastSigma κ b jumps spec E n) _ (hAm U hU), EventuallyEq.rfl⟩
    obtain ⟨T, hT, hTe⟩ := hS U hU
    have h2 : MeasurableSet[aeSigma (ℋ ⊔ pastSigma κ b jumps spec E n) P]
        {ω | Disjoint (WalkLaw.stageSet κ b jumps spec E n ω) (U : Set ℂ)} :=
      ⟨T, (le_sup_right : pastSigma κ b jumps spec E n ≤ ℋ ⊔ _) _ hT, hTe⟩
    exact h1.inter h2
  · filter_upwards [hAo, hoS] with ω h1 h2
    have e : H \ (A ω ∪ WalkLaw.stageSet κ b jumps spec E n ω) =
        (H \ A ω) ∩ (H \ WalkLaw.stageSet κ b jumps spec E n ω) := by
      ext z
      simp only [Set.mem_sdiff, mem_union, mem_inter_iff]
      tauto
    rw [e]
    exact h1.inter h2
  · filter_upwards [hS'ae] with ω hω
    rw [hω]

end InteractingSLE.Theorem14.GW2Rd
