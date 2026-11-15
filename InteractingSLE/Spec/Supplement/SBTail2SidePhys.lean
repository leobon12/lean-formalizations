/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2SideTips
import InteractingSLE.Spec.Supplement.SBTail2SideArcs
import InteractingSLE.Spec.Supplement.SBTail2SideClosed
import InteractingSLE.Spec.Supplement.WalkUnionLawMain

/-! # Measurable full physical sets and both sides under R51

The dense code includes all ordinary-piece contacts and all real connectors.
Regularization supplies measurable launch events; exact terminal-state agreement
transfers the resulting closed set and its sides back to the original history.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Side

open Exist.Staged Exist.StagedLaw GW2aCont

/-- The countable point index for all pieces and connectors of a finite program. -/
abbrev PhysIndex (spec : ExplSpec) := Unit ⊕
  ((Fin spec.2.2.length × (Unit ⊕ (ℕ × ℕ))) ⊕ (Fin spec.2.2.length × (Unit ⊕ ℚ)))

/-- R51 and measurable driver coordinates give a measurable dense code of the
entire physical set, with equality almost surely in the whole complex plane. -/
theorem exists_measurable_physSet_dense_code {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hR : StagedPiecesRegular κ b jumps P spec E) :
    ∃ F : Ω → PhysIndex spec → ℂ, (∀ i, Measurable fun ω => F ω i) ∧
      ∀ᵐ ω ∂P, ExplState.physSet κ b jumps spec (fun j => E j ω) = closure (range (F ω)) := by
  let E' := StagedReg.regHist spec E
  have hR' := WalkLaw.stagedPiecesRegular_regHist hR
  obtain ⟨M, hMae, hMm, hMp⟩ := hR'.ae_pieceRegular.exists_measurable_mem
  obtain ⟨T, hTm, hT⟩ := exists_measurable_piece_dense_code hb spec
    (E := E') (StagedReg.measurable_regHist hEm) StagedReg.isRegularDriver_regHist hMm hMp
  obtain ⟨A, hAm, hA⟩ := exists_measurable_arc_dense_code hb spec
    (E := E') (StagedReg.measurable_regHist hEm) StagedReg.isRegularDriver_regHist
  let F : Ω → PhysIndex spec → ℂ := fun ω => Sum.elim (fun _ => (spec.1 : ℂ))
    (Sum.elim (fun p => T p.1 ω p.2) (fun p => A p.1 ω p.2))
  refine ⟨F, ?_, ?_⟩
  · rintro (_ | (⟨k, i⟩ | ⟨k, i⟩))
    · exact measurable_const
    · exact hTm k i
    · exact hAm k i
  · filter_upwards [hMae, StagedReg.ae_run_regHist hR] with ω hωM hrun
    rw [← StagedReg.physSet_eq_of_run_eq (hrun spec.2.2.length), physSet_eq]
    have hr : range (F ω) = ({(spec.1 : ℂ)} ∪ ⋃ k : Fin spec.2.2.length, range (T k ω)) ∪
        ⋃ k : Fin spec.2.2.length, range (A k ω) := by
      ext z
      constructor
      · rintro ⟨(_ | (⟨k, i⟩ | ⟨k, i⟩)), rfl⟩
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr (mem_iUnion.2 ⟨k, ⟨i, rfl⟩⟩))
        · exact Or.inr (mem_iUnion.2 ⟨k, ⟨i, rfl⟩⟩)
      · rintro ((hz | hz) | hz)
        · rcases hz with rfl
          exact ⟨Sum.inl (), rfl⟩
        · obtain ⟨k, i, rfl⟩ := mem_iUnion.1 hz
          exact ⟨Sum.inr (Sum.inl (k, i)), rfl⟩
        · obtain ⟨k, i, rfl⟩ := mem_iUnion.1 hz
          exact ⟨Sum.inr (Sum.inr (k, i)), rfl⟩
    rw [hr, closure_union, closure_union, isClosed_singleton.closure_eq,
      closure_iUnion_of_finite, closure_iUnion_of_finite]
    have hTc : (⋃ k : Fin spec.2.2.length, closure (range (T k ω))) =
        ⋃ k : Fin spec.2.2.length, ({(spec.1 : ℂ)} ∪ pieceTips κ b jumps spec (fun j => E' j ω) k) :=
      iUnion_congr fun k => hT ω hωM k
    have hAc : (⋃ k : Fin spec.2.2.length, closure (range (A k ω))) =
        ⋃ k : Fin spec.2.2.length, ({(spec.1 : ℂ)} ∪
          ((↑) : ℝ → ℂ) '' arcAt κ b jumps spec (fun j => E' j ω) k) :=
      iUnion_congr fun k => hA ω k
    rw [hTc, hAc]
    ext z
    simp only [mem_union, mem_singleton_iff, mem_iUnion, Finset.mem_range, exists_prop,
      Fin.exists_iff]
    constructor
    · rintro ((hz | ⟨k, hk, hp⟩) | ⟨k, hk, ha⟩)
      · exact Or.inl (Or.inl hz)
      · exact Or.inl (Or.inr ⟨k, hk, Or.inr hp⟩)
      · exact Or.inr ⟨k, hk, Or.inr ha⟩
    · rintro ((hz | ⟨k, hk, hz | hp⟩) | ⟨k, hk, hz | ha⟩)
      · exact Or.inl (Or.inl hz)
      · exact Or.inl (Or.inl hz)
      · exact Or.inl (Or.inr ⟨k, hk, hp⟩)
      · exact Or.inl (Or.inl hz)
      · exact Or.inr ⟨k, hk, ha⟩

/-- Both actual sides of an R51 history have versions with measurable graphs.
The side definition's real-point exclusion is retained. -/
theorem exists_measurable_physSet_side_versions {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hR : StagedPiecesRegular κ b jumps P spec E) :
    (∃ S : Ω → Set ℂ, MeasurableSet {p : Ω × ℂ | p.2 ∈ S p.1} ∧
      ∀ᵐ ω ∂P, rightSideOf (ExplState.physSet κ b jumps spec (fun j => E j ω)) = S ω) ∧
    (∃ S : Ω → Set ℂ, MeasurableSet {p : Ω × ℂ | p.2 ∈ S p.1} ∧
      ∀ᵐ ω ∂P, leftSideOf (ExplState.physSet κ b jumps spec (fun j => E j ω)) = S ω) := by
  obtain ⟨F, hFm, hF⟩ := exists_measurable_physSet_dense_code hb spec hEm hR
  exact ⟨exists_measurable_side_version_of_dense_code hFm hF isOpen_Ioi,
    exists_measurable_side_version_of_dense_code hFm hF isOpen_Iio⟩

end InteractingSLE.Theorem14.SB.Side
