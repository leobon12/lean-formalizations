/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRealGerm
import InteractingSLE.WangWu.ReverseContactMartFilt2Markov

/-!
# The marked pocket-pair law from a retained inner restart law

PROVE-POCKET-SIDEIN. The conditional restart producer is stated on its full
retained record. Measurability of both filled sets then gives the exact
two-set marked law consumed by the incoming germ comparison. The outer
filled-set germ may also be retained using the smaller-germ theorem.
The restart law itself remains a named mathematical input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField WangWu PocketUnionPt

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens} {C U F : Ω → Set ℂ}

/-- A retained inner restart law containing both set records supplies the
precise pair-marked law. The premise is an ordinary history-marked local-set
law on the full record, suitable for a conditional restart construction. -/
theorem pair_marked_law_of_retained_inner
    (hNested : ∀ ω, U ω ⊆ C ω)
    (hCRecord : Measurable[ℋ, hittingSigma] (fun ω => extHullSet (C ω) (F ω)))
    (hURecord : Measurable[ℋ, hittingSigma] (fun ω => extHullSet (U ω) (F ω)))
    (hRestartRetained : IsHistoryAvoidanceLocal ℋ (fun ω => extHullSet (U ω) (F ω)) h P) :
    IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (fun ω => extHullSet (C ω) (F ω)) hittingSigma ⊔
        MeasurableSpace.comap (fun ω => extHullSet (U ω) (F ω)) hittingSigma)
      (fun ω => extHullSet (C ω) (F ω) ∪ extHullSet (U ω) (F ω)) h P := by
  have hsub : ∀ ω, extHullSet (C ω) (F ω) ⊆ extHullSet (U ω) (F ω) := by
    intro ω z hz
    refine ⟨hz.1, hz.2.elim (fun hnot => Or.inl fun hzU => hnot (hNested ω hzU)) Or.inr⟩
  have heq : (fun ω => extHullSet (C ω) (F ω) ∪ extHullSet (U ω) (F ω)) =
      (fun ω => extHullSet (U ω) (F ω)) := funext fun ω => union_eq_right.2 (hsub ω)
  rw [heq]
  exact IsHistoryAvoidanceLocal.mono_marks hRestartRetained
    (sup_le hCRecord.comap_le hURecord.comap_le)

/-- The retained inner law also permits the germ of the smaller outer
filled set. No extra union law conditioned on this germ is assumed. -/
theorem pair_marked_law_with_outer_germ_of_retained_inner [IsProbabilityMeasure P]
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hℋ : ℋ ≤ mΩ)
    (hNested : ∀ ω, U ω ⊆ C ω)
    (hCRecord : Measurable[ℋ, hittingSigma] (fun ω => extHullSet (C ω) (F ω)))
    (hURecord : Measurable[ℋ, hittingSigma] (fun ω => extHullSet (U ω) (F ω)))
    (hRestartRetained : IsHistoryAvoidanceLocal ℋ (fun ω => extHullSet (U ω) (F ω)) h P) :
    IsHistoryAvoidanceLocal
      ((MeasurableSpace.comap (fun ω => extHullSet (C ω) (F ω)) hittingSigma ⊔
        MeasurableSpace.comap (fun ω => extHullSet (U ω) (F ω)) hittingSigma) ⊔
        germSigma (fun ω => extHullSet (C ω) (F ω)) h)
      (fun ω => extHullSet (C ω) (F ω) ∪ extHullSet (U ω) (F ω)) h P := by
  have hsub : ∀ ω, extHullSet (C ω) (F ω) ⊆ extHullSet (U ω) (F ω) := by
    intro ω z hz
    exact ⟨hz.1, hz.2.elim (fun hnot => Or.inl fun hzU => hnot (hNested ω hzU)) Or.inr⟩
  have hAug := Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh hℋ
    (hURecord.mono hℋ le_rfl) hRestartRetained hCRecord
    (fun ω z hz => hsub ω hz.1)
  have heq : (fun ω => extHullSet (C ω) (F ω) ∪ extHullSet (U ω) (F ω)) =
      (fun ω => extHullSet (U ω) (F ω)) := funext fun ω => union_eq_right.2 (hsub ω)
  rw [heq]
  exact IsHistoryAvoidanceLocal.mono_marks hAug
    (sup_le_sup_right (sup_le hCRecord.comap_le hURecord.comap_le) _)

end InteractingSLE.Sec7.PocketStopSide
