/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfPhysLimit

/-!
# Raw image events on strict upper dyadic physical lines

Packet PROVE-CFCHART2. The stopped-history transfer includes all raw generators,
including the announcing times. Compact-avoidance pieces therefore have versions
in the physical marks without any assertion at an inclusive capacity cutoff.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfPhys

open WangWu LawUnique GlueCond Cond44Ref CfRegQ Prop411Q
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq dyIdx dyF dyIdx_eq_iff)
open CrossCond.Word49 (dyqR dyqR_pos dyqR_coe dyqR_toNNReal divR_coe divR_le_dyqR div_le_dyq)

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}

/-- The strict dyadic index is determined by the capacities at its two endpoints
whenever the upper endpoint is pre-contact. -/
theorem dyIdx_qTheta_iff (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) {p : Ω × HistorySpace 0 0}
    {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p) (n k : ℕ)
    (hpre : (dyq n k : ℝ) ∈ qgPre W VL VR ζ s E p) :
    dyIdx n (qTheta W VL VR ζ s E r p) = k ↔
      (r : ℝ) < capClock (qgCurve W s E p) (dyq n k) ∧
        ¬ ((((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ∈ qgPre W VL VR ζ s E p ∧
          (r : ℝ) < capClock (qgCurve W s E p) (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ)) := by
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  obtain ⟨hθP, hθc⟩ := qTheta_spec hEg hr
  have key : ∀ u : ℝ, u ∈ qgPre W VL VR ζ s E p →
      ((qTheta W VL VR ζ s E r p : ℝ) < u ↔
        (r : ℝ) < capClock (qgCurve W s E p) u) := by
    intro u hu
    constructor
    · intro hlt
      rw [← hθc]
      exact hγ.strictMonoOn_capClock hθP hu hlt
    · intro hlt
      by_contra hle
      have h := hγ.strictMonoOn_capClock.monotoneOn hu hθP (not_lt.1 hle)
      rw [hθc] at h
      exact (not_lt_of_ge h) hlt
  have hlo := hγ.icc _ hpre ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (div_le_dyq n k)⟩
  rw [dyIdx_eq_iff]
  constructor
  · rintro ⟨hlo', hhi⟩
    refine ⟨(key _ hpre).1 (NNReal.coe_lt_coe.2 hhi), fun h => ?_⟩
    exact not_lt_of_ge (NNReal.coe_le_coe.2 hlo') ((key _ hlo).2 h.2)
  · rintro ⟨hhi, hlo'⟩
    refine ⟨?_, NNReal.coe_lt_coe.1 ((key _ hpre).2 hhi)⟩
    by_contra h
    exact hlo' ⟨hlo, (key _ hlo).1 (NNReal.coe_lt_coe.2 (not_le.1 h))⟩

section Marks

variable [mΩ : MeasurableSpace Ω] {μ : Measure (Ω × HistorySpace 0 0)} {mL mR : ℕ}
  {xL : Fin mL → ℝ} {xR : Fin mR → ℝ}

/-- Every safe strict dyadic piece of a raw event has a version in the two
physical stopped histories. All announcing-time generators are covered by the
landed `marks47_inter`. -/
theorem imageLineSafe_piece_marks (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hgood : ∀ᵐ p ∂μ, p ∈ E) {r : ℝ≥0} {D : Set (Ω × HistorySpace 0 0)}
    (hD : MeasurableSet[qRaw xL xR W VL VR ζ s E r] D)
    (hlive : ∀ᵐ p ∂μ, p ∈ D → (r : WithTop ℝ≥0) < qT W VL VR ζ s E p)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (n k : ℕ) :
    ∃ B, MeasurableSet[CrossCond.cfGlueMarks W VL VR ζ s (dyq n k)] B ∧ B =ᵐ[μ]
      D ∩ {p | dyIdx n (qTheta W VL VR ζ s E r p) = k} ∩ imageLineSafe W VL VR ζ s E C (dyq n k) := by
  have ht := dyqR_pos n k
  obtain ⟨B1, hB1, he1⟩ := marks47_inter xL xR ht hEg hgood r
    (by exact_mod_cast ht.le) le_rfl hD
  obtain ⟨B2, hB2, he2⟩ := marks47_inter xL xR ht hEg hgood r
    (t' := (k : ℚ) / 2 ^ n) (by push_cast; positivity) (divR_le_dyqR n k) MeasurableSet.univ
  obtain ⟨B3, hB3, he3⟩ := imageLineSafe_marks hEg hgood ht hC hCH
  rw [dyqR_toNNReal] at hB1 hB2 hB3 he3
  rw [dyqR_coe] at he1
  rw [divR_coe] at he2
  refine ⟨B1 ∩ B2ᶜ ∩ B3, (hB1.inter hB2.compl).inter hB3, ?_⟩
  refine ((he1.inter he2.compl).inter he3).trans ?_
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hlive] with p hp
  simp only [mem_inter_iff, mem_compl_iff, mem_univ, true_and, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨hDp, hhi⟩, hlo⟩, hs⟩
    exact ⟨⟨hDp, (dyIdx_qTheta_iff hEg (hp hDp) n k hs.1).2 ⟨hhi.2, hlo⟩⟩, hs⟩
  · rintro ⟨⟨hDp, hidx⟩, hs⟩
    obtain ⟨hhi, hlo⟩ := (dyIdx_qTheta_iff hEg (hp hDp) n k hs.1).1 hidx
    exact ⟨⟨⟨hDp, hs.1, hhi⟩, hlo⟩, hs⟩

end Marks

end InteractingSLE.Sec5.CfPhys
