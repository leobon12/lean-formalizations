/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishConditional

/-!
# Seed marks and reduced words in record coordinates

Packet PROVE-CFCHART2. The version definitions of the record marks preserve their
zero seeds at every record, including off the good event. Thus only strict side order,
not an additional seed identity, is needed for the remaining geometric input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfFinish

open CfConv Restart Exist.StagedLaw CrossCond.Word49

/-- The regularized left record marks preserve their zero seed everywhere. -/
theorem recordXL_zero {n : ℕ} {x : Fin (n + 1) → ℝ} (hx : x 0 = 0)
    (s : ℝ≥0) (r : RecData) : recordXL s x r 0 = 0 := by
  classical
  by_cases hg : RecordGaps s r
  · rw [recordXL, ite_eq_left hg]
    change (Fin.snoc (α := fun _ => ℝ) (fun i => psiL (rdrv r) s (x i)) (junL (rdrv r) s))
      ((0 : Fin (n + 1)).castSucc) = 0
    rw [Fin.snoc_castSucc, hx]
    exact ite_eq_left rfl
  · simp only [recordXL, ite_eq_right hg]

/-- The regularized right record marks preserve their zero seed everywhere. -/
theorem recordXR_zero {n : ℕ} {x : Fin (n + 1) → ℝ} (hx : x 0 = 0)
    (s : ℝ≥0) (r : RecData) : recordXR s x r 0 = 0 := by
  classical
  by_cases hg : RecordGaps s r
  · rw [recordXR, ite_eq_left hg]
    change (Fin.snoc (α := fun _ => ℝ) (fun i => psiR (rdrv r) s (x i)) (junR (rdrv r) s))
      ((0 : Fin (n + 1)).castSucc) = 0
    rw [Fin.snoc_castSucc, hx]
    exact ite_eq_left rfl
  · simp only [recordXR, ite_eq_right hg]

/-- For the actual record-coordinate definitions, strict side order is the only
remaining input to deterministic erasure and the almost sure flow-type classification. -/
theorem exists_erasure_record_flowType_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {x : Fin (nL + 1) → ℝ} {y : Fin (nR + 1) → ℝ} (hx : x 0 = 0) (hy : y 0 = 0)
    (ρL : Fin (nL + 1 + 1) → ℝ) (ρR : Fin (nR + 1 + 1) → ℝ)
    (s : ℝ≥0) (R : Ω → RecData)
    (hsep : ∀ᵐ ω ∂P, StrictAnti (recordXL s x (R ω)) ∧ StrictMono (recordXR s y (R ω))) :
    ∃ (kL kR : ℕ) (eL : Fin (kL + 1) ↪o Fin (nL + 1 + 1))
      (eR : Fin (kR + 1) ↪o Fin (nR + 1 + 1)),
      eL 0 = 0 ∧ eR 0 = 0 ∧
      (∀ j, j ∉ range eL → ρL j = 0) ∧ (∀ j, j ∉ range eR → ρR j = 0) ∧
      ∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType κ 0 c
        (recordXL s x (R ω) ∘ eL) (recordXR s y (R ω) ∘ eR) (ρL ∘ eL) (ρR ∘ eR) :=
  exists_erasure_flowType_ae hκ ρL ρR
    (hsep.mono fun ω hω => ⟨hω.1, hω.2, recordXL_zero hx s (R ω), recordXR_zero hy s (R ω)⟩)

end InteractingSLE.Sec5.CfFinish
