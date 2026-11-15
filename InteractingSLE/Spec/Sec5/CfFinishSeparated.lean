/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishClassify

/-!
# Deterministic erasure and almost sure classification

Packet PROVE-CFCHART2. The retained index lists depend only on the deterministic
weights. Every sample with strictly separated marks is classified after that same erasure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfFinish

open Restart

/-- Choose one ordered erasure, independent of the sample, then classify every
strictly separated realization of the random force positions. -/
theorem exists_erasure_flowType_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {vL : Ω → Fin (nL + 1) → ℝ} {vR : Ω → Fin (nR + 1) → ℝ}
    (hsep : ∀ᵐ ω ∂P, StrictAnti (vL ω) ∧ StrictMono (vR ω) ∧ vL ω 0 = 0 ∧ vR ω 0 = 0) :
    ∃ (kL kR : ℕ) (eL : Fin (kL + 1) ↪o Fin (nL + 1))
      (eR : Fin (kR + 1) ↪o Fin (nR + 1)),
      eL 0 = 0 ∧ eR 0 = 0 ∧
      (∀ j, j ∉ range eL → ρL j = 0) ∧ (∀ j, j ∉ range eR → ρR j = 0) ∧
      ∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType κ 0 c
        (vL ω ∘ eL) (vR ω ∘ eR) (ρL ∘ eL) (ρR ∘ eR) := by
  obtain ⟨kL, eL, heL0, hρL, heL⟩ := CfResume.exists_ordered_zero_erasure ρL
  obtain ⟨kR, eR, heR0, hρR, heR⟩ := CfResume.exists_ordered_zero_erasure ρR
  refine ⟨kL, kR, eL, eR, heL0, heR0, heL, heR, ?_⟩
  filter_upwards [hsep] with ω hω
  apply exists_isFlowType_force hκ
    (fun _ _ hij => hω.1 (eL.strictMono hij))
    (fun _ _ hij => hω.2.1 (eR.strictMono hij))
  · change vL ω (eL 0) = 0
    rw [heL0]
    exact hω.2.2.1
  · change vR ω (eR 0) = 0
    rw [heR0]
    exact hω.2.2.2
  · intro i
    exact hρL i.succ (Fin.succ_ne_zero i)
  · intro j
    exact hρR j.succ (Fin.succ_ne_zero j)

end InteractingSLE.Sec5.CfFinish
