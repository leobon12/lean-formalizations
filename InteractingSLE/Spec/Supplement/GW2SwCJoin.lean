/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SwBCat
import InteractingSLE.Spec.Supplement.GW2SwcCarrier
import InteractingSLE.Spec.Sec7.ContinuityProbBase
import InteractingSLE.Spec.Sec7.ContinuityProbCollision

/-!
# The joined driver of a switched schedule has a generating trace

Packet PROVE-GW2-SWITCH (round 3). Iterating the boundary-permitting Loewner concatenation
(`LoewnerConcat.isGeneratingTrace_catPath_bdry`) over the pieces of a schedule:

* `HasPieceExt Δ D j`: the stopped driver of piece `j` (`stopDrv (Δ j) (D j)` on `[0, stopTime]`) agrees
  with a continuous driver from `0` that has a generating trace on `[0, ∞)` (no `ℍ`-avoidance);
* **`exists_trace_joinDrv`**: then the joined driver `Swc.joinDrv Δ D (n+1)` agrees, up to the total
  time `joinTime Δ D (n+1)`, with a continuous driver with a generating trace on `[0, ∞)`;
* **`exists_isGeneratingTrace_joinDrv`**: the joined driver itself has a generating trace on
  `[0, joinTime Δ D (n+1)]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.SwC

open GW2Schedule Exist Staged StagedLaw Swc Sec7.StripSideHeightProb

/-- **A trace-generating extension of piece `j`**: a continuous driver from `0`, generating a trace on
`[0, ∞)`, equal to the piece's stopped driver up to its stop. -/
def HasPieceExt (Δ : ℕ → ℝ≥0∞) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) : Prop :=
  ∃ (w : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), Continuous w ∧ w 0 = 0 ∧ IsGeneratingTrace w ⊤ α ∧
    ∀ u : ℝ≥0, (u : ℝ) ≤ stopTime (Δ j) (D j) → w u = stopDrv (Δ j) (D j) u

variable {Δ : ℕ → ℝ≥0∞} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The joined driver agrees with a trace-generating driver up to the total time.** -/
theorem exists_trace_joinDrv : ∀ n : ℕ, (∀ j < n + 1, HasPieceExt Δ D j) →
    ∃ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W ∧ W 0 = 0 ∧ IsGeneratingTrace W ⊤ γ ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ joinTime Δ D (n + 1) → W t = joinDrv Δ D (n + 1) t
  | 0, h => by
    obtain ⟨w, α, hw, hw0, hα, hagree⟩ := h 0 Nat.zero_lt_one
    have hS0 : stopDrv (Δ 0) (D 0) 0 = 0 := by
      have h0 := hagree 0 (by simpa using stopTime_nonneg (Δ 0) (D 0))
      rw [hw0, NNReal.coe_zero] at h0
      exact h0.symm
    refine ⟨w, α, hw, hw0, hα, fun t ht => ?_⟩
    have ht' : (t : ℝ) ≤ stopTime (Δ 0) (D 0) := by
      have e : joinTime Δ D 1 = 0 + stopTime (Δ 0) (D 0) := rfl
      rw [e, zero_add] at ht
      exact ht
    rw [hagree t ht']
    change _ = (if (t : ℝ) ≤ 0 then (0 : ℝ) else 0 + stopDrv (Δ 0) (D 0) ((t : ℝ) - 0))
    by_cases ht0 : (t : ℝ) ≤ 0
    · rw [ite_eq_left ht0, le_antisymm ht0 t.2, hS0]
    · rw [ite_eq_right ht0, zero_add, sub_zero]
  | n + 1, h => by
    obtain ⟨W, γ, hW, hW0, hγ, hag⟩ := exists_trace_joinDrv n (fun j hj => h j (by omega))
    obtain ⟨w, α, hw, hw0, hα, hagree⟩ := h (n + 1) (by omega)
    set a : ℝ≥0 := (joinTime Δ D (n + 1)).toNNReal with hadef
    have hTa : (a : ℝ) = joinTime Δ D (n + 1) := Real.coe_toNNReal _ (joinTime_nonneg Δ D _)
    refine ⟨catPath W a w, LoewnerConcat.joinedTrace W γ a α, continuous_catPath hW hw hw0,
      catPath_zero hW0,
      LoewnerConcat.isGeneratingTrace_catPath_bdry hW hW0 hw hw0 (hγ.mono_horizon le_top) hα,
      fun t ht => ?_⟩
    change _ = (if (t : ℝ) ≤ joinTime Δ D (n + 1) then joinDrv Δ D (n + 1) t else
      joinDrv Δ D (n + 1) (joinTime Δ D (n + 1)) +
        stopDrv (Δ (n + 1)) (D (n + 1)) ((t : ℝ) - joinTime Δ D (n + 1)))
    by_cases hta : t ≤ a
    · have htR : (t : ℝ) ≤ joinTime Δ D (n + 1) := by
        rw [← hTa]; exact_mod_cast hta
      rw [catPath_of_le hta, ite_eq_left htR]
      exact hag t htR
    · have htR : ¬ (t : ℝ) ≤ joinTime Δ D (n + 1) := by
        rw [← hTa]; exact_mod_cast hta
      rw [ite_eq_right htR]
      have hcat : catPath W a w t = W a + w (t - a) := by
        simp only [catPath, hta, ↓reduceIte]
      have hsub : ((t - a : ℝ≥0) : ℝ) = (t : ℝ) - joinTime Δ D (n + 1) := by
        rw [NNReal.coe_sub (le_of_not_ge hta), hTa]
      have hle : ((t - a : ℝ≥0) : ℝ) ≤ stopTime (Δ (n + 1)) (D (n + 1)) := by
        rw [hsub]
        rw [joinTime_succ] at ht
        linarith
      rw [hcat, hag a hTa.le, hTa, hagree (t - a) hle, hsub]

/-- **The joined driver of a schedule generates a trace up to its total time.** -/
theorem exists_isGeneratingTrace_joinDrv (n : ℕ) (h : ∀ j < n + 1, HasPieceExt Δ D j) :
    ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t : ℝ≥0 => joinDrv Δ D (n + 1) t)
      ((joinTime Δ D (n + 1)).toNNReal : ℝ≥0∞) γ := by
  obtain ⟨W, γ, -, -, hγ, hag⟩ := exists_trace_joinDrv n h
  refine ⟨γ, IsGeneratingTrace.of_eqOn_lt hγ fun t ht => ?_⟩
  have hlt := NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 ht)
  rw [Real.coe_toNNReal _ (joinTime_nonneg Δ D _)] at hlt
  exact (hag t hlt.le).symm

end InteractingSLE.Theorem14.GW2TipSystem.SwC
