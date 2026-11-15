/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbFlow
import InteractingSLE.Spec.Supplement.SB2VoCol
import InteractingSLE.Spec.Supplement.CounterflowRange

/-!
# A swallowed point that is never visited has swallowed rational points to its right

Packet PROVE-GW2-RELDET (round 38, decision D73 route (ii)). The tip-exclusion event must be measurable in the stage
word and the driver code, so it is read at rational points `q` beyond the far junction `J` (`GW2Bh.aliveRead` reads
`Alive` at a fixed point). This file gives the deterministic link to the collision of `J` itself
(`FlowSwallowStatement`):

* **`exists_rat_not_alive_of_collide`**: for a continuous driver from `0` with a generating trace on `[0, ∞)`, if the
  Loewner image of `y > 0` meets the driver at `t₀` and the trace never visits `y`, then some rational `q > y` is not
  alive at `t₀`. Proof: at the collision the tip is real and at least `y`
  (`Restart.FlowStopIdentLL.real_tip_of_rightImg_eq`), it is not `y`, so a rational `q` lies strictly between; a real
  tip right of `q` leaves `q` no forward solution (`GW2Rd.not_alive_of_tip_eq_pos`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Rd

open MartChar.RealFlow

/-- **A swallowed point that is never visited has swallowed rational points to its right.** -/
theorem exists_rat_not_alive_of_collide {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {y : ℝ} (hy : 0 < y) (hvis : ∀ t, η t ≠ (y : ℂ)) {t₀ : ℝ≥0}
    (hcoll : rightImg (fun s : ℝ => w s.toNNReal) y t₀ ≤ w t₀) :
    ∃ q : ℚ, y < q ∧ ¬ Alive (fun s : ℝ => w s.toNNReal) q t₀ := by
  set U : ℝ → ℝ := fun s => w s.toNNReal with hUdef
  have hU : Continuous U := hw.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp [hUdef, hw0]
  have hUt : U t₀ = w t₀ := by simp [hUdef]
  -- the collision time is positive
  have ht0 : (0 : ℝ) < t₀ := by
    rcases eq_or_lt_of_le t₀.coe_nonneg with h | h
    · exfalso
      have h0 := rightImg_zero hU hU0 hy.le
      rw [← h, h0] at hcoll
      have : w t₀ = 0 := by
        have e : t₀ = 0 := by exact_mod_cast h.symm
        rw [e, hw0]
      linarith
    · exact h
  have hcoll' : rightImg U y t₀ = U t₀ :=
    le_antisymm (by rw [hUt]; exact hcoll) (le_rightImg hU y t₀.coe_nonneg)
  -- the trace at the collision is the tip of the hull
  have hLT : IsLoewnerTraceLT U t₀ (fun s : ℝ => η s.toNNReal) :=
    CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace (hη.mono_horizon le_top)
  have hc : ContinuousOn (fun s : ℝ => η s.toNNReal) (Icc 0 t₀) :=
    hη.2.1.comp continuous_real_toNNReal.continuousOn fun s _ =>
      show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ⊤ from le_top
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hLT hU hU0 ht0 hc
  have htip := TraceClose.extendFrom_zero_eq hLT hU hU0 ht0 hc
  have hηt : η (t₀ : ℝ).toNNReal = η t₀ := by rw [Real.toNNReal_coe]
  rw [hηt] at htip
  obtain ⟨him, hre⟩ := Restart.FlowStopIdentLL.real_tip_of_rightImg_eq hU hU0 t₀.coe_nonneg hB htip hcoll'
  have hreal : η t₀ = (((η t₀).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hlt : y < (η t₀).re := by
    refine lt_of_le_of_ne hre fun h => hvis t₀ ?_
    rw [hreal, ← h]
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have hlim : Tendsto (fwdMapInv U t₀) (𝓝[H] 0) (𝓝 (((η t₀).re : ℝ) : ℂ)) := by
    have h := TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT hLT hU hU0 ht0 hc
    simp only [hηt] at h
    rwa [hreal] at h
  refine ⟨q, hq1, fun hal => ?_⟩
  exact not_alive_of_tip_eq_pos hU hU0 t₀.coe_nonneg hlim (hy.trans hq1) hq2.le
    ⟨_, WangWu.isForwardSol_of_alive hU hal⟩

end InteractingSLE.Theorem14.GW2Rd
