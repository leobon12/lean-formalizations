/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedPhysical
import InteractingSLE.Spec.Supplement.WalkSideWord

/-!
# S3: the exposed second-word value at an interior landing

For a piece launched from the original real boundary, an interior physical
landing cannot come from an alive old real point. Thus an unmarked negative
coordinate has precisely the new left height, and an unmarked positive
coordinate has precisely the new right height. This supplies the exposed
value used with the second-path geometry, without an assumption on the
numerical values of the original boundary data.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart GW1W GW1Conn

/-- A negative unmarked stopped coordinate with an interior physical
landing has the new left height if old real points cannot land inside H. -/
theorem stopWord_fn_neg_of_no_old_interior {κ : ℝ} {word : BoundaryWord}
    {chart : Chart} (hc : HasBdryLimits chart.2.1)
    (hOld : ∀ x : ℝ, LuM.bdVal chart (x : ℂ) ∉ H) {θ : ℝ} {r : RecData}
    (hB : HasBdryLimits (QuantumZipper.fwdMapInv (rdrv r) (rtime r)))
    {y : ℝ} (hy0 : y < 0) (hy : y ∉ (stopWord κ (word, θ, r)).jumps)
    (hyH : LuM.bdVal (chart.loewner (rdrv r) (rtime r)) (y : ℂ) ∈ H) :
    (stopWord κ (word, θ, r)).fn y = -sleLambda κ - θ * chiC κ := by
  by_cases hfirst : ∀ i < flowLineNL word.fn word.jumps 0,
      markPosL (rdrv r) (rtime r) ((padFL 0 0 word.fn word.jumps).1.1 i) < y
  · exact stopWord_fn_first word θ r hy0 hy hfirst
  · push Not at hfirst
    obtain ⟨i, hi, hiy⟩ := hfirst
    have hlt : y < markPosL (rdrv r) (rtime r) ((padFL 0 0 word.fn word.jumps).1.1 i) :=
      lt_of_le_of_ne hiy fun he => hy (he ▸ markPosL_mem_jumps_stopWord (κ := κ) word θ r hi)
    obtain ⟨q, hq, hqA, hqy⟩ := exists_rat_lt_of_lt_markPosL
      (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hlt
    have hq0 : (q : ℝ) < 0 := hq.trans_le (padFL_fst_fst_nonpos word hi)
    obtain ⟨x, -, hxA, hxy⟩ := exists_alive_eq_of_lt_re
      (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hq0 hqA hqy
    have he := bdVal_loewner_fwdMap hc (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hB hxA
    rw [hxy] at he
    exact False.elim (hOld x (he ▸ hyH))

/-- The corresponding positive coordinate has the new right height. -/
theorem stopWord_fn_pos_of_no_old_interior {κ : ℝ} {word : BoundaryWord}
    {chart : Chart} (hc : HasBdryLimits chart.2.1)
    (hOld : ∀ x : ℝ, LuM.bdVal chart (x : ℂ) ∉ H) {θ : ℝ} {r : RecData}
    (hB : HasBdryLimits (QuantumZipper.fwdMapInv (rdrv r) (rtime r)))
    {y : ℝ} (hy0 : 0 < y)
    (hyH : LuM.bdVal (chart.loewner (rdrv r) (rtime r)) (y : ℂ) ∈ H) :
    (stopWord κ (word, θ, r)).fn y = sleLambda κ - θ * chiC κ := by
  rcases Lh.stopWord_fn_pos_cases word θ r hy0 with he | hmark
  · exact he
  · obtain ⟨x, -, hxA, hxy⟩ := Lh.exists_alive_eq_of_markPos_lt
      (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hmark
    have he := bdVal_loewner_fwdMap hc (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hB hxA
    rw [hxy] at he
    exact False.elim (hOld x (he ▸ hyH))

/-- For a piece launched from any original real seed, the exposed stopped
word has the prescribed left or right height at every unmarked interior
landing, with no original-boundary-value alternative. -/
theorem stopWord_exposed_value_from_real_seed {κ : ℝ} {word : BoundaryWord}
    (x₀ : ℝ) {θ : ℝ} {r : RecData}
    (hB : HasBdryLimits (QuantumZipper.fwdMapInv (rdrv r) (rtime r)))
    {y : ℝ} (hy0 : y ≠ 0) (hy : y ∉ (stopWord κ (word, θ, r)).jumps)
    (hyH : LuM.bdVal ((Chart.id.recenter x₀).loewner (rdrv r) (rtime r)) (y : ℂ) ∈ H) :
    (stopWord κ (word, θ, r)).fn y =
      if y < 0 then -sleLambda κ - θ * chiC κ else sleLambda κ - θ * chiC κ := by
  have hc : HasBdryLimits (Chart.id.recenter x₀).2.1 := fun p _ =>
    ⟨p + x₀, ((continuous_id.add continuous_const).tendsto p).mono_left nhdsWithin_le_nhds⟩
  have hOld : ∀ x : ℝ, LuM.bdVal (Chart.id.recenter x₀) (x : ℂ) ∉ H := by
    intro x
    rw [bdVal_init_real]
    simp only [QuantumZipper.H, mem_ofPred_eq, Complex.ofReal_im, lt_self_iff_false, not_false_eq_true]
  rcases hy0.lt_or_gt with hneg | hpos
  · rw [ite_eq_left hneg]
    exact stopWord_fn_neg_of_no_old_interior hc hOld hB hneg hy hyH
  · rw [ite_eq_right (not_lt.2 hpos.le)]
    exact stopWord_fn_pos_of_no_old_interior hc hOld hB hpos hyH

end InteractingSLE.Theorem14.SB.S3
