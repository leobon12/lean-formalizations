/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterGlue

/-!
# Prop 5.9's root stage: the deterministic facts of the history start

Packet PROVE-STAGED-REP2. For a good counterflow history (`goodSet49 s`: good hitting history with strict junction
gaps) and the strictly ordered (4.4) flow word, the root start `histStart` read in the counterflow chart is an ordered
force word with strictly ordered marks and is not a threshold configuration of the junction word
(`histStart_ordered`, `histStart_strict`, `not_threshold_histStart`); the same holds after a positive dilation
(`*_dil`). These are the start conditions of clause 1 of the killed stage law. (The proofs are PROVE-GLUECOND's
`not_threshold_img` and PROVE-STAGED-REP's `ae_strict_imgStart` read on the history alone.)

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open GlueCond CrossCond.Word49 WangWu MartChar.RealFlow Prop59Stage StagedRep LawUnique Prop49Exit

section Start

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {s : ℝ≥0} {y : HistorySpace 0 0}

theorem histStart_ordered (hF : IsOrderedForceWord xL xR) (hy : y ∈ goodSet49 s) :
    IsOrderedForceWord (histStart xL xR s y).2.1 (histStart xL xR s y).2.2 := by
  obtain ⟨-, hjL, hjR⟩ := hy
  have hw := continuous_cfDrv0 s y
  refine ⟨antitone_snoc (fun i i' hii => psiL_mono hw s.coe_nonneg hjL (hF.2.1 i) (hF.1 hii))
      (fun i => junL_le_psiL hw s.coe_nonneg hjL (hF.2.1 i)),
    snoc_le (fun i => psiL_nonpos hw s.coe_nonneg hjL (hF.2.1 i))
      ((junL_le_psiL hw s.coe_nonneg hjL le_rfl).trans (psiL_nonpos hw s.coe_nonneg hjL le_rfl)),
    monotone_snoc (fun j j' hjj => psiR_mono hw s.coe_nonneg hjR (hF.2.2.2 j) (hF.2.2.1 hjj))
      (fun j => psiR_le_junR hw s.coe_nonneg hjR (hF.2.2.2 j)),
    le_snoc (fun j => psiR_nonneg hw s.coe_nonneg hjR (hF.2.2.2 j))
      ((psiR_nonneg hw s.coe_nonneg hjR le_rfl).trans (psiR_le_junR hw s.coe_nonneg hjR le_rfl))⟩

theorem histStart_strict (hF : IsOrderedForceWord xL xR) (hxLs : StrictAnti xL) (hxRs : StrictMono xR)
    (hy : y ∈ goodSet49 s) :
    StrictAnti (histStart xL xR s y).2.1 ∧ StrictMono (histStart xL xR s y).2.2 := by
  obtain ⟨hy', hjL, hjR⟩ := hy
  have hw := continuous_cfDrv0 s y
  have hal : ∀ a, 0 < a → Alive (cfDrv0 s y) a s := fun a ha => (alive_cfDrv0_of_mem_goodHitSet hy' s ha).1
  have hal' : ∀ a, 0 < a → Alive (fun r => -cfDrv0 s y r) a s := fun a ha =>
    (alive_cfDrv0_of_mem_goodHitSet hy' s ha).2
  exact ⟨strictAnti_snoc (fun i i' hii => psiL_lt_psiL hw s.coe_nonneg hal hjL (hxLs hii) (hF.2.1 i))
      (fun i => junL_lt_psiL hw s.coe_nonneg hal hjL (hF.2.1 i)),
    strictMono_snoc (fun j j' hjj => psiR_lt_psiR hw s.coe_nonneg hal' hjR (hxRs hjj) (hF.2.2.2 j))
      (fun j => psiR_lt_junR hw s.coe_nonneg hal' hjR (hF.2.2.2 j))⟩

theorem not_threshold_histStart (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hy : y ∈ goodSet49 s) :
    ¬ ForceWord.ThresholdCondition (jwL cL6 κ ρL) (jwR cR6 κ ρR) 0 (histStart xL xR s y).2.1
      (histStart xL xR s y).2.2 := by
  obtain ⟨-, hjL, hjR⟩ := hy
  have hw := continuous_cfDrv0 s y
  show ¬ ForceWord.ThresholdCondition (jwL cL6 κ ρL) (jwR cR6 κ ρR) 0
    (Fin.snoc (fun i => psiL (cfDrv0 s y) s (xL i)) (junL (cfDrv0 s y) s))
    (Fin.snoc (fun j => psiR (cfDrv0 s y) s (xR j)) (junR (cfDrv0 s y) s))
  simp only [ForceWord.ThresholdCondition, jwL, jwR, not_or, not_le]
  have hjL0 : junL (cfDrv0 s y) s ≠ 0 := div_ne_zero (by norm_num) hjL.ne'
  have hjR0 : junR (cfDrv0 s y) s ≠ 0 := div_ne_zero (by norm_num) hjR.ne
  rw [sum_filter_snoc_eq_zero _ _ _ _ hjL0, sum_filter_snoc_eq_zero _ _ _ _ hjR0]
  have eL : (Finset.univ.filter fun i => psiL (cfDrv0 s y) s (xL i) = 0) =
      Finset.univ.filter fun i => xL i = 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => by_contra fun h0 => psiL_ne_zero hw s.coe_nonneg hjL (hF.2.1 i) h0 h, fun h => ?_⟩
    simp [psiL, h]
  have eR : (Finset.univ.filter fun j => psiR (cfDrv0 s y) s (xR j) = 0) =
      Finset.univ.filter fun j => xR j = 0 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => by_contra fun h0 => psiR_ne_zero hw s.coe_nonneg hjR (hF.2.2.2 j) h0 h, fun h => ?_⟩
    simp [psiR, h]
  rw [eL, eR]
  refine ⟨neg_two_lt_sum_filter_zero (c := κ / 2 - 2) (by linarith) (fun i i' hii h => ?_) h44.1,
    neg_two_lt_sum_filter_zero (c := 0) (by norm_num) (fun j j' hjj h => ?_) h44.2⟩
  · exact le_antisymm (hF.2.1 i') (h ▸ hF.1 hii)
  · exact le_antisymm (h ▸ hF.2.2.1 hjj) (hF.2.2.2 j')

/-! ### After a positive dilation -/

variable {lam : ℝ}

theorem histStart_ordered_dil (hlam : 0 < lam) (hF : IsOrderedForceWord xL xR) (hy : y ∈ goodSet49 s) :
    IsOrderedForceWord (fun i => lam * (histStart xL xR s y).2.1 i) (fun j => lam * (histStart xL xR s y).2.2 j) := by
  obtain ⟨h1, h2, h3, h4⟩ := histStart_ordered hF hy
  exact ⟨fun i i' hii => mul_le_mul_of_nonneg_left (h1 hii) hlam.le,
    fun i => mul_nonpos_of_nonneg_of_nonpos hlam.le (h2 i),
    fun j j' hjj => mul_le_mul_of_nonneg_left (h3 hjj) hlam.le, fun j => mul_nonneg hlam.le (h4 j)⟩

theorem histStart_strict_dil (hlam : 0 < lam) (hF : IsOrderedForceWord xL xR) (hxLs : StrictAnti xL)
    (hxRs : StrictMono xR) (hy : y ∈ goodSet49 s) :
    StrictAnti (fun i => lam * (histStart xL xR s y).2.1 i) ∧
      StrictMono (fun j => lam * (histStart xL xR s y).2.2 j) := by
  obtain ⟨h1, h2⟩ := histStart_strict hF hxLs hxRs hy
  exact ⟨fun i i' hii => mul_lt_mul_of_pos_left (h1 hii) hlam, fun j j' hjj => mul_lt_mul_of_pos_left (h2 hjj) hlam⟩

theorem not_threshold_histStart_dil (hlam : 0 < lam) (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hy : y ∈ goodSet49 s) :
    ¬ ForceWord.ThresholdCondition (jwL cL6 κ ρL) (jwR cR6 κ ρR) 0
      (fun i => lam * (histStart xL xR s y).2.1 i) (fun j => lam * (histStart xL xR s y).2.2 j) := by
  have h := not_threshold_histStart hκ hF h44 hy (ρL := ρL) (ρR := ρR)
  rwa [← ZhanGT4.UpMark.thresholdCondition_smul _ _ hlam.ne', mul_zero] at h

end Start

end InteractingSLE.Sec5.CrossCond.StagedRepLater
