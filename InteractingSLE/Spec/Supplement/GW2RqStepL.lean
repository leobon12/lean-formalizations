/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqStepR

/-!
# The left angle region of a stopped piece: heights and ranks (decision D33)

PROVE-GW2-ROOTX round 8, the mirror of `GW2RqStepR`. The negative labels of `c' = stopWord κ (c, θ, r)` are the
images `pLs i = markPosL (rdrv r) (rtime r) (xL i)` of the old left labels. A point `v < 0` off the jumps carries the
old height reached by the first `KL v` labels (`fnL_stop`, `fnL_stop_eq_old`); `KL v = 0` reads the piece's left side
`−λ − θχ`. If `markPosL` is strictly increasing on `[aL, 0]`:

* **`rkL_stop`**: `rkL c' v = (KL v − 1) + δL` when `KL v ≥ 1`;
* `rkL_stop_zero`: `rkL c' v = 0` right of the seed image.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rq

open Restart Exist.Staged Exist.StagedLaw
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

section Left

variable {κ : ℝ} (c : BoundaryWord) (θ : ℝ) (r : RecData)

/-- The images of the old left labels under the piece's left mark flow. -/
def pLs (i : Fin (flowLineNL c.fn c.jumps 0)) : ℝ := markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i)

/-- The number of old left labels whose images are right of `v`. -/
def KL (v : ℝ) : ℕ := (Finset.univ.filter fun i : Fin (flowLineNL c.fn c.jumps 0) => v < pLs c r i).card

/-- The left seed shift. -/
def δL (κ : ℝ) : ℕ :=
  if markPosL (rdrv r) (rtime r) 0 < 0 ∧ leftLim c.fn 0 ≠ -sleLambda κ - θ * chiC κ then 1 else 0

theorem zero_lt_flowLineNL : 0 < flowLineNL c.fn c.jumps 0 := by unfold flowLineNL; omega

theorem pLs_zero : pLs c r ⟨0, zero_lt_flowLineNL c⟩ = markPosL (rdrv r) (rtime r) 0 := rfl

theorem antitone_pLs : Antitone (pLs c r) := fun i _ h =>
  Sec7.StripSideHeightProb.markPosL_anti (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)
    (GW3Word.flowLineXL_nonpos c.fn c.jumps i) ((Sec7.StripDet.strictAnti_flowLineXL c.fn c.jumps).antitone h)

theorem lt_pLs_iff (v : ℝ) (i : Fin (flowLineNL c.fn c.jumps 0)) : v < pLs c r i ↔ (i : ℕ) < KL c r v := by
  have h := mem_iff_lt_card (S := Finset.univ.filter fun i : Fin (flowLineNL c.fn c.jumps 0) => v < pLs c r i)
    (fun j hj k hk => by
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ _, hj.2.trans_le (antitone_pLs c r hk)⟩) i
  unfold KL
  rw [Finset.mem_filter] at h
  simpa only [Finset.mem_univ, true_and] using h

theorem KL_le_card (v : ℝ) : KL c r v ≤ flowLineNL c.fn c.jumps 0 :=
  (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])

theorem pLs_mem_jumps (i : Fin (flowLineNL c.fn c.jumps 0)) : pLs c r i ∈ (stopWord κ (c, θ, r)).jumps := by
  have h := GW1W.markPosL_mem_jumps_stopWord (κ := κ) c θ r i.isLt
  rwa [show (padFL 0 0 c.fn c.jumps).1.1 i = flowLineXL c.fn c.jumps 0 i from padFL_fst_fst_fin _ _ i] at h

/-- Every negative jump of the stopped word is an image of an old left label. -/
theorem exists_pLs_eq {y : ℝ} (hy : y ∈ (stopWord κ (c, θ, r)).jumps) (hy0 : y < 0) :
    ∃ i : Fin (flowLineNL c.fn c.jumps 0), y = pLs c r i := by
  rcases Sec5.CrossCond.StagedFinal.mem_jumps_stopWord hy with ⟨i, hi⟩ | h0 | ⟨j, hj⟩
  · exact ⟨i, hi⟩
  · linarith
  · have := Sec7.StripSideHeightProb.markPos_nonneg (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)
      (GW3Word.flowLineXR_nonneg c.fn c.jumps j)
    linarith

/-- **The heights left of the tip of a stopped word**, read from the first `KL v` labels. -/
theorem fnL_stop {v : ℝ} (hv : v < 0) (hvJ : v ∉ (stopWord κ (c, θ, r)).jumps) :
    (stopWord κ (c, θ, r)).fn v = -sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter
      (fun i : Fin (flowLineNL c.fn c.jumps 0) => (i : ℕ) < KL c r v), flowLineRhoL κ c.fn c.jumps 0 θ i) -
        θ * chiC κ := by
  classical
  have h := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ)
    (Sec7.StripSideHeightProb.isMarkOrder_stopWord c r) hvJ hv.ne
  refine h.trans ?_
  rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hv]
  simp only [padFL_fst_fst_fin, padFL_snd_fst_fin]
  have e : Finset.univ.filter (fun i : Fin (flowLineNL c.fn c.jumps 0) =>
      v < markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i)) =
      Finset.univ.filter (fun i : Fin (flowLineNL c.fn c.jumps 0) => (i : ℕ) < KL c r v) :=
    Finset.filter_congr fun i _ => lt_pLs_iff c r v i
  rw [e]

/-- **The old heights left of the tip**, read from the labels right of `u`. -/
theorem fn_old_L (hκ : 0 < κ) {u : ℝ} (hu : u < 0) (huJ : u ∉ c.jumps) :
    c.fn u = -sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter
      (fun i : Fin (flowLineNL c.fn c.jumps 0) => u < flowLineXL c.fn c.jumps 0 i),
        flowLineRhoL κ c.fn c.jumps 0 θ i) - θ * chiC κ := by
  have h1 := Exist.forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 θ hu.ne
    (by simpa using huJ)
  rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hu, add_zero] at h1
  linarith

/-- The labels right of a point of the old interval after label `k` are the first `k + 1`. -/
theorem lt_xL_iff_of_mem {k : ℕ} (hk : k < flowLineNL c.fn c.jumps 0) {u : ℝ}
    (hu : u < flowLineXL c.fn c.jumps 0 ⟨k, hk⟩)
    (hu' : ∀ j : Fin (flowLineNL c.fn c.jumps 0), k < (j : ℕ) → flowLineXL c.fn c.jumps 0 j < u)
    (j : Fin (flowLineNL c.fn c.jumps 0)) : u < flowLineXL c.fn c.jumps 0 j ↔ (j : ℕ) < k + 1 := by
  constructor
  · intro h
    by_contra hj
    exact absurd h (not_lt.2 (hu' j (by omega)).le)
  · intro h
    exact hu.trans_le ((Sec7.StripDet.strictAnti_flowLineXL c.fn c.jumps).antitone
      (Fin.le_def.2 (show (j : ℕ) ≤ k by omega)))

/-- **A point of the stopped word with `KL v = k + 1` carries the old height after label `k`.** -/
theorem fnL_stop_eq_old (hκ : 0 < κ) {v : ℝ} (hv : v < 0) (hvJ : v ∉ (stopWord κ (c, θ, r)).jumps) {k : ℕ}
    (hK : KL c r v = k + 1) (hk : k < flowLineNL c.fn c.jumps 0) {u : ℝ} (hu0 : u < 0) (huJ : u ∉ c.jumps)
    (hu : u < flowLineXL c.fn c.jumps 0 ⟨k, hk⟩)
    (hu' : ∀ j : Fin (flowLineNL c.fn c.jumps 0), k < (j : ℕ) → flowLineXL c.fn c.jumps 0 j < u) :
    (stopWord κ (c, θ, r)).fn v = c.fn u := by
  rw [fnL_stop c θ r hv hvJ, fn_old_L c θ hκ hu0 huJ, hK,
    Finset.filter_congr fun j _ => lt_xL_iff_of_mem c hk hu hu' j]

/-- Right of the seed image the stopped word has the piece's left side. -/
theorem fnL_stop_of_gt {v : ℝ} (hv : v < 0) (hvJ : v ∉ (stopWord κ (c, θ, r)).jumps)
    (hv0 : markPosL (rdrv r) (rtime r) 0 < v) : (stopWord κ (c, θ, r)).fn v = -sleLambda κ - θ * chiC κ := by
  have hK : KL c r v = 0 := by
    by_contra hne
    have := (lt_pLs_iff c r v ⟨0, zero_lt_flowLineNL c⟩).2 (by simp; omega)
    rw [pLs_zero] at this
    linarith
  rw [fnL_stop c θ r hv hvJ, hK]
  simp

/-- **No genuine jump right of the seed image.** -/
theorem rkL_stop_zero {v : ℝ} (hv0 : markPosL (rdrv r) (rtime r) 0 ≤ v) : rkL (stopWord κ (c, θ, r)) v = 0 := by
  unfold rkL
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y hy ⟨hvy, hy0⟩
  obtain ⟨i, rfl⟩ := exists_pLs_eq c θ r (Finset.mem_filter.1 hy).1 hy0
  have := antitone_pLs c r (Fin.le_def.2 (Nat.zero_le (i : ℕ)) : (⟨0, zero_lt_flowLineNL c⟩ :
    Fin (flowLineNL c.fn c.jumps 0)) ≤ i)
  rw [pLs_zero] at this
  linarith

/-! ### The region after the seed image, when the region is not split -/

variable {c r}

theorem pLs_lt_iff {aL : ℝ} (hA : StrictMonoOn (markPosL (rdrv r) (rtime r)) (Icc aL 0))
    {i j : Fin (flowLineNL c.fn c.jumps 0)} (hi : aL ≤ flowLineXL c.fn c.jumps 0 i)
    (hj : aL ≤ flowLineXL c.fn c.jumps 0 j) : pLs c r i < pLs c r j ↔ j < i := by
  have hsa := Sec7.StripDet.strictAnti_flowLineXL c.fn c.jumps
  constructor
  · intro h
    by_contra hij
    have := antitone_pLs c r (not_lt.1 hij)
    linarith
  · intro h
    exact hA ⟨hi, GW3Word.flowLineXL_nonpos _ _ _⟩ ⟨hj, GW3Word.flowLineXL_nonpos _ _ _⟩ (hsa h)

theorem markPosL_lt_pLs {aL : ℝ} (hA : StrictMonoOn (markPosL (rdrv r) (rtime r)) (Icc aL 0))
    {j : Fin (flowLineNL c.fn c.jumps 0)} (hj : aL < flowLineXL c.fn c.jumps 0 j) :
    markPosL (rdrv r) (rtime r) aL < pLs c r j :=
  hA ⟨le_rfl, hj.le.trans (GW3Word.flowLineXL_nonpos _ _ _)⟩ ⟨hj.le, GW3Word.flowLineXL_nonpos _ _ _⟩ hj

theorem pLs_le_markPosL {aL : ℝ} (haL : aL ≤ 0) {j : Fin (flowLineNL c.fn c.jumps 0)}
    (hj : flowLineXL c.fn c.jumps 0 j ≤ aL) : pLs c r j ≤ markPosL (rdrv r) (rtime r) aL :=
  Sec7.StripSideHeightProb.markPosL_anti (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) haL hj

/-- Right of the image of `aL`, only labels inside the region are counted. -/
theorem KL_le_pLc {aL : ℝ} (haL : aL ≤ 0) {v : ℝ} (hv : markPosL (rdrv r) (rtime r) aL < v) :
    KL c r v ≤ pLc c aL := by
  by_contra h
  push Not at h
  have hlt : KL c r v - 1 < flowLineNL c.fn c.jumps 0 := by have := KL_le_card c r v; omega
  have hmem := (lt_pLs_iff c r v ⟨KL c r v - 1, hlt⟩).2 (by simp; omega)
  have hout : ¬ aL < flowLineXL c.fn c.jumps 0 ⟨KL c r v - 1, hlt⟩ := by
    rw [xL_gt_iff]; simp; omega
  have := pLs_le_markPosL (c := c) (r := r) haL (not_lt.1 hout)
  linarith

/-- The left seed weight at angle `θ` reads the old first height. -/
theorem seedL_height (hκ : 0 < κ) :
    -sleLambda κ * (1 + flowLineRhoL κ c.fn c.jumps 0 θ ⟨0, zero_lt_flowLineNL c⟩) - θ * chiC κ =
      leftLim c.fn 0 := by
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  change -sleLambda κ * (1 + (-(leftLim c.fn 0 + θ * chiC κ) / sleLambda κ - 1)) - θ * chiC κ = _
  field_simp
  ring

/-- A left label after the seed is a genuine jump: its weight is nonzero. -/
theorem flowLineRhoL_ne_zero (hκ : 0 < κ) {j : Fin (flowLineNL c.fn c.jumps 0)} (hj : (j : ℕ) ≠ 0) :
    flowLineRhoL κ c.fn c.jumps 0 θ j ≠ 0 := by
  have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  obtain ⟨j, hj'⟩ := j
  rcases j with _ | k
  · exact absurd rfl hj
  · set s := (jumpSet c.fn c.jumps).filter (· < (0 : ℝ)) with hs
    have hk : k < s.card := by
      have e : flowLineNL c.fn c.jumps 0 = s.card + 1 := rfl
      omega
    have e : flowLineRhoL κ c.fn c.jumps 0 θ ⟨k + 1, hj'⟩ =
        (rightLim c.fn (s.orderEmbOfFin rfl (Fin.rev ⟨k, hk⟩)) -
          leftLim c.fn (s.orderEmbOfFin rfl (Fin.rev ⟨k, hk⟩))) / sleLambda κ := rfl
    rw [e]
    have hmem := (Finset.mem_filter.1 (s.orderEmbOfFin_mem rfl (Fin.rev ⟨k, hk⟩))).1
    have hne := (Finset.mem_filter.1 hmem).2
    exact div_ne_zero (sub_ne_zero.2 hne.symm) hlam

theorem sum_filter_succL (f : Fin (flowLineNL c.fn c.jumps 0) → ℝ) {k : ℕ}
    (hk : k < flowLineNL c.fn c.jumps 0) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (flowLineNL c.fn c.jumps 0) => (j : ℕ) < k + 1), f j =
      (∑ j ∈ Finset.univ.filter (fun j : Fin (flowLineNL c.fn c.jumps 0) => (j : ℕ) < k), f j) + f ⟨k, hk⟩ := by
  have e : Finset.univ.filter (fun j : Fin (flowLineNL c.fn c.jumps 0) => (j : ℕ) < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun j : Fin (flowLineNL c.fn c.jumps 0) => (j : ℕ) < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [e, Finset.sum_insert (by simp), add_comm]

variable (c r)

/-- **The one-sided limits of a stopped word at a left label image inside an unsplit region.** -/
theorem lims_pLs {aL : ℝ} (hA : StrictMonoOn (markPosL (rdrv r) (rtime r)) (Icc aL 0))
    {j : ℕ} (hj : j < pLc c aL) (hj0 : pLs c r ⟨j, hj.trans_le (pLc_le c aL)⟩ < 0) :
    leftLim (stopWord κ (c, θ, r)).fn (pLs c r ⟨j, hj.trans_le (pLc_le c aL)⟩) =
        -sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter
          (fun i : Fin (flowLineNL c.fn c.jumps 0) => (i : ℕ) < j + 1), flowLineRhoL κ c.fn c.jumps 0 θ i) -
          θ * chiC κ ∧
      rightLim (stopWord κ (c, θ, r)).fn (pLs c r ⟨j, hj.trans_le (pLc_le c aL)⟩) =
        -sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter
          (fun i : Fin (flowLineNL c.fn c.jumps 0) => (i : ℕ) < j), flowLineRhoL κ c.fn c.jumps 0 θ i) -
          θ * chiC κ := by
  classical
  have hpL := pLc_le c aL
  have hjN : j < flowLineNL c.fn c.jumps 0 := hj.trans_le hpL
  set c' := stopWord κ (c, θ, r) with hc'
  have hb' := c'.isPiecewiseConstantBoundaryData
  set y := pLs c r ⟨j, hjN⟩ with hy
  have hxin : ∀ i : Fin (flowLineNL c.fn c.jumps 0), (i : ℕ) < pLc c aL → aL < flowLineXL c.fn c.jumps 0 i :=
    fun i hi => (xL_gt_iff c aL i).2 hi
  have hyA : markPosL (rdrv r) (rtime r) aL < y := markPosL_lt_pLs hA (hxin ⟨j, hjN⟩ hj)
  have haL : aL ≤ 0 := (hxin ⟨j, hjN⟩ hj).le.trans (GW3Word.flowLineXL_nonpos _ _ _)
  -- the next stop to the left
  set prv : ℝ := if h : j + 1 < pLc c aL then pLs c r ⟨j + 1, h.trans_le hpL⟩ else markPosL (rdrv r) (rtime r) aL
    with hprv
  have hprvy : prv < y := by
    rw [hprv]
    split_ifs with h
    · exact (pLs_lt_iff hA (hxin _ h).le (hxin ⟨j, hjN⟩ hj).le).2 (Fin.lt_def.2 (by simp))
    · exact hyA
  have hprvA : markPosL (rdrv r) (rtime r) aL ≤ prv := by
    rw [hprv]
    split_ifs with h
    · exact (markPosL_lt_pLs hA (hxin _ h)).le
    · exact le_rfl
  have hle : ∀ i : Fin (flowLineNL c.fn c.jumps 0), j < (i : ℕ) → pLs c r i ≤ prv := by
    intro i hi
    by_cases hia : aL < flowLineXL c.fn c.jumps 0 i
    · have hi' := (xL_gt_iff c aL i).1 hia
      have h1 : j + 1 < pLc c aL := by omega
      rw [hprv]
      simp only [h1, ↓reduceDIte]
      exact antitone_pLs c r (Fin.le_def.2 (by simp; omega))
    · exact (pLs_le_markPosL haL (not_lt.1 hia)).trans hprvA
  have hgapL : ∀ t ∈ c'.jumps, t ∉ Ioo (y - (y - prv)) y := by
    intro t ht htI
    rw [sub_sub_cancel] at htI
    have ht0 : t < 0 := htI.2.trans hj0
    obtain ⟨i, rfl⟩ := exists_pLs_eq c θ r ht ht0
    by_cases hij : (i : ℕ) ≤ j
    · have := antitone_pLs c r (Fin.le_def.2 hij : i ≤ ⟨j, hjN⟩)
      linarith [htI.2]
    · have := hle i (by omega)
      linarith [htI.1]
  obtain ⟨z₁, hz₁a, hz₁b, hz₁J⟩ := Sec4.exists_mem_Ioo_not_mem c'.jumps hprvy
  have hKz₁ : KL c r z₁ = j + 1 := by
    apply le_antisymm
    · by_contra h
      push Not at h
      have hlt : j + 1 < flowLineNL c.fn c.jumps 0 := by have := KL_le_card c r z₁; omega
      have hmem := (lt_pLs_iff c r z₁ ⟨j + 1, hlt⟩).2 (by simp; omega)
      have := hle ⟨j + 1, hlt⟩ (by simp)
      linarith
    · have := (lt_pLs_iff c r z₁ ⟨j, hjN⟩).1 hz₁b
      simp at this
      omega
  refine ⟨?_, ?_⟩
  · rw [leftLim_eq_of_gap' hb' hgapL ⟨by rw [sub_sub_cancel]; exact hz₁a, hz₁b⟩,
      fnL_stop c θ r (hz₁b.trans hj0) hz₁J, hKz₁]
  · -- the next stop to the right
    set nxt : ℝ := if h : 0 < j then pLs c r ⟨j - 1, by omega⟩ else 0 with hnxt
    have hynxt : y < nxt := by
      rw [hnxt]
      split_ifs with h
      · exact (pLs_lt_iff hA (hxin ⟨j, hjN⟩ hj).le (hxin _ (by simp; omega)).le).2 (Fin.lt_def.2 (by simp; omega))
      · exact hj0
    have hnxt0 : nxt ≤ 0 := by
      rw [hnxt]
      split_ifs with h
      · exact Sec7.StripSideHeightProb.markPosL_nonpos (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)
          (GW3Word.flowLineXL_nonpos _ _ _)
      · exact le_rfl
    have hge : ∀ i : Fin (flowLineNL c.fn c.jumps 0), (i : ℕ) < j → nxt ≤ pLs c r i := by
      intro i hi
      have h : 0 < j := by omega
      rw [hnxt]
      simp only [h, ↓reduceDIte]
      exact antitone_pLs c r (Fin.le_def.2 (by simp; omega))
    have hgapR : ∀ t ∈ c'.jumps, t ∉ Ioo y (y + (nxt - y)) := by
      intro t ht htI
      rw [add_sub_cancel] at htI
      have ht0 : t < 0 := lt_of_lt_of_le htI.2 hnxt0
      obtain ⟨i, rfl⟩ := exists_pLs_eq c θ r ht ht0
      by_cases hij : (i : ℕ) < j
      · have := hge i hij
        linarith [htI.2]
      · have := antitone_pLs c r (Fin.le_def.2 (not_lt.1 hij) : (⟨j, hjN⟩ : Fin _) ≤ i)
        linarith [htI.1]
    obtain ⟨z₀, hz₀a, hz₀b, hz₀J⟩ := Sec4.exists_mem_Ioo_not_mem c'.jumps hynxt
    have hKz₀ : KL c r z₀ = j := by
      apply le_antisymm
      · by_contra h
        push Not at h
        have hmem := (lt_pLs_iff c r z₀ ⟨j, hjN⟩).2 (by simp; omega)
        linarith
      · rcases Nat.eq_zero_or_pos j with h0 | hpos
        · omega
        · have := (lt_pLs_iff c r z₀ ⟨j - 1, by omega⟩).1 (hz₀b.trans_le (hge ⟨j - 1, by omega⟩ (by simp; omega)))
          simp at this
          omega
    rw [rightLim_eq_of_gap' hb' hgapR ⟨hz₀a, by rw [add_sub_cancel]; exact hz₀b⟩,
      fnL_stop c θ r (lt_of_lt_of_le hz₀b hnxt0) hz₀J, hKz₀]

/-- **The rank of a point of an unsplit left region after the seed image.** -/
theorem rkL_stop (hκ : 0 < κ) {aL : ℝ} (haL : aL ≤ 0) (hA : StrictMonoOn (markPosL (rdrv r) (rtime r)) (Icc aL 0))
    {v : ℝ} (hv : markPosL (rdrv r) (rtime r) aL < v) (hK : 1 ≤ KL c r v) :
    rkL (stopWord κ (c, θ, r)) v = (KL c r v - 1) + δL c θ r κ := by
  classical
  have hpL := pLc_le c aL
  have hKp := KL_le_pLc (c := c) (r := r) haL hv
  have hxin : ∀ i : Fin (flowLineNL c.fn c.jumps 0), (i : ℕ) < pLc c aL → aL < flowLineXL c.fn c.jumps 0 i :=
    fun i hi => (xL_gt_iff c aL i).2 hi
  set c' := stopWord κ (c, θ, r) with hc'
  set D : Prop := markPosL (rdrv r) (rtime r) 0 < 0 ∧ leftLim c.fn 0 ≠ -sleLambda κ - θ * chiC κ with hD
  set S := Finset.univ.filter (fun j : Fin (flowLineNL c.fn c.jumps 0) => (j : ℕ) < KL c r v ∧ ((j : ℕ) ≠ 0 ∨ D))
    with hS
  have hinj : Set.InjOn (pLs c r) (S : Set (Fin (flowLineNL c.fn c.jumps 0))) := by
    intro i hi j hj hij
    have hi' := (Finset.mem_filter.1 hi).2.1
    have hj' := (Finset.mem_filter.1 hj).2.1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := (pLs_lt_iff hA (hxin j (by omega)).le (hxin i (by omega)).le).2 h
      linarith
    · have := (pLs_lt_iff hA (hxin i (by omega)).le (hxin j (by omega)).le).2 h
      linarith
  have hmp0 : markPosL (rdrv r) (rtime r) 0 ≤ 0 :=
    Sec7.StripSideHeightProb.markPosL_nonpos (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) le_rfl
  have hseed : ∀ hlt : pLs c r ⟨0, zero_lt_flowLineNL c⟩ < 0,
      leftLim c'.fn (pLs c r ⟨0, zero_lt_flowLineNL c⟩) = leftLim c.fn 0 ∧
        rightLim c'.fn (pLs c r ⟨0, zero_lt_flowLineNL c⟩) = -sleLambda κ - θ * chiC κ := by
    intro hlt
    have hl := lims_pLs (κ := κ) c θ r hA (j := 0) (by omega) hlt
    have e : Finset.univ.filter (fun i : Fin (flowLineNL c.fn c.jumps 0) => (i : ℕ) < 0 + 1) =
        {⟨0, zero_lt_flowLineNL c⟩} := by
      ext i; simp [Fin.ext_iff]
    have e0 : Finset.univ.filter (fun i : Fin (flowLineNL c.fn c.jumps 0) => (i : ℕ) < 0) = ∅ := by
      ext i; simp
    refine ⟨?_, ?_⟩
    · rw [hl.1, e, Finset.sum_singleton, seedL_height θ hκ]
    · rw [hl.2, e0, Finset.sum_empty]; ring
  have himg : (jumpSet c'.fn c'.jumps).filter (fun y => v < y ∧ y < 0) = S.image (pLs c r) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, hS, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hyJ, hvy, hy0⟩
      obtain ⟨j, rfl⟩ := exists_pLs_eq c θ r (Finset.mem_filter.1 hyJ).1 hy0
      have hjK := (lt_pLs_iff c r v j).1 hvy
      refine ⟨j, ⟨hjK, ?_⟩, rfl⟩
      by_cases hj0 : (j : ℕ) = 0
      · right
        have hj : j = ⟨0, zero_lt_flowLineNL c⟩ := Fin.ext hj0
        subst hj
        refine ⟨by rw [← pLs_zero]; exact hy0, fun hH => ?_⟩
        have hgen := (Finset.mem_filter.1 hyJ).2
        obtain ⟨h1, h2⟩ := hseed hy0
        exact hgen (by rw [h1, h2, hH])
      · exact Or.inl hj0
    · rintro ⟨j, ⟨hjK, hjD⟩, rfl⟩
      have hjN : (j : ℕ) < pLc c aL := by omega
      have hneg : pLs c r j < 0 := by
        by_cases hj0 : (j : ℕ) = 0
        · have hj : j = ⟨0, zero_lt_flowLineNL c⟩ := Fin.ext hj0
          rw [hj, pLs_zero]
          rcases hjD with h | h
          · exact absurd hj0 h
          · exact h.1
        · have h0 : (⟨0, zero_lt_flowLineNL c⟩ : Fin (flowLineNL c.fn c.jumps 0)) < j :=
            Fin.lt_def.2 (Nat.pos_of_ne_zero hj0)
          have := (pLs_lt_iff hA (hxin j hjN).le (hxin _ (by simp; omega)).le).2 h0
          rw [pLs_zero] at this
          exact lt_of_lt_of_le this hmp0
      have hmemJ := pLs_mem_jumps c θ r (κ := κ) j
      have hvlt := (lt_pLs_iff c r v j).2 hjK
      refine ⟨Finset.mem_filter.2 ⟨hmemJ, ?_⟩, hvlt, hneg⟩
      by_cases hj0 : (j : ℕ) = 0
      · have hj : j = ⟨0, zero_lt_flowLineNL c⟩ := Fin.ext hj0
        subst hj
        obtain ⟨h1, h2⟩ := hseed hneg
        rw [h1, h2]
        rcases hjD with h | h
        · exact absurd hj0 h
        · exact h.2
      · obtain ⟨j, hjlt⟩ := j
        have hl := lims_pLs (κ := κ) c θ r hA (j := j) hjN hneg
        rw [hl.1, hl.2, sum_filter_succL (fun i => flowLineRhoL κ c.fn c.jumps 0 θ i) hjlt]
        intro he
        have hne := flowLineRhoL_ne_zero (c := c) θ hκ (j := ⟨j, hjlt⟩) hj0
        have hlam : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
        apply hne
        have : sleLambda κ * flowLineRhoL κ c.fn c.jumps 0 θ ⟨j, hjlt⟩ = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hlam
        · exact h
  unfold rkL
  rw [himg, Finset.card_image_of_injOn hinj]
  have hKN : KL c r v ≤ flowLineNL c.fn c.jumps 0 := KL_le_card c r v
  unfold δL
  split_ifs with hDd
  · have e : S = Finset.univ.filter (fun j : Fin (flowLineNL c.fn c.jumps 0) => (j : ℕ) < KL c r v) := by
      rw [hS]
      exact Finset.filter_congr fun j _ => ⟨fun h => h.1, fun h => ⟨h, Or.inr hDd⟩⟩
    rw [e, card_filter_val_lt hKN]
    omega
  · have e : S = (Finset.univ.filter (fun j : Fin (flowLineNL c.fn c.jumps 0) => (j : ℕ) < KL c r v)).erase
        ⟨0, zero_lt_flowLineNL c⟩ := by
      ext j
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, Fin.ext_iff]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact ⟨h2, h1⟩
        · exact absurd h2 hDd
      · rintro ⟨h1, h2⟩
        exact ⟨h2, Or.inl h1⟩
    rw [e, Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp; omega⟩),
      card_filter_val_lt hKN]
    omega

end Left

end InteractingSLE.Theorem14.GW2Rq
