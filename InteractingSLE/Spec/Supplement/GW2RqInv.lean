/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqStepL
import InteractingSLE.Spec.Supplement.GW2SdpInv
import InteractingSLE.Spec.Exist.StagedLaw3Main

/-!
# The rank pairing and the far counts along the stage words (decision D33)

PROVE-GW2-ROOTX round 8. Two angle regions `(aL, 0)`, `(0, aR)` of a word are **paired** (`PairR`) when heights of
equal rank on the two sides read the same angle (`h_R − h_L = 2λ`). A piece is **split-free** against the regions
(`SplitFree`) when, on each side, its mark flow either keeps the whole region (strictly increasing, with a nondegenerate
side if the piece has positive time) or swallows all of it.

* **`pairR_stopWord`**: a split-free piece keeps the pairing, with the regions moved to `markPosL aL`, `markPos aR`;
* `card_farR_stopWord`, `card_farL_stopWord`: the number of jumps beyond the moved regions does not increase;
* **`StageQ`**, `SplitFreePast`, **`stageQ_stageWord`**: along a past whose pieces are split-free against SDE's
  junctions (`GW2Sdp.junctionL/R`), every stage word is paired with at most `N` jumps beyond each junction, `N` the
  number of jumps of the root word.

Deterministic. The almost-sure split-freeness of the history's pieces is the probabilistic input.
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

/-- **The rank pairing of two angle regions.** -/
def PairR (κ : ℝ) (c : BoundaryWord) (aL aR : ℝ) : Prop :=
  ∀ u v, 0 < u → u < aR → u ∉ c.jumps → aL < v → v < 0 → v ∉ c.jumps → rkR c u = rkL c v →
    c.fn u - c.fn v = 2 * sleLambda κ

/-- **A split-free piece**: on each side its mark flow keeps the region (strictly increasing, nondegenerate side if
the piece has positive time) or swallows all of it. -/
def SplitFree (r : RecData) (aL aR : ℝ) : Prop :=
  ((StrictMonoOn (markPos (rdrv r) (rtime r)) (Icc 0 aR) ∧ (0 < rtime r → 0 < markPos (rdrv r) (rtime r) 0)) ∨
      markPos (rdrv r) (rtime r) aR = markPos (rdrv r) (rtime r) 0) ∧
    ((StrictMonoOn (markPosL (rdrv r) (rtime r)) (Icc aL 0) ∧
        (0 < rtime r → markPosL (rdrv r) (rtime r) 0 < 0)) ∨
      markPosL (rdrv r) (rtime r) aL = markPosL (rdrv r) (rtime r) 0)

section Step

variable {κ : ℝ} (c : BoundaryWord) (θ : ℝ) (r : RecData)

/-- An old point before the first right label has the old first right height. -/
theorem old_rank0_R (hκ : 0 < κ) {u : ℝ} (hu0 : 0 < u) (huJ : u ∉ c.jumps)
    (hlt : ∀ j : Fin (flowLineNR c.fn c.jumps 0), 0 < (j : ℕ) → u < flowLineXR c.fn c.jumps 0 j) :
    c.fn u = rightLim c.fn 0 := by
  have h0 : flowLineXR c.fn c.jumps 0 ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ < u := by rw [xR_zero]; exact hu0
  rw [fn_old_R c 0 hκ hu0 huJ, Finset.filter_congr fun j _ => xR_le_iff_of_mem c _ h0 hlt j]
  have e : Finset.univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) => (j : ℕ) < 0 + 1) =
      {⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩} := by
    ext i; simp [Fin.ext_iff]
  rw [e, Finset.sum_singleton]
  exact seedR_height (c := c) 0 hκ

/-- An old point after the first left label (towards `0`) has the old first left height. -/
theorem old_rank0_L (hκ : 0 < κ) {v : ℝ} (hv0 : v < 0) (hvJ : v ∉ c.jumps)
    (hlt : ∀ j : Fin (flowLineNL c.fn c.jumps 0), 0 < (j : ℕ) → flowLineXL c.fn c.jumps 0 j < v) :
    c.fn v = leftLim c.fn 0 := by
  have h0 : v < flowLineXL c.fn c.jumps 0 ⟨0, zero_lt_flowLineNL c⟩ := by rw [xL_zero]; exact hv0
  rw [fn_old_L c 0 hκ hv0 hvJ, Finset.filter_congr fun j _ => lt_xL_iff_of_mem c _ h0 hlt j]
  have e : Finset.univ.filter (fun j : Fin (flowLineNL c.fn c.jumps 0) => (j : ℕ) < 0 + 1) =
      {⟨0, zero_lt_flowLineNL c⟩} := by
    ext i; simp [Fin.ext_iff]
  rw [e, Finset.sum_singleton]
  exact seedL_height (c := c) 0 hκ

theorem markPos_zero_of_rtime {r : RecData} (h : rtime r = 0) : markPos (rdrv r) (rtime r) 0 = 0 := by
  rw [h]; exact markPos_time_zero (continuous_rdrv r) (rdrv_zero r) le_rfl

theorem markPosL_zero_of_rtime {r : RecData} (h : rtime r = 0) : markPosL (rdrv r) (rtime r) 0 = 0 := by
  rw [h]; exact markPosL_time_zero (continuous_rdrv r) (rdrv_zero r) le_rfl

/-- **The reading of a point of the moved right region.** -/
theorem readR (hκ : 0 < κ) {aR : ℝ} (haR : 0 ≤ aR)
    (hs : (StrictMonoOn (markPos (rdrv r) (rtime r)) (Icc 0 aR) ∧
        (0 < rtime r → 0 < markPos (rdrv r) (rtime r) 0)) ∨
      markPos (rdrv r) (rtime r) aR = markPos (rdrv r) (rtime r) 0)
    {u : ℝ} (hu0 : 0 < u) (hua : u < markPos (rdrv r) (rtime r) aR) (huJ : u ∉ (stopWord κ (c, θ, r)).jumps) :
    (0 < rtime r ∧ (stopWord κ (c, θ, r)).fn u = sleLambda κ - θ * chiC κ ∧ rkR (stopWord κ (c, θ, r)) u = 0) ∨
    (StrictMonoOn (markPos (rdrv r) (rtime r)) (Icc 0 aR) ∧ (0 < rtime r → 0 < markPos (rdrv r) (rtime r) 0) ∧
      0 < aR ∧ ∃ k u₀, 0 < u₀ ∧ u₀ < aR ∧ u₀ ∉ c.jumps ∧ rkR c u₀ = k ∧
        (stopWord κ (c, θ, r)).fn u = c.fn u₀ ∧ rkR (stopWord κ (c, θ, r)) u = k + δR c θ r κ ∧
        (k = 0 → c.fn u₀ = rightLim c.fn 0)) := by
  have hmp0J : markPos (rdrv r) (rtime r) 0 ∈ (stopWord κ (c, θ, r)).jumps := by
    rw [← pRs_zero c r]; exact pRs_mem_jumps c θ r _
  have hne : u ≠ markPos (rdrv r) (rtime r) 0 := fun h => huJ (h ▸ hmp0J)
  rcases lt_or_gt_of_ne hne with h | h
  · left
    refine ⟨?_, fnR_stop_of_lt c θ r hu0 huJ h, rkR_stop_zero c θ r h.le⟩
    rcases (rtime_nonneg r).lt_or_eq with ht | ht
    · exact ht
    · rw [markPos_zero_of_rtime ht.symm] at h; linarith
  · right
    have hA : StrictMonoOn (markPos (rdrv r) (rtime r)) (Icc 0 aR) ∧
        (0 < rtime r → 0 < markPos (rdrv r) (rtime r) 0) := by
      rcases hs with hs | hs
      · exact hs
      · rw [hs] at hua; linarith
    have haR' : 0 < aR := by
      rcases haR.lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at hua; linarith
    have hK1 : 1 ≤ KR c r u := by
      have := (pRs_le_iff c r u ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩).1 (by rw [pRs_zero]; exact h.le)
      simp at this; omega
    have hKp := KR_le_pRc (c := c) (r := r) haR hua
    have hpR := pRc_le c aR
    set k := KR c r u - 1 with hk
    have hkN : k < flowLineNR c.fn c.jumps 0 := by omega
    have hxk := (xR_lt_iff c aR ⟨k, hkN⟩).2 (by simp; omega)
    obtain ⟨u₀, hu₁, hu₂, hu₀J, hu₃⟩ := exists_pt_right c hkN hxk
    have hu₀0 : 0 < u₀ := (GW3Word.flowLineXR_nonneg _ _ _).trans_lt hu₁
    refine ⟨hA.1, hA.2, haR', k, u₀, hu₀0, hu₂, hu₀J, rkR_eq c hkN hu₁ fun j hj => (hu₃ j hj).le,
      fnR_stop_eq_old c θ r hκ hu0 huJ (by omega) hkN hu₀0 hu₀J hu₁ hu₃, ?_, fun hk0 => ?_⟩
    · rw [rkR_stop c θ r hκ haR hA.1 hua huJ hK1]
    · exact old_rank0_R c hκ hu₀0 hu₀J fun j hj => hu₃ j (by omega)

/-- **The reading of a point of the moved left region.** -/
theorem readL (hκ : 0 < κ) {aL : ℝ} (haL : aL ≤ 0)
    (hs : (StrictMonoOn (markPosL (rdrv r) (rtime r)) (Icc aL 0) ∧
        (0 < rtime r → markPosL (rdrv r) (rtime r) 0 < 0)) ∨
      markPosL (rdrv r) (rtime r) aL = markPosL (rdrv r) (rtime r) 0)
    {v : ℝ} (hv0 : v < 0) (hva : markPosL (rdrv r) (rtime r) aL < v)
    (hvJ : v ∉ (stopWord κ (c, θ, r)).jumps) :
    (0 < rtime r ∧ (stopWord κ (c, θ, r)).fn v = -sleLambda κ - θ * chiC κ ∧ rkL (stopWord κ (c, θ, r)) v = 0) ∨
    (StrictMonoOn (markPosL (rdrv r) (rtime r)) (Icc aL 0) ∧ (0 < rtime r → markPosL (rdrv r) (rtime r) 0 < 0) ∧
      aL < 0 ∧ ∃ k v₀, v₀ < 0 ∧ aL < v₀ ∧ v₀ ∉ c.jumps ∧ rkL c v₀ = k ∧
        (stopWord κ (c, θ, r)).fn v = c.fn v₀ ∧ rkL (stopWord κ (c, θ, r)) v = k + δL c θ r κ ∧
        (k = 0 → c.fn v₀ = leftLim c.fn 0)) := by
  have hmp0J : markPosL (rdrv r) (rtime r) 0 ∈ (stopWord κ (c, θ, r)).jumps := by
    rw [← pLs_zero c r]; exact pLs_mem_jumps c θ r _
  have hne : v ≠ markPosL (rdrv r) (rtime r) 0 := fun h => hvJ (h ▸ hmp0J)
  rcases lt_or_gt_of_ne hne with h | h
  · right
    have hA : StrictMonoOn (markPosL (rdrv r) (rtime r)) (Icc aL 0) ∧
        (0 < rtime r → markPosL (rdrv r) (rtime r) 0 < 0) := by
      rcases hs with hs | hs
      · exact hs
      · rw [hs] at hva; linarith
    have haL' : aL < 0 := by
      rcases haL.lt_or_eq with h' | h'
      · exact h'
      · rw [h'] at hva; linarith
    have hK1 : 1 ≤ KL c r v := by
      have := (lt_pLs_iff c r v ⟨0, zero_lt_flowLineNL c⟩).1 (by rw [pLs_zero]; exact h)
      simp at this; omega
    have hKp := KL_le_pLc (c := c) (r := r) haL hva
    have hpL := pLc_le c aL
    set k := KL c r v - 1 with hk
    have hkN : k < flowLineNL c.fn c.jumps 0 := by omega
    have hxk := (xL_gt_iff c aL ⟨k, hkN⟩).2 (by simp; omega)
    obtain ⟨v₀, hv₁, hv₂, hv₀J, hv₃⟩ := exists_pt_left c hkN hxk
    have hv₀0 : v₀ < 0 := hv₂.trans_le (GW3Word.flowLineXL_nonpos _ _ _)
    refine ⟨hA.1, hA.2, haL', k, v₀, hv₀0, hv₁, hv₀J, rkL_eq c hkN hv₂ fun j hj => (hv₃ j hj).le,
      fnL_stop_eq_old c θ r hκ hv0 hvJ (by omega) hkN hv₀0 hv₀J hv₂ hv₃, ?_, fun hk0 => ?_⟩
    · rw [rkL_stop c θ r hκ haL hA.1 hva hK1]
    · exact old_rank0_L c hκ hv₀0 hv₀J fun j hj => hv₃ j (by omega)
  · left
    refine ⟨?_, fnL_stop_of_gt c θ r hv0 hvJ h, rkL_stop_zero c θ r h.le⟩
    rcases (rtime_nonneg r).lt_or_eq with ht | ht
    · exact ht
    · rw [markPosL_zero_of_rtime ht.symm] at h; linarith

/-- **A split-free piece keeps the rank pairing.** -/
theorem pairR_stopWord (hκ : 0 < κ) {aL aR : ℝ} (haL : aL ≤ 0) (haR : 0 ≤ aR) (h : PairR κ c aL aR)
    (hs : SplitFree r aL aR) :
    PairR κ (stopWord κ (c, θ, r)) (markPosL (rdrv r) (rtime r) aL) (markPos (rdrv r) (rtime r) aR) := by
  intro u v hu0 hua huJ hva hv0 hvJ hrk
  -- the old pairing at rank `0` couples the two seed shifts
  have hseed : 0 < aR → aL < 0 → rightLim c.fn 0 - leftLim c.fn 0 = 2 * sleLambda κ := by
    intro hR hL
    obtain ⟨u₀, hu₁, hu₂, hu₀J, hu₃⟩ := exists_pt_right c (Supp8.GB6.zero_lt_flowLineNR _ _)
      (by rw [xR_zero]; exact hR)
    obtain ⟨v₀, hv₁, hv₂, hv₀J, hv₃⟩ := exists_pt_left c (zero_lt_flowLineNL c) (by rw [xL_zero]; exact hL)
    rw [xR_zero] at hu₁
    rw [xL_zero] at hv₂
    have hp := h u₀ v₀ hu₁ hu₂ hu₀J hv₁ hv₂ hv₀J
      ((rkR_eq c (Supp8.GB6.zero_lt_flowLineNR _ _) (by rw [xR_zero]; exact hu₁) fun j hj => (hu₃ j hj).le).trans
        (rkL_eq c (zero_lt_flowLineNL c) (by rw [xL_zero]; exact hv₂) fun j hj => (hv₃ j hj).le).symm)
    rw [old_rank0_R c hκ hu₁ hu₀J hu₃, old_rank0_L c hκ hv₂ hv₀J hv₃] at hp
    exact hp
  rcases readR c θ r hκ haR hs.1 hu0 hua huJ with ⟨hT, hfu, hru⟩ | ⟨hA, hsA, haR', k, u₀, hu₀0, hu₀a, hu₀J, hrk₀,
      hfu, hru, hk0⟩ <;>
    rcases readL c θ r hκ haL hs.2 hv0 hva hvJ with ⟨hT', hfv, hrv⟩ | ⟨hB, hsB, haL', k', v₀, hv₀0, hv₀a, hv₀J,
      hrk₀', hfv, hrv, hk0'⟩
  · rw [hfu, hfv]; ring
  · -- right side read at the seed, left side at an old height of rank `0`
    rw [hru, hrv] at hrk
    have hk' : k' = 0 := by omega
    have hδ : δL c θ r κ = 0 := by omega
    have hneg := hsB hT
    have hL0 : leftLim c.fn 0 = -sleLambda κ - θ * chiC κ := by
      unfold δL at hδ
      by_contra hne
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hneg, hne⟩)] at hδ
      exact one_ne_zero hδ
    rw [hfu, hfv, hk0' hk', hL0]; ring
  · rw [hru, hrv] at hrk
    have hk : k = 0 := by omega
    have hδ : δR c θ r κ = 0 := by omega
    have hpos := hsA hT'
    have hR0 : rightLim c.fn 0 = sleLambda κ - θ * chiC κ := by
      unfold δR at hδ
      by_contra hne
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hpos, hne⟩)] at hδ
      exact one_ne_zero hδ
    rw [hfu, hfv, hk0 hk, hR0]; ring
  · -- both sides read old heights: the seed shifts agree
    have hδ : δR c θ r κ = δL c θ r κ := by
      rcases (rtime_nonneg r).lt_or_eq with hT | hT
      · have hpos := hsA hT
        have hneg := hsB hT
        have hs0 := hseed haR' haL'
        unfold δR δL
        have hiff : rightLim c.fn 0 ≠ sleLambda κ - θ * chiC κ ↔ leftLim c.fn 0 ≠ -sleLambda κ - θ * chiC κ := by
          constructor
          · intro h1 h2; exact h1 (by linarith)
          · intro h1 h2; exact h1 (by linarith)
        by_cases h1 : rightLim c.fn 0 ≠ sleLambda κ - θ * chiC κ
        · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hpos, h1⟩), ite_eq_left_of_eq_true _ _ (eq_true ⟨hneg, hiff.1 h1⟩)]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h1 h'.2),
            ite_eq_right_of_eq_false _ _ (eq_false fun h' => (mt hiff.2 h1) h'.2)]
      · unfold δR δL
        rw [markPos_zero_of_rtime hT.symm, markPosL_zero_of_rtime hT.symm]
        simp
    rw [hru, hrv, hδ] at hrk
    have hkk : k = k' := by omega
    rw [hfu, hfv]
    exact h u₀ v₀ hu₀0 hu₀a hu₀J hv₀a hv₀0 hv₀J (hrk₀.trans (hkk.trans hrk₀'.symm))

/-- **The jumps beyond the moved right region are images of old jumps beyond `aR`.** -/
theorem card_farR_stopWord {aR : ℝ} (haR : 0 ≤ aR) :
    ((stopWord κ (c, θ, r)).jumps.filter fun y => markPos (rdrv r) (rtime r) aR < y).card ≤
      (c.jumps.filter fun y => aR < y).card := by
  classical
  have hsub : (stopWord κ (c, θ, r)).jumps.filter (fun y => markPos (rdrv r) (rtime r) aR < y) ⊆
      (c.jumps.filter fun y => aR < y).image (markPos (rdrv r) (rtime r)) := by
    intro y hy
    obtain ⟨hyJ, hya⟩ := Finset.mem_filter.1 hy
    have hy0 : 0 < y := lt_of_le_of_lt (Sec7.StripSideHeightProb.markPos_nonneg (continuous_rdrv r) (rdrv_zero r)
      (rtime_nonneg r) haR) hya
    obtain ⟨j, rfl⟩ := exists_pRs_eq c θ r hyJ hy0
    have hxa : aR < flowLineXR c.fn c.jumps 0 j := by
      by_contra hle
      have := Sec7.StripSideHeightProb.markPos_mono (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)
        (GW3Word.flowLineXR_nonneg _ _ j) (not_lt.1 hle)
      exact absurd hya (not_lt.2 this)
    have hj0 : (j : ℕ) ≠ 0 := fun h0 => by
      have : j = ⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩ := Fin.ext h0
      rw [this, xR_zero] at hxa
      linarith
    exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 (xR_mem_jumpSet c hj0)).1, hxa⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- **The jumps beyond the moved left region are images of old jumps beyond `aL`.** -/
theorem card_farL_stopWord {aL : ℝ} (haL : aL ≤ 0) :
    ((stopWord κ (c, θ, r)).jumps.filter fun y => y < markPosL (rdrv r) (rtime r) aL).card ≤
      (c.jumps.filter fun y => y < aL).card := by
  classical
  have hsub : (stopWord κ (c, θ, r)).jumps.filter (fun y => y < markPosL (rdrv r) (rtime r) aL) ⊆
      (c.jumps.filter fun y => y < aL).image (markPosL (rdrv r) (rtime r)) := by
    intro y hy
    obtain ⟨hyJ, hya⟩ := Finset.mem_filter.1 hy
    have hy0 : y < 0 := lt_of_lt_of_le hya (Sec7.StripSideHeightProb.markPosL_nonpos (continuous_rdrv r)
      (rdrv_zero r) (rtime_nonneg r) haL)
    obtain ⟨i, rfl⟩ := exists_pLs_eq c θ r hyJ hy0
    have hxa : flowLineXL c.fn c.jumps 0 i < aL := by
      by_contra hle
      have := Sec7.StripSideHeightProb.markPosL_anti (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r)
        (GW3Word.flowLineXL_nonpos _ _ i) (not_lt.1 hle)
      exact absurd hya (not_lt.2 this)
    have hi0 : (i : ℕ) ≠ 0 := fun h0 => by
      have : i = ⟨0, zero_lt_flowLineNL c⟩ := Fin.ext h0
      rw [this, xL_zero] at hxa
      linarith
    exact Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 (xL_mem_jumpSet c hi0)).1, hxa⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end Step

/-! ### Along the stage words -/

/-- **The invariant of a stage word**: the regions are paired and at most `N` jumps lie beyond each junction. -/
structure StageQ (κ : ℝ) (c : BoundaryWord) (aL aR : ℝ) (N : ℕ) : Prop where
  pair : PairR κ c aL aR
  farR : (c.jumps.filter fun y => aR < y).card ≤ N
  farL : (c.jumps.filter fun y => y < aL).card ≤ N

section Stage

universe v

variable {S : Type v}

theorem junctionL_nonpos' : ∀ (n : ℕ) (x : GW2JDetR5.Past S n), GW2Sdp.junctionL n x ≤ 0
  | 0, _ => le_rfl
  | n + 1, x => Sec7.StripSideHeightProb.markPosL_nonpos (continuous_rdrv x.2) (rdrv_zero x.2) (rtime_nonneg x.2)
      (junctionL_nonpos' n x.1)

theorem junctionR_nonneg' : ∀ (n : ℕ) (x : GW2JDetR5.Past S n), 0 ≤ GW2Sdp.junctionR n x
  | 0, _ => le_rfl
  | n + 1, x => Sec7.StripSideHeightProb.markPos_nonneg (continuous_rdrv x.2) (rdrv_zero x.2) (rtime_nonneg x.2)
      (junctionR_nonneg' n x.1)

/-- **Every piece of a past is split-free against the junctions before it.** -/
def SplitFreePast : (n : ℕ) → GW2JDetR5.Past S n → Prop
  | 0 => fun _ => True
  | n + 1 => fun x => SplitFreePast n x.1 ∧ SplitFree x.2 (GW2Sdp.junctionL n x.1) (GW2Sdp.junctionR n x.1)

/-- **The invariant along the stage words**: along a split-free past, every stage word is paired at SDE's junctions,
with at most `N` jumps beyond each junction, if the root word has at most `N` jumps. -/
theorem stageQ_stageWord {κ : ℝ} (hκ : 0 < κ) (W₀ : S → BoundaryWord) (θ : ℕ → ℝ) {N : ℕ}
    (h0 : ∀ x, (W₀ x).jumps.card ≤ N) :
    ∀ (n : ℕ) (x : GW2JDetR5.Past S n), SplitFreePast n x →
      StageQ κ (GW2JDetR5.stageWord (κ := κ) W₀ θ n x) (GW2Sdp.junctionL n x) (GW2Sdp.junctionR n x) N
  | 0, x, _ => by
    refine ⟨fun u v hu0 hua _ _ _ _ _ => ?_, (Finset.card_filter_le _ _).trans (h0 x),
      (Finset.card_filter_le _ _).trans (h0 x)⟩
    exact absurd (hu0.trans hua) (lt_irrefl _)
  | n + 1, x, hx => by
    have ih := stageQ_stageWord hκ W₀ θ h0 n x.1 hx.1
    have haL := junctionL_nonpos' n x.1
    have haR := junctionR_nonneg' n x.1
    exact ⟨pairR_stopWord _ (θ n) x.2 hκ haL haR ih.pair hx.2,
      (card_farR_stopWord _ (θ n) x.2 haR).trans ih.farR, (card_farL_stopWord _ (θ n) x.2 haL).trans ih.farL⟩

end Stage

end InteractingSLE.Theorem14.GW2Rq
