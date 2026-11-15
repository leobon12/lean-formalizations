/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WmFar
import InteractingSLE.Spec.Sec7.StripSideHeightProbSide
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Exist.StagedLaw3Adm

/-!
# The near structure (N3), step A: the height profile of a stopped piece

Packet PROVE-GW2-SDE (round 15; D24: SDE defines the scaled cover's gap and proves (N3)). The stage word is the root
word flowed through the history pieces: stage `j + 1` is `stopWord κ (stage j, θ_j, record_j)`, the force word whose
positions are the images (`markPosL`, `markPos`) of the earlier word's flow-line labels under the piece's record
and whose weights are the earlier word's flow-line weights at the piece's angle (`padFL κ θ`), shifted by `θχ`.
This file reads its heights:

* **`fn_stopWord_left`**: at a point `z < 0` of the stopped word, for any reference point `a ≤ 0` of the earlier word:
  if `z` lies right of the image of `a`, the height is the piece's left side `−λ − θχ` or the earlier word's height at a
  point of `(a, 0)`; if `z` lies left of the image of `a`, it is the earlier word's height at a point left of `a`;
* **`fn_stopWord_right`**: the mirror statement at `z > 0` (the piece's right side is `λ − θχ`).

So heights are carried from the earlier word, on the same side of any reference point, and the only new heights are
the piece's two sides. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Sdp

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSideHeightProb

/-- **The heights left of a stopped piece** (relative to a reference point `a ≤ 0` of the earlier word). -/
theorem fn_stopWord_left {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {a z : ℝ} (ha : a ≤ 0)
    (hz : z < 0) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps) :
    (markPosL (rdrv r) (rtime r) a < z →
      (stopWord κ (c, θ, r)).fn z = -sleLambda κ - θ * chiC κ ∨
        ∃ y, a < y ∧ y < 0 ∧ y ∉ c.jumps ∧ (stopWord κ (c, θ, r)).fn z = c.fn y) ∧
    (z < markPosL (rdrv r) (rtime r) a → ∃ y, y < a ∧ y ∉ c.jumps ∧ (stopWord κ (c, θ, r)).fn z = c.fn y) := by
  classical
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT := rtime_nonneg r
  have hb := c.isPiecewiseConstantBoundaryData
  set w := rdrv r with hwdef
  set T := rtime r with hTdef
  set xL := flowLineXL c.fn c.jumps 0 with hxLdef
  set ρL := flowLineRhoL κ c.fn c.jumps 0 θ with hρLdef
  set pL : Fin (flowLineNL c.fn c.jumps 0) → ℝ := fun i => markPosL w T (xL i) with hpL
  have hxL0 : ∀ i, xL i ≤ 0 := fun i => GW3Word.flowLineXL_nonpos c.fn c.jumps i
  have hanti : ∀ {u v : ℝ}, u ≤ 0 → v ≤ u → markPosL w T v ≤ markPosL w T u := fun hu hvu =>
    markPosL_anti hw hw0 hT hu hvu
  -- the height of the stopped word at `z`
  have hfn : (stopWord κ (c, θ, r)).fn z =
      -sleLambda κ * (1 + ∑ i ∈ univ.filter (fun i => z < pL i), ρL i) - θ * chiC κ := by
    have h := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ)
      (isMarkOrder_stopWord c r) hzJ hz.ne
    refine h.trans ?_
    rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hz]
    simp only [padFL_fst_fst_fin, padFL_snd_fst_fin, hpL, hρLdef, hxLdef, hwdef, hTdef]
  -- the earlier word's height at a point `y < 0` whose left labels are exactly those of the filter
  have hcy : ∀ y, y < 0 → y ∉ c.jumps → (∀ i, y < xL i ↔ z < pL i) → (stopWord κ (c, θ, r)).fn z = c.fn y := by
    intro y hy hyJ hiff
    have h1 := Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hy.ne (by simpa using hyJ)
    rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hy, add_zero] at h1
    rw [hfn, Finset.filter_congr fun i _ => (hiff i).symm]
    linarith
  have hz0 : 0 < flowLineNL c.fn c.jumps 0 := Supp8.GB6.zero_lt_flowLineNL _ _
  by_cases hF : ∃ i, z < pL i
  · -- some label image lies right of `z`
    have hFne : (univ.filter fun i => z < pL i).Nonempty := by
      obtain ⟨i, hi⟩ := hF
      exact ⟨i, mem_filter.2 ⟨mem_univ _, hi⟩⟩
    set hi := (univ.filter fun i => z < pL i).inf' hFne xL with hhi
    obtain ⟨i₀, hi₀F, hi₀⟩ := Finset.exists_mem_eq_inf' hFne xL
    rw [← hhi] at hi₀
    have hzi₀ : z < pL i₀ := (mem_filter.1 hi₀F).2
    have hk1 : ∀ i, z < pL i → hi ≤ xL i := fun i h =>
      Finset.inf'_le (s := univ.filter fun i => z < pL i) xL (mem_filter.2 ⟨mem_univ i, h⟩)
    have hhi0 : hi ≤ 0 := (hk1 i₀ hzi₀).trans (hxL0 i₀)
    -- below every label in the filter and above every label outside it
    have hsep : ∀ j, ¬ z < pL j → xL j < hi := by
      intro j hj
      by_contra hcon
      have h := hanti (hxL0 j) (not_lt.1 hcon)
      rw [hi₀] at h
      exact hj (hzi₀.trans_le h)
    have hiff : ∀ y, (∀ j, ¬ z < pL j → xL j < y) → y < hi → ∀ i, y < xL i ↔ z < pL i := by
      intro y hlo hyhi i
      refine ⟨fun h => ?_, fun h => hyhi.trans_le (hk1 i h)⟩
      by_contra hn
      exact absurd h (not_lt.2 (hlo i hn).le)
    refine ⟨fun hza => Or.inr ?_, fun hza => ?_⟩
    · -- `z` right of the image of `a`: a preimage point in `(a, 0)`
      have hahi : a < hi := by
        by_contra hcon
        have h := hanti ha (not_lt.1 hcon)
        rw [hi₀] at h
        exact absurd (hza.trans hzi₀) (not_lt.2 h)
      by_cases hG : ∃ j, ¬ z < pL j
      · have hGne : (univ.filter fun j => ¬ z < pL j).Nonempty := by
          obtain ⟨j, hj⟩ := hG
          exact ⟨j, mem_filter.2 ⟨mem_univ _, hj⟩⟩
        set lo := (univ.filter fun j => ¬ z < pL j).sup' hGne xL with hlo
        obtain ⟨j₀, hj₀G, hj₀⟩ := Finset.exists_mem_eq_sup' hGne xL
        rw [← hlo] at hj₀
        have hk2 : ∀ j, ¬ z < pL j → xL j ≤ lo := fun j h =>
          Finset.le_sup' (s := univ.filter fun j => ¬ z < pL j) xL (mem_filter.2 ⟨mem_univ j, h⟩)
        have hlohi : lo < hi := by rw [hj₀]; exact hsep j₀ (mem_filter.1 hj₀G).2
        obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps (max_lt hlohi hahi)
        refine ⟨y, (le_max_right _ _).trans_lt hy1, hy2.trans_le hhi0, hyJ, hcy y (hy2.trans_le hhi0) hyJ
          (hiff y (fun j hj => (hk2 j hj).trans_lt ((le_max_left _ _).trans_lt hy1)) hy2)⟩
      · simp only [not_exists, not_not] at hG
        obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps hahi
        refine ⟨y, hy1, hy2.trans_le hhi0, hyJ, hcy y (hy2.trans_le hhi0) hyJ
          (hiff y (fun j hj => absurd (hG j) hj) hy2)⟩
    · -- `z` left of the image of `a`: a preimage point left of `a`
      by_cases hG : ∃ j, ¬ z < pL j
      · have hGne : (univ.filter fun j => ¬ z < pL j).Nonempty := by
          obtain ⟨j, hj⟩ := hG
          exact ⟨j, mem_filter.2 ⟨mem_univ _, hj⟩⟩
        set lo := (univ.filter fun j => ¬ z < pL j).sup' hGne xL with hlo
        obtain ⟨j₀, hj₀G, hj₀⟩ := Finset.exists_mem_eq_sup' hGne xL
        rw [← hlo] at hj₀
        have hk2 : ∀ j, ¬ z < pL j → xL j ≤ lo := fun j h =>
          Finset.le_sup' (s := univ.filter fun j => ¬ z < pL j) xL (mem_filter.2 ⟨mem_univ j, h⟩)
        have hj₀z : ¬ z < pL j₀ := (mem_filter.1 hj₀G).2
        have hlohi : lo < hi := by rw [hj₀]; exact hsep j₀ hj₀z
        have hloa : lo < a := by
          by_contra hcon
          have h := hanti (hxL0 j₀) (show a ≤ xL j₀ from hj₀ ▸ not_lt.1 hcon)
          exact hj₀z (hza.trans_le h)
        obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps (lt_min hlohi hloa)
        have hyhi : y < hi := hy2.trans_le (min_le_left _ _)
        exact ⟨y, hy2.trans_le (min_le_right _ _), hyJ, hcy y (hyhi.trans_le hhi0) hyJ
          (hiff y (fun j hj => (hk2 j hj).trans_lt hy1) hyhi)⟩
      · simp only [not_exists, not_not] at hG
        obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps
          (show min hi a - 1 < min hi a by linarith)
        have hyhi : y < hi := hy2.trans_le (min_le_left _ _)
        exact ⟨y, hy2.trans_le (min_le_right _ _), hyJ, hcy y (hyhi.trans_le hhi0) hyJ
          (hiff y (fun j hj => absurd (hG j) hj) hyhi)⟩
  · -- no label image right of `z`: the piece's left side
    simp only [not_exists] at hF
    have hside : (stopWord κ (c, θ, r)).fn z = -sleLambda κ - θ * chiC κ := by
      rw [hfn, Finset.filter_false_of_mem fun i _ => hF i, Finset.sum_empty]
      ring
    refine ⟨fun _ => Or.inl hside, fun hza => ?_⟩
    have h0 : pL ⟨0, hz0⟩ = markPosL w T 0 := rfl
    exact absurd (hza.trans_le ((hanti le_rfl ha).trans h0.symm.le)) (hF ⟨0, hz0⟩)

/-- **The heights right of a stopped piece** (relative to a reference point `b ≥ 0` of the earlier word). -/
theorem fn_stopWord_right {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {b z : ℝ} (hb0 : 0 ≤ b)
    (hz : 0 < z) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps) :
    (z < markPos (rdrv r) (rtime r) b →
      (stopWord κ (c, θ, r)).fn z = sleLambda κ - θ * chiC κ ∨
        ∃ y, 0 < y ∧ y < b ∧ y ∉ c.jumps ∧ (stopWord κ (c, θ, r)).fn z = c.fn y) ∧
    (markPos (rdrv r) (rtime r) b < z → ∃ y, b < y ∧ y ∉ c.jumps ∧ (stopWord κ (c, θ, r)).fn z = c.fn y) := by
  classical
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT := rtime_nonneg r
  have hb := c.isPiecewiseConstantBoundaryData
  set w := rdrv r with hwdef
  set T := rtime r with hTdef
  set xR := flowLineXR c.fn c.jumps 0 with hxRdef
  set ρR := flowLineRhoR κ c.fn c.jumps 0 θ with hρRdef
  set pR : Fin (flowLineNR c.fn c.jumps 0) → ℝ := fun j => markPos w T (xR j) with hpR
  have hxR0 : ∀ j, 0 ≤ xR j := fun j => GW3Word.flowLineXR_nonneg c.fn c.jumps j
  have hmono : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → markPos w T u ≤ markPos w T v := fun hu huv =>
    markPos_mono hw hw0 hT hu huv
  have hfn : (stopWord κ (c, θ, r)).fn z =
      sleLambda κ * (1 + ∑ j ∈ univ.filter (fun j => pR j ≤ z), ρR j) - θ * chiC κ := by
    have h := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ)
      (isMarkOrder_stopWord c r) hzJ hz.ne'
    refine h.trans ?_
    rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hz.le]
    simp only [padFL_fst_snd_fin, padFL_snd_snd_fin, hpR, hρRdef, hxRdef, hwdef, hTdef]
  have hcy : ∀ y, 0 < y → y ∉ c.jumps → (∀ j, xR j ≤ y ↔ pR j ≤ z) → (stopWord κ (c, θ, r)).fn z = c.fn y := by
    intro y hy hyJ hiff
    have h1 := Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hy.ne' (by simpa using hyJ)
    rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hy.le, add_zero] at h1
    rw [hfn, Finset.filter_congr fun j _ => (hiff j).symm]
    linarith
  have hz0 : 0 < flowLineNR c.fn c.jumps 0 := Supp8.GB6.zero_lt_flowLineNR _ _
  have h0 : pR ⟨0, hz0⟩ = markPos w T 0 := rfl
  by_cases hG : ∃ j, pR j ≤ z
  · have hGne : (univ.filter fun j => pR j ≤ z).Nonempty := by
      obtain ⟨j, hj⟩ := hG
      exact ⟨j, mem_filter.2 ⟨mem_univ _, hj⟩⟩
    set lo := (univ.filter fun j => pR j ≤ z).sup' hGne xR with hlo
    obtain ⟨j₀, hj₀G, hj₀⟩ := Finset.exists_mem_eq_sup' hGne xR
    rw [← hlo] at hj₀
    have hj₀z : pR j₀ ≤ z := (mem_filter.1 hj₀G).2
    have hk1 : ∀ j, pR j ≤ z → xR j ≤ lo := fun j h =>
      Finset.le_sup' (s := univ.filter fun j => pR j ≤ z) xR (mem_filter.2 ⟨mem_univ j, h⟩)
    have hlo0 : 0 ≤ lo := (hxR0 j₀).trans hj₀.symm.le
    have hsep : ∀ j, ¬ pR j ≤ z → lo < xR j := by
      intro j hj
      by_contra hcon
      have h := hmono (hxR0 j) (show xR j ≤ xR j₀ from hj₀ ▸ not_lt.1 hcon)
      exact hj (h.trans hj₀z)
    have hiff : ∀ y, lo < y → (∀ j, ¬ pR j ≤ z → y < xR j) → ∀ j, xR j ≤ y ↔ pR j ≤ z := by
      intro y hloy hhi j
      refine ⟨fun h => ?_, fun h => (hk1 j h).trans hloy.le⟩
      by_contra hn
      exact absurd h (not_le.2 (hhi j hn))
    refine ⟨fun hzb => Or.inr ?_, fun hzb => ?_⟩
    · -- `z` left of the image of `b`: a preimage point in `(0, b)`
      have hlob : lo < b := by
        by_contra hcon
        have h := hmono hb0 (show b ≤ xR j₀ from hj₀ ▸ not_lt.1 hcon)
        exact absurd (hzb.trans_le h) (not_lt.2 hj₀z)
      by_cases hH : ∃ j, ¬ pR j ≤ z
      · have hHne : (univ.filter fun j => ¬ pR j ≤ z).Nonempty := by
          obtain ⟨j, hj⟩ := hH
          exact ⟨j, mem_filter.2 ⟨mem_univ _, hj⟩⟩
        set hi := (univ.filter fun j => ¬ pR j ≤ z).inf' hHne xR with hhi
        obtain ⟨j₁, hj₁H, hj₁⟩ := Finset.exists_mem_eq_inf' hHne xR
        rw [← hhi] at hj₁
        have hk2 : ∀ j, ¬ pR j ≤ z → hi ≤ xR j := fun j h =>
          Finset.inf'_le (s := univ.filter fun j => ¬ pR j ≤ z) xR (mem_filter.2 ⟨mem_univ j, h⟩)
        have hlohi : lo < hi := by rw [hj₁]; exact hsep j₁ (mem_filter.1 hj₁H).2
        obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps (lt_min hlohi hlob)
        exact ⟨y, hlo0.trans_lt hy1, hy2.trans_le (min_le_right _ _), hyJ, hcy y (hlo0.trans_lt hy1) hyJ
          (hiff y hy1 fun j hj => (hy2.trans_le (min_le_left _ _)).trans_le (hk2 j hj))⟩
      · simp only [not_exists, not_not] at hH
        obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps hlob
        exact ⟨y, hlo0.trans_lt hy1, hy2, hyJ, hcy y (hlo0.trans_lt hy1) hyJ
          (hiff y hy1 fun j hj => absurd (hH j) hj)⟩
    · -- `z` right of the image of `b`: a preimage point right of `b`
      by_cases hH : ∃ j, ¬ pR j ≤ z
      · have hHne : (univ.filter fun j => ¬ pR j ≤ z).Nonempty := by
          obtain ⟨j, hj⟩ := hH
          exact ⟨j, mem_filter.2 ⟨mem_univ _, hj⟩⟩
        set hi := (univ.filter fun j => ¬ pR j ≤ z).inf' hHne xR with hhi
        obtain ⟨j₁, hj₁H, hj₁⟩ := Finset.exists_mem_eq_inf' hHne xR
        rw [← hhi] at hj₁
        have hj₁z : ¬ pR j₁ ≤ z := (mem_filter.1 hj₁H).2
        have hk2 : ∀ j, ¬ pR j ≤ z → hi ≤ xR j := fun j h =>
          Finset.inf'_le (s := univ.filter fun j => ¬ pR j ≤ z) xR (mem_filter.2 ⟨mem_univ j, h⟩)
        have hlohi : lo < hi := by rw [hj₁]; exact hsep j₁ hj₁z
        have hbhi : b < hi := by
          by_contra hcon
          have h := hmono (hxR0 j₁) (show xR j₁ ≤ b from hj₁ ▸ not_lt.1 hcon)
          exact hj₁z (h.trans hzb.le)
        obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps (max_lt hlohi hbhi)
        have hloy : lo < y := (le_max_left _ _).trans_lt hy1
        exact ⟨y, (le_max_right _ _).trans_lt hy1, hyJ, hcy y (hlo0.trans_lt hloy) hyJ
          (hiff y hloy fun j hj => hy2.trans_le (hk2 j hj))⟩
      · simp only [not_exists, not_not] at hH
        obtain ⟨y, hy1, hy2, hyJ⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps
          (show max lo b < max lo b + 1 by linarith)
        have hloy : lo < y := (le_max_left _ _).trans_lt hy1
        exact ⟨y, (le_max_right _ _).trans_lt hy1, hyJ, hcy y (hlo0.trans_lt hloy) hyJ
          (hiff y hloy fun j hj => absurd (hH j) hj)⟩
  · -- no label image left of `z`: the piece's right side
    simp only [not_exists, not_le] at hG
    have hside : (stopWord κ (c, θ, r)).fn z = sleLambda κ - θ * chiC κ := by
      rw [hfn, Finset.filter_false_of_mem fun j _ => not_le.2 (hG j), Finset.sum_empty]
      ring
    refine ⟨fun _ => Or.inl hside, fun hzb => ?_⟩
    exact absurd ((hmono le_rfl hb0).trans_lt hzb) (not_lt.2 (h0 ▸ (hG ⟨0, hz0⟩)).le)

end InteractingSLE.Theorem14.GW2Sdp
