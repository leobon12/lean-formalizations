/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripDetStage
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal

/-!
# (4.4) for the word of a restarted flow line

Packet PROVE-STRIPSYS21, item (i). Specification §7.4, proof of Aux. lemma 130 (p. 410): after the first piece of the
angle-varying path, run at angle `θ₀`, "the continuation's word satisfies (4.4)": its left seed total is `−δχ/λ`, its
right seed total `δχ/λ` (`δ = θ − θ₀`), and the original totals are unchanged. In Lean the word of the conditional
field after a stopped piece is PROVE-STAGEDLAW's `Exist.StagedLaw.stopWord κ (c, θ₀, r)` (the sorted force word of the
angle-`θ₀` flow line of `c` at the mark images read from the record `r`, shifted by `−θ₀χ`). This file proves:

* **`markPos_nonneg`**, **`markPosL_nonpos`**: the images of right (left) marks lie right (left) of the tip;
* **`cond44_flowLine_stopWord`**: if `c + θχ ≤ −λ + πχ` left of `0` and `c + θχ ≥ λ` right of `0` (off the jumps; the
  (4.4) form of the boundary heights of `c` at angle `θ`) and `θ₀ ≤ θ ≤ θ₀ + π`, the angle-`θ` flow-line word of
  `stopWord κ (c, θ₀, r)` satisfies (4.4), for **every** record `r`.

Proof: off its jumps, the stop word's height at `y` is a height of the force data of `c`'s flow word with some prefix of
its weights; the empty prefixes give the two sides of the piece (`−λ − θ₀χ` left of the tip, `λ − θ₀χ` right of it),
the others are heights of `c` plus `θ₀χ` (strictly ordered positions, `exists_left_point`), so adding `θχ` gives the
hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace StripDet

open Sec4 QuantumZipper Restart Exist Exist.Staged Exist.StagedLaw

/-! ### Mark images lie on their side of the tip -/

/-- **The image of a right mark lies right of the tip.** -/
theorem markPos_nonneg {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T x : ℝ} (hT : 0 ≤ T) (hx : 0 ≤ x) :
    0 ≤ markPos w T x := by
  unfold markPos
  refine EReal.toReal_nonneg (le_iInf fun q => ?_)
  unfold markTerm
  split_ifs with hq
  · obtain ⟨hxq, u, hu⟩ := hq
    exact EReal.coe_nonneg.2 (re_fwdMap_pos hw hw0 (hx.trans_lt hxq) hu ⟨hT, le_rfl⟩).le
  · exact le_top

/-- **The image of a left mark lies left of the tip.** -/
theorem markPosL_nonpos {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T x : ℝ} (hT : 0 ≤ T) (hx : x ≤ 0) :
    markPosL w T x ≤ 0 := by
  unfold markPosL
  have := markPos_nonneg (w := fun s => -w s) hw.neg (by simp [hw0]) hT (neg_nonneg.2 hx)
  linarith

theorem rdrv_zero (r : RecData) : rdrv r 0 = 0 := by
  simp only [rdrv, Real.toNNReal_zero]
  exact LocalExt.histDrv_zero _

theorem rtime_nonneg (r : RecData) : 0 ≤ rtime r := (r.2.1.toNNReal).2

/-! ### Points with a prescribed prefix of marks -/

/-- A point left of `0`, off a finite set, with exactly the first `j` left marks right of it. -/
theorem exists_left_point {n : ℕ} {xL : Fin n → ℝ} (hxL : StrictAnti xL) (hxL0 : ∀ i, xL i ≤ 0) (E : Finset ℝ)
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∃ x, x < 0 ∧ x ∉ E ∧ univ.filter (fun i => x < xL i) = univ.filter (fun i : Fin n => i.val < j) := by
  set i₀ : Fin n := ⟨j - 1, by omega⟩ with hi₀
  obtain ⟨a, hau, ha⟩ : ∃ a, a < xL i₀ ∧ ∀ i : Fin n, j ≤ i.val → xL i ≤ a := by
    by_cases hj : j < n
    · exact ⟨xL ⟨j, hj⟩, hxL (Fin.mk_lt_mk.2 (by omega)), fun i hi => hxL.antitone (Fin.mk_le_mk.2 hi)⟩
    · exact ⟨xL i₀ - 1, by linarith, fun i hi => absurd i.isLt (by omega)⟩
  obtain ⟨x, hax, hxu, hxE⟩ := exists_mem_Ioo_not_mem E hau
  refine ⟨x, hxu.trans_le (hxL0 i₀), hxE, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hc
    exact absurd (ha i (not_lt.1 hc)) (not_le.2 (hax.trans h))
  · intro h
    exact hxu.trans_le (hxL.antitone (Fin.mk_le_mk.2 (by omega)))

/-- A point right of `0`, off a finite set, with exactly the first `j` right marks left of it (or on it). -/
theorem exists_right_point {n : ℕ} {xR : Fin n → ℝ} (hxR : StrictMono xR) (hxR0 : ∀ i, 0 ≤ xR i) (E : Finset ℝ)
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ∃ x, 0 < x ∧ x ∉ E ∧ univ.filter (fun i => xR i ≤ x) = univ.filter (fun i : Fin n => i.val < j) := by
  set i₀ : Fin n := ⟨j - 1, by omega⟩ with hi₀
  obtain ⟨u, hlu, hu⟩ : ∃ u, xR i₀ < u ∧ ∀ i : Fin n, j ≤ i.val → u ≤ xR i := by
    by_cases hj : j < n
    · exact ⟨xR ⟨j, hj⟩, hxR (Fin.mk_lt_mk.2 (by omega)), fun i hi => hxR.monotone (Fin.mk_le_mk.2 hi)⟩
    · exact ⟨xR i₀ + 1, by linarith, fun i hi => absurd i.isLt (by omega)⟩
  obtain ⟨x, hlx, hxu, hxE⟩ := exists_mem_Ioo_not_mem E hlu
  refine ⟨x, (hxR0 i₀).trans_lt hlx, hxE, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hc
    exact absurd (hu i (not_lt.1 hc)) (not_le.2 (h.trans_lt hxu))
  · intro h
    exact (hxR.monotone (Fin.mk_le_mk.2 (by omega) : i ≤ i₀)).trans hlx.le

/-- A prefix sum of padded weights is a prefix sum over `Fin n`. -/
theorem sum_range_pad {n j : ℕ} (hj : j ≤ n) (f : Fin n → ℝ) :
    ∑ i ∈ Finset.range j, (if hi : i < n then f ⟨i, hi⟩ else 0) =
      ∑ i ∈ univ.filter (fun i : Fin n => i.val < j), f i := by
  rw [Finset.sum_filter]
  have e : ∀ i : Fin n, (if i.val < j then f i else 0) =
      (fun k : ℕ => if k < j then (if hk : k < n then f ⟨k, hk⟩ else 0) else 0) i.val := fun i => by
    simp only [i.isLt, ↓reduceDIte, Fin.eta]
  rw [Finset.sum_congr rfl fun i _ => e i, Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k < j then (if hk : k < n then f ⟨k, hk⟩ else 0) else 0) n, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The cumulative maximum of a sequence that is nonpositive up to `k` is nonpositive at `k`. -/
theorem cumMax_nonpos {f : ℕ → ℝ} : ∀ {k : ℕ}, (∀ i ≤ k, f i ≤ 0) → cumMax f k ≤ 0
  | 0, h => h 0 le_rfl
  | k + 1, h => max_le (cumMax_nonpos fun i hi => h i (by omega)) (h (k + 1) le_rfl)

/-! ### (4.4) for the restarted word -/

/-- **(4.4) for the word of a restarted flow line** (spec p. 410). If the boundary word `c` has (4.4) heights at
angle `θ` (`c + θχ ≤ −λ + πχ` left of `0`, `c + θχ ≥ λ` right of `0`, off its jumps) and `θ₀ ≤ θ ≤ θ₀ + π`, then for
every record `r` of a stopped angle-`θ₀` piece, the angle-`θ` flow-line word of the stop word `stopWord κ (c, θ₀, r)`
satisfies (4.4). -/
theorem cond44_flowLine_stopWord {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : BoundaryWord) (θ₀ θ : ℝ) (r : RecData)
    (hθ : θ₀ ≤ θ) (hθπ : θ ≤ θ₀ + Real.pi)
    (hL : ∀ y : ℝ, y < 0 → y ∉ c.jumps → c.fn y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ c.jumps → sleLambda κ ≤ c.fn y + θ * chiC κ) :
    Cond44 κ (flowLineRhoL κ (stopWord κ (c, θ₀, r)).fn (stopWord κ (c, θ₀, r)).jumps 0 θ)
      (flowLineRhoR κ (stopWord κ (c, θ₀, r)).fn (stopWord κ (c, θ₀, r)).jumps 0 θ) := by
  have hχ := chiC_pos hκ hκ4
  have hl := sleLambda_pos hκ
  have hlam : Real.pi / Real.sqrt κ = sleLambda κ := rfl
  have hc := c.isPiecewiseConstantBoundaryData
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  set nL := flowLineNL c.fn c.jumps 0 with hnL
  set nR := flowLineNR c.fn c.jumps 0 with hnR
  set pL : ℕ → ℝ := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) with hpL
  set pR : ℕ → ℝ := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) with hpR
  set ρL := (padFL κ θ₀ c.fn c.jumps).2.1 with hρL
  set ρR := (padFL κ θ₀ c.fn c.jumps).2.2 with hρR
  have hsw : stopWord κ (c, θ₀, r) = forceWord κ nL nR pL pR ρL ρR (θ₀ * chiC κ) := rfl
  -- the left marks have nonpositive images
  have hpL0 : ∀ i, pL i ≤ 0 := by
    intro i
    refine markPosL_nonpos (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) ?_
    show (if hi : i < nL then flowLineXL c.fn c.jumps 0 ⟨i, hi⟩ else 0) ≤ 0
    split_ifs
    · exact hF.2.1 _
    · exact le_rfl
  have hraw : rawPos nL pL pR nL = 0 := by simp [rawPos]
  -- the heights of `c`'s flow word at angle `θ₀`
  have hleft : ∀ j, 1 ≤ j → j ≤ nL → ∃ x, x < 0 ∧ x ∉ c.jumps ∧
      -sleLambda κ * (1 + ∑ i ∈ Finset.range j, ρL i) = c.fn x + θ₀ * chiC κ := by
    intro j hj1 hjn
    obtain ⟨x, hx0, hxE, hS⟩ := exists_left_point (strictAnti_flowLineXL c.fn c.jumps) hF.2.1
      (insert 0 c.jumps) hj1 hjn
    have hxJ : x ∉ c.jumps := fun h => hxE (Finset.mem_insert_of_mem h)
    refine ⟨x, hx0, hxJ, ?_⟩
    have e1 := forceBoundaryData_of_neg (κ := κ) (flowLineRhoL κ c.fn c.jumps 0 θ₀) (flowLineRhoR κ c.fn c.jumps 0 θ₀)
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) hx0
    rw [Exist.forceBoundaryData_flowLine_seed hκ hc 0 θ₀ hx0.ne (by rwa [add_zero]), add_zero, hS] at e1
    rw [e1, hρL, ← sum_range_pad hjn]
    rfl
  have hright : ∀ j, 1 ≤ j → j ≤ nR → ∃ x, 0 < x ∧ x ∉ c.jumps ∧
      sleLambda κ * (1 + ∑ i ∈ Finset.range j, ρR i) = c.fn x + θ₀ * chiC κ := by
    intro j hj1 hjn
    obtain ⟨x, hx0, hxE, hS⟩ := exists_right_point (strictMono_flowLineXR c.fn c.jumps) hF.2.2.2
      (insert 0 c.jumps) hj1 hjn
    have hxJ : x ∉ c.jumps := fun h => hxE (Finset.mem_insert_of_mem h)
    refine ⟨x, hx0, hxJ, ?_⟩
    have e1 := forceBoundaryData_of_nonneg (κ := κ) (flowLineRhoL κ c.fn c.jumps 0 θ₀)
      (flowLineRhoR κ c.fn c.jumps 0 θ₀) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) hx0.le
    rw [Exist.forceBoundaryData_flowLine_seed hκ hc 0 θ₀ hx0.ne' (by rwa [add_zero]), add_zero, hS] at e1
    rw [e1, hρR, ← sum_range_pad hjn]
    rfl
  refine cond44_flowLine_of_heights hκ (stopWord κ (c, θ₀, r)).isPiecewiseConstantBoundaryData θ
    (fun y hy _ => ?_) (fun y hy _ => ?_)
  · -- left of the tip: at most `nL` sorted positions lie left of `y`
    set m := ((Finset.range (nL + 1 + nR)).filter fun k => cumMax (rawPos nL pL pR) k < y).card with hm
    have hfn : (stopWord κ (c, θ₀, r)).fn y = wordHeight κ nL ρL ρR (θ₀ * chiC κ) m := by rw [hsw]; rfl
    have hmle : m ≤ nL := by
      have hsub : (Finset.range (nL + 1 + nR)).filter (fun k => cumMax (rawPos nL pL pR) k < y) ⊆
          Finset.range nL := by
        intro k hk
        rw [Finset.mem_filter, Finset.mem_range] at hk
        rw [Finset.mem_range]
        by_contra hkn
        have h1 : rawPos nL pL pR nL ≤ cumMax (rawPos nL pL pR) k :=
          (le_cumMax _ nL).trans (monotone_cumMax _ (not_lt.1 hkn))
        rw [hraw] at h1
        linarith [hk.2]
      calc m ≤ (Finset.range nL).card := Finset.card_le_card hsub
        _ = nL := Finset.card_range nL
    have hwh : wordHeight κ nL ρL ρR (θ₀ * chiC κ) m =
        -sleLambda κ * (1 + ∑ i ∈ Finset.range (nL - m), ρL i) - θ₀ * chiC κ := by
      simp only [wordHeight, hmle, ↓reduceIte, hlam]
    rw [hfn, hwh]
    rcases Nat.eq_zero_or_pos (nL - m) with h0 | hpos
    · rw [h0, Finset.range_zero, Finset.sum_empty]
      nlinarith
    · obtain ⟨x, hx0, hxJ, hx⟩ := hleft (nL - m) hpos (Nat.sub_le _ _)
      have := hL x hx0 hxJ
      linarith
  · -- right of the tip: every left position and the tip lie left of `y`
    set m := ((Finset.range (nL + 1 + nR)).filter fun k => cumMax (rawPos nL pL pR) k < y).card with hm
    have hfn : (stopWord κ (c, θ₀, r)).fn y = wordHeight κ nL ρL ρR (θ₀ * chiC κ) m := by rw [hsw]; rfl
    have hcum : cumMax (rawPos nL pL pR) nL ≤ 0 := by
      refine cumMax_nonpos fun i hi => ?_
      unfold rawPos
      split_ifs
      · exact hpL0 _
      · exact le_rfl
      · omega
    have hmge : nL + 1 ≤ m := by
      have hsub : Finset.range (nL + 1) ⊆
          (Finset.range (nL + 1 + nR)).filter (fun k => cumMax (rawPos nL pL pR) k < y) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, ((monotone_cumMax _ (by omega : k ≤ nL)).trans hcum).trans_lt hy⟩
      calc nL + 1 = (Finset.range (nL + 1)).card := (Finset.card_range _).symm
        _ ≤ m := Finset.card_le_card hsub
    have hmle : m ≤ nL + 1 + nR := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    have hwh : wordHeight κ nL ρL ρR (θ₀ * chiC κ) m =
        sleLambda κ * (1 + ∑ i ∈ Finset.range (m - nL - 1), ρR i) - θ₀ * chiC κ := by
      have : ¬ m ≤ nL := by omega
      simp only [wordHeight, this, ↓reduceIte, hlam]
    rw [hfn, hwh]
    rcases Nat.eq_zero_or_pos (m - nL - 1) with h0 | hpos
    · rw [h0, Finset.range_zero, Finset.sum_empty]
      nlinarith
    · obtain ⟨x, hx0, hxJ, hx⟩ := hright (m - nL - 1) hpos (by omega)
      have := hR x hx0 hxJ
      linarith

end StripDet

end Sec7

end InteractingSLE
