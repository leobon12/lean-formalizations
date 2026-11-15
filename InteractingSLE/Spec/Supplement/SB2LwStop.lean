/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveWord

/-!
# SB2(2)'s word: the stop word of one upper piece, seen from the lower flow

Packet PROVE-T14-SB2LOW (ruling R99). Lemma SB2's second assertion (supplement p. 632, `source/spec/p625-671.md`
L141): "If the erased upper history has an old right side of angle `ψ_j`, its height is `λ − ψ_jχ` [...] On an exposed
old upper-left side [...] All these old groups are admissible." The conditional word after an ordinary piece of angle
`θ` is PROVE-STAGEDLAW3's stop word `stopWord κ (c, θ, record)`. This file proves the deterministic facts about it that
the upper schedule's word recursion uses:

* **`exists_alive_eq_of_markPos_lt`**: every real point right of the image `markPos w T 0` of the seed's right side is
  the image of an alive positive point (intermediate values of the real flow);
* **`stopWord_fn_pos_cases`**: right of the tip the stop word is the new right-side height `λ − θχ`, or the point lies
  right of `markPos w T 0` (hence is the image of an alive point, where `GW1W.stopWord_fn_fwdMap` applies);
* **`stopWord_fn_neg_mem`**: left of the tip every height of the stop word is the new left-side height `−λ − θχ` or a
  height of the launch word at some negative point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

namespace InteractingSLE.Theorem14.SB.Lh

open Exist Exist.StagedLaw Exist.Staged Restart GW1Conn GW1W

section Flow

variable {w : ℝ → ℝ} {T : ℝ}

/-- **Intermediate values of the real flow**: a real point right of `markPos w T 0` (the image of the seed's right
side) is the image of an alive positive point. -/
theorem exists_alive_eq_of_markPos_lt (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {y : ℝ}
    (hy : markPos w T 0 < y) :
    ∃ y₀ : ℝ, 0 < y₀ ∧ (∃ u, IsForwardSol w (y₀ : ℂ) T u) ∧ (fwdMap w T y₀).re = y := by
  have hH := isRealHalf_of hw hw0 hT
  have hq : ∃ q : ℚ, (0 : ℝ) < q ∧ (∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u) ∧
      (fwdMap w T ((q : ℝ) : ℂ)).re < y := by
    by_contra hno
    push Not at hno
    have := le_markPos hw hw0 hT (x := 0) (c := y) fun q hq hal => hno q hq hal
    linarith
  obtain ⟨q, hq0, hqA, hqy⟩ := hq
  obtain ⟨N, hN⟩ := hH.2.2.2.2.2.2 (y + 1)
  set z : ℝ := max N q + 1 with hz
  have hqz : (q : ℝ) < z := by have := le_max_right N (q : ℝ); linarith
  have hzA : ∃ u, IsForwardSol w (z : ℂ) T u := hH.2.1 q z hq0 hqz hqA
  have hfz : y + 1 ≤ (fwdMap w T z).re := hN z (by have := le_max_left N (q : ℝ); linarith) hzA
  have hA : ∀ x ∈ Icc (q : ℝ) z, ∃ u, IsForwardSol w (x : ℂ) T u := fun x hx => by
    rcases hx.1.lt_or_eq with h | h
    · exact hH.2.1 q x hq0 h hqA
    · rw [← h]; exact hqA
  have hcont : ContinuousOn (fun x : ℝ => (fwdMap w T x).re) (Icc (q : ℝ) z) := by
    intro x hx
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨η, hη, hf⟩ := hH.2.2.2.2.2.1 x (lt_of_lt_of_le hq0 hx.1) (hA x hx) ε hε
    refine ⟨η, hη, fun x' hx' hd => ?_⟩
    rw [Real.dist_eq] at hd ⊢
    exact hf x' (hA x' hx') hd
  obtain ⟨y₀, hy₀, he⟩ := intermediate_value_Icc hqz.le hcont ⟨hqy.le, by linarith⟩
  exact ⟨y₀, lt_of_lt_of_le hq0 hy₀.1, hA y₀ hy₀, he⟩

end Flow

section StopWord

variable {κ : ℝ}

/-- The first right position of the padded flow-line word is the seed `0`. -/
theorem padFL_fst_snd_zero (b : ℝ → ℝ) (J : Finset ℝ) : (padFL 0 0 b J).1.2 0 = 0 := by
  have hpos : 0 < flowLineNR b J 0 := by unfold flowLineNR; omega
  have h := padFL_fst_snd_fin b J ⟨0, hpos⟩
  exact h.trans rfl

/-- **Right of the tip**, the stop word is the new right-side height `λ − θχ`, or the point lies right of the image
`markPos` of the seed's right side. -/
theorem stopWord_fn_pos_cases (c : BoundaryWord) (θ : ℝ) (r : RecData) {y : ℝ} (hy : 0 < y) :
    (stopWord κ (c, θ, r)).fn y = sleLambda κ - θ * chiC κ ∨ markPos (rdrv r) (rtime r) 0 < y := by
  have hmo := isMarkOrder_stopWord c r
  set nL := flowLineNL c.fn c.jumps 0 with hnL
  set nR := flowLineNR c.fn c.jumps 0 with hnR
  set pL : ℕ → ℝ := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) with hpL
  set pR : ℕ → ℝ := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) with hpR
  set ρL := (padFL κ θ c.fn c.jumps).2.1 with hρL
  set ρR := (padFL κ θ c.fn c.jumps).2.2 with hρR
  have hW : stopWord κ (c, θ, r) = forceWord κ nL nR pL pR ρL ρR (θ * chiC κ) := rfl
  rw [hW]
  have hk := le_index_forceWord_of_pos (κ := κ) (nR := nR) (pR := pR) (ρL := ρL) (ρR := ρR)
    (s := θ * chiC κ) hmo.2.1 hy
  rcases Nat.lt_or_ge ((forceWord κ nL nR pL pR ρL ρR (θ * chiC κ)).index y) (nL + 2) with hlt | hge
  · left
    have he : (forceWord κ nL nR pL pR ρL ρR (θ * chiC κ)).index y = nL + 1 := by omega
    change wordHeight κ nL ρL ρR (θ * chiC κ) ((forceWord κ nL nR pL pR ρL ρR (θ * chiC κ)).index y) = _
    rw [he]
    unfold wordHeight
    simp only [show ¬ nL + 1 ≤ nL by omega, ↓reduceIte, show nL + 1 - nL - 1 = 0 by omega, Finset.range_zero,
      Finset.sum_empty, add_zero, mul_one]
    rfl
  · right
    have h1 : cumMax (rawPos nL pL pR) (nL + 1) < y := by
      by_contra hn
      push Not at hn
      have : (forceWord κ nL nR pL pR ρL ρR (θ * chiC κ)).index y ≤ nL + 1 := by
        unfold BoundaryWord.index
        change ((Finset.range (nL + 1 + nR)).filter fun i => cumMax (rawPos nL pL pR) i < y).card ≤ nL + 1
        calc ((Finset.range (nL + 1 + nR)).filter fun i => cumMax (rawPos nL pL pR) i < y).card
            ≤ (Finset.range (nL + 1)).card := by
              refine Finset.card_le_card fun i hi => ?_
              rw [Finset.mem_filter] at hi
              rw [Finset.mem_range]
              by_contra hi'
              have := monotone_cumMax (rawPos nL pL pR) (show nL + 1 ≤ i by omega)
              linarith [hi.2]
          _ = nL + 1 := Finset.card_range _
      omega
    have h2 : rawPos nL pL pR (nL + 1) = pR 0 := by
      unfold rawPos
      simp only [show ¬ nL + 1 < nL by omega, show nL + 1 ≠ nL by omega, ↓reduceIte,
        show nL + 1 - nL - 1 = 0 by omega]
    have h3 := le_cumMax (rawPos nL pL pR) (nL + 1)
    rw [h2] at h3
    have h4 : pR 0 = markPos (rdrv r) (rtime r) 0 := by
      simp only [hpR, padFL_fst_snd_zero]
    linarith

/-- **Left of the tip**, every height of the stop word is the new left-side height `−λ − θχ` or a height of the
launch word at a negative point (the left partial sums of the flow-line word are the original left heights). -/
theorem stopWord_fn_neg_mem (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {y : ℝ} (hy : y < 0) :
    (stopWord κ (c, θ, r)).fn y = -sleLambda κ - θ * chiC κ ∨
      ∃ x < 0, x ∉ c.jumps ∧ (stopWord κ (c, θ, r)).fn y = c.fn x := by
  obtain ⟨m, hm, he⟩ := exists_fn_forceWord_of_neg (κ := κ) (nL := flowLineNL c.fn c.jumps 0)
    (nR := flowLineNR c.fn c.jumps 0)
    (pL := fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
    (pR := fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))
    (ρL := (padFL κ θ c.fn c.jumps).2.1) (ρR := (padFL κ θ c.fn c.jumps).2.2) (s := θ * chiC κ) hy
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  have hW : stopWord κ (c, θ, r) = forceWord κ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0)
      (fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))
      (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) := rfl
  rw [hW, he]
  rcases m with _ | j
  · left
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, mul_one]
    rfl
  · right
    have hj : j < flowLineNL c.fn c.jumps 0 := by omega
    rw [sum_range_padFL_left κ θ c hj]
    have hsum : ∑ l ∈ univ.filter (fun l => l ≤ (⟨j, hj⟩ : Fin (flowLineNL c.fn c.jumps 0))),
        flowLineRhoL κ c.fn c.jumps 0 θ l =
        ∑ l ∈ univ.filter (fun l => l ≤ (⟨j, hj⟩ : Fin (flowLineNL c.fn c.jumps 0))),
          flowLineRhoL κ c.fn c.jumps 0 0 l - θ * chiC κ / sleLambda κ := by
      rw [Finset.sum_congr rfl (fun l _ => flowLineRhoL_theta κ c.fn c.jumps θ l), Finset.sum_add_distrib,
        sum_filter_le_ite_val_eq_zero _ _ ⟨0, by unfold flowLineNL; omega⟩ rfl]
      ring
    rw [hsum, GW3Word.filter_le_eq_filter_le_flowLineXL]
    obtain ⟨x, -, hx, hxJ, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoL_eq hκ c.isPiecewiseConstantBoundaryData
      (lo := flowLineXL c.fn c.jumps 0 ⟨j, hj⟩ - 1) (by linarith) (GW3Word.flowLineXL_nonpos c.fn c.jumps ⟨j, hj⟩)
    refine ⟨x, lt_of_lt_of_le hx (GW3Word.flowLineXL_nonpos _ _ _), hxJ, ?_⟩
    rw [hS, Sec4.cumWeightLeft]
    change -sleLambda κ * (1 + (-c.fn x / sleLambda κ - 1 - θ * chiC κ / sleLambda κ)) - θ * chiC κ = c.fn x
    field_simp
    ring

end StopWord

end InteractingSLE.Theorem14.SB.Lh
