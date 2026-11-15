/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LtRun
import InteractingSLE.Spec.Supplement.SB4RTrWalk0

/-!
# SB2(2)'s lockstep induction: the starting stage

Packet PROVE-SB2-LIFTSET (target 1; handoff PROVE-T14-SB2LIFT §R10.2 item 2, §R4.2, §R5.2). The relative lower walk
of SB2(2) (data `b₂`, genuine jumps `J₂`, root `0`) starts with a flow instruction launched from its root. The actual
lower walk `B` (data `b₁`, genuine jumps `J₁`) visits `R = max (A ∩ ℝ)` once ("erase `B` through its unique visit to
`R`", supplement p. 631). The lockstep induction `stCorr_run_of_steps` needs the state correspondence `StCorr ι R`
at a starting stage. This file proves it in the two cases of the visit:

* **`stCorr_start_arc`** (`R` on an actual connector, or `R` the actual threshold point): the actual walk moves right
  from its current point `pt ≤ R` at its connector instruction `n` (odd), with no restart mark in `(pt, R]`; the
  relative walk's first piece has zero lifetime (its lower-angle right seed is immediately unavailable: "It may begin
  with a real interval"), and the outward height at `R` is low, so the relative walk also moves right from `0`. After
  the two connectors the states correspond (relative stage `2` faces actual stage `n + 1`, offset `n − 1`), and the
  first relative connector is the `ι`-image of the part of the actual one right of `R` ("if the erasure endpoint lies
  inside a connector, retain only its remaining part");
* **`stCorr_start_piece`** (`R` on an actual piece): the actual flow instruction `n` (even) launches from a state
  with current point and right record `≤ R`, and the relative walk launches its first piece from the root. With the
  launch observables of the two pieces (the same data as `StepOK`'s flow case, with the root's records `0`), the
  states after the two launches correspond (relative stage `1` faces actual stage `n + 1`, offset `n`).

Supporting lemmas: `run_one_walk` (the relative walk's first state is the launch from the root), `launch_arcs`,
`launch_init_zero` (a zero-lifetime launch from the root: status *thr none* at `0`, record `0`), and
**`rightLim_add_le_of_gap`**: the outward height at `R` is low when it is low at the threshold point `pt ≤ R` and no
restart mark lies in `(pt, R]` (GW1's stage input "the original height just right of the new record is low" at the
threshold gives `hlow` of `stCorr_start_arc`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ}

/-! ### The first steps of a walk -/

/-- A walk program has at least two instructions (a flow and a connector). -/
theorem one_lt_length_boundaryWalkSpec (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) (right : Bool) :
    1 < (boundaryWalkSpec b J θ right).2.2.length := by
  simp only [boundaryWalkSpec, List.length_flatten, List.map_replicate, List.length_cons, List.length_nil,
    List.sum_replicate, smul_eq_mul]
  omega

/-- **The first state of a walk** is the launch of its first piece from the root `0`. -/
theorem run_one_walk (b : ℝ → ℝ) (J : Finset ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ b J (boundaryWalkSpec b J θ true) D 1 = ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤ := by
  rw [run_succ_walk_flow (by have := one_lt_length_boundaryWalkSpec b J θ true; omega) (by norm_num),
    GW1Conn.run_zero]
  rfl

/-- A launch records no connector. -/
theorem launch_arcs (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k d θ t).2.1 = s.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | p | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
  · simp only [ExplState.launch]
    split_ifs <;> rfl

/-- **The relative root with a zero-lifetime first piece**. -/
theorem launch_init_zero {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver d) (h0 : d.2 = 0) :
    stStatus (ExplState.launch (ExplState.init 0) 0 d θ ⊤) = stThr none ∧
      stPt (ExplState.launch (ExplState.init 0) 0 d θ ⊤) = 0 ∧
      stRecR (ExplState.launch (ExplState.init 0) 0 d θ ⊤) = 0 ∧
      stAngle (ExplState.launch (ExplState.init 0) 0 d θ ⊤) = θ ∧
      (ExplState.launch (ExplState.init 0) 0 d θ ⊤).2.1 = [] := by
  have hne : min ⊤ d.2 ≠ ⊤ := by rw [h0]; simp
  obtain ⟨-, hθ, hrec, -, hst, hpt⟩ := launch_eq_of_ne_top (ExplState.init 0) 0 d θ ⊤ hne
  refine ⟨?_, ?_, ?_, hθ, launch_arcs _ _ _ _ _⟩
  · rw [hst]
    unfold lStatus
    simp only [h0, ↓reduceIte]
    rfl
  · rw [hpt]
    unfold lPt
    simp only [h0, ↓reduceIte]
    rfl
  · rw [hrec]
    unfold lRecR
    have hempty : {x : ℝ | stRecR (ExplState.init 0) < x ∧ ¬ lAlive (stChart (ExplState.init 0)) ⊤ d x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx
      refine Lf.lAlive_zero _ hreg h0 ?_
      show ((x : ℂ) - ((0 : ℝ) : ℂ)) ≠ 0
      have : (0 : ℝ) < x := hx
      simpa using this.ne'
    rw [hempty, insert_empty_eq, csSup_singleton]
    rfl


/-! ### The starting stage -/

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ}

/-- **The outward height at `R` is low** when it is low at the current point `pt ≤ R` of a state whose restart
marks all lie beyond `R` (no admissible mark on `(pt, R]`). -/
theorem rightLim_add_le_of_gap (hb : IsPiecewiseConstantBoundaryData b₁ J₁) {s : ExplState}
    (hθ : stAngle s = θ) (hptR : stPt s ≤ R)
    (hlow : rightLim b₁ (stPt s) + θ * chiC κ ≤ -sleLambda κ)
    (hgap : ∀ x ∈ restartSet κ b₁ J₁ s, R < x) :
    rightLim b₁ R + θ * chiC κ ≤ -sleLambda κ := by
  classical
  obtain ⟨hi, hRhi, hconst⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_rightLim hb R
  set w : ℝ := if hC : (restartSet κ b₁ J₁ s).Nonempty then (restartSet κ b₁ J₁ s).min' hC else R + 1 with hw
  have hRw : R < w := by
    rw [hw]
    split_ifs with hC
    · exact hgap _ (Finset.min'_mem _ hC)
    · linarith
  obtain ⟨x, hxI, hxJ⟩ := (Ioo_infinite (lt_min hRhi hRw)).exists_notMem_finset J₁
  have hx1 : R < x := hxI.1
  have hx2 : x < hi := lt_of_lt_of_le hxI.2 (min_le_left _ _)
  have hx3 : x < w := lt_of_lt_of_le hxI.2 (min_le_right _ _)
  have hC : ∀ z ∈ jumpSet b₁ J₁, stPt s < z → z < w → rightLim b₁ z + θ * chiC κ ≤ -sleLambda κ := by
    intro z hz hpz hzw
    by_contra hgt
    push Not at hgt
    have hz' : z ∈ restartSet κ b₁ J₁ s := Finset.mem_filter.2 ⟨hz, hpz, by rw [hθ]; exact hgt⟩
    have hne : (restartSet κ b₁ J₁ s).Nonempty := ⟨z, hz'⟩
    have hmin := (restartSet κ b₁ J₁ s).min'_le z hz'
    simp only [hw, hne, ↓reduceDIte] at hzw
    exact absurd hmin (not_le.2 hzw)
  rcases eq_or_lt_of_le hptR with hpt | hpt
  · rw [← hpt]; exact hlow
  · have hbx := add_le_neg_of_connector hb hlow hC (hpt.trans hx1) hx3 hxJ
    rwa [hconst x ⟨hx1, hx2⟩] at hbx

/-- **The starting stage when `R` lies on an actual connector** (or is the actual threshold point): the actual walk
moves right from its current point `pt ≤ R` at instruction `n` (odd), with no restart mark in `(pt, R]`; the
relative walk's first piece has zero lifetime, and the outward height at `R` is low, so the relative walk moves
right from `0`. After the connectors the states correspond with effective start `R`, and the relative connector
is the `ι`-image of the part of the actual one right of `R`. -/
theorem stCorr_start_arc (h : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (hn : n < (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hodd : n % 2 = 1)
    (hmove : ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) none true =
      if hC : (restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)).Nonempty then
        ExplState.moveAlong (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) true
          ((restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) true)
    (hθ : stAngle (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) = θ)
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≤ R)
    (hgap : ∀ x ∈ restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n), R < x)
    (hlow : rightLim b₁ R + θ * chiC κ ≤ -sleLambda κ)
    (hreg : IsRegularDriver (D₂ 0)) (h0 : (D₂ 0).2 = 0) :
    StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) ∧
      ∃ a : Set ℝ, (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.1 =
          (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n).2.1 ++ [a] ∧
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2).2.1 = [ι '' (a ∩ Ici R)] := by
  set s₁ := ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n with hs₁
  set s₂ := ExplState.launch (ExplState.init 0) 0 (D₂ 0) θ ⊤ with hs₂
  obtain ⟨hst₂, hpt₂, hrec₂, hθ₂, harcs₂⟩ := launch_init_zero (θ := θ) hreg h0
  have h1 : ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1 = s₂ := run_one_walk b₂ J₂ D₂
  have h2 : ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2 = ExplState.contStep κ b₂ J₂ s₂ none true := by
    rw [run_succ_walk_cont (by have := one_lt_length_boundaryWalkSpec b₂ J₂ θ true; omega) (by norm_num), h1]
  have hR0 : ι R = 0 := h.map_base
  have hlow₂ : rightLim b₂ (stPt s₂) + stAngle s₂ * chiC κ ≤ -sleLambda κ := by
    rw [hpt₂, hθ₂, ← hR0, h.rightLim_eq R le_rfl]
    exact hlow
  have hmove₂ := contStep_thr_none_right (κ := κ) b₂ J₂ s₂ hst₂ hlow₂
  have hrun₁ : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1) =
      ExplState.contStep κ b₁ J₁ s₁ none true := run_succ_walk_cont hn hodd
  obtain ⟨c1, c2, c3, c4, a, ha₁, ha₂⟩ := contStep_corr (κ := κ) h (hθ₂.trans hθ.symm) le_rfl hpt
    (by rw [hpt₂, hR0]) hgap (by rw [hrec₂, max_eq_right hrec, hR0]) hmove hmove₂
  rw [hrun₁, h2]
  exact ⟨⟨c1, c2, c3, c4⟩, a, ha₁, by rw [ha₂, harcs₂, List.nil_append]⟩

/-- **The starting stage when `R` lies on an actual piece**: the actual flow instruction `n` (even) launches from a
state (not an interior tip) with current point and right record `≤ R`, and the relative walk's first piece is
launched from its root. Given the launch observables of the two pieces (as in `StepOK`), the states after the two
launches correspond with effective start `R`. -/
theorem stCorr_start_piece (h : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (hlaunch : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1) =
      ExplState.launch (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) n (D₁ n) θ ⊤)
    (htip : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≠ .inr (.inl ()))
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≤ R)
    (hT : (D₂ 0).2 = ⊤ ↔ (D₁ n).2 = ⊤) (h0 : (D₂ 0).2 = 0 ↔ (D₁ n).2 = 0)
    (hR : (∃ x : ℝ, 0 < x ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x) ↔
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)) ⊤ (D₁ n) x)
    (hL₁ : ¬ ∃ x : ℝ, x < stRecL (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ∧
      lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)) ⊤ (D₁ n) x)
    (hL₂ : ¬ ∃ x : ℝ, x < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x)
    (hrec' : (D₁ n).2 ≠ ⊤ → lRecR (ExplState.init 0) ⊤ (D₂ 0) =
      ι (max (lRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ⊤ (D₁ n)) R)) :
    StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) := by
  rw [hlaunch, run_one_walk b₂ J₂ D₂]
  have hR0 : ι R = 0 := h.map_base
  obtain ⟨c1, c2, c3, c4⟩ := launch_corr (s₂ := ExplState.init 0) (p := R) (ι := ι) n 0 htip
    (by intro e; cases e) hT h0 hR hL₁ hL₂ (by rw [max_eq_right hpt, hR0]; rfl)
    (by rw [max_eq_right hrec, hR0]; rfl) hrec'
  exact ⟨c3, c1, c2, c4⟩

end InteractingSLE.Theorem14.SB.Lk
