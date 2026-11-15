/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LpAE
import InteractingSLE.Spec.Supplement.GW1WalkChainRun

/-!
# The future part of a walk after a split (towards the order of the stages along a parametrization)

Packet PROVE-SB2-LIFTSET (round 3). The start bundles of `SB2LpAE` ask that the actual prefix before the stage
through `R` lie on the head `β₀ '' [0, t_L]` of every proper parametrization `β₀`. This needs the order of the walk's
stages, which GW1 controls by two per-step facts (the hypotheses of `GW1WalkChain.walkChainRepresentation_of_
pieceSimpleAt`): each launched piece meets the retained physical part only at its seed (`PieceSimpleAt`), and each
connector clears it (`WalkConnectorClearance`). This file runs them from an arbitrary split stage:

* **`FutPart P q s`**: the physical part of `s` is `P ∪ T`, with `T` preconnected through the seed `q`, meeting `P`
  only at `q`, holding the current point unless `s` is done, and unbounded once `s` is done;
* step lemmas: `futPart_start`, `futPart_add`, `futPart_launch` (finite positive, zero and infinite lifetimes, via
  GW1's arcs and proper curves of a simple piece), `futPart_moveAlong`, `futPart_moveToEnd`, `futPart_setDead`;
* **`futPart_run`**: the invariant along the run from any stage where it holds;
* **`prefix_facts`**: started at `{0}` (`futPart_init`), every prefix of the walk is preconnected and holds its current
  point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1Bookkeep GW1W

/-- **The future part of a walk state after a split at `P`**: the physical part is `P ∪ T`, with `T` preconnected
through the seed `q`, meeting `P` only at `q`, holding the current point unless the walk is done, and unbounded once
it is done. -/
def FutPart (P : Set ℂ) (q : ℂ) (s : ExplState) : Prop :=
  ∃ T : Set ℂ, statePhysicalSet 0 s = P ∪ T ∧ IsPreconnected T ∧ q ∈ T ∧ (∀ z ∈ T, z ∈ P → z = q) ∧
    (stStatus s ≠ stDone → (stPt s : ℂ) ∈ T) ∧ (stStatus s = stDone → ¬ Bornology.IsBounded T)

/-- A proper curve has unbounded range. -/
theorem not_isBounded_range_of_isProperCurve {ρ : ℝ≥0 → ℂ} (hρ : Supp9B.IsProperCurve ρ) :
    ¬ Bornology.IsBounded (range ρ) := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_closedBall 0
  obtain ⟨t, ht⟩ := (hρ.2.2.2.eventually (eventually_gt_atTop M)).exists
  have := hM ⟨t, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

/-- The split starts at any state whose current point is physical. -/
theorem futPart_start {s : ExplState} (hq : (stPt s : ℂ) ∈ statePhysicalSet 0 s) (hnd : stStatus s ≠ stDone) :
    FutPart (statePhysicalSet 0 s) (stPt s) s :=
  ⟨{(stPt s : ℂ)}, (union_eq_left.2 (singleton_subset_iff.2 hq)).symm, isPreconnected_singleton, rfl,
    fun _ hz _ => hz, fun _ => rfl, fun h => absurd h hnd⟩

/-- Adding a preconnected set `S` through the current point that meets the old physical part only there. -/
theorem futPart_add {P : Set ℂ} {q : ℂ} {s s' : ExplState} (h : FutPart P q s) (hnd : stStatus s ≠ stDone)
    {S : Set ℂ} (hset : statePhysicalSet 0 s' = statePhysicalSet 0 s ∪ S) (hS : IsPreconnected S)
    (hpS : (stPt s : ℂ) ∈ S) (hmeet : ∀ z ∈ S, z ∈ statePhysicalSet 0 s → z = stPt s)
    (hpt : stStatus s' ≠ stDone → (stPt s' : ℂ) ∈ S) (hunb : stStatus s' = stDone → ¬ Bornology.IsBounded S) :
    FutPart P q s' := by
  obtain ⟨T, hT, hTc, hqT, hTP, hpT, -⟩ := h
  have hpT' := hpT hnd
  refine ⟨T ∪ S, by rw [hset, hT, union_assoc], hTc.union _ hpT' hpS hS, Or.inl hqT, ?_,
    fun h' => Or.inr (hpt h'), fun h' hb => hunb h' (hb.subset subset_union_right)⟩
  rintro z (hz | hz) hzP
  · exact hTP z hz hzP
  · have hz' := hmeet z hz (by rw [hT]; exact Or.inl hzP)
    exact hTP z (hz' ▸ hpT') hzP


/-- **A launch keeps the future part** (piece simplicity: the new piece meets the old physical part only at its
seed). -/
theorem futPart_launch {P : Set ℂ} {q : ℂ} {s : ExplState} (h : FutPart P q s) (hnd : stStatus s ≠ stDone)
    (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (hP : PieceSimpleAt (stChart s) D.1 D.2 (statePhysicalSet 0 s) (stPt s)
      (stPt (ExplState.launch s k D θ ⊤))) :
    FutPart P q (ExplState.launch s k D θ ⊤) := by
  have hset := GW1WalkChain.statePhysicalSet_launch 0 s k D θ ⊤
  simp only [min_top_left] at hset
  have hmeet := GW1WalkChain.tipSet_inter_of_pieceSimpleAt hP
  by_cases htop : D.2 = ⊤
  · obtain ⟨f, α, ρ, hρ, -, hρ0, -, hρset⟩ := exists_isProperCurve_of_pieceSimpleAt (htop ▸ hP)
    have hdone := (launch_eq_of_top s k D θ ⊤ (by simp only [htop, min_self])).2.2.2.2.1
    have hS : (stChart s).tipSet (fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) D.2 = range ρ := by
      rw [hρset, htop]
    refine futPart_add h hnd (S := range ρ) (by rw [hset, hS]) (isPreconnected_range hρ.1) ⟨0, hρ0⟩
      (fun z hz hzo => ?_) (fun h' => absurd hdone h') (fun _ => not_isBounded_range_of_isProperCurve hρ)
    have : z ∈ (stChart s).tipSet (fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) D.2 ∩ statePhysicalSet 0 s :=
      ⟨hS ▸ hz, hzo⟩
    rw [hmeet] at this
    exact this
  · have hne : min (⊤ : ℝ≥0∞) D.2 ≠ ⊤ := by rw [min_top_left]; exact htop
    have hnd' : stStatus (ExplState.launch s k D θ ⊤) ≠ stDone := by
      obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
      simp only [ExplState.launch, min_top_left, htop, ↓reduceIte, not_top_lt]
      split_ifs <;> try (intro heq; cases heq)
      all_goals (rcases status with _ | _ | _ | _ | _ | _ <;> intro heq <;> cases heq)
    by_cases hzero : D.2 = 0
    · obtain ⟨hZ, hq⟩ := GW1WalkChain.tipSet_zero_of_pieceSimpleAt (hzero ▸ hP)
      refine futPart_add h hnd (S := {(stPt s : ℂ)}) (by rw [hset, hzero, hZ]) isPreconnected_singleton rfl
        (fun z hz _ => hz) (fun _ => by rw [hq]; rfl) (fun h' => absurd h' hnd')
    · set T := D.2.toNNReal with hTdef
      have hT : (T : ℝ≥0∞) = D.2 := ENNReal.coe_toNNReal htop
      have hTpos : 0 < T := by
        apply pos_iff_ne_zero.2
        intro h0
        apply hzero
        rw [← hT, h0, ENNReal.coe_zero]
      obtain ⟨f, α, γ, hγ, hγset, -, -, -, hγ0, hγ1, -⟩ := exists_isArc_of_pieceSimpleAt hTpos (hT.symm ▸ hP)
      have hS : (stChart s).tipSet (fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) D.2 = γ '' Iic 1 := by
        rw [hγset, hT]
      have hγc : IsPreconnected (γ '' Iic 1) := isPreconnected_Iic.image γ hγ.1
      refine futPart_add h hnd (S := γ '' Iic 1) (by rw [hset, hS]) hγc ⟨0, mem_Iic.2 zero_le, hγ0⟩
        (fun z hz hzo => ?_) (fun _ => ⟨1, mem_Iic.2 le_rfl, hγ1⟩) (fun h' => absurd h' hnd')
      have : z ∈ (stChart s).tipSet (fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) D.2 ∩ statePhysicalSet 0 s :=
        ⟨hS ▸ hz, hzo⟩
      rw [hmeet] at this
      exact this

/-- **A connector move keeps the future part** (connector clearance). -/
theorem futPart_moveAlong {P : Set ℂ} {q : ℂ} {s : ExplState} (h : FutPart P q s) (hnd : stStatus s ≠ stDone)
    (r : Bool) (x : ℝ)
    (hC : GW1WalkChain.ConnectorClearance 0 s (((↑) : ℝ → ℂ) '' (if r then Icc (stPt s) x else Icc x (stPt s))))
    (hd : if r then stPt s ≤ x else x ≤ stPt s) :
    FutPart P q (ExplState.moveAlong s r x true) := by
  have hI : IsPreconnected (((↑) : ℝ → ℂ) '' (if r then Icc (stPt s) x else Icc x (stPt s))) := by
    cases r
    · exact isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
    · exact isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
  have hp : (stPt s : ℂ) ∈ ((↑) : ℝ → ℂ) '' (if r then Icc (stPt s) x else Icc x (stPt s)) := by
    cases r
    · exact ⟨stPt s, ⟨by simpa using hd, le_rfl⟩, rfl⟩
    · exact ⟨stPt s, ⟨le_rfl, by simpa using hd⟩, rfl⟩
  have hx : (x : ℂ) ∈ ((↑) : ℝ → ℂ) '' (if r then Icc (stPt s) x else Icc x (stPt s)) := by
    cases r
    · exact ⟨x, ⟨le_rfl, by simpa using hd⟩, rfl⟩
    · exact ⟨x, ⟨by simpa using hd, le_rfl⟩, rfl⟩
  refine futPart_add h hnd (GW1WalkChain.statePhysicalSet_moveAlong 0 s r x true) hI hp hC (fun _ => ?_)
    (fun h' => absurd h' ?_)
  · rw [GW1W.stPt_moveAlong]; exact hx
  · rw [stStatus_moveAlong']; intro e; cases e

/-- **A move to the end keeps the future part and makes it unbounded** (connector clearance of the ray). -/
theorem futPart_moveToEnd {P : Set ℂ} {q : ℂ} {s : ExplState} (h : FutPart P q s) (hnd : stStatus s ≠ stDone)
    (r : Bool) (hC : GW1WalkChain.ConnectorClearance 0 s (range (GW1WalkChain.realRay r (stPt s)))) :
    FutPart P q (ExplState.moveToEnd s r) := by
  have hρ := GW1WalkChain.isProperCurve_realRay r (stPt s)
  refine futPart_add h hnd (GW1WalkChain.statePhysicalSet_moveToEnd 0 s r) (isPreconnected_range hρ.1)
    ⟨0, GW1WalkChain.realRay_zero r (stPt s)⟩ hC (fun h' => absurd (stStatus_moveToEnd'' s r) h')
    (fun _ => not_isBounded_range_of_isProperCurve hρ)

/-- Marking a state dead keeps the future part. -/
theorem futPart_setDead {P : Set ℂ} {q : ℂ} {s : ExplState} (h : FutPart P q s) (hnd : stStatus s ≠ stDone) :
    FutPart P q (setDead s) := by
  obtain ⟨T, hT, hTc, hqT, hTP, hpT, -⟩ := h
  refine ⟨T, hT, hTc, hqT, hTP, fun _ => hpT hnd, fun h' => ?_⟩
  rw [stStatus_setDead] at h'
  cases h'


/-! ### Along the run -/

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The future part along a walk run** from any stage where it holds, given GW1's per-step facts (piece simplicity
at launches, connector clearance; the hypotheses of `walkChainRepresentation_of_pieceSimpleAt`). -/
theorem futPart_run
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))))
    (hC : GW1WalkChain.WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)
    {P : Set ℂ} {q : ℂ} {n₀ : ℕ} (h₀ : FutPart P q (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n₀)) :
    ∀ n, n₀ ≤ n → FutPart P q (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact h₀
  | succ n _ ih =>
    set spec := boundaryWalkSpec b jumps θ right with hspec
    by_cases hdone : stStatus (ExplState.run κ b jumps spec D n) = stDone
    · have heq : ExplState.run κ b jumps spec D (n + 1) = ExplState.run κ b jumps spec D n :=
        Lx.run_eq_of_done spec D hdone (n + 1) (Nat.le_succ n)
      rw [heq]; exact ih
    · have hpt : (stPt (ExplState.run κ b jumps spec D n) : ℂ) ∈
          statePhysicalSet 0 (ExplState.run κ b jumps spec D n) := by
        obtain ⟨T, hT, -, -, -, hpT, -⟩ := ih
        rw [hT]; exact Or.inr (hpT hdone)
      cases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with
      | some p =>
        obtain ⟨c, θ'⟩ := p
        have hn : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by
          rw [hl]; exact Option.some_ne_none _
        have heq := GW1W.launch_walk hn
        have hpiece := hP n c θ' hl hpt
        obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hn
        have htime : instrTime spec n = ⊤ := by
          simp only [spec, instrTime, GW1Conn.getElem?_boundaryWalkSpec, hlen, hev, ↓reduceIte]
        obtain ⟨_, _, hc⟩ := eq_launch_of_launches spec D hl
        rw [htime, min_top_left, hc, heq] at hpiece
        rw [heq]
        exact futPart_launch ih hdone n (D n) θ hpiece
      | none =>
        by_cases hlen : n < spec.2.2.length
        · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
          · have heq := GW1W.run_succ_walk_flow (κ := κ) (D := D) hlen hev
            have hnl := hl
            rw [heq] at hnl
            rw [heq, GW1W.flowStep_eq_self_of_noLaunch _ _ _ _ _ hnl]
            exact ih
          · have heq := GW1W.run_succ_walk_cont (κ := κ) (D := D) hlen hodd
            rcases GW1WalkChain.contStep_none_cases (κ := κ) b jumps (ExplState.run κ b jumps spec D n) right
              with hs | hs | ⟨r, x, hd, hs⟩ | ⟨r, hs⟩
            · rw [heq, hs]; exact ih
            · rw [heq, hs]; exact futPart_setDead ih hdone
            · rw [heq, hs]
              refine futPart_moveAlong ih hdone r x ((hC n).1 r x (heq.trans hs)) ?_
              cases r
              · exact (show x < stPt (ExplState.run κ b jumps spec D n) by simpa using hd).le
              · exact (show stPt (ExplState.run κ b jumps spec D n) < x by simpa using hd).le
            · rw [heq, hs]; exact futPart_moveToEnd ih hdone r ((hC n).2 r (heq.trans hs))
        · have heq : ExplState.run κ b jumps spec D (n + 1) = ExplState.run κ b jumps spec D n := by
            rw [run_succ, GW1Conn.getElem?_boundaryWalkSpec, ite_eq_right hlen]
          rw [heq]; exact ih

end Run

/-- The initial state of a walk from `0`: the split at `{0}`. -/
theorem futPart_init : FutPart {0} 0 (ExplState.init 0) :=
  ⟨{0}, by rw [statePhysicalSet_init, union_self], isPreconnected_singleton, rfl, fun _ hz _ => hz,
    fun _ => by show ((0 : ℝ) : ℂ) ∈ ({0} : Set ℂ); simp, fun h => absurd h (by intro e; cases e)⟩

section Head

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **Every prefix of a walk is preconnected and holds its current point** (GW1's per-step facts). -/
theorem prefix_facts
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))))
    (hC : GW1WalkChain.WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D) (n : ℕ) :
    IsPreconnected (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) ∧
      (stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) ≠ stDone →
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) : ℂ) ∈
          statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) := by
  have h0 : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D 0 = ExplState.init 0 := rfl
  obtain ⟨T, hT, hTc, h0T, -, hpT, -⟩ := futPart_run hP hC (n₀ := 0) (h0 ▸ futPart_init) n (Nat.zero_le n)
  have hT' : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) = T := by
    rw [hT, union_eq_right.2 (singleton_subset_iff.2 h0T)]
  rw [hT']
  exact ⟨hTc, hpT⟩

end Head

end InteractingSLE.Theorem14.SB.Lk
