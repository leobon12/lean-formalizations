/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LdMark

/-!
# SB2(2): the piece start's `recAfter`, and the piece start whose piece reaches `∞`

Packet PROVE-SB2-LIFTSET (round 8).

* **`recAfter_of_piece`**: if a launched piece of finite lifetime carries `R`, not yet in the walk, the record after
  the piece is `≥ R`. The new record is the supremum of the points beyond the old record in the closure of the new
  filled prefix (SB2LIFT's `lRecR_run_eq`, bounded by `bddAbove_beyond_fill`); `R` is such a point because the piece is
  adherent to its points in `ℍ` (`tipSet_adherent`) — unless the piece is a single point, its seed, which is already in
  the walk (piece simplicity, `WalkChainFacts`). This is `PieceStartData.recAfter` for finite lifetimes.
* **`range_eq_physSet_of_piece_top`**: when the piece through `R` has infinite lifetime, `recAfter` can fail, but the
  walk is done right after the piece: the range identity holds with no later step data (`stepData_of_done`), no
  `recAfter` and no run inputs (the fix announced in handoff §R7.2 item 1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **`recAfter` at a piece start**: if a launched piece of finite lifetime carries `R`, not yet in the walk, the
record after the piece is at least `R` (`R` lies on the piece, which is adherent to its points in `ℍ`, so `R` is in the
closure of the new filled prefix; the new record is the supremum of such points, `lRecR_run_eq`). -/
theorem recAfter_of_piece (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {o : ℕ} {R : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)).2.2.2.1 o ≠ none)
    (hfin : (D o).2 ≠ ⊤) (hinv : RecInv κ b jumps θ D o)
    (hn : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o))
    (hRmem : (R : ℂ) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o) (D o)).1.tipSet
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o) (D o)).2.1
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o) (D o)).2.2) :
    R ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o with hs
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hlaunch := GW1W.launch_walk hl
  have hmin : min (⊤ : ℝ≥0∞) (D o).2 ≠ ⊤ := by rw [min_eq_right le_top]; exact hfin
  have hrec' : stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) = lRecR s ⊤ (D o) := by
    rw [hlaunch]; exact (launch_eq_of_ne_top s o (D o) θ ⊤ hmin).2.2.1
  rw [hrec', lRecR_run_eq hP hl' hfin hinv]
  have hbdd := (bddAbove_beyond_fill hP hfin hinv (stRecR s)).insert (stRecR s)
  by_cases hRr : R ≤ stRecR s
  · exact hRr.trans (le_csSup hbdd (mem_insert _ _))
  refine le_csSup hbdd (Or.inr ⟨lt_of_not_ge hRr, ?_⟩)
  -- `R` is a limit of points of the new piece in `ℍ`
  set X := (newPc s (D o)).1.tipSet (newPc s (D o)).2.1 (newPc s (D o)).2.2 with hX
  have hPR : GW1P.PieceRegular (D o).1 (min ⊤ (D o).2) := by
    have h := hP o c θ' hl'
    rwa [Lx.instrTime_boundaryWalk_of_launch hl'] at h
  have hcc := isConformal_runChart_of_reg (κ := κ) (b := b) (jumps := jumps) _ hP o
  have hbe := (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) _ D hP o).1
  have hXP : X ⊆ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1) := by
    intro z hz
    show z ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))
    rw [hlaunch, GW1WalkChain.statePhysicalSet_launch]
    exact Or.inr hz
  rcases tipSet_adherent hbe hcc hcc.2.1 hPR with had | hsub
  · refine closure_mono (fun z hz => ?_) (had hRmem)
    exact ⟨hz.2, Or.inl (subset_closure (hXP hz.1))⟩
  · exfalso
    -- the piece is its seed, which is already in the walk
    have hnd : stStatus s ≠ stDone := by
      intro hd
      have e := Lx.run_eq_of_done (boundaryWalkSpec b jumps θ true) D hd (o + 1) (Nat.le_succ o)
      rw [hlaunch] at e
      have h1 := congrArg (fun t : ExplState => t.1.length) e
      rw [launch_pieces, ← hs] at h1
      simp at h1
    have hseed := (prefix_facts hW.1 hW.2 o).2 hnd
    have hc : c = stChart s := (eq_launch_of_launches _ _ hl').2.2
    have hpiece := hW.1 o c θ' hl' hseed
    rw [Lx.instrTime_boundaryWalk_of_launch hl', hc] at hpiece
    have hmeet := GW1WalkChain.tipSet_inter_of_pieceSimpleAt hpiece
    have hq : (stPt s : ℂ) ∈ X := by
      have : (stPt s : ℂ) ∈ ({(stPt s : ℂ)} : Set ℂ) := rfl
      rw [← hmeet] at this
      exact this.1
    have hRq : (R : ℂ) = stPt s := hsub hRmem hq
    exact hn (hRq ▸ hseed)


variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **SB2(2)'s physical sets at a piece start whose piece reaches `∞`** (deterministic, one sample): the actual walk is
done right after the piece through `R`, so no later step data, no `recAfter` and no run inputs are needed. -/
theorem range_eq_physSet_of_piece_top (hι : RayCorr b₁ J₁ b₂ J₂ R ι) {o N : ℕ} (ho : o % 2 = 0)
    (hlaunch : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) =
      ExplState.launch (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) o (D₁ o) θ ⊤)
    (htop : (D₁ o).2 = ⊤)
    (htip : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≠ .inr (.inl ()))
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≤ R)
    (hT : (D₂ 0).2 = ⊤ ↔ (D₁ o).2 = ⊤) (h0 : (D₂ 0).2 = 0 ↔ (D₁ o).2 = 0)
    (hR : (∃ x : ℝ, 0 < x ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x) ↔
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) ⊤ (D₁ o) x)
    (hL₁ : ¬ ∃ x : ℝ, x < stRecL (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ∧
      lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) ⊤ (D₁ o) x)
    (hL₂ : ¬ ∃ x : ℝ, x < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x)
    (hlift₀ : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o))
      (newPc (ExplState.init 0) (D₂ 0)))
    (hRmem : (R : ℂ) ∈ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).1.tipSet
      (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).2.1
      (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).2.2)
    (h1N : 1 ≤ N) (hlen : ∀ i, 1 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hP₀ : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊆ β₀ '' Iic tL) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  have hdone1 : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) = stDone := by
    rw [hlaunch]
    exact (launch_eq_of_top _ o (D₁ o) θ ⊤ (by rw [htop, min_self])).2.2.2.2.1
  have hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone := by
    rw [Lx.run_eq_of_done _ D₁ hdone1 (N + o) (by omega)]; exact hdone1
  refine range_eq_physSet_start_piece hι ho hlaunch htip hpt hrec hT h0 hR hL₁ hL₂ (fun h => absurd htop h) hlift₀
    hRmem h1N hlen ?_ hN₁ hN₂ hd hβr hβ hβL hγ0 hhead htail hray hP₀
  intro i hi _ _
  rw [Lx.run_eq_of_done _ D₁ hdone1 (i + o) (by omega)]
  exact stepData_of_done _ hdone1

end InteractingSLE.Theorem14.SB.Lk
