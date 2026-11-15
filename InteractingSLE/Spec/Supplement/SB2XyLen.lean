/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XyRun
import InteractingSLE.Spec.Supplement.GW1WalkFinish

/-!
# The lengths of the run inputs: the actual walk finishes within the relative program

Packet PROVE-T14-SB2LIFT (round 28; LIFTSET's item 4, fields `len`, `len₂`). After the start, every round of the
actual walk (a flow step then a connector step) either finishes the walk or moves its right record to a new jump point
right of `R` (`flow_round`): a dead or stuck walk never finishes (`dead_persist`, `stuck_persist`); a launch never
ends at an arc mark (`stStatus_launch_ne_arcM`); a connector from a right threshold moves to the next restart mark
beyond the record (`WalkMovesRight`) or to the end. Counting rounds (`GW1WalkFinish.done_of_finite_progress`):

* **`first_done_le`**: the first finished stage is at most `o + 2 + 2·#{jumps of b₁ right of R}`;
* **`card_jumps_le`**: the jumps right of `R` inject into the relative jumps (`RayCorr`);
* hence **`len_rel`**: the lockstep's length `N` is at most the relative program's length.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A dead walk stays dead.** -/
theorem dead_persist {k : ℕ} (h : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) = stDead) :
    ∀ j, k ≤ j → stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j) = stDead := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact h
  | succ j _ ih =>
    rcases run_succ_walk_cases (κ := κ) (b := b) (jumps := J) (θ := θ) D j with e | e | e
    · rw [e]; exact ih
    · rw [e, flowStep_of_dead ih]; exact ih
    · rw [e]; exact (contStep_of_dead ih true).2.1

/-- **A walk at an arc mark with an inadmissible seed is stuck.** -/
theorem stuck_persist {k : ℕ}
    (hst : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) = GW1W.stArcM true)
    (hadm : ¬ ExplState.IsAdmissibleSeed κ (leftLim b (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k)))
      (rightLim b (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k))) θ) :
    ∀ j, k ≤ j → ExplState.run κ b J (boundaryWalkSpec b J θ true) D j =
      ExplState.run κ b J (boundaryWalkSpec b J θ true) D k := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j _ ih =>
    rcases run_succ_walk_cases (κ := κ) (b := b) (jumps := J) (θ := θ) D j with e | e | e
    · rw [e]; exact ih
    · rw [e, ih]; exact flowStep_of_arcM_not_adm hst hadm j (D j) ⊤
    · rw [e, ih]; exact contStep_of_arcM hst true

/-- **A connector from a right threshold**: the walk finishes, or its record moves to a jump point beyond the
record. -/
theorem cont_round {k : ℕ} (hk : k < (boundaryWalkSpec b J θ true).2.2.length) (hodd : k % 2 = 1)
    (hthr : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) = stThr (some true))
    (hW : WalkMovesRight κ b J θ D k) :
    stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)) = stDone ∨
      (stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)) ∈ jumpSet b J ∧
        stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) <
          stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1))) := by
  have e := GW1W.run_succ_walk_cont (κ := κ) (b := b) (jumps := J) (θ := θ) (right := true) (D := D) hk hodd
  rw [contStep_thr_true' b J _ hthr] at e
  split_ifs at e with hC
  · have hw := Finset.mem_filter.1 ((GW1W.restartSet κ b J
      (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k)).min'_mem hC)
    have hlt := (hW true _ true e).2
    refine Or.inr ⟨?_, ?_⟩
    · rw [e, stRecR_moveAlong_true, max_eq_right hlt.le]; exact hw.1
    · rw [e, stRecR_moveAlong_true, max_eq_right hlt.le]; exact hlt
  · exact Or.inl (by rw [e]; exact stStatus_moveToEnd'' _ _)

/-- **One round of the walk from a flow stage of status `FlowSt`**: it finishes, or its record moves to a new jump
point beyond the record. -/
theorem flow_round {k M : ℕ} {p : ℝ} (hk : k + 1 < (boundaryWalkSpec b J θ true).2.2.length) (hev : k % 2 = 0)
    (hF : FlowSt p (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k))
    (hnd : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) ≠ stDone)
    (hkM : k ≤ M) (hM : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D M) = stDone)
    (hC : ContSt p (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)))
    (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) (hrec : RecInv κ b J θ D k)
    (hW : WalkMovesRight κ b J θ D (k + 1)) :
    stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1 + 1)) = stDone ∨
      (stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1 + 1)) ∈ jumpSet b J ∧
        stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) <
          stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1 + 1))) := by
  have hk' : k < (boundaryWalkSpec b J θ true).2.2.length := by omega
  -- the flow stage is at an arc mark with an admissible seed
  have hst : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) = GW1W.stArcM true := by
    rcases hF with ⟨h, -⟩ | h | h
    · exact h
    · exact absurd h hnd
    · have := dead_persist h M hkM
      rw [hM] at this; cases this
  have hadm : ExplState.IsAdmissibleSeed κ (leftLim b (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k)))
      (rightLim b (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k))) θ := by
    by_contra hadm
    have := stuck_persist hst hadm M hkM
    rw [this, hst] at hM; cases hM
  have hlaunch : ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1) =
      ExplState.launch (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) k (D k) θ ⊤ := by
    rw [GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := J) (θ := θ) (right := true) (D := D) hk' hev,
      GW1WalkExit.flowStep_of_launchReady (Or.inr ⟨hst, hadm⟩) k (D k)]
  have hne : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)) ≠ GW1W.stArcM true := by
    rw [hlaunch]; exact stStatus_launch_ne_arcM _ _ _ _
  have hle := stRecR_run_le_succ' hP hrec
  rcases hC with hthr | ⟨h, -⟩ | h | h
  · rcases cont_round hk (by omega) hthr hW with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, lt_of_le_of_lt hle h2⟩
  · exact absurd h hne
  · exact Or.inl (by rw [done_of_le h (Nat.le_succ _)])
  · exfalso
    have := dead_persist h M (by
      by_contra hlt; push Not at hlt
      have hMk : M = k := le_antisymm (Nat.lt_succ_iff.1 hlt) hkM
      subst hMk; exact hnd hM)
    rw [hM] at this; cases this

/-- **The first finished stage after the start**: the walk finishes within one round per jump point right of `R`. -/
theorem first_done_le {o M : ℕ} {R : ℝ} (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D)
    (hrec : ∀ k, k < M → RecInv κ b J θ D k) (hWall : ∀ k, k < M → WalkMovesRight κ b J θ D k)
    (hM : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D M) = stDone)
    (hmin : ∀ i, i < M → stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D i) ≠ stDone)
    (hML : M ≤ (boundaryWalkSpec b J θ true).2.2.length) (ho : o % 2 = 0)
    (hflow : ∀ k, o + 2 ≤ k → k ≤ M → k % 2 = 0 →
      FlowSt R (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k))
    (hcont : ∀ k, o + 2 ≤ k → k ≤ M → k % 2 = 1 →
      ContSt R (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k))
    (hq0 : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (o + 2)) ≠ stDone →
      stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (o + 2)) ∈ jumpSet b J ∧
        R < stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (o + 2))) :
    M ≤ o + 2 + 2 * ((jumpSet b J).filter (fun x => R < x)).card := by
  by_cases hd0 : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (o + 2)) = stDone
  · have : M ≤ o + 2 := by
      by_contra h; push Not at h; exact hmin _ h hd0
    omega
  obtain ⟨hq0J, hRq0⟩ := hq0 hd0
  set q : ℕ → ℝ := fun n => stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (o + 2 + 2 * n)) with hq
  set Jq := (jumpSet b J).filter (fun x => q 0 < x) with hJq
  have key := GW1WalkFinish.done_of_finite_progress Jq q
    (fun n => stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (o + 2 + 2 * n)) = stDone) true
    (fun n h => done_of_le h (by omega)) (fun n _ hnd => ?_)
  · have hMle : M ≤ o + 2 + 2 * (Jq.card + 1) := by
      by_contra h; push Not at h; exact hmin _ h key
    have hcard : Jq.card + 1 ≤ ((jumpSet b J).filter (fun x => R < x)).card := by
      have hsub : insert (q 0) Jq ⊆ (jumpSet b J).filter (fun x => R < x) := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Finset.mem_filter.2 ⟨hq0J, by simpa [hq] using hRq0⟩
        · have h := Finset.mem_filter.1 hx
          exact Finset.mem_filter.2 ⟨h.1, lt_trans (by simpa [hq] using hRq0) h.2⟩
      have hnot : q 0 ∉ Jq := fun h => lt_irrefl _ (Finset.mem_filter.1 h).2
      have := Finset.card_le_card hsub
      rwa [Finset.card_insert_of_notMem hnot] at this
    omega
  · -- one round from the flow stage `k = o + 2 + 2 n`
    set k := o + 2 + 2 * n with hk
    have hkM : k < M := by
      by_contra h; push Not at h; exact hnd (done_of_le hM h)
    have e2 : o + 2 + 2 * (n + 1) = k + 1 + 1 := by omega
    show stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (o + 2 + 2 * (n + 1))) = stDone ∨
      (q (n + 1) ∈ Jq ∧ GW1WalkFinish.sideCoord true (q n) < GW1WalkFinish.sideCoord true (q (n + 1)))
    simp only [hq, e2, GW1WalkFinish.sideCoord, ↓reduceIte]
    by_cases hd1 : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)) = stDone
    · exact Or.inl (done_of_le hd1 (Nat.le_succ _))
    have hk1M : k + 1 < M := by
      rcases Nat.lt_or_ge (k + 1) M with h | h
      · exact h
      · exact absurd (by rw [show k + 1 = M by omega]; exact hM) hd1
    rcases flow_round (by omega) (by omega) (hflow k (by omega) hkM.le (by omega)) hnd hkM.le hM
      (hcont (k + 1) (by omega) hk1M.le (by omega)) hP (hrec k hkM) (hWall (k + 1) hk1M) with h | ⟨hJ, hlt⟩
    · exact Or.inl h
    · refine Or.inr ⟨Finset.mem_filter.2 ⟨hJ, ?_⟩, hlt⟩
      have hmono : stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (o + 2 + 2 * 0)) ≤
          stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) :=
        stRecR_run_mono hP (N := M) hrec (by omega) hkM.le
      exact lt_of_le_of_lt hmono hlt

/-- **The jumps right of `R` inject into the relative jumps.** -/
theorem card_jumps_le {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} (hι : RayCorr b₁ J₁ b₂ J₂ R ι) :
    ((jumpSet b₁ J₁).filter (fun x => R < x)).card ≤ (jumpSet b₂ J₂).card := by
  refine Finset.card_le_card_of_injOn ι (fun x hx => ?_) (fun x hx y hy hxy => ?_)
  · have h := Finset.mem_filter.1 hx
    exact (hι.mem_jumpSet_iff x h.2).2 h.1
  · have hx' := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    have hy' := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    exact hι.mono.injOn (mem_Ici.2 hx'.le) (mem_Ici.2 hy'.le) hxy

/-- **The lockstep's length fits the relative program.** -/
theorem len_rel {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    {o N : ℕ} (hN : N + o ≤ o + 2 + 2 * ((jumpSet b₁ J₁).filter (fun x => R < x)).card) :
    N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length := by
  rw [GW1WalkFinish.boundaryWalk_length]
  have := card_jumps_le hι
  omega

end InteractingSLE.Theorem14.SB.Mn
