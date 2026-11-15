/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2McTrace
import InteractingSLE.Spec.Supplement.SB2MaRun
import InteractingSLE.Spec.Supplement.SB2LpStep

/-!
# Real points of a prefix beyond the record are in its closed fill

Packet PROVE-T14-SB2LIFT (round 17; the actual half of `OnSegFill` for the prefix after a launch, handoff §R16.2 1(c)).
Along the right walk with regular launches, no left moves and the record invariant (`RecInv`, PROVE-SB2-LIFTSET's
bounded `recInv_ptRec_run_le`):

* **`chart_mem_trace_of_mem_tip`**: a real physical point of a new piece beyond the record has its chart point on the
  stopped trace. The tip set is the boundary image of the trace (`tipSet_stopped_eq_of_tendsto`), and the boundary
  map is injective at the chart point (`injAt_of_continuousWithinAt`);
* **`not_lAlive_of_mem_tip`**: such a point is dead at the stop (`not_lAlive_of_mem_trace`);
* `exists_launch_of_mem_pieces`: every recorded piece is the new piece of an earlier launch;
* **`arcs_subset_Iic_run`**: before the walk is done, all connectors lie left of the record;
* **`notMem_prefix_of_beyond`**: before the walk is done, the prefix has no real point beyond the record. The root is
  at `0 ≤ recR`, connectors lie left of it, and a real point of an old piece beyond the record would be dead at that
  piece's stop, against `BeyondOK`;
* **`mem_closure_prefix_succ_of_mem`**: at a launch, a real point of the new prefix beyond the record lies in the
  closed fill of the new prefix. It lies on the new piece, is dead at the stop, and `lAlive_run_iff` converts this.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **A real point of a new piece beyond the record has its chart point on the stopped trace.** -/
theorem chart_mem_trace_of_mem_tip {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) {x : ℝ} (hok : BeyondOK κ b jumps θ right D n x)
    (hx : (x : ℂ) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (D n)).1.tipSet
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (D n)).2.1
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (D n)).2.2) :
    (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).1 x ∈
      trOf (D n) '' Icc 0 (D n).2.toNNReal := by
  obtain ⟨hlaunch, hoff, hbd, -⟩ := hok
  set spec := boundaryWalkSpec b jumps θ right with hspec
  set s₀ := ExplState.run κ b jumps spec D n with hs₀
  have hlne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by rw [hl]; simp
  have hPR := pieceRegular_of_launch hP hlne
  have hcc := isConformal_runChart_of_reg spec hP n
  obtain ⟨hbe, -⟩ := GW1P.isClosed_pieces_run spec D hP n
  obtain ⟨ĝ, C, hf, -⟩ := hbe
  have hĝ : ContinuousOn ĝ {z : ℂ | 0 ≤ z.im} := GW1P.continuousOn_of_tendsto hf
  have hgg : EqOn ĝ (stChart s₀).2.1 H := fun z hz => by
    have : (𝓝[H] z).NeBot := GW1P.neBot_nhdsWithin_H (QuantumZipper.H_subset_Hbar hz)
    exact tendsto_nhds_unique (hf z (QuantumZipper.H_subset_Hbar hz))
      ((hcc.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)
  obtain ⟨hfc, hre⟩ := continuousWithinAt_runChart_fwd hP x n hlaunch hoff
  have hyH : (stChart s₀).1 x ∈ Hbar := show 0 ≤ ((stChart s₀).1 x).im by rw [hre]
  have hyx : ĝ ((stChart s₀).1 x) = x := by
    have : (𝓝[H] ((stChart s₀).1 x)).NeBot := GW1P.neBot_nhdsWithin_H hyH
    exact tendsto_nhds_unique (hf _ hyH) hbd
  have hinjy := injAt_of_continuousWithinAt hcc.2.1 hcc.2.2 hĝ hgg (by simp) hyx hfc rfl
  have hmin : min (⊤ : ℝ≥0∞) (D n).2 = (D n).2 := min_eq_right le_top
  have hα := isGeneratingTrace_trOf hPR
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → trOf (D n) t ∈ Hbar := fun t ht =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  change (x : ℂ) ∈ (stChart s₀).tipSet (fun r : ℝ≥0 => (D n).1 (min (r : ℝ≥0∞) (min ⊤ (D n).2)).toNNReal)
    (min ⊤ (D n).2) at hx
  rw [hmin, CounterflowRange.tipSet_stopped_eq_of_tendsto hα hPR.2.1 hPR.1 (fun t ht => hf _ (hαH t ht))] at hx
  obtain ⟨_, ⟨t, ht, rfl⟩, hxt⟩ := hx
  have heq : trOf (D n) t = (stChart s₀).1 x := hinjy _ (hαH t ht) (by rw [hxt, hyx])
  refine ⟨t, ⟨zero_le, ?_⟩, heq⟩
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
  exact ht

/-- **A real point of a new piece beyond the record is dead at the stop.** -/
theorem not_lAlive_of_mem_tip {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) {x : ℝ} (hok : BeyondOK κ b jumps θ right D n x)
    (hx : (x : ℂ) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (D n)).1.tipSet
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (D n)).2.1
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (D n)).2.2) :
    ¬ lAlive (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) ⊤ (D n) x := by
  have hlne : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none := by
    rw [hl]; simp
  have hPR := pieceRegular_of_launch hP hlne
  have hre := (continuousWithinAt_runChart_fwd hP x n hok.1 hok.2.1).2
  exact not_lAlive_of_mem_trace hPR hfin hre hok.2.2.2 (chart_mem_trace_of_mem_tip hP hl hfin hok hx)

/-- **Every recorded piece is the new piece of an earlier launch.** -/
theorem exists_launch_of_mem_pieces {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} :
    ∀ (n : ℕ) (p : Pc), p ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n).1 →
      ∃ j < n, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j ≠ none ∧
        p = newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j) (D j)
  | 0, p, hp => by
    simp [ExplState.run, ExplState.init] at hp
  | n + 1, p, hp => by
    rcases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n with _ | ⟨c, θ'⟩
    · rw [GW1P.pieces_run_succ_of_noLaunch _ D hl] at hp
      obtain ⟨j, hj, h1, h2⟩ := exists_launch_of_mem_pieces n p hp
      exact ⟨j, by omega, h1, h2⟩
    · have hlne : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none := by
        rw [hl]; simp
      rw [GW1Bookkeep.pieces_run_succ_of_launch hlne, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · obtain ⟨j, hj, h1, h2⟩ := exists_launch_of_mem_pieces n p hp
        exact ⟨j, by omega, h1, h2⟩
      · exact ⟨n, by omega, hlne, rfl⟩

/-- **The record never decreases** up to `N` (LIFTSET's `stRecR_run_le_succ'` along the run). -/
theorem stRecR_run_mono {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    {N : ℕ} (hrec : ∀ k, k < N → RecInv κ b jumps θ D k) {j n : ℕ} (hjn : j ≤ n) (hnN : n ≤ N) :
    stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D j) ≤
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) := by
  induction n, hjn using Nat.le_induction with
  | base => exact le_rfl
  | succ m hjm ih => exact (ih (by omega)).trans (stRecR_run_le_succ' hP (hrec m (by omega)))

theorem stRecR_run_zero (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = 0 := by
  simp [ExplState.run, ExplState.init, boundaryWalkSpec]

/-- **Before the walk is done, all connectors lie left of the record.** -/
theorem arcs_subset_Iic_run {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {N : ℕ}
    (hrec : ∀ k, k < N → RecInv κ b jumps θ D k) (hlm : ∀ k, NoLeftMove κ b jumps θ D k) :
    ∀ n, n ≤ N → stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone →
      ∀ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n).2.1,
        a ⊆ Iic (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
  | 0, _, _ => by
    intro a ha
    simp [ExplState.run, ExplState.init] at ha
  | n + 1, hn, hst => by
    set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hsdef
    have hst' : stStatus s ≠ stDone := fun h =>
      hst (by rw [GW1WalkFinish.done_run_succ _ D h]; exact h)
    have ih := arcs_subset_Iic_run hP hrec hlm n (by omega) hst'
    have hmono := stRecR_run_le_succ' hP (hrec n (by omega))
    have hold : ∀ a ∈ s.2.1, a ⊆ Iic (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1))) :=
      fun a ha => (ih a ha).trans (Iic_subset_Iic.2 hmono)
    by_cases hk : n < (boundaryWalkSpec b jumps θ true).2.2.length
    · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
      · have hstep := GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true)
          (D := D) hk hev
        have harcs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.1 = s.2.1 := by
          rw [hstep]
          rcases flowStep_trichotomy (κ := κ) (b := b) false s n (D n) θ ⊤ with e | e | e
          · rw [e]
          · rw [e, arcs_setDead]
          · rw [e, Lx.arcs_launch']
        rw [harcs]
        exact hold
      · have hstep := GW1W.run_succ_walk_cont (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true)
          (D := D) hk hodd
        rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s none true with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩
        · rw [hstep, e] at hold ⊢
          exact hold
        · rw [hstep, e, arcs_setDead]
          rw [hstep, e] at hold
          exact hold
        · cases r
          · exact absurd (hstep.trans e) (hlm n x m)
          · rw [hstep, e, moveAlong_arcs_true]
            rw [hstep, e] at hold
            intro a ha
            rcases List.mem_append.1 ha with ha | ha
            · exact hold a ha
            · rw [List.mem_singleton.1 ha]
              rw [GW1W.stRecR_moveAlong_true]
              exact fun z hz => le_max_of_le_right hz.2
        · exfalso
          apply hst
          rw [hstep, e]
          exact stStatus_moveToEnd'' s r
    · have e : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) = s := by
        rw [run_succ]
        have : (boundaryWalkSpec b jumps θ true).2.2[n]? = none := List.getElem?_eq_none (not_lt.1 hk)
        rw [this]
      rw [e]
      exact ih

/-- **Before the walk is done, the prefix has no real point beyond the record.** -/
theorem notMem_prefix_of_beyond {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hrec : ∀ k, k ≤ n → RecInv κ b jumps θ D k) (hlm : ∀ k, NoLeftMove κ b jumps θ D k)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone) {x : ℝ}
    (hx : stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x) :
    (x : ℂ) ∉ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n := by
  have hrec' : ∀ k, k < n → RecInv κ b jumps θ D k := fun k hk => hrec k hk.le
  have hmono : ∀ j, j ≤ n → stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D j) ≤
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) := fun j hj =>
    stRecR_run_mono hP hrec' hj le_rfl
  have h0 : (0 : ℝ) ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) := by
    have := hmono 0 (Nat.zero_le n)
    rwa [stRecR_run_zero] at this
  unfold SB.prefixPhysSet
  simp only [mem_union, mem_singleton_iff, mem_iUnion]
  rintro ((h | ⟨p, hp, hxp⟩) | ⟨a, ha, y, hy, hyx⟩)
  · -- the root
    have : x = 0 := by
      have h' : (x : ℂ) = ((0 : ℝ) : ℂ) := by rw [h]; simp [boundaryWalkSpec]
      exact_mod_cast h'
    linarith
  · -- an old piece
    obtain ⟨j, hj, hlne, rfl⟩ := exists_launch_of_mem_pieces n p hp
    have hokn := hrec n le_rfl x hx
    obtain ⟨hfinj, halive⟩ := hokn.1 j hj hlne
    have hokj := hrec j hj.le x ((hmono j hj.le).trans_lt hx)
    obtain ⟨⟨c, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hlne
    exact not_lAlive_of_mem_tip hP hl hfinj hokj hxp halive
  · -- a connector
    have hy' : y = x := by exact_mod_cast hyx
    have := arcs_subset_Iic_run hP hrec' hlm n le_rfl hst a ha (hy' ▸ hy)
    exact absurd this (not_le.2 hx)

/-- **At a launch, a real point of the new prefix beyond the record lies in the closed fill of the new prefix.** -/
theorem mem_closure_prefix_succ_of_mem {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) (hrec : ∀ k, k ≤ n → RecInv κ b jumps θ D k) (hlm : ∀ k, NoLeftMove κ b jumps θ D k)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone) {x : ℝ}
    (hx : stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x)
    (hmem : (x : ℂ) ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) :
    (x : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1))) := by
  have hok := hrec n le_rfl x hx
  have hlne : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none := by
    rw [hl]; simp
  have hdead : ¬ lAlive (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ⊤ (D n) x := by
    have hold := notMem_prefix_of_beyond hP hrec hlm hst hx
    obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl
    rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
    simp only [SB.prefixPhysSet] at hmem hold
    rw [GW1Bookkeep.pieces_run_succ_of_launch hlne, he, Lx.arcs_launch'] at hmem
    simp only [mem_union, mem_singleton_iff, mem_iUnion, List.mem_append, List.mem_singleton] at hmem hold
    rcases hmem with (h | ⟨p, hp, hxp⟩) | h
    · exact absurd (Or.inl (Or.inl h)) hold
    · rcases hp with hp | rfl
      · exact absurd (Or.inl (Or.inr ⟨p, hp, hxp⟩)) hold
      · exact not_lAlive_of_mem_tip hP hl hfin hok hxp
    · exact absurd (Or.inr h) hold
  by_contra hcl
  exact hdead ((lAlive_run_iff hP hl hfin x hok.1 hok.2.1 hok.2.2.1 hok.2.2.2).2 hcl)

end InteractingSLE.Theorem14.SB.Lk
