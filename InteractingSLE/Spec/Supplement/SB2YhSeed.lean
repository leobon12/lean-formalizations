/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3DuWalk
import InteractingSLE.Spec.Supplement.SB2JcRel
import InteractingSLE.Spec.Supplement.SB2JRight
import InteractingSLE.Spec.Supplement.SB2YgChart
import InteractingSLE.Spec.Supplement.SB2YhLine

/-!
# B's stage chart at a tail seed

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2` at a tail stage). At a launch of the boundary walk at a stage `n ≥ 1`
(regular launches, no left moves or hits):

* `status_contStep_none`, **`arcM_of_launch_walk`**: the stage starts at an arc mark (the connector before it moved
  the current point with its mark flag set);
* **`stage_seed_facts`**: with `R` the current point and `c` the run chart, every real point of the prefix is `≤ R`,
  the forward chart has real boundary values `e` on `(R, ∞)` tending to `0` at `R⁺` (the chart reads `0` at `R` and is
  continuous from `ℍ` there, LIFTSET's `Lk.zero_cont_of_lt`), and the inverse's boundary map `gc` (continuous on `ℍ̄`,
  within bounded distance of the identity) sends `0` to `R` and `(0, ∞)` into `(R, ∞)`, with `Re gc y → R⁺` as
  `y → 0⁺` (`SB2YhLine`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- After a connector without a stop value the status is an arc mark, done, or dead. -/
theorem status_contStep_none (s : ExplState) (pref : Bool) :
    (∃ r, stStatus (ExplState.contStep κ b jumps s none pref) = GW1W.stArcM r) ∨
      stStatus (ExplState.contStep κ b jumps s none pref) = GW1Conn.stDone ∨
      stStatus (ExplState.contStep κ b jumps s none pref) = GW1Conn.stDead := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ, recR, recL⟩ := s
  rcases status with u | u | (_ | r) | ⟨r, (_ | _)⟩ | u | u
  all_goals
    unfold ExplState.contStep
    dsimp only
  all_goals (repeat' split)
  all_goals first
    | exact Or.inr (Or.inr rfl)
    | exact Or.inr (Or.inl rfl)
    | exact Or.inl ⟨_, rfl⟩
    | contradiction
    | (exfalso; simp_all)

/-- **A launch of the walk at a stage `n ≥ 1` is from an arc mark.** -/
theorem arcM_of_launch_walk {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} (hn : 0 < n)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    ∃ r, stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) = GW1W.stArcM r := by
  obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hl
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hodd : m % 2 = 1 := by omega
  have hc := GW1W.run_succ_walk_cont (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true) (D := D)
    (show m < (boundaryWalkSpec b jumps θ true).2.2.length by omega) hodd
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ D hl'
  have hndd := Dv.not_dead_of_launch _ D hl'
  rw [hc] at hnd hndd ⊢
  rcases status_contStep_none (κ := κ) (b := b) (jumps := jumps)
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D m) true with h | h | h
  · exact h
  · exact absurd h hnd
  · exact absurd h hndd

/-- **B's stage chart at a tail seed.** -/
theorem stage_seed_facts {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ} (hn : 0 < n)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    (∀ y : ℝ, (y : ℂ) ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n →
      y ≤ stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ∧
    ∃ (e : ℝ → ℝ) (gc : ℂ → ℂ) (Cc : ℝ),
      (∀ x : ℝ, stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x →
        Tendsto (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).1 (𝓝[H] (x : ℂ))
          (𝓝 (e x : ℂ))) ∧
      Tendsto e (𝓝[>] (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))) (𝓝 0) ∧
      (∀ q ∈ Hbar, Tendsto (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1
        (𝓝[H] q) (𝓝 (gc q))) ∧
      ContinuousOn gc Hbar ∧ (∀ q ∈ Hbar, ‖gc q - q‖ ≤ Cc) ∧
      gc 0 = (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℂ) ∧
      (∀ y : ℝ, 0 < y → ∃ x : ℝ, stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x ∧
        gc (y : ℂ) = x) ∧
      Tendsto (fun y : ℝ => (gc (y : ℂ)).re) (𝓝[>] 0)
        (𝓝[>] (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))) := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D n with hs
  obtain ⟨⟨c', θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hndd : stStatus s ≠ GW1Conn.stDead := Dv.not_dead_of_launch w D hl'
  have hlen := Lk.lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) w D hl
  -- the records
  have hM : ∀ i, i < n + 1 → stStatus (ExplState.run κ b jumps w D i) ≠ GW1Conn.stDone := fun i hi hd =>
    hnd (by rw [hs, Lx.run_eq_of_done w D hd n (by omega)]; exact hd)
  have hfin := fin_before_first_done hM
  have hri := recInv_ptRec_run_le hP (N := n) (fun j hj hlj => hfin j (by omega) hlj) hlm hlh
  have hrec : ∀ k, k ≤ n → RecInv κ b jumps θ D k := fun k hk => (hri k hk).1
  have hpt : stPt s = stRecR s := by
    rcases (hri n le_rfl).2 with h | h | h
    · exact absurd h hnd
    · exact absurd h hndd
    · exact h
  have hbeyond : ∀ y : ℝ, (y : ℂ) ∈ SB.prefixPhysSet κ b jumps w D n → y ≤ stPt s := fun y hy => by
    by_contra hlt
    exact notMem_prefix_of_beyond hP hrec hlm hnd (hpt ▸ not_le.1 hlt) hy
  -- the chart reads `0` at the seed and is continuous from `ℍ` there
  obtain ⟨r, hst⟩ := arcM_of_launch_walk hn hl
  obtain ⟨hz, hcw⟩ := Lk.zero_cont_of_lt (fun k _ c θ hlk => hP k c θ hlk) (fun j hj hlj => hfin j (by omega) hlj)
    (fun j _ => hlm j) (fun j _ => hlh j) hlen.le hst
  -- the chart facts
  obtain ⟨s₀, LY, gc, Cc, hcD, -, -, -, -, hgc, hCc⟩ := stageChart_facts w D hP n hnd
  have hPc : IsCompact (SB.prefixPhysSet κ b jumps w D n) := Lx.isCompact_prefixPhysSet_run w D hP n hnd
  obtain ⟨f, hf, -⟩ := Lx.isRightEntryValue_runChart w D hP n hnd hPc rfl hbeyond
  set R := stPt s with hR
  have hf0 : Tendsto f (𝓝[>] R) (𝓝 0) := by
    have hcw' : Tendsto (stChart s).1 (𝓝[H] (R : ℂ)) (𝓝 0) := by
      have := hcw.tendsto
      rwa [hz] at this
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.tendsto_nhdsWithin_nhds.1 hcw' (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
    have hx0 : R < x := hx
    have hlim := hf x hx0
    have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ (x : ℂ).im by simp)
    have hle : ‖((f x : ℝ) : ℂ)‖ ≤ ε / 2 := by
      refine le_of_tendsto (hlim.norm) ?_
      have hxδ' : dist (x : ℂ) (R : ℂ) < δ := by
        rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]; rwa [Real.dist_eq] at hxδ
      filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds
        (show (x : ℂ) ∈ ball (R : ℂ) δ from hxδ'))] with z hz
      have h1 := hδε hz.1 hz.2
      rw [dist_zero_right] at h1
      exact h1.le
    rw [dist_zero_right, ← Complex.norm_real]
    linarith
  have hfreeY : ∀ x : ℝ, R < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (fillH (SB.prefixPhysSet κ b jumps w D n)) :=
    fun x hx => Lx.exists_ball_disjoint_fillH_right hPc fun y hy => lt_of_le_of_lt (hbeyond y hy) hx
  have hgcc : ContinuousOn gc Hbar := GW1P.continuousOn_of_tendsto hgc
  have hf' : ∀ x : ℝ, R < x → Tendsto (stChart s).1 (𝓝[H] (x : ℂ)) (𝓝 (f x : ℂ)) := fun x hx => hf x hx
  exact ⟨hbeyond, f, gc, Cc, hf', hf0, hgc, hgcc, hCc, g_zeroR hcD hf' hfreeY hgc hf0 hgcc,
    fun y hy => g_pos_of_posR hcD hf' hfreeY hgc hf0 hgcc hCc hy, tendsto_g_re_right hcD hf' hfreeY hgc hf0 hgcc hCc⟩

end InteractingSLE.Theorem14.SB.Sx
