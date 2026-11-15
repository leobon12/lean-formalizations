/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcWalk

/-!
# F2b′: B's seed at a tail stage is the right end of the retained union

Packet PROVE-AUX61-NOJUMP (round 21, D34, component A). **`realMax_retX_eq`** (deterministic, at a sample with the
walk facts `WalkGood`): at a tail stage `ℓ` (even, `relOff < ℓ`, B launching), B's point `stPt (run ℓ)` is the largest
real point of the retained union `A ∪ B_{<ℓ}`:
* `R = max (A ∩ ℝ)` has entered the walk before `ℓ` (`Lk.s2HullRight`, `entryStage_spec`);
* the walk prefix lies left of the walk's point by the record invariants (`recInv_ptRec_run_le`,
  `notMem_prefix_of_beyond`; PROVE-R6-CORNER's `isDrivenCurve_walkStage_old`).

Also **`isCompact_retX`** and the retained union as a pinch-invariant path image from `0`
(**`exists_path_retX`**, joining the two pinch-invariant prefixes).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Nc

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn Dv

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {ω : Ω}

/-- The retained union at a launch is compact. -/
theorem isCompact_retX (hg : WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    IsCompact (retX κ b jumps E u l k ℓ ω) := by
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hl'
  obtain ⟨pA, hp, -, -, -, hpA⟩ := hg.upath
  have hAc : IsCompact (upperPrefix κ b jumps E u l k ω) := hpA ▸ isCompact_Icc.image_of_continuousOn hp
  exact hAc.union (Lx.isCompact_prefixPhysSet_run _ _ hg.reg ℓ hnd)

/-- **B's point at a tail stage is the largest real point of the retained union.** -/
theorem realMax_retX_eq (hg : WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hoff : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ) (hev : ℓ % 2 = 0) :
    realMax (retX κ b jumps E u l k ℓ ω) =
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set s := ExplState.run κ b jumps w D ℓ with hs
  set Pn := SB.prefixPhysSet κ b jumps w D ℓ with hPn
  obtain ⟨pA, hpc, hp0, hpH, -, hpA⟩ := hg.upath
  obtain ⟨β, hβ, hβ0, hβr, hS1, -⟩ := hg.proper
  set A := upperPrefix κ b jumps E u l k ω with hAdef
  set R := realMax A with hRdef
  have hP := hg.reg
  have hlm := hg.noLeftMove
  have hlh := hg.noLeftHit
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hndd : stStatus s ≠ GW1Conn.stDead := not_dead_of_launch w D hl'
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) w D hl
  -- the records
  have hM : ∀ i, i < ℓ + 1 → stStatus (ExplState.run κ b jumps w D i) ≠ GW1Conn.stDone := fun i hi hd =>
    hnd (by rw [hs, Lx.run_eq_of_done w D hd ℓ (by omega)]; exact hd)
  have hfin := fin_before_first_done hM
  have hri := recInv_ptRec_run_le hP (N := ℓ) (fun j hj hlj => hfin j (by omega) hlj) hlm hlh
  have hrec : ∀ k, k ≤ ℓ → RecInv κ b jumps θ D k := fun k hk => (hri k hk).1
  have hpt : stPt s = stRecR s := by
    rcases (hri ℓ le_rfl).2 with h | h | h
    · exact absurd h hnd
    · exact absurd h hndd
    · exact h
  have hbeyond : ∀ y : ℝ, (y : ℂ) ∈ Pn → y ≤ stPt s := fun y hy => by
    by_contra hlt
    exact notMem_prefix_of_beyond hP hrec hlm hnd (hpt ▸ not_le.1 hlt) hy
  -- the entry of `R` before `ℓ`
  have hS1' : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by rw [hpA]; exact hS1
  obtain ⟨-, tR, htR, -⟩ := Lk.s2HullRight hpc hp0 hpH hβ hβ0 hS1'
  rw [hpA] at htR
  have hRphys : (R : ℂ) ∈ ExplState.physSet κ b jumps w D := by rw [← hβr, ← htR]; exact mem_range_self tR
  have hex := exists_mem_statePhysicalSet_succ (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) hRphys
  obtain ⟨hent, -⟩ := entryStage_spec κ θ b jumps hex
  have hso : startOff κ θ b jumps R D ≤ relOff κ θ b jumps R D := by unfold relOff; split_ifs <;> omega
  have hse : entryStage κ θ b jumps R D ≤ startOff κ θ b jumps R D + 1 := by unfold startOff; omega
  have hse' : startOff κ θ b jumps R D % 2 = 0 := startOff_even κ θ b jumps R D
  have hre : relOff κ θ b jumps R D % 2 = 0 := relOff_even κ θ b jumps R D
  have hel : entryStage κ θ b jumps R D + 1 ≤ ℓ := by omega
  have hRin : (R : ℂ) ∈ Pn := WalkIntRunChron.prefixPhysSet_mono w D hel hent
  -- the largest real point
  have hAc : IsCompact A := hpA ▸ isCompact_Icc.image_of_continuousOn hpc
  refine realMax_eq_of_le (isCompact_retX hg hl) (Or.inr (hg.pinv ℓ hnd).2) fun y hy => ?_
  rcases hy with hy | hy
  · exact (Lx.le_realMax_of_mem hAc hy).trans (hbeyond R hRin)
  · exact hbeyond y hy

/-- **The retained union at a launch is a pinch-invariant path image from `0`.** -/
theorem exists_path_retX (hg : WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
      LuM.PInv 0 (p '' Icc 0 1) ∧ p '' Icc 0 1 = retX κ b jumps E u l k ℓ ω := by
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hl'
  obtain ⟨pA, hpc, hp0, hpH, hpv, hpA⟩ := hg.upath
  have h0A : (0 : ℂ) ∈ pA '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩
  have hv : LuM.PInv 0 (retX κ b jumps E u l k ℓ ω) := by
    rcases (hg.pinv ℓ hnd).1 with h1 | ⟨q, hq⟩
    · have e : retX κ b jumps E u l k ℓ ω = pA '' Icc 0 1 := by
        unfold retX; rw [h1, ← hpA, union_eq_left]
        simpa using h0A
      rw [e]; exact hpv
    · have hq0 : q 0 ∈ pA '' Icc 0 1 := by rw [hq.2.1]; exact_mod_cast h0A
      have h2 := hpv.join (LuM.IsPrefixPath.isFFPath hq) hq0
      unfold retX; rw [← hpA, ← hq.2.2.2.2]; exact h2
  rcases hv with h1 | ⟨p, hp⟩
  · refine ⟨fun _ => 0, continuousOn_const, rfl, fun _ _ => le_rfl, ?_, ?_⟩
    · left
      ext z; simp only [mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨_, _, rfl⟩; simp
      · intro hz; exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hz]; simp⟩
    · rw [h1]; ext z; simp only [mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨_, _, rfl⟩; simp
      · intro hz; exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hz]; simp⟩
  · obtain ⟨hpc', hp0', -, hpH', hpA'⟩ := id hp
    refine ⟨p, hpc', by rw [hp0']; simp, hpH', ?_, hpA'⟩
    rw [hpA']; exact Or.inr ⟨p, hp⟩

end InteractingSLE.Theorem14.SB.Nc
