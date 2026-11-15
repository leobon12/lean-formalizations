/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2GiRoot

/-!
# The retained union's largest real point at the relative root is `R`

Packet PROVE-GW2-GEOM2, round 17 (decision D79). CONDFIN's root line mean (`Cy.hmean_root_obj`) reads the root
offset through the right entry chart at `realMax X` (`X = Nc.retX`, the retained union), NOJUMP's 9F gives it at
`R = realMax A`. They agree on the root event:

* **`prefix_subset_hullK_new`**: at a pure piece entry B's prefix lies in `K_A` (the cut of the walk's
  parametrization at the seed, before the visit of `R`; the opening of CORNER's `Dv.isDrivenCurve_walkStage_new`);
* **`realMax_retX_root`**: at a sample with the walk facts, B launching at `ℓ` and entering `R` before its lifetime,
  `realMax X = R` (a mark entry: `Gi.realMax_retX_eq_of_explored` and the piece starting at `R`; a pure piece entry:
  the prefix in `K_A`).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Gj

open Sec7.PocketTraversal Sec7.Lemma71C Dv Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **At a pure piece entry B's prefix lies in `K_A`.** -/
theorem prefix_subset_hullK_new {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im)
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β)
    (hRnew : (realMax (pA '' Icc 0 1) : ℂ) ∉
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hRtip : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = (realMax (pA '' Icc 0 1) : ℂ))
    (hlife : (D n).2 - (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (realMax (pA '' Icc 0 1)) : ℝ≥0∞) ≠ 0)
    : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n ⊆ hullK (pA '' Icc 0 1) := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D n with hs
  set A := pA '' Icc 0 1 with hAdef
  set Pn := SB.prefixPhysSet κ b jumps w D n with hPn
  set R := realMax A with hRdef
  set sh := visitTime s (D n) R with hshdef
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) w D hl
  obtain ⟨hshL, hsh, hshmin⟩ := visitTime_spec hP hl hRtip
  have hshlt : (sh : ℝ≥0∞) < (D n).2 := lt_of_le_of_ne hshL fun h => hlife (by rw [← h, tsub_self])
  -- S2's hull of the upper prefix and the visit of `R`
  obtain ⟨-, tR, htR, -, hhead, -, hright⟩ := Lk.s2HullRight hpc hp0 hpH hβ hβ0 hS1
  have hRold : β tR ∉ statePhysicalSet 0 s := by rw [htR]; exact hRnew
  obtain ⟨hord1, hord2⟩ := startPiece_order hP hW hl hpos hβ hβ0 hβr hRold (hsh.trans htR.symm)
    (fun t ht h => hshmin t ht (h.trans htR)) hshlt
  -- the cut of `β` at the seed
  have hPc : IsCompact Pn := Lx.isCompact_prefixPhysSet_run w D hP n hnd
  have hPp : IsPreconnected Pn := by
    rcases hpinv with h | ⟨p, hp⟩
    · rw [h]; exact isPreconnected_singleton
    · rw [← hp.2.2.2.2]; exact isPreconnected_Icc.image _ hp.1
  have h0P : β 0 ∈ Pn := by
    rw [hβ0]; exact Or.inl (Or.inl (by simp [hw, boundaryWalkSpec]))
  have hPr : Pn ⊆ range β := by
    rw [hβr]; exact statePhysicalSet_subset_physSet (κ := κ) (b := b) (jumps := jumps) (D := D) hlen.le
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  obtain ⟨T, hTdef⟩ : ∃ T : Set ℂ, T = pcPt s (D n) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} := ⟨_, rfl⟩
  have htipT := htip.trans hTdef.symm
  have hTr : T ⊆ range β := by rw [hβr, ← htipT]; exact tipSet_subset_physSet_launch hl
  have hpcc := continuousOn_pcPt_launch hP hl
  have hTp : IsPreconnected T := hTdef ▸ (WalkSide.isPreconnected_le_ennreal _).image _ hpcc
  have hPT : Pn ∩ T = {((stPt s : ℝ) : ℂ)} := by
    rw [← htipT, inter_comm]; exact tip_inter_old_eq hW hl
  have hinj := pcPt_injOn_launch hP hW hl
  have hRT : (R : ℂ) ∈ T := hTdef ▸ ⟨sh, hshL, hsh⟩
  have hRseed : (R : ℂ) ≠ ((stPt s : ℝ) : ℂ) := fun h => hRnew (by
    have : ((stPt s : ℝ) : ℂ) ∈ Pn ∩ T := hPT ▸ mem_singleton _
    rw [h]; exact this.1)
  obtain ⟨σ, hσ, hPσ, hTσ⟩ := exists_arc_of_cut hβ hPc hPp h0P hPr hTr hTp hPT ⟨R, hRT, hRseed⟩
  have hσtR : σ < tR := by
    obtain ⟨τ, hτ, he⟩ := hTσ hRT
    have hτR : τ = tR := hβ.2.1 (he.trans htR.symm)
    rw [← hτR]
    refine lt_of_le_of_ne hτ fun h => hRseed ?_
    rw [← he, ← h, hσ]
  -- fills and the largest real point
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  have hAH : ∀ z ∈ A, 0 ≤ z.im := by rintro _ ⟨r, hr, rfl⟩; exact hpH r hr
  rw [hPσ]; exact (image_mono (Icc_subset_Icc_right hσtR.le)).trans hhead

variable {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

/-- **The retained union's largest real point at a root sample is `R`.** -/
theorem realMax_retX_root {ω : Ω} (hg : Nc.WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hent : Nd.entrR κ b jumps E u l k ℓ ω < Nc.bLife b jumps E ℓ ω) :
    realMax (Nc.retX κ b jumps E u l k ℓ ω) = realMax (upperPrefix κ b jumps E u l k ω) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  set s := ExplState.run κ b jumps w D ℓ with hs
  set A := upperPrefix κ b jumps E u l k ω with hAdef
  set R := realMax A with hRdef
  obtain ⟨pA, hpc, hp0, hpH, -, hpA⟩ := hg.upath
  obtain ⟨β, hβ, hβ0, hβr, hS1, -⟩ := hg.proper
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hl'
  have hX : Nc.retX κ b jumps E u l k ℓ ω = A ∪ SB.prefixPhysSet κ b jumps w D ℓ := rfl
  have hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 ∧ pcPt s (D ℓ) t = (R : ℂ) := by
    by_contra hv
    have he := Ck.entrTime_eq_life hv
    have : Nd.entrR κ b jumps E u l k ℓ ω = (D ℓ).2 := he
    rw [this] at hent
    exact lt_irrefl _ hent
  have hτ : Nd.entrR κ b jumps E u l k ℓ ω = (visitTime s (D ℓ) R : ℝ≥0∞) := Ck.entrTime_eq_visitTime hvis
  have hpos : (D ℓ).2 ≠ 0 := (lt_of_le_of_lt (zero_le (α := ℝ≥0∞)) hent).ne'
  have hlife : (D ℓ).2 - (visitTime s (D ℓ) R : ℝ≥0∞) ≠ 0 := by
    rw [← hτ]; exact (tsub_pos_of_lt hent).ne'
  have hAc : IsCompact A := by rw [hAdef, ← hpA]; exact isCompact_Icc.image_of_continuousOn hpc
  have h0A : ((0 : ℝ) : ℂ) ∈ A := by rw [hAdef, ← hpA]; exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hp0]; simp⟩
  have hRA : (R : ℂ) ∈ A := Nc.realMax_mem hAc h0A
  by_cases hold : (R : ℂ) ∈ statePhysicalSet 0 s
  · -- a mark entry: the piece starts at `R`
    have h0 : visitTime s (D ℓ) R = 0 := Lk.visitTime_eq_zero_of_old hg.reg hg.chain hl hpos hold
    have hP0 : pcPt s (D ℓ) 0 = (R : ℂ) := by
      have := (visitTime_spec hg.reg hl hvis).2.1
      rwa [h0] at this
    have hst : ((stPt s : ℝ) : ℂ) = (R : ℂ) := (pcPt_zero_launch hg.reg hg.chain hl hpos).symm.trans hP0
    rw [Gi.realMax_retX_eq_of_explored hg hl hold]
    exact_mod_cast hst
  · -- a pure piece entry: the prefix lies in `K_A`
    have hsub := prefix_subset_hullK_new hg.reg hg.chain hl hpos (hg.pinv ℓ hnd).1 hpc hp0 hpH hβ hβ0 hβr
      (by rw [hpA]; exact hS1) (by rw [hpA]; exact hold) (by rw [hpA]; exact hvis) (by rw [hpA]; exact hlife)
    rw [hpA] at hsub
    rw [hX]
    refine Dv.realMax_eq_of_le (Nc.isCompact_retX hg hl) (Or.inl hRA) fun y hy => ?_
    rcases hy with hy | hy
    · exact Lx.le_realMax_of_mem hAc hy
    · rcases hsub hy with h | ⟨y', hy', he⟩
      · exact absurd (fillH_subset_H _ h) (by show ¬ 0 < ((y : ℝ) : ℂ).im; simp)
      · rw [← Complex.ofReal_injective he]; exact hy'.2

end InteractingSLE.Theorem14.SB.Gj
