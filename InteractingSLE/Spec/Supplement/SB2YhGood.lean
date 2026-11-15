/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3DuWalk

/-!
# The retained union at a tail stage: package, seed, density of good times

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2` at a tail stage). At a launch of the boundary walk at a stage `n`
whose start state already contains `R = max (A ∩ ℝ)` (`A` the upper prefix, the hypotheses of CORNER's
`Dv.isDrivenCurve_walkStage_old`), for the retained union `X = A ∪ P_n` (`P_n` the walk's physical prefix):

* **`stage_good_facts`**: `X` is compact, `fill X` is a hull, `realMax X` is the stage's current point and bounds every
  real point of `X`; the canonical chart `Mo.hullChart (fill X) 0` has inverse boundary limits with finite fibres
  (CORNER's `exists_canon_package_pinv` for the stage path); the times of the piece in `ℍ ∖ fill X` are dense below
  its lifetime (Lemma S3's density `S3.Asm.hgd_of_launch_tailH` for `fill A`, upgraded to `fill X` by CORNER's
  `mem_diff_fill_union` through the tail lift).

The proof follows `Dv.isDrivenCurve_walkStage_old` and `Dv.isDrivenCurve_stage_fin`. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn Dv

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The retained union at a tail stage.** -/
theorem stage_good_facts {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β)
    (hR : (realMax (pA '' Icc 0 1) : ℂ) ∈
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hS3 : ∀ tR : ℝ≥0, β tR = (realMax (pA '' Icc 0 1) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H) :
    IsCompact (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∧
      IsHPHull (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ∧
      realMax (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) =
        stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∧
      (∀ y : ℝ, (y : ℂ) ∈ pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n →
        y ≤ stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ∧
      (∃ g : ℂ → ℂ, (∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH (pA '' Icc 0 1 ∪
          SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) 0).2.1 (𝓝[H] q) (𝓝 (g q))) ∧
        ∀ z, (g ⁻¹' {z} ∩ {w : ℂ | 0 ≤ w.im}).Finite) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < (D n).2 → t ∈ closure {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (D n).2 ∧
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t' ∈
          H \ fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)} := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D n with hs
  set A := pA '' Icc 0 1 with hAdef
  set Pn := SB.prefixPhysSet κ b jumps w D n with hPn
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hndd : stStatus s ≠ GW1Conn.stDead := not_dead_of_launch w D hl'
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) w D hl
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
  have hbeyond : ∀ y : ℝ, (y : ℂ) ∈ Pn → y ≤ stPt s := fun y hy => by
    by_contra hlt
    exact notMem_prefix_of_beyond hP hrec hlm hnd (hpt ▸ not_le.1 hlt) hy
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
  have hq0 := pcPt_zero_launch hP hW hl hpos
  obtain ⟨t₁, ht₁0, ht₁L⟩ : ∃ t₁ : ℝ≥0, 0 < t₁ ∧ (t₁ : ℝ≥0∞) < (D n).2 := by
    obtain ⟨r, hr0, hrL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hpos)
    exact ⟨r, by exact_mod_cast hr0, hrL⟩
  have h0L : ((0 : ℝ≥0) : ℝ≥0∞) < (D n).2 := pos_iff_ne_zero.2 hpos
  have hT2 : ∃ y ∈ T, y ≠ ((stPt s : ℝ) : ℂ) := ⟨pcPt s (D n) t₁, hTdef ▸ ⟨t₁, ht₁L.le, rfl⟩, fun h =>
    (ne_of_gt ht₁0) (hinj ht₁L h0L (h.trans hq0.symm))⟩
  obtain ⟨σ, hσ, hPσ, hTσ⟩ := exists_arc_of_cut hβ hPc hPp h0P hPr hTr hTp hPT hT2
  -- the good times of the piece for `A`
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨-, tR, htR, -, -, -, hright⟩ := Lk.s2HullRight hpc hp0 hpH hβ hβ0 hS1
  have hAH := Dv.isHPHull_fillH_path hpc hp0
  have hDom : (Mo.hullChart (fillH A) 0).2.1 '' H = H \ fillH A := (Mo.isDomainChart_hullChart hAH 0).image_eq
  have hden0 := S3.Asm.hgd_of_launch_tailH hP hW hl hAc.isClosed hDom hβ hβ0 hβr htR hR hright (hS3 tR htR)
  have hgoodeq : goodT (Mo.hullChart (fillH A) 0) s (D n) =
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2 ∧ pcPt s (D n) t ∈ H \ fillH A} := by
    ext t; simp only [goodT, hDom]
  rw [hgoodeq] at hden0
  -- the largest real point
  have hle : ∀ y : ℝ, (y : ℂ) ∈ A ∪ β '' Icc 0 σ → y ≤ stPt s := by
    rintro y (hy | hy)
    · exact (Lx.le_realMax_of_mem hAc hy).trans (hbeyond _ hR)
    · rw [← hPσ] at hy; exact hbeyond y hy
  have hX : A ∪ Pn = A ∪ β '' Icc 0 σ := by rw [hPσ]
  rw [hX]
  -- the canonical package of the stage path
  set X := A ∪ β '' Icc 0 σ with hXdef
  have hXc : IsCompact X := hAc.union (isCompact_Icc.image hβ.1)
  obtain ⟨p, hpc', hp0', hpH', hpv', himg⟩ := stagePath_pinv hpc hp0 hpH hpv hβ hβ0 σ
  obtain ⟨e, g, hrc, hgc, hgi, hgt, hgf, hgfr⟩ := exists_canon_package_pinv hpc' hp0' hpH' hpv'
  have hS1X : p '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by
    rw [himg]; exact union_subset hS1 ((image_subset_range _ _).trans (range_subset_closedLeftSide β))
  have hrc' : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1))
      ((Mo.hullChart (fillH (p '' Icc 0 1)) 0).recenter (-(-e))) := by rwa [neg_neg]
  obtain ⟨tL, γ, hγ⟩ := Lk.exists_tailLiftCurve hpc' hp0' hpH' hβ hβ0 hS1X hrc' hgc hgi hgt hgf
  have hA := isHPHull_fillH_path hpc' hp0'
  rw [himg] at hγ hgt hgi hgfr hA
  have hxX : ((stPt s : ℝ) : ℂ) ∈ X := Or.inr ⟨σ, ⟨bot_le, le_rfl⟩, hσ⟩
  have hRx : realMax X = stPt s := realMax_eq_of_le hXc hxX hle
  have htL : tL = σ := hβ.2.1 (by rw [hγ.1, hRx, hσ])
  rw [htL] at hγ
  refine ⟨hXc, hA, hRx, hle, ⟨g, hgt, hgf⟩, fun t ht => closure_mono ?_ (hden0 ht)⟩
  rintro t' ⟨ht'L, ht'⟩
  refine ⟨ht'L, ?_⟩
  have hT' : pcPt s (D n) t' ∈ T := by rw [hTdef]; exact ⟨t', ht'L, rfl⟩
  obtain ⟨τ, hτ, hτe⟩ := hTσ hT'
  have hτσ : σ < τ := by
    refine lt_of_le_of_ne hτ fun h => ?_
    rw [← h, hσ] at hτe
    have him : (0 : ℝ) < (pcPt s (D n) t').im := ht'.1
    rw [← hτe] at him
    simp at him
  have hmem := mem_diff_fill_union hAc hβ hA hγ hgt hgi hgfr (s := τ - σ) (tsub_pos_of_lt hτσ)
    (by rw [add_tsub_cancel_of_le hτ, hτe]; exact ht')
  rwa [add_tsub_cancel_of_le hτ, hτe] at hmem

end InteractingSLE.Theorem14.SB.Sx
