/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YhGood

/-!
# The retained union at a pure piece entry: entrance time, head, package, density

Packet PROVE-T14-SB2LIFT (round 33, D51 item 3: the root S2 clause). At a launch of the boundary walk at a stage `n`
whose start state does not contain `R = max (A ∩ ℝ)` while the piece visits `R` (a pure piece entry; the hypotheses of
CORNER's `Dv.isDrivenCurve_walkStage_new`), for the retained union `X = A ∪ P_n`:

* **`root_good_facts`**: the visit time `sh` of `R` is positive, below the lifetime, and the first visit; the head
  (the piece on `[0, sh]`) and the prefix lie in the compact hull `K_A`; `X` is compact, `fill X` is a hull, `realMax X
  = R` bounds every real point of `X`; the canonical chart of `fill X` has inverse boundary limits with finite fibres;
  the times after `sh` with the piece in `ℍ ∖ fill X` are dense below the lifetime; the seed is left of `R`.

The proof follows `Dv.isDrivenCurve_walkStage_new` and `Sx.stage_good_facts`. Deterministic.
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

/-- **The retained union at a pure piece entry.** -/
theorem root_good_facts {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β)
    (hRnew : (realMax (pA '' Icc 0 1) : ℂ) ∉
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hRtip : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = (realMax (pA '' Icc 0 1) : ℂ))
    (hshlt : ((visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (realMax (pA '' Icc 0 1)) : ℝ≥0) : ℝ≥0∞) < (D n).2)
    (hS3 : ∀ tR : ℝ≥0, β tR = (realMax (pA '' Icc 0 1) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H) :
    0 < visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax (pA '' Icc 0 1)) ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
        (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax (pA '' Icc 0 1))) =
        (realMax (pA '' Icc 0 1) : ℂ) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 →
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = (realMax (pA '' Icc 0 1) : ℂ) →
        visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax (pA '' Icc 0 1)) ≤ t) ∧
      (∀ t : ℝ≥0,
        t ≤ visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax (pA '' Icc 0 1)) →
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t ∈ hullK (pA '' Icc 0 1)) ∧
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n ⊆ hullK (pA '' Icc 0 1) ∧
      IsCompact (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∧
      IsHPHull (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ∧
      realMax (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) =
        realMax (pA '' Icc 0 1) ∧
      (∀ y : ℝ, (y : ℂ) ∈ pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n →
        y ≤ realMax (pA '' Icc 0 1)) ∧
      (∃ g : ℂ → ℂ, (∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH (pA '' Icc 0 1 ∪
          SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) 0).2.1 (𝓝[H] q) (𝓝 (g q))) ∧
        ∀ z, (g ⁻¹' {z} ∩ {w : ℂ | 0 ≤ w.im}).Finite) ∧
      (∀ t : ℝ≥0, ((visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
          (realMax (pA '' Icc 0 1)) + t : ℝ≥0) : ℝ≥0∞) < (D n).2 →
        t ∈ closure {t' : ℝ≥0 | ((visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
          (realMax (pA '' Icc 0 1)) + t' : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 ∧
          pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
            (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
              (realMax (pA '' Icc 0 1)) + t') ∈
            H \ fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)}) ∧
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < realMax (pA '' Icc 0 1) := by
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
  have hY1 : Pn ⊆ hullK A := by
    rw [hPσ]; exact (image_mono (Icc_subset_Icc_right hσtR.le)).trans hhead
  have hfill : fillH (A ∪ Pn) = fillH (A ∪ β '' Icc 0 tR) := by
    rw [fillH_union_of_subset_hullK hAc hAH hY1, fillH_union_of_subset_hullK hAc hAH hhead]
  have hrealK : ∀ y : ℝ, (y : ℂ) ∈ hullK A → y ≤ R := by
    intro y hy
    rcases hy with h | ⟨y', hy', he⟩
    · exact absurd h.1 (by simp [QuantumZipper.H])
    · rw [← Complex.ofReal_injective he]; exact hy'.2
  have hle : ∀ y : ℝ, (y : ℂ) ∈ A ∪ Pn → y ≤ R := by
    rintro y (hy | hy)
    · exact Lx.le_realMax_of_mem hAc hy
    · exact hrealK y (hY1 hy)
  have hle' : ∀ y : ℝ, (y : ℂ) ∈ A ∪ β '' Icc 0 tR → y ≤ R := by
    rintro y (hy | hy)
    · exact Lx.le_realMax_of_mem hAc hy
    · exact hrealK y (hhead hy)
  have hXc : IsCompact (A ∪ Pn) := hAc.union hPc
  have hRX : (R : ℂ) ∈ A ∪ Pn := by
    have hS : IsCompact {y : ℝ | (y : ℂ) ∈ A} :=
      Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage hAc
    have h0A : ((0 : ℝ) : ℂ) ∈ A := ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hp0]; simp⟩
    exact Or.inl (hS.sSup_mem ⟨0, h0A⟩)
  -- the head
  have hheadK : ∀ t : ℝ≥0, t ≤ sh → pcPt s (D n) t ∈ hullK A := by
    intro t ht
    rcases ht.lt_or_eq with hlt | heq
    · obtain ⟨t', ht'⟩ := hTr (hTdef ▸ ⟨t, (ENNReal.coe_le_coe.2 hlt.le).trans hshL, rfl⟩ : pcPt s (D n) t ∈ T)
      exact hhead ⟨t', ⟨bot_le, (hord1 t hlt t' ht').le⟩, ht'⟩
    · rw [heq, hsh, ← htR]; exact hhead ⟨tR, ⟨bot_le, le_rfl⟩, rfl⟩
  have hq0 := pcPt_zero_launch hP hW hl hpos
  have hsh' : pcPt s (D n) sh = (R : ℂ) := hsh
  have hq0' : pcPt s (D n) 0 = ((stPt s : ℝ) : ℂ) := hq0
  have hsh0 : 0 < sh := by
    refine pos_iff_ne_zero.2 fun h => hRseed ?_
    rw [← hsh', h, hq0']
  have hstR : stPt s < R := by
    have hP0 : ((stPt s : ℝ) : ℂ) ∈ Pn := by
      have : ((stPt s : ℝ) : ℂ) ∈ Pn ∩ T := hPT ▸ mem_singleton _
      exact this.1
    exact lt_of_le_of_ne (hle _ (Or.inr hP0)) fun h => hRseed (by rw [h])
  -- the canonical package of the stage path at the visit of `R`
  set X := A ∪ β '' Icc 0 tR with hXdef
  obtain ⟨p, hpc', hp0', hpH', hpv', himg⟩ := stagePath_pinv hpc hp0 hpH hpv hβ hβ0 tR
  obtain ⟨e, g, hrc, hgc, hgi, hgt, hgf, hgfr⟩ := exists_canon_package_pinv hpc' hp0' hpH' hpv'
  have hS1X : p '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by
    rw [himg]; exact union_subset hS1 ((image_subset_range _ _).trans (range_subset_closedLeftSide β))
  have hrc' : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1))
      ((Mo.hullChart (fillH (p '' Icc 0 1)) 0).recenter (-(-e))) := by rwa [neg_neg]
  obtain ⟨tL, γ, hγ⟩ := Lk.exists_tailLiftCurve hpc' hp0' hpH' hβ hβ0 hS1X hrc' hgc hgi hgt hgf
  have hA := isHPHull_fillH_path hpc' hp0'
  rw [himg] at hγ hgt hgi hgfr hA
  have hXc' : IsCompact X := hAc.union (isCompact_Icc.image hβ.1)
  have hxX : ((R : ℝ) : ℂ) ∈ X := Or.inr ⟨tR, ⟨bot_le, le_rfl⟩, htR⟩
  have hRx : realMax X = R := realMax_eq_of_le hXc' hxX hle'
  have htL : tL = tR := hβ.2.1 (by rw [hγ.1, hRx, htR])
  rw [htL] at hγ
  have hRxU : realMax (A ∪ Pn) = R := realMax_eq_of_le hXc hRX hle
  -- the density after `sh`
  have hAH' := isHPHull_fillH_path hpc hp0
  have hDom : (Mo.hullChart (fillH A) 0).2.1 '' H = H \ fillH A := (Mo.isDomainChart_hullChart hAH' 0).image_eq
  have hden0 := hgd_after hP hW hl hAc.isClosed hDom hβ hβr hord2 hright (hS3 tR htR)
  have hafter : ∀ t : ℝ≥0, sh < t → (t : ℝ≥0∞) < (D n).2 → pcPt s (D n) t ∈ β '' Ioi tR := by
    intro t ht htL'
    obtain ⟨t', ht'⟩ := hTr (hTdef ▸ ⟨t, htL'.le, rfl⟩ : pcPt s (D n) t ∈ T)
    exact ⟨t', hord2 t ht htL' t' ht', ht'⟩
  have hgood : ∀ u ∈ {v : ℝ≥0 | (v : ℝ≥0∞) < (D n).2} ∩ goodT (Mo.hullChart (fillH A) 0) s (D n), sh < u →
      u - sh ∈ {t' : ℝ≥0 | ((sh + t' : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 ∧
        pcPt s (D n) (sh + t') ∈ H \ fillH (A ∪ Pn)} := by
    rintro u ⟨huL', huL, hu⟩ hsu
    rw [hDom] at hu
    have hu' : sh + (u - sh) = u := add_tsub_cancel_of_le hsu.le
    refine ⟨by rw [hu']; exact huL, ?_⟩
    rw [hu', hfill]
    obtain ⟨τ, hτ, hτe⟩ := hafter u hsu huL'
    have hmem := mem_diff_fill_union hAc hβ hA hγ hgt hgi hgfr (s := τ - tR) (tsub_pos_of_lt hτ)
      (by rw [add_tsub_cancel_of_le hτ.le, hτe]; exact hu)
    rwa [add_tsub_cancel_of_le hτ.le, hτe] at hmem
  have hopen : IsOpen {v : ℝ≥0 | (v : ℝ≥0∞) < (D n).2} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hden : ∀ t : ℝ≥0, ((sh + t : ℝ≥0) : ℝ≥0∞) < (D n).2 →
      t ∈ closure {t' : ℝ≥0 | ((sh + t' : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 ∧
        pcPt s (D n) (sh + t') ∈ H \ fillH (A ∪ Pn)} :=
    mem_closure_shift hshlt (fun u hu huL => hopen.inter_closure ⟨huL, hden0 ⟨hu, huL⟩⟩) hgood
  refine ⟨hsh0, hsh, hshmin, hheadK, hY1, hXc, ?_, hRxU, hle, ⟨g, ?_, hgf⟩, hden, hstR⟩
  · rw [hfill]; exact hA
  · rw [hfill]; exact hgt

end InteractingSLE.Theorem14.SB.Sx
