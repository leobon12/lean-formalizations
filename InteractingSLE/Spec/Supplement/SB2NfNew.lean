/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcDrv
import InteractingSLE.Spec.Supplement.SB2NcRmax
import InteractingSLE.Spec.Supplement.SB2JbTop

/-!
# F2b′'s root at a pure piece entry: the entry chart, the head inside the hull

Packet PROVE-AUX61-NOJUMP (round 22, the root variant, D51/D57). At the root `ℓ = relOff` of a pure piece entry, the
relative piece is B's piece read from its visit time `sh` of `R = max (A ∩ ℝ)`. PROVE-R6-CORNER's
`Dv.isDrivenCurve_walkStage_new` gives a driven canonical stage curve for some offset; **`walkStage_new_root`** is its
proof with the conclusion strengthened as in `Nc.isDrivenCurve_walkStage_old_entry` (the offset makes the recentred
chart a right entry chart at `R`), and with the root's geometry:

* B's piece up to `sh` and B's prefix lie in the hull `K_A = hullK A` of the upper prefix (so they add nothing to the
  fill: `Dv.fillH_union_of_subset_hullK`);
* the retained union's largest real point is `R`.

`isRightEntryChart_congr`: the entry-chart property only sees the fill.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Nf

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn Dv Nc

/-- The entry-chart property only sees the fill. -/
theorem isRightEntryChart_congr {X X' : Set ℂ} (h : fillH X = fillH X') {R : ℝ} {c : Chart} :
    IsRightEntryChart X R c ↔ IsRightEntryChart X' R c := by
  unfold IsRightEntryChart; rw [h]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The root at a pure piece entry** (deterministic): CORNER's `Dv.isDrivenCurve_walkStage_new` with the offset a
right entry value at `R`, the head of the piece and B's prefix inside `K_A`, and `R` the largest real point of the
retained union. -/
theorem walkStage_new_root {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
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
    (hlife : (D n).2 - (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (realMax (pA '' Icc 0 1)) : ℝ≥0∞) ≠ 0)
    (hS3 : ∀ tR : ℝ≥0, β tR = (realMax (pA '' Icc 0 1) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H) :
    (∀ t : ℝ≥0, t ≤ visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
        (realMax (pA '' Icc 0 1)) →
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t ∈ hullK (pA '' Icc 0 1)) ∧
    SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n ⊆ hullK (pA '' Icc 0 1) ∧
    realMax (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) =
      realMax (pA '' Icc 0 1) ∧
    ∃ x₀ : ℝ, IsRightEntryChart (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
        (realMax (pA '' Icc 0 1))
        ((Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
          0).recenter x₀) ∧ IsDrivenCurve (canonCurve
      (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) x₀
      (fun t => pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
        (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
          (realMax (pA '' Icc 0 1)) + t))
      ((D n).2 - (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
        (realMax (pA '' Icc 0 1)) : ℝ≥0∞))) := by
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
  have hY1 : Pn ⊆ hullK A := by
    rw [hPσ]; exact (image_mono (Icc_subset_Icc_right hσtR.le)).trans hhead
  have hfill : fillH (A ∪ Pn) = fillH (A ∪ β '' Icc 0 tR) := by
    rw [fillH_union_of_subset_hullK hAc hAH hY1, fillH_union_of_subset_hullK hAc hAH hhead]
  simp_rw [canonCurve_congr_fill hfill]
  have hle : ∀ y : ℝ, (y : ℂ) ∈ A ∪ β '' Icc 0 tR → y ≤ R := by
    rintro y (hy | hy)
    · exact Lx.le_realMax_of_mem hAc hy
    · rcases hhead hy with h | ⟨y', hy', he⟩
      · exact absurd h.1 (by simp [QuantumZipper.H])
      · rw [← Complex.ofReal_injective he]; exact hy'.2
  have hRA : (R : ℂ) ∈ A := Nc.realMax_mem hAc (x := 0) ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hp0]; simp⟩
  have hRX : realMax (A ∪ β '' Icc 0 tR) = R := Dv.realMax_eq_of_le (hAc.union (isCompact_Icc.image hβ.1))
    (Or.inl hRA) hle
  have hRXn : realMax (A ∪ Pn) = R := Dv.realMax_eq_of_le (hAc.union hPc) (Or.inl hRA) fun y hy => by
    rcases hy with hy | hy
    · exact hle y (Or.inl hy)
    · rw [hPσ] at hy
      exact hle y (Or.inr ((image_mono (Icc_subset_Icc_right hσtR.le)) hy))
  have hconv : ∀ x₀ : ℝ, IsRightEntryChart (A ∪ β '' Icc 0 tR) (realMax (A ∪ β '' Icc 0 tR))
      ((Mo.hullChart (fillH (A ∪ β '' Icc 0 tR)) 0).recenter x₀) →
      IsRightEntryChart (A ∪ Pn) R ((Mo.hullChart (fillH (A ∪ Pn)) 0).recenter x₀) := fun x₀ h => by
    rw [hfill, isRightEntryChart_congr hfill]; rw [hRX] at h; exact h
  have hheadq : ∀ t : ℝ≥0, t ≤ sh → pcPt s (D n) t ∈ hullK A := by
    intro t ht
    rcases ht.lt_or_eq with htl | hte
    · obtain ⟨t', ht'⟩ := hTr (hTdef ▸ ⟨t, (ENNReal.coe_le_coe.2 htl.le).trans hshL, rfl⟩ :
        pcPt s (D n) t ∈ T)
      exact hhead ⟨t', ⟨bot_le, (hord1 t htl t' ht').le⟩, ht'⟩
    · rw [hte, hsh, ← htR]; exact hhead ⟨tR, ⟨bot_le, le_rfl⟩, rfl⟩
  refine ⟨hheadq, hY1, hRXn, ?_⟩
  -- the good times of the piece after `sh`
  have hAH' := isHPHull_fillH_path hpc hp0
  have hDom : (Mo.hullChart (fillH A) 0).2.1 '' H = H \ fillH A := (Mo.isDomainChart_hullChart hAH' 0).image_eq
  have hden0 := hgd_after hP hW hl hAc.isClosed hDom hβ hβr hord2 hright (hS3 tR htR)
  set q : ℝ≥0 → ℂ := fun t => pcPt s (D n) (sh + t) with hqdef
  have hq0 : q 0 = β tR := by simp only [hqdef, add_zero, htR]; exact hsh
  have hgood : ∀ u ∈ goodT (Mo.hullChart (fillH A) 0) s (D n), sh < u →
      u - sh ∈ {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (D n).2 - (sh : ℝ≥0∞) ∧ q t' ∈ H \ fillH A} := by
    rintro u ⟨huL, hu⟩ hsu
    refine ⟨?_, ?_⟩
    · rw [ENNReal.coe_sub]; exact tsub_le_tsub_right huL _
    · simp only [hqdef, add_tsub_cancel_of_le hsu.le]; rw [← hDom]; exact hu
  have hden : ∀ t : ℝ≥0, ((sh + t : ℝ≥0) : ℝ≥0∞) < (D n).2 →
      t ∈ closure {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (D n).2 - (sh : ℝ≥0∞) ∧ q t' ∈ H \ fillH A} :=
    mem_closure_shift hshlt (fun u hu huL => hden0 ⟨hu, huL⟩) hgood
  -- the piece after `sh` runs along `β` beyond `tR`
  have hafter : ∀ t : ℝ≥0, 0 < t → ((sh + t : ℝ≥0) : ℝ≥0∞) < (D n).2 → q t ∈ β '' Ici tR := by
    intro t ht htL
    obtain ⟨t', ht'⟩ := hTr (hTdef ▸ ⟨sh + t, htL.le, rfl⟩ : pcPt s (D n) (sh + t) ∈ T)
    exact ⟨t', (hord2 (sh + t) (lt_add_of_pos_right sh ht) htL t' ht').le, ht'⟩
  have hclosedβ : IsClosed (β '' Ici tR) :=
    (WalkCont.isClosedEmbedding_of_isProperCurve hβ).isClosedMap _ isClosed_Ici
  rcases eq_or_ne (D n).2 ⊤ with htop | hfinL
  · -- the infinite last piece
    have hLt : (D n).2 - (sh : ℝ≥0∞) = ⊤ := by rw [htop, ENNReal.top_sub_coe]
    rw [hLt]
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (D n).2 := fun t => by rw [htop]; exact ENNReal.coe_lt_top
    have hqc : Continuous q := by
      have : Continuous (pcPt s (D n)) := by
        rw [← continuousOn_univ]
        exact hpcc.mono fun t _ => (hlt t).le
      exact this.comp (continuous_const.add continuous_id)
    have hqi : Function.Injective q := fun a b' hab => add_left_cancel (hinj (hlt (sh + a)) (hlt (sh + b')) hab)
    have hdone : stStatus (ExplState.run κ b jumps w D (n + 1)) = GW1Conn.stDone := by
      by_contra hnd'
      exact fin_of_not_done hnd' hl htop
    have hphys := physSet_walk_eq_of_done (κ := κ) (θ := θ) (b := b) (J := jumps) (D := D) (n := n + 1)
      (Nat.succ_le_of_lt hlen) hdone
    have hsucc := prefixPhysSet_succ_of_launch hl'
    have hqβ : range q = β '' Ici tR := by
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨t, rfl⟩
        rcases eq_or_ne t 0 with h0 | h0
        · rw [h0, hq0]; exact mem_image_of_mem β self_mem_Ici
        · exact hafter t (pos_iff_ne_zero.2 h0) (hlt _)
      · rintro _ ⟨τ, hτ, rfl⟩
        have hmem : β τ ∈ SB.prefixPhysSet κ b jumps w D (n + 1) := by
          have := mem_range_self (f := β) τ
          rw [hβr, hphys] at this
          exact this
        rw [hsucc] at hmem
        rcases hmem with hP' | hT'
        · exfalso
          have hP'' : β τ ∈ Pn := hP'
          rw [hPσ] at hP''
          obtain ⟨τ', hτ', he⟩ := hP''
          have := hβ.2.1 he
          exact absurd (this ▸ hτ'.2 : τ ≤ σ) (not_le.2 (hσtR.trans_le hτ))
        · have hT'' : β τ ∈ T := by rw [← htipT]; exact hT'
          rw [hTdef] at hT''
          obtain ⟨t, -, ht⟩ := hT''
          rcases lt_trichotomy t sh with hlt' | heq | hgt
          · exact absurd (hord1 t hlt' τ ht.symm) (not_lt.2 hτ)
          · refine ⟨0, ?_⟩
            rw [hq0, ← ht, heq]; exact (hsh.trans htR.symm).symm
          · exact ⟨t - sh, by simp only [hqdef, add_tsub_cancel_of_le hgt.le]; exact ht⟩
    have hden' : ∀ t : ℝ≥0, t ∈ closure {t' : ℝ≥0 | q t' ∈ H \ fillH A} := fun t =>
      closure_mono (fun t' ht' => ht'.2) (hden t (hlt _))
    obtain ⟨x₀, hEC, hdr⟩ := isDrivenCurve_stage_top_entry hpc hp0 hpH hpv hβ hβ0 hS1 htR hle hqc hqi hq0 hqβ hden'
    exact ⟨x₀, hconv x₀ hEC, hdr⟩
  · -- a finite piece
    set L := (D n).2.toNNReal with hLdef
    have hLe : ((L : ℝ≥0) : ℝ≥0∞) = (D n).2 := ENNReal.coe_toNNReal hfinL
    have hshL' : sh < L := by have := hshlt; rw [← hLe] at this; exact_mod_cast this
    have hLsub : (D n).2 - (sh : ℝ≥0∞) = ((L - sh : ℝ≥0) : ℝ≥0∞) := by rw [← hLe, ENNReal.coe_sub]
    rw [hLsub] at hden ⊢
    have hLpos : 0 < L - sh := tsub_pos_of_lt hshL'
    have hlt : ∀ t : ℝ≥0, t < L - sh → ((sh + t : ℝ≥0) : ℝ≥0∞) < (D n).2 := fun t ht => by
      rw [← hLe]; exact_mod_cast (lt_tsub_iff_left.1 ht)
    have hqc : ContinuousOn q (Icc 0 (L - sh)) := by
      refine hpcc.comp (continuous_const.add continuous_id).continuousOn ?_
      intro t ht
      show ((sh + t : ℝ≥0) : ℝ≥0∞) ≤ (D n).2
      rw [← hLe]; exact_mod_cast ((le_tsub_iff_left hshL'.le).1 ht.2)
    have hqi : InjOn q (Iio (L - sh)) := fun a ha b' hb hab => add_left_cancel (hinj (hlt a ha) (hlt b' hb) hab)
    have hqβ : ∀ t, t ≤ L - sh → q t ∈ β '' Ici tR := by
      intro t ht
      rcases eq_or_ne t 0 with h0 | h0
      · rw [h0, hq0]; exact mem_image_of_mem β self_mem_Ici
      rcases eq_or_lt_of_le ht with htL | htL
      · have hcl : q t ∈ closure (q '' Ioo 0 (L - sh)) := by
          refine ((hqc t ⟨bot_le, ht⟩).mono Ioo_subset_Icc_self).mem_closure_image ?_
          rw [closure_Ioo hLpos.ne, htL]; exact right_mem_Icc.2 hLpos.le
        refine closure_minimal ?_ hclosedβ hcl
        rintro _ ⟨u, hu, rfl⟩
        exact hafter u hu.1 (hlt u hu.2)
      · exact hafter t (pos_iff_ne_zero.2 h0) (hlt t htL)
    have hden' : ∀ t : ℝ≥0, t < L - sh →
        t ∈ closure {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ ((L - sh : ℝ≥0) : ℝ≥0∞) ∧ q t' ∈ H \ fillH A} := fun t ht =>
      hden t (hlt t ht)
    obtain ⟨x₀, hEC, hdr⟩ := isDrivenCurve_stage_fin_entry hpc hp0 hpH hpv hβ hβ0 hS1 htR hle hLpos hqc hqi hq0 hqβ
      hden'
    exact ⟨x₀, hconv x₀ hEC, hdr⟩

/-- **The infinite last piece at a pure piece entry has infinite relative capacity** (deterministic; LIFTSET's
`Lk.canon_old_top` with the cut at the visit `tR` of `R`; the piece up to its visit time `sh` runs along the walk
from the cut to `tR`, so the capacity of the head and the shifted piece is `2 T` plus that of the head). -/
theorem canon_new_top {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
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
    (hlife : (D n).2 - (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (realMax (pA '' Icc 0 1)) : ℝ≥0∞) ≠ 0)
    (hS3 : ∀ tR : ℝ≥0, β tR = (realMax (pA '' Icc 0 1) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H)
    (htop : (D n).2 = ⊤) :
    ∃ x₁ : ℝ, IsDrivenCurve (canonCurve (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) x₁
      (fun t => pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
        (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
          (realMax (pA '' Icc 0 1)) + t)) ⊤) ∧
      capLife (canonCurve (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) x₁
      (fun t => pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
        (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
          (realMax (pA '' Icc 0 1)) + t)) ⊤) = ⊤ := by
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
  have hY1 : Pn ⊆ hullK A := by
    rw [hPσ]; exact (image_mono (Icc_subset_Icc_right hσtR.le)).trans hhead
  have hfill : fillH (A ∪ Pn) = fillH (A ∪ β '' Icc 0 tR) := by
    rw [fillH_union_of_subset_hullK hAc hAH hY1, fillH_union_of_subset_hullK hAc hAH hhead]
  simp_rw [canonCurve_congr_fill hfill]
  have hle : ∀ y : ℝ, (y : ℂ) ∈ A ∪ β '' Icc 0 tR → y ≤ R := by
    rintro y (hy | hy)
    · exact Lx.le_realMax_of_mem hAc hy
    · rcases hhead hy with h | ⟨y', hy', he⟩
      · exact absurd h.1 (by simp [QuantumZipper.H])
      · rw [← Complex.ofReal_injective he]; exact hy'.2
  -- the good times of the piece after `sh`
  have hAH' := isHPHull_fillH_path hpc hp0
  have hDom : (Mo.hullChart (fillH A) 0).2.1 '' H = H \ fillH A := (Mo.isDomainChart_hullChart hAH' 0).image_eq
  have hden0 := hgd_after hP hW hl hAc.isClosed hDom hβ hβr hord2 hright (hS3 tR htR)
  set q : ℝ≥0 → ℂ := fun t => pcPt s (D n) (sh + t) with hqdef
  have hq0 : q 0 = β tR := by simp only [hqdef, add_zero, htR]; exact hsh
  have hgood : ∀ u ∈ goodT (Mo.hullChart (fillH A) 0) s (D n), sh < u →
      u - sh ∈ {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (D n).2 - (sh : ℝ≥0∞) ∧ q t' ∈ H \ fillH A} := by
    rintro u ⟨huL, hu⟩ hsu
    refine ⟨?_, ?_⟩
    · rw [ENNReal.coe_sub]; exact tsub_le_tsub_right huL _
    · simp only [hqdef, add_tsub_cancel_of_le hsu.le]; rw [← hDom]; exact hu
  have hden : ∀ t : ℝ≥0, ((sh + t : ℝ≥0) : ℝ≥0∞) < (D n).2 →
      t ∈ closure {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (D n).2 - (sh : ℝ≥0∞) ∧ q t' ∈ H \ fillH A} :=
    mem_closure_shift hshlt (fun u hu huL => hden0 ⟨hu, huL⟩) hgood
  -- the piece after `sh` runs along `β` beyond `tR`
  have hafter : ∀ t : ℝ≥0, 0 < t → ((sh + t : ℝ≥0) : ℝ≥0∞) < (D n).2 → q t ∈ β '' Ici tR := by
    intro t ht htL
    obtain ⟨t', ht'⟩ := hTr (hTdef ▸ ⟨sh + t, htL.le, rfl⟩ : pcPt s (D n) (sh + t) ∈ T)
    exact ⟨t', (hord2 (sh + t) (lt_add_of_pos_right sh ht) htL t' ht').le, ht'⟩
  have hclosedβ : IsClosed (β '' Ici tR) :=
    (WalkCont.isClosedEmbedding_of_isProperCurve hβ).isClosedMap _ isClosed_Ici
  have hLt : (D n).2 - (sh : ℝ≥0∞) = ⊤ := by rw [htop, ENNReal.top_sub_coe]
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (D n).2 := fun t => by rw [htop]; exact ENNReal.coe_lt_top
  have hqc : Continuous q := by
    have : Continuous (pcPt s (D n)) := by
      rw [← continuousOn_univ]
      exact hpcc.mono fun t _ => (hlt t).le
    exact this.comp (continuous_const.add continuous_id)
  have hqi : Function.Injective q := fun a b' hab => add_left_cancel (hinj (hlt (sh + a)) (hlt (sh + b')) hab)
  have hdone : stStatus (ExplState.run κ b jumps w D (n + 1)) = GW1Conn.stDone := by
    by_contra hnd'
    exact fin_of_not_done hnd' hl htop
  have hphys := physSet_walk_eq_of_done (κ := κ) (θ := θ) (b := b) (J := jumps) (D := D) (n := n + 1)
    (Nat.succ_le_of_lt hlen) hdone
  have hsucc := prefixPhysSet_succ_of_launch hl'
  have hqβ : range q = β '' Ici tR := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨t, rfl⟩
      rcases eq_or_ne t 0 with h0 | h0
      · rw [h0, hq0]; exact mem_image_of_mem β self_mem_Ici
      · exact hafter t (pos_iff_ne_zero.2 h0) (hlt _)
    · rintro _ ⟨τ, hτ, rfl⟩
      have hmem : β τ ∈ SB.prefixPhysSet κ b jumps w D (n + 1) := by
        have := mem_range_self (f := β) τ
        rw [hβr, hphys] at this
        exact this
      rw [hsucc] at hmem
      rcases hmem with hP' | hT'
      · exfalso
        have hP'' : β τ ∈ Pn := hP'
        rw [hPσ] at hP''
        obtain ⟨τ', hτ', he⟩ := hP''
        have := hβ.2.1 he
        exact absurd (this ▸ hτ'.2 : τ ≤ σ) (not_le.2 (hσtR.trans_le hτ))
      · have hT'' : β τ ∈ T := by rw [← htipT]; exact hT'
        rw [hTdef] at hT''
        obtain ⟨t, -, ht⟩ := hT''
        rcases lt_trichotomy t sh with hlt' | heq | hgt
        · exact absurd (hord1 t hlt' τ ht.symm) (not_lt.2 hτ)
        · refine ⟨0, ?_⟩
          rw [hq0, ← ht, heq]; exact (hsh.trans htR.symm).symm
        · exact ⟨t - sh, by simp only [hqdef, add_tsub_cancel_of_le hgt.le]; exact ht⟩
  have hden' : ∀ t : ℝ≥0, t ∈ closure {t' : ℝ≥0 | q t' ∈ H \ fillH A} := fun t =>
    closure_mono (fun t' ht' => ht'.2) (hden t (hlt _))
  obtain ⟨x₀, hF⟩ := isDrivenCurve_stage_top hpc hp0 hpH hpv hβ hβ0 hS1 htR hle hqc hqi hq0 hqβ hden'
  -- the piece up to `sh` runs along `β` from the cut to `tR`
  have hhe := WalkCont.isClosedEmbedding_of_isProperCurve hβ
  have hpcsh : pcPt s (D n) '' Icc 0 sh = β '' Icc σ tR := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      rcases ht.2.lt_or_eq with htl | hte
      · obtain ⟨τ, hτ, he⟩ := hTσ (hTdef ▸ ⟨t, (ENNReal.coe_le_coe.2 htl.le).trans hshL, rfl⟩ :
          pcPt s (D n) t ∈ T)
        exact ⟨τ, ⟨hτ, (hord1 t htl τ he).le⟩, he⟩
      · rw [hte, hsh, ← htR]; exact mem_image_of_mem β ⟨hσtR.le, le_rfl⟩
    · have hsub : pcPt s (D n) '' Icc 0 sh ⊆ range β := fun z hz => by
        obtain ⟨t, ht, rfl⟩ := hz
        exact hTr (hTdef ▸ ⟨t, (ENNReal.coe_le_coe.2 ht.2).trans hshL, rfl⟩)
      have hSp : IsPreconnected (β ⁻¹' (pcPt s (D n) '' Icc 0 sh)) := by
        rw [← hhe.isInducing.isPreconnected_image, image_preimage_eq_of_subset hsub]
        exact isPreconnected_Icc.image _ (hpcc.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hshL)
      have hσS : σ ∈ β ⁻¹' (pcPt s (D n) '' Icc 0 sh) :=
        ⟨0, ⟨le_rfl, bot_le⟩, by rw [pcPt_zero_launch hP hW hl hpos, hσ]⟩
      have htRS : tR ∈ β ⁻¹' (pcPt s (D n) '' Icc 0 sh) := ⟨sh, ⟨bot_le, le_rfl⟩, by rw [hsh, htR]⟩
      rintro _ ⟨τ, hτ, rfl⟩
      exact hSp.Icc_subset hσS htRS hτ
  have hsplit : ∀ T : ℝ≥0, β '' Icc 0 tR ∪ q '' Icc 0 T = Pn ∪ pcPt s (D n) '' Icc 0 (sh + T) := by
    intro T
    have h1 : β '' Icc 0 tR = β '' Icc 0 σ ∪ β '' Icc σ tR := by
      rw [← image_union, Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ σ) hσtR.le]
    have h2 : pcPt s (D n) '' Icc 0 (sh + T) = pcPt s (D n) '' Icc 0 sh ∪ q '' Icc 0 T := by
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨t, ht, rfl⟩
        rcases le_total t sh with hts | hts
        · exact Or.inl ⟨t, ⟨bot_le, hts⟩, rfl⟩
        · refine Or.inr ⟨t - sh, ⟨bot_le, tsub_le_iff_left.2 ht.2⟩, ?_⟩
          simp only [hqdef, add_tsub_cancel_of_le hts]
      · rintro _ (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
        · exact ⟨t, ⟨bot_le, ht.2.trans le_self_add⟩, rfl⟩
        · exact ⟨sh + t, ⟨bot_le, add_le_add le_rfl ht.2⟩, rfl⟩
    rw [h1, h2, hpcsh, hPσ, union_assoc]
  have hcapK : ∀ T : ℝ≥0, IsHPHull (fillH (β '' Icc 0 tR ∪ q '' Icc 0 T)) ∧
      ConformalImage.hcapSet (fillH (β '' Icc 0 tR ∪ q '' Icc 0 T)) =
        2 * T + ConformalImage.hcapSet (fillH (β '' Icc 0 tR)) := fun T => by
    have hT := hcap_prefix_piece hP hW hl htop (sh + T)
    have h0 := hcap_prefix_piece hP hW hl htop sh
    have e0 : β '' Icc 0 tR = Pn ∪ pcPt s (D n) '' Icc 0 sh := by
      have := hsplit 0
      rw [add_zero] at this
      rw [← this]
      refine (union_eq_left.2 ?_).symm
      rintro _ ⟨t, ht, rfl⟩
      have ht0 : t = 0 := le_antisymm ht.2 bot_le
      rw [ht0, hq0]; exact mem_image_of_mem β ⟨bot_le, le_rfl⟩
    rw [hsplit T]
    refine ⟨hT.1, ?_⟩
    rw [hT.2, e0, h0.2]
    push_cast; ring
  -- LIFTSET's `Lk.canon_old_top` argument, with the cut at `tR`
  obtain ⟨e, g, γ, hA, hgt, hgi, hgc, hgfr, hγ⟩ := Lk.cut_package hpc hp0 hpH hpv hβ hβ0 hS1 htR hle
  set X := A ∪ β '' Icc 0 tR with hXdef
  have hXc : IsCompact X := hAc.union (isCompact_Icc.image hβ.1)
  obtain ⟨φ₀, hφc, hφ0, hφm, hφs, hqφ⟩ := Dv.exists_timeChange_top hβ hqc hqi hq0 hqβ
  set q' : ℝ≥0 → ℂ := fun t => β (tR + φ₀ t) with hq'def
  have hqq' : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ⊤ → q t = q' t := fun t _ => hqφ t
  have hgood' : {t' : ℝ≥0 | q t' ∈ H \ fillH A} ⊆ Dv.canonGood X q' ⊤ := by
    rintro t' ht'
    have ht'0 : 0 < t' := by
      refine lt_of_le_of_ne bot_le fun h => ?_
      have ht0 : q 0 ∈ H \ fillH A := h ▸ ht'
      rw [hq0, htR] at ht0
      have him : (0 : ℝ) < (((R : ℝ) : ℂ)).im := ht0.1
      simp at him
    refine ⟨le_top, ?_⟩
    have ht'' : q t' ∈ H \ fillH A := ht'
    rw [hqφ t'] at ht''
    exact Dv.mem_diff_fill_union hAc hβ hA hγ hgt hgi hgfr (by rw [← hφ0]; exact hφm ht'0) ht''
  have hdq : ∀ t : ℝ≥0, t ∈ closure (Dv.canonGood X q' ⊤) := fun t => closure_mono hgood' (hden' t)
  have hζl : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (γ (φ₀ t) - ((-e : ℝ) : ℂ))) (𝓝 (q' t)) :=
    fun t => hγ.2.2.2 (φ₀ t)
  have hζc : Continuous (fun t => γ (φ₀ t)) := hγ.2.1.1.comp hφc
  have hval : ∀ t, Dv.canonVal X x₀ q ⊤ t = γ (φ₀ t) + ((e - x₀ : ℝ) : ℂ) := fun t => by
    rw [Lk.canonVal_congr hqq']
    exact Lk.canonVal_eq_of_lift_shift hA hζc (fun t => hγ.2.1.2.2.1 _) hζl hgt hgi hgfr (hdq t) x₀
  have hex : e = x₀ := by
    have h0 := hF.zero
    unfold Dv.canonCurve at h0
    simp only [↓reduceIte, Real.toNNReal_zero] at h0
    rw [hval 0, hφ0, hγ.2.2.1, zero_add] at h0
    have := congrArg Complex.re h0
    simp at this; linarith
  have hφtop : Tendsto φ₀ atTop atTop :=
    tendsto_atTop_atTop_of_monotone hφm.monotone fun y => ⟨(hφs y).choose, (hφs y).choose_spec.ge⟩
  have hqtr : Tendsto (fun t => ‖q t‖) atTop atTop := by
    have h1 : Tendsto (fun t => tR + φ₀ t) atTop atTop :=
      tendsto_atTop_mono (fun t => le_add_self) hφtop
    exact (hβ.2.2.2.comp h1).congr fun t => by simp only [Function.comp, hqφ t]
  have hD := Mo.isDomainChart_hullChart hA 0
  have hcc := Mo.isConformal_hullChart hA 0
  have hoff : BdryOff (Mo.hullChart (fillH X) 0) := Lk.bdryOff_of_ext hcc hgc hgi hgt
  obtain ⟨C, hC⟩ := Lk.hullChart_ext_bounded hA hgt
  have hs₂ : ∀ z, (stChart (ExplState.init 0)).1 z = z := fun z => by
    simp [ExplState.init, stChart, Chart.id, Chart.recenter]
  have hgdq : ∀ t, t ∈ closure (goodTp (Mo.hullChart (fillH X) 0) q ⊤) := fun t => by
    have hG : goodTp (Mo.hullChart (fillH X) 0) q ⊤ = Dv.canonGood X q' ⊤ := by
      rw [← Dv.canonGood_congr hqq']
      ext t'; simp only [goodTp, Dv.canonGood, hD.2.1, mem_ofPred_eq]
    rw [hG]; exact hdq t
  have hheadX : β '' Icc 0 tR ⊆ hullK X := by
    rintro _ ⟨τ, hτ, rfl⟩
    have hmem : β τ ∈ X := Or.inr ⟨τ, hτ, rfl⟩
    rcases (show (0 : ℝ) ≤ (β τ).im from hβ.2.2.1 τ).lt_or_eq with hpos' | hzero
    · exact Or.inl (mem_fillH_of_mem_closure hpos' (subset_closure hmem))
    · have hre : β τ = (((β τ).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      rw [hre] at hmem ⊢
      exact Or.inr ⟨(β τ).re, ⟨FinRel.realMin_le_of_mem hXc hmem, Lx.le_realMax_of_mem hXc hmem⟩, rfl⟩
  have hKpc : IsCompact (β '' Icc 0 tR) := isCompact_Icc.image hβ.1
  rw [hex] at hγ
  have hqr : ∀ t, q t ∈ range β := fun t => image_subset_range _ _ (hqβ ▸ mem_range_self t)
  have hcap := Lk.capLife_root_top hγ hβ hcc.1.continuousOn hcc.2.2 hoff hs₂ hqc hqi hq0
    (fun t => hqβ ▸ mem_range_self t) hgdq hqtr hA hXc hD hgc hgi hgt hC hheadX hKpc (image_subset_range _ _) hqc
    hqr hcapK
  refine ⟨x₀, hF, ?_⟩
  rw [Lk.canonCurve_top_eq_stCurvep hA]
  exact hcap

end InteractingSLE.Theorem14.SB.Nf
