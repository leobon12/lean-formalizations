/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3DuWalk

/-!
# SB2(2)'s joint stage induction: the matching of the two good sets

Packet PROVE-SB2-LIFTSET (round 20). The run-chart stage curve `stCurvep` reads the piece at the times
`goodTp c q L` (the point in `c⁻¹ '' ℍ = ℍ ∖ fill A`, `A` the upper prefix); CORNER's canonical curve `Dv.canonCurve`
reads it at `Dv.canonGood X q L` (the point in `ℍ ∖ fill X`, `X = A ∪ prefix_n`). At a stage whose start state already
contains `R = max (A ∩ ℝ)` (every relative stage `j ≥ 2`) the two sets agree:

* the prefix is the initial arc `β([0, σ])` of a proper parametrization `β` of the walk, with the seed at `β σ`, and the
  piece runs along `β([σ, ∞))` (`Dv.exists_arc_of_cut`, as in `Dv.isDrivenCurve_walkStage_old`);
* a point of the piece in `ℍ` is `β (σ + s)` with `s > 0`; off `fill A` it is off `fill X`
  (`Dv.mem_diff_fill_union`, through the tail lift of `β` for the hull chart of `X`).

Results: **`canonGood_eq_old`** (walk level) and **`goodTp_eq_canonGood_old`** (with `c⁻¹ '' ℍ = ℍ ∖ fill A`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Sec7.PocketTraversal Sec7.Lemma71C LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The cut at an old stage** (walk level): the prefix is the initial arc `β([0, σ])` with the seed at `β σ`, the
piece runs along `β([σ, ∞))`, and the seed is the largest real point of `A ∪ β([0, σ])` (`R = max (A ∩ ℝ)` explored). -/
theorem old_cut {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {A : Set ℂ} (hAc : IsCompact A) {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hR : (realMax A : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) :
    ∃ σ : ℝ≥0, β σ = ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℝ) : ℂ) ∧
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n = β '' Icc 0 σ ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 →
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t ∈ β '' Ici σ) ∧
      ∀ y : ℝ, (y : ℂ) ∈ A ∪ β '' Icc 0 σ →
        y ≤ stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D n with hs
  set Pn := SB.prefixPhysSet κ b jumps w D n with hPn
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hndd : stStatus s ≠ GW1Conn.stDead := Dv.not_dead_of_launch w D hl'
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
  obtain ⟨σ, hσ, hPσ, hTσ⟩ := Dv.exists_arc_of_cut hβ hPc hPp h0P hPr hTr hTp hPT hT2
  refine ⟨σ, hσ, hPσ, fun t ht => hTσ (by rw [hTdef]; exact ⟨t, ht, rfl⟩), ?_⟩
  rintro y (hy | hy)
  · exact (Lx.le_realMax_of_mem hAc hy).trans (hbeyond _ hR)
  · rw [← hPσ] at hy; exact hbeyond y hy

/-- **The hull chart of `A ∪ β([0, σ])` at a cut** (CORNER's canonical package with the tail lift of `β` after
`σ`). -/
theorem cut_package {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β) {σ : ℝ≥0} {x : ℝ} (hσ : β σ = (x : ℂ))
    (hle : ∀ y : ℝ, (y : ℂ) ∈ pA '' Icc 0 1 ∪ β '' Icc 0 σ → y ≤ x) :
    ∃ (e : ℝ) (g : ℂ → ℂ) (γ : ℝ≥0 → ℂ), IsHPHull (fillH (pA '' Icc 0 1 ∪ β '' Icc 0 σ)) ∧
      (∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH (pA '' Icc 0 1 ∪ β '' Icc 0 σ)) 0).2.1 (𝓝[H] q) (𝓝 (g q))) ∧
      EqOn g (Mo.hullChart (fillH (pA '' Icc 0 1 ∪ β '' Icc 0 σ)) 0).2.1 H ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧
      MapsTo g (Hbar \ H) (frontier (H \ fillH (pA '' Icc 0 1 ∪ β '' Icc 0 σ))) ∧
      Lk.IsTailLiftCurve (Mo.hullChart (fillH (pA '' Icc 0 1 ∪ β '' Icc 0 σ)) 0) x (-e) β σ γ := by
  set A := pA '' Icc 0 1 with hAdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨p, hpc', hp0', hpH', hpv', himg⟩ := Dv.stagePath_pinv hpc hp0 hpH hpv hβ hβ0 σ
  set X := A ∪ β '' Icc 0 σ with hXdef
  have hXc : IsCompact X := hAc.union (isCompact_Icc.image hβ.1)
  obtain ⟨e, g, hrc, hgc, hgi, hgt, hgf, hgfr⟩ := Dv.exists_canon_package_pinv hpc' hp0' hpH' hpv'
  have hS1X : p '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by
    rw [himg]; exact union_subset hS1 ((image_subset_range _ _).trans (Dv.range_subset_closedLeftSide β))
  have hrc' : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1))
      ((Mo.hullChart (fillH (p '' Icc 0 1)) 0).recenter (-(-e))) := by rwa [neg_neg]
  obtain ⟨tL, γ, hγ⟩ := Lk.exists_tailLiftCurve hpc' hp0' hpH' hβ hβ0 hS1X hrc' hgc hgi hgt hgf
  have hA := Dv.isHPHull_fillH_path hpc' hp0'
  rw [himg] at hγ hgt hgi hgfr hA
  have hxX : (x : ℂ) ∈ X := Or.inr ⟨σ, ⟨bot_le, le_rfl⟩, hσ⟩
  have hRx : realMax X = x := Dv.realMax_eq_of_le hXc hxX hle
  have htL : tL = σ := hβ.2.1 (by rw [hγ.1, hRx, hσ])
  rw [htL, hRx] at hγ
  exact ⟨e, g, γ, hA, hgt, hgi, hgc, hgfr, hγ⟩

/-- **The good sets agree at an old stage** (walk level): with the upper prefix `A` a pinch-invariant path image from
`0` on the closed left of a proper parametrization `β` of the walk, and `R = max (A ∩ ℝ)` already explored at stage
`n`, the canonical good times of the piece for `A ∪ prefix_n` are its times in `ℍ ∖ fill A`. -/
theorem canonGood_eq_old {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
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
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) :
    Dv.canonGood (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
        (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 =
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2 ∧
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t ∈ H \ fillH (pA '' Icc 0 1)} := by
  classical
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  set A := pA '' Icc 0 1 with hAdef
  refine Subset.antisymm (fun t ht => ⟨ht.1, ht.2.1, fun hf => ht.2.2 (fillH_mono subset_union_left hf)⟩) ?_
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨σ, hσ, hPσ, hTσ, hle⟩ := old_cut hP hW hlm hlh hl hpos hpinv hAc hβ hβ0 hβr hR
  obtain ⟨e, g, γ, hA, hgt, hgi, -, hgfr, hγ⟩ := cut_package hpc hp0 hpH hpv hβ hβ0 hS1 hσ hle
  rintro t ⟨htL', htH⟩
  refine ⟨htL', ?_⟩
  rw [hPσ]
  obtain ⟨τ, hτ, hτe⟩ := hTσ t htL'
  have hτσ : σ < τ := by
    refine lt_of_le_of_ne hτ fun h => ?_
    rw [← h, hσ] at hτe
    have him : (0 : ℝ) < (pcPt s (D n) t).im := htH.1
    rw [← hτe] at him
    simp at him
  obtain ⟨u, rfl⟩ : ∃ u : ℝ≥0, τ = σ + u := ⟨τ - σ, (add_tsub_cancel_of_le hτ).symm⟩
  have hu : 0 < u := by
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    rw [h0, add_zero] at hτσ
    exact lt_irrefl _ hτσ
  rw [← hτe] at htH ⊢
  exact Dv.mem_diff_fill_union hAc hβ hA hγ hgt hgi hgfr hu htH

/-- **The run-chart good times are the canonical good times at an old stage**, for a chart `c` with
`c⁻¹ '' ℍ = ℍ ∖ fill A`. -/
theorem goodTp_eq_canonGood_old {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
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
    {c : Chart} (hDom : c.2.1 '' H = H \ fillH (pA '' Icc 0 1)) :
    goodTp c (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 =
      Dv.canonGood (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
        (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 := by
  rw [canonGood_eq_old hP hW hlm hlh hl hpos hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hR]
  ext t
  simp only [goodTp, hDom, mem_ofPred_eq]

end InteractingSLE.Theorem14.SB.Lk
