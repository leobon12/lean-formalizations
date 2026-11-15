/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcDrv

/-!
# The root piece's canonical curve is driven in the chart recentred at the right entry value (deterministic)

Packet PROVE-GW2-GEOM2, round 16 (decision D70: `Mz.CanonIdentOn` at `relOff`). At a pure piece entry the relative
root is B's piece read from its visit time `sh` of `R = max (A ∩ ℝ)`. CORNER's `Dv.isDrivenCurve_walkStage_new` gives a
driven canonical curve for *some* offset; the identification needs the offset that makes the recentred chart a right
entry chart at `R` (NOJUMP did the same for the tails, `Nc.isDrivenCurve_walkStage_old_entry`).

* `isRightEntryChart_congr_fill`: the entry clause only sees the fill;
* **`isDrivenCurve_walkStage_new_entry`**: CORNER's proof verbatim, finished with NOJUMP's
  `Nc.isDrivenCurve_stage_fin_entry` / `Nc.isDrivenCurve_stage_top_entry`, and the head `P[0, sh]` of the piece
  inside `K_A` (it runs along the walk's parametrization before the visit of `R`, `startPiece_order`).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Gi

open Sec7.PocketTraversal Sec7.Lemma71C Dv Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

/-- The right entry clause only depends on the fill of the explored set. -/
theorem isRightEntryChart_congr_fill {X X' : Set ℂ} (h : fillH X = fillH X') {R : ℝ} {c : Chart} :
    IsRightEntryChart X R c ↔ IsRightEntryChart X' R c := by
  unfold IsRightEntryChart; rw [h]

/-- Two offsets recentring the same chart into right entry charts at the same point agree. -/
theorem eq_of_isRightEntryChart {X : Set ℂ} {R : ℝ} {c : Chart} {e₁ e₂ : ℝ}
    (h₁ : IsRightEntryChart X R (c.recenter e₁)) (h₂ : IsRightEntryChart X R (c.recenter e₂)) : e₁ = e₂ := by
  obtain ⟨-, ⟨f₁, hf₁, hl₁⟩, -, -⟩ := h₁
  obtain ⟨-, ⟨f₂, hf₂, hl₂⟩, -, -⟩ := h₂
  -- at every `x > R` the two boundary values differ by `e₂ - e₁`
  have hxe : ∀ x : ℝ, R < x → f₁ x + e₁ = f₂ x + e₂ := by
    intro x hx
    have : (𝓝[H] (x : ℂ)).NeBot := Exist.StagedLaw.neBot_nhdsWithin_H_real x
    have t₁ := (hf₁ x hx).add_const (e₁ : ℂ)
    have t₂ := (hf₂ x hx).add_const (e₂ : ℂ)
    have heq : (fun z => (c.recenter e₁).1 z + (e₁ : ℂ)) = fun z => (c.recenter e₂).1 z + (e₂ : ℂ) := by
      funext z; simp only [Chart.recenter, sub_add_cancel]
    rw [heq] at t₁
    have := tendsto_nhds_unique t₁ t₂
    exact_mod_cast this
  have h1 : Tendsto (fun x => f₁ x + e₁) (𝓝[>] R) (𝓝 (0 + e₁)) := hl₁.add_const e₁
  have h2 : Tendsto (fun x => f₂ x + e₂) (𝓝[>] R) (𝓝 (0 + e₂)) := hl₂.add_const e₂
  have h1' : Tendsto (fun x => f₂ x + e₂) (𝓝[>] R) (𝓝 (0 + e₁)) :=
    h1.congr' (eventually_nhdsWithin_of_forall fun x hx => hxe x hx)
  have := tendsto_nhds_unique h1' h2
  simpa using this

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **F2a at the start piece of a pure piece entry, with the entry offset** (deterministic): CORNER's
`Dv.isDrivenCurve_walkStage_new` with the conclusion strengthened as in NOJUMP's `Nc.isDrivenCurve_walkStage_old_entry`
(the offset makes the recentred chart of `A ∪ prefix_n` a right entry chart at `R`), and the head of the piece before
its visit time `sh` of `R` inside `K_A`. -/
theorem isDrivenCurve_walkStage_new_entry {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
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
    ∃ x₀ : ℝ, IsRightEntryChart (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
        (realMax (pA '' Icc 0 1))
        ((Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
          0).recenter x₀) ∧
      IsDrivenCurve (canonCurve
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
  have hheadP : ∀ t : ℝ≥0, t ≤ sh → pcPt s (D n) t ∈ hullK A := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [h, hsh, ← htR]; exact hhead ⟨tR, ⟨bot_le, le_rfl⟩, rfl⟩
    · have hTt : pcPt s (D n) t ∈ T := hTdef ▸ ⟨t, (ENNReal.coe_le_coe.2 ht).trans hshL, rfl⟩
      obtain ⟨τ, hτ⟩ := hTr hTt
      exact hτ ▸ hhead ⟨τ, ⟨bot_le, (hord1 t h τ hτ).le⟩, rfl⟩
  refine ⟨hheadP, ?_⟩
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
  have hentX : ∀ {x₀ : ℝ}, IsRightEntryChart (A ∪ β '' Icc 0 tR) (realMax (A ∪ β '' Icc 0 tR))
      ((Mo.hullChart (fillH (A ∪ β '' Icc 0 tR)) 0).recenter x₀) →
      IsRightEntryChart (A ∪ Pn) R ((Mo.hullChart (fillH (A ∪ Pn)) 0).recenter x₀) := by
    intro x₀ hent
    have hXc : IsCompact (A ∪ β '' Icc 0 tR) := hAc.union (isCompact_Icc.image hβ.1)
    have hRX : (R : ℂ) ∈ A ∪ β '' Icc 0 tR := Or.inr ⟨tR, ⟨bot_le, le_rfl⟩, htR⟩
    rw [Dv.realMax_eq_of_le hXc hRX hle, ← hfill] at hent
    exact (isRightEntryChart_congr_fill hfill).2 hent
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
    obtain ⟨x₀, hent, hdrv⟩ := Nc.isDrivenCurve_stage_top_entry hpc hp0 hpH hpv hβ hβ0 hS1 htR hle hqc hqi hq0 hqβ
      hden'
    exact ⟨x₀, hentX hent, hdrv⟩
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
    obtain ⟨x₀, hent, hdrv⟩ := Nc.isDrivenCurve_stage_fin_entry hpc hp0 hpH hpv hβ hβ0 hS1 htR hle hLpos hqc hqi hq0
      hqβ hden'
    exact ⟨x₀, hentX hent, hdrv⟩

end InteractingSLE.Theorem14.SB.Gi
