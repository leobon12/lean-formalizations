/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3DuArc
import InteractingSLE.Spec.Supplement.SBS3LtDensity
import InteractingSLE.Spec.Supplement.SB2McRun
import InteractingSLE.Spec.Supplement.SB2LpStep
import InteractingSLE.Spec.Supplement.SB2MaSet
import InteractingSLE.Spec.Supplement.SB2LuAcc
import InteractingSLE.Spec.Supplement.SB2MdLift
import InteractingSLE.Spec.Supplement.SB2HEntry
import InteractingSLE.Spec.Supplement.WalkIntRunChronCarrier
import InteractingSLE.Spec.Supplement.SB2JwOrder
import InteractingSLE.Spec.Supplement.SB2JyTip
import InteractingSLE.Spec.Supplement.SB2JyEnd
import InteractingSLE.Spec.Supplement.SB2JwStage0
import InteractingSLE.Spec.Supplement.SB2LkDom
import InteractingSLE.Spec.Supplement.S9BJoint

/-!
# D5's F2a along the lower walk: the stage curves of a sample

Worker PROVE-R6-CORNER (round 9). The deterministic walk instantiation of `Dv.SB2LowerStageDrivenStatement`
(`SBS3DvStage`): at a sample with regular launches, GW1's walk chain facts, no left moves or hits, pinch-invariant
prefixes, a proper parametrization `β` of the walk with the upper prefix `A` on its closed left, and Lemma S3's tail
form in `ℍ` after the visit to `R = max (A ∩ ℝ)`.

* `isDrivenCurve_walkStage_old`: a stage whose start state already contains `R` (the prefix is `β([0, σ])` with the
  seed at `β σ`, beyond every real point of `A` and the prefix; the piece runs along `β([σ, ∞))`);
* `isDrivenCurve_walkStage_new`: stage `0` at a pure piece entry, read from the piece's visit time `sh` of `R`
  (`startPiece_order`: before `sh` the piece is on `β([0, t_R))`, after it on `β((t_R, ∞))`; the prefix and
  `β([0, t_R])` lie in the compact hull `K_A`, so they do not change the fill);
* `fillH_union_of_subset_hullK`, `canonCurve_congr_fill`, `mem_closure_shift`: the fill and density bookkeeping;
* `visitTime_eq_zero_of_old`: an old point is visited only at the seed, at time `0`;
* **`isDrivenCurve_walkStage`**: the case split on the relative stage (the entry stage of `R`, the mark and arc
  entries, `relOff`), giving drivenness at every non-zero stage whose actual piece launches.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Dv

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- A launch record rules out a dead state. -/
theorem not_dead_of_launch (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ')) :
    stStatus (ExplState.run κ b jumps spec D k) ≠ GW1Conn.stDead := by
  intro hd
  have hins := (eq_launch_of_launches spec D hl).1
  have hsame : ExplState.run κ b jumps spec D (k + 1) = ExplState.run κ b jumps spec D k := by
    rw [run_succ, hins]
    exact isTerminal_flowStep (Or.inr hd) k (D k) θ' (instrTime spec k)
  have hnone := launches_run_of_le (κ := κ) (b := b) (jumps := jumps) spec D (le_refl k)
  rw [hsame, hnone] at hl
  cases hl

/-- **F2a at a stage whose explored part already contains `R`** (deterministic): along the right walk with regular
launches, the walk chain facts and no left moves or hits, at a launched stage `n` of positive lifetime whose prefix is
pinch-invariant, with the upper prefix `A` (a pinch-invariant path image from `0`) on the closed left of a proper
parametrization `β` of the walk, `R = max (A ∩ ℝ)` in the explored part at `n` and the tail form of Lemma S3 in `ℍ`
after the visit to `R`: the canonical stage curve of the actual piece for `A ∪ prefix_n` is driven. -/
theorem isDrivenCurve_walkStage_old {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
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
    ∃ x₀ : ℝ, IsDrivenCurve (canonCurve
      (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) x₀
      (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2) := by
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
  have hAH := isHPHull_fillH_path hpc hp0
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
  have hq0' : pcPt s (D n) 0 = β σ := by rw [hq0, hσ]
  rcases eq_or_ne (D n).2 ⊤ with htop | hfinL
  · -- the infinite last piece
    rw [htop] at hpcc hinj hden0 hTdef ⊢
    have hqc : Continuous (pcPt s (D n)) := by
      rw [← continuousOn_univ]
      exact hpcc.mono fun t _ => (show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    have hqi : Function.Injective (pcPt s (D n)) := fun a b' hab =>
      hinj (show (a : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top) (show (b' : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top) hab
    have hdone : stStatus (ExplState.run κ b jumps w D (n + 1)) = GW1Conn.stDone := by
      by_contra hnd'
      exact fin_of_not_done hnd' hl htop
    have hphys := physSet_walk_eq_of_done (κ := κ) (θ := θ) (b := b) (J := jumps) (D := D) (n := n + 1)
      (Nat.succ_le_of_lt hlen) hdone
    have hsucc := prefixPhysSet_succ_of_launch hl'
    have hqβ : range (pcPt s (D n)) = β '' Ici σ := by
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨t, rfl⟩; exact hTσ (hTdef ▸ ⟨t, (show (t : ℝ≥0∞) ≤ ⊤ from le_top), rfl⟩)
      · rintro _ ⟨τ, hτ, rfl⟩
        have hmem : β τ ∈ SB.prefixPhysSet κ b jumps w D (n + 1) := by
          have := mem_range_self (f := β) τ
          rw [hβr, hphys] at this
          exact this
        rw [hsucc] at hmem
        rcases hmem with hP' | hT'
        · have hP'' : β τ ∈ Pn := hP'
          rw [hPσ] at hP''
          obtain ⟨τ', hτ', he⟩ := hP''
          have := hβ.2.1 he
          have hτσ : τ = σ := le_antisymm (this ▸ hτ'.2) hτ
          rw [hτσ, ← hq0']; exact mem_range_self 0
        · have hT'' : β τ ∈ T := by rw [← htipT]; exact hT'
          rw [hTdef] at hT''
          obtain ⟨t, -, ht⟩ := hT''
          exact ⟨t, ht⟩
    have hden : ∀ t : ℝ≥0, t ∈ closure {t' : ℝ≥0 | pcPt s (D n) t' ∈ H \ fillH A} := fun t => by
      have := hden0 (show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
      refine closure_mono (fun t' ht' => ht'.2) this
    exact isDrivenCurve_stage_top hpc hp0 hpH hpv hβ hβ0 hS1 hσ hle hqc hqi hq0' hqβ hden
  · -- a finite piece
    set L := (D n).2.toNNReal with hLdef
    have hLe : ((L : ℝ≥0) : ℝ≥0∞) = (D n).2 := ENNReal.coe_toNNReal hfinL
    rw [← hLe] at hpcc hinj hden0 hTdef ⊢
    have hLpos : 0 < L := by
      have := pos_iff_ne_zero.2 hpos
      rw [← hLe] at this; exact_mod_cast this
    have hqc : ContinuousOn (pcPt s (D n)) (Icc 0 L) :=
      hpcc.mono fun t ht => (show (t : ℝ≥0∞) ≤ L by exact_mod_cast ht.2)
    have hqi : InjOn (pcPt s (D n)) (Iio L) := fun a ha b' hb hab =>
      hinj (show (a : ℝ≥0∞) < L by exact_mod_cast ha) (show (b' : ℝ≥0∞) < L by exact_mod_cast hb) hab
    have hqβ : ∀ t, t ≤ L → pcPt s (D n) t ∈ β '' Ici σ := fun t ht =>
      hTσ (hTdef ▸ ⟨t, by exact_mod_cast ht, rfl⟩)
    have hden : ∀ t : ℝ≥0, t < L →
        t ∈ closure {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (L : ℝ≥0∞) ∧ pcPt s (D n) t' ∈ H \ fillH A} := fun t ht =>
      hden0 (show (t : ℝ≥0∞) < L by exact_mod_cast ht)
    exact isDrivenCurve_stage_fin hpc hp0 hpH hpv hβ hβ0 hS1 hσ hle hLpos hqc hqi hq0' hqβ hden

/-! ### Fills -/

/-- Points of the compact hull `K_A` add nothing to the fill of `A ⊆ ℍ̄`. -/
theorem fillH_union_of_subset_hullK {A Y : Set ℂ} (hA : IsCompact A) (hAH : ∀ z ∈ A, 0 ≤ z.im)
    (hY : Y ⊆ hullK A) : fillH (A ∪ Y) = fillH A := by
  refine Subset.antisymm ?_ (fillH_mono subset_union_left)
  have h1 : fillH (A ∪ Y) ⊆ fillH (fillH A ∪ (A ∪ Y)) := fillH_mono subset_union_right
  have h2 : fillH (fillH A ∪ (A ∪ Y)) = fillH (fillH A) := by
    refine Supp9B.fillH_eq_of_subset_union_real subset_union_left ?_
    rintro z (hz | hz | hz)
    · exact Or.inl hz
    · by_cases hzH : z ∈ H
      · exact Or.inl (mem_fillH_of_mem_closure hzH (subset_closure hz))
      · exact Or.inr (le_antisymm (not_lt.1 hzH) (hAH z hz))
    · rcases hY hz with h | ⟨y, -, rfl⟩
      · exact Or.inl h
      · exact Or.inr (by simp)
  exact h1.trans (h2 ▸ Lk.fillH_fillH_subset hA)

/-- The canonical curve only depends on the fill of the explored set. -/
theorem canonCurve_congr_fill {X X' : Set ℂ} (h : fillH X = fillH X') (x₀ : ℝ) (q : ℝ≥0 → ℂ) (L : ℝ≥0∞) :
    canonCurve X x₀ q L = canonCurve X' x₀ q L := by
  unfold canonCurve canonVal canonGood
  rw [h]

/-- Density transported along the time shift `u ↦ u − sh`. -/
theorem mem_closure_shift {G G' : Set ℝ≥0} {sh : ℝ≥0} {L : ℝ≥0∞} (hshL : (sh : ℝ≥0∞) < L)
    (hG : ∀ u : ℝ≥0, sh ≤ u → (u : ℝ≥0∞) < L → u ∈ closure G) (hGG' : ∀ u ∈ G, sh < u → u - sh ∈ G') :
    ∀ t : ℝ≥0, ((sh + t : ℝ≥0) : ℝ≥0∞) < L → t ∈ closure G' := by
  have hpos : ∀ t : ℝ≥0, 0 < t → ((sh + t : ℝ≥0) : ℝ≥0∞) < L → t ∈ closure G' := by
    intro t ht htL
    have hu : sh < sh + t := lt_add_of_pos_right sh ht
    have hcl := hG (sh + t) hu.le htL
    have hcl' : sh + t ∈ closure (Ioi sh ∩ G) := isOpen_Ioi.inter_closure ⟨hu, hcl⟩
    have hmap : MapsTo (fun u : ℝ≥0 => u - sh) (Ioi sh ∩ G) G' := fun u hu' => hGG' u hu'.2 hu'.1
    have := map_mem_closure (continuous_id.sub continuous_const) hcl' hmap
    simpa using this
  intro t htL
  rcases eq_or_lt_of_le (bot_le : (⊥ : ℝ≥0) ≤ t) with h0 | ht
  · rw [← h0]
    obtain ⟨ε, hε0, hεL⟩ : ∃ ε : ℝ≥0, 0 < ε ∧ ((sh + ε : ℝ≥0) : ℝ≥0∞) < L := by
      obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hshL
      refine ⟨r - sh, tsub_pos_of_lt (by exact_mod_cast hr1), ?_⟩
      rw [add_tsub_cancel_of_le (by exact_mod_cast hr1.le)]; exact hr2
    have hsub : Ioo 0 ε ⊆ closure G' := fun t' ht' =>
      hpos t' ht'.1 (lt_of_le_of_lt (by exact_mod_cast (add_le_add_right ht'.2.le sh : sh + t' ≤ sh + ε)) hεL)
    have := closure_mono hsub
    rw [closure_closure, closure_Ioo hε0.ne] at this
    exact this ⟨le_rfl, hε0.le⟩
  · exact hpos t ht htL

/-- **F2a at the start piece of a pure piece entry** (deterministic): as `isDrivenCurve_walkStage_old`, but `R` is new
at stage `n` and is visited by its piece; the piece is read from its visit time `sh` of `R`, with positive lifetime
left. -/
theorem isDrivenCurve_walkStage_new {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
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
    ∃ x₀ : ℝ, IsDrivenCurve (canonCurve
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
    exact isDrivenCurve_stage_top hpc hp0 hpH hpv hβ hβ0 hS1 htR hle hqc hqi hq0 hqβ hden'
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
    exact isDrivenCurve_stage_fin hpc hp0 hpH hpv hβ hβ0 hS1 htR hle hLpos hqc hqi hq0 hqβ hden'

/-- A launched piece of positive lifetime visits an old point only at its seed, at time `0`: the visit time of an old
point is `0`. -/
theorem visitTime_eq_zero_of_old {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {R : ℝ}
    (hR : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) :
    visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R = 0 := by
  classical
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have hint := tip_inter_old_eq hW hl
  unfold visitTime
  by_cases hne : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = R
  · obtain ⟨t, ht, he⟩ := hne
    have hmem : (R : ℂ) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 ∩
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) := by
      refine ⟨?_, hR⟩
      rw [htip]; exact ⟨t, ht, he⟩
    rw [hint, mem_singleton_iff] at hmem
    have h0 : pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) 0 = R :=
      (pcPt_zero_launch hP hW hl hpos).trans hmem.symm
    exact le_antisymm (csInf_le (OrderBot.bddBelow _) ⟨by simp, h0⟩) bot_le
  · simp only [not_exists, not_and] at hne
    have he : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2 ∧
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = R} = ∅ :=
      eq_empty_of_forall_notMem fun t ht => hne t ht.1 ht.2
    rw [he, NNReal.sInf_empty]

/-- **F2a at a sample** (deterministic): along the right walk with regular launches, the walk chain facts, no left
moves or hits and pinch-invariant prefixes, with the upper prefix `A` (a pinch-invariant path image from `0`) on the
closed left of a proper parametrization `β` of the walk and Lemma S3's tail form in `ℍ` after the visit to
`R = max (A ∩ ℝ)`: at every relative stage `j` that is not a zero stage and whose actual piece launches, the canonical
stage curve is driven. Stage `0` at a pure piece entry is read from the visit time of `R`; every other stage starts
from a state whose explored part contains `R`. -/
theorem isDrivenCurve_walkStage {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k)
    (hpinv : ∀ n, stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ GW1Conn.stDone →
      LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {A : Set ℂ} (hA : pA '' Icc 0 1 = A)
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : A ⊆ InteractingSLE.closedLeftSide β)
    (hS3 : ∀ tR : ℝ≥0, β tR = (realMax A : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ A ∩ H)
    {j : ℕ} (hodd : j % 2 ≠ 1) (hzr : j = 0 → ¬ ZeroRoot κ θ b jumps (realMax A) D)
    (hlife : (D (j + relOff κ θ b jumps (realMax A) D)).2 -
      ((if j = 0 then visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
          (relOff κ θ b jumps (realMax A) D)) (D (relOff κ θ b jumps (realMax A) D))
          (realMax A) else 0 : ℝ≥0) : ℝ≥0∞) ≠ 0)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
      (j + relOff κ θ b jumps (realMax A) D + 1)).2.2.2.1
        (j + relOff κ θ b jumps (realMax A) D) ≠ none) :
    ∃ x₀ : ℝ, IsDrivenCurve (canonCurve
      (A ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D
        (j + relOff κ θ b jumps (realMax A) D)) x₀
      (fun t => pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
          (j + relOff κ θ b jumps (realMax A) D))
        (D (j + relOff κ θ b jumps (realMax A) D))
        ((if j = 0 then visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
          (relOff κ θ b jumps (realMax A) D)) (D (relOff κ θ b jumps (realMax A) D))
          (realMax A) else 0) + t))
      ((D (j + relOff κ θ b jumps (realMax A) D)).2 -
        ((if j = 0 then visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
          (relOff κ θ b jumps (realMax A) D)) (D (relOff κ θ b jumps (realMax A) D))
          (realMax A) else 0 : ℝ≥0) : ℝ≥0∞))) := by
  classical
  subst hA
  set w := boundaryWalkSpec b jumps θ true with hw
  set A := pA '' Icc 0 1 with hAdef
  set R := realMax A with hRdef
  set o := relOff κ θ b jumps R D with ho
  -- the entry of `R`
  obtain ⟨-, tR, htR, -⟩ := Lk.s2HullRight hpc hp0 hpH hβ hβ0 hS1
  have hRphys : (R : ℂ) ∈ ExplState.physSet κ b jumps w D := by rw [← hβr, ← htR]; exact mem_range_self tR
  have hex := exists_mem_statePhysicalSet_succ (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) hRphys
  obtain ⟨hent, -⟩ := entryStage_spec κ θ b jumps hex
  have hoff := startOff_eq κ θ b jumps R D
  have hso : startOff κ θ b jumps R D ≤ o := by rw [ho]; unfold relOff; split_ifs <;> omega
  have hse : entryStage κ θ b jumps R D ≤ startOff κ θ b jumps R D + 1 := by unfold startOff; omega
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch w D hl'
  by_cases hj : j = 0
  · -- relative stage `0`
    subst hj
    simp only [zero_add, ↓reduceIte] at hl hl' hlife hnd ⊢
    have hpos : (D o).2 ≠ 0 := fun h => hlife (by rw [h]; exact zero_tsub _)
    by_cases hold : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps w D o)
    · -- `R` is already explored: the piece starts at its seed
      have hsh0 : visitTime (ExplState.run κ b jumps w D o) (D o) R = 0 := visitTime_eq_zero_of_old hP hW hl hpos hold
      simp only [hsh0, zero_add, ENNReal.coe_zero, tsub_zero]
      exact isDrivenCurve_walkStage_old hP hW hlm hlh hl hpos (hpinv o hnd) hpc hp0 hpH hpv hβ hβ0 hβr hS1 hold hS3
    · -- a pure piece entry: the piece visits `R`
      have hnm : ¬ MarkEntry κ θ b jumps R D := fun hm => hold (by
        have he1 := hoff.1 hm.1
        have : o = entryStage κ θ b jumps R D + 1 := by rw [ho, relOff_of_mark κ θ b jumps hm]; omega
        rw [this]; exact hent)
      have hna : ¬ ArcEntry κ θ b jumps R D := fun ha => hzr rfl ⟨ha, hnm⟩
      have hoe : o = entryStage κ θ b jumps R D := by rw [ho, relOff_of_not_mark κ θ b jumps hnm]; exact hoff.2 hna
      have hnew : (R : ℂ) ∈ SB.prefixPhysSet κ b jumps w D (o + 1) := by rw [hoe]; exact hent
      rw [prefixPhysSet_succ_of_launch hl'] at hnew
      obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
      have hRtip : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D o).2 ∧ pcPt (ExplState.run κ b jumps w D o) (D o) t = (R : ℂ) := by
        rcases hnew with h | h
        · exact absurd h hold
        · rw [htip] at h; obtain ⟨t, ht, he⟩ := h; exact ⟨t, ht, he⟩
      exact isDrivenCurve_walkStage_new hP hW hl hpos (hpinv o hnd) hpc hp0 hpH hpv hβ hβ0 hβr hS1 hold hRtip
        hlife hS3
  · -- a later stage: `R` is explored before it
    simp only [hj, ↓reduceIte, zero_add, ENNReal.coe_zero, tsub_zero] at hlife ⊢
    have hge : entryStage κ θ b jumps R D + 1 ≤ j + o := by omega
    have hold := statePhysicalSet_mono (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) hge hent
    exact isDrivenCurve_walkStage_old hP hW hlm hlh hl hlife (hpinv _ hnd) hpc hp0 hpH hpv hβ hβ0 hβr hS1 hold hS3

end InteractingSLE.Theorem14.SB.Dv




