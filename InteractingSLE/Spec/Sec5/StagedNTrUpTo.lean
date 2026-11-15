/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrObs

/-!
# Prop 5.9's switching rule only reads the stages up to their switching times

Packet PROVE-STAGED-NODETRANSFER (towards `NodeGluePast`). PROVE-STAGED-REPJ's `StageAt`/`PieceAt` compare stages at
two samples on their whole lifetime. For the glued past (causality: the canonical past of a later stage is read before
the restart) only agreement **up to the switching time** is available. This file shows that it suffices:

* `StageUpTo d d' ω ω' T`: start, driver, marks and clock agree on `[0, T]`, both stages alive there;
* `StageUpTo.clkInv`, `StageUpTo.mem_swSet`: hitting and inverse of clock values `g ≤ clk T` agree;
* **`StageUpTo.mem_swEv`**, `StageUpTo.swT`, `StageUpTo.nextStart`: the switch events at grid points `G n m ≤ clk T`
  (the grid increasing in its second index) and the switch data on them agree;
* `PieceUpTo`, `CanonUpTo` (the candidate pieces of a list agree up to the switching times of its prefixes);
* **`canonR_canonY_upTo`**: the canonical reached events and starts agree; **`mem_swGen_upTo`**: the generators of the
  switch σ-algebras agree.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedNTr

open Prop59System Prop59Stage Prop59Pieces StagedCand StagedAdapt StagedRepJ

/-! ### Stages agreeing up to a time -/

section Stage

variable {Ω Ω' : Type*} {nL₀ nR₀ : ℕ}

/-- **Two stages agree up to the time `T`** at the samples `ω`, `ω'`. -/
structure StageUpTo {j : ℕ} (d : StageData Ω (nL₀ + j) (nR₀ + j)) (d' : StageData Ω' (nL₀ + j) (nR₀ + j)) (ω : Ω)
    (ω' : Ω') (T : ℝ≥0) : Prop where
  y : d.y ω = d'.y ω'
  W : ∀ u ≤ T, d.W u ω = d'.W u ω'
  VL : ∀ i, ∀ u ≤ T, d.VL i u ω = d'.VL i u ω'
  VR : ∀ k, ∀ u ≤ T, d.VR k u ω = d'.VR k u ω'
  lt : ∀ u ≤ T, (u : ℝ≥0∞) < d.ζ ω ∧ (u : ℝ≥0∞) < d'.ζ ω'
  clk : ∀ u ≤ T, d.clk ω u = d'.clk ω' u

variable {hnL : 0 < nL₀} {hnR : 0 < nR₀} {j : ℕ} {d : StageData Ω (nL₀ + j) (nR₀ + j)}
  {d' : StageData Ω' (nL₀ + j) (nR₀ + j)} {ω : Ω} {ω' : Ω'} {T : ℝ≥0}

/-- **Clock values reached by time `T` are hit at the same piece time.** -/
theorem StageUpTo.clkInv (h : StageUpTo d d' ω ω' T) (hm : StrictMono (d.clk ω)) (hm' : StrictMono (d'.clk ω'))
    {g : ℝ≥0} (hg : g ≤ d.clk ω T) :
    (ω ∈ clkHit d g ↔ ω' ∈ clkHit d' g) ∧ Prop59System.clkInv d g ω = Prop59System.clkInv d' g ω' ∧
      Prop59System.clkInv d g ω ≤ T := by
  classical
  have hle : ∀ {s : ℝ≥0}, d.clk ω s = g → s ≤ T := fun {s} hs => by
    by_contra hlt
    push Not at hlt
    have := hm hlt
    rw [hs] at this
    exact absurd hg (not_le.2 this)
  have hle' : ∀ {s : ℝ≥0}, d'.clk ω' s = g → s ≤ T := fun {s} hs => by
    by_contra hlt
    push Not at hlt
    have := hm' hlt
    rw [hs, ← h.clk T le_rfl] at this
    exact absurd hg (not_le.2 this)
  have hiff : ω ∈ clkHit d g ↔ ω' ∈ clkHit d' g := by
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s, by rw [← h.clk s (hle hs)]; exact hs⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, by rw [h.clk s (hle' hs)]; exact hs⟩
  refine ⟨hiff, ?_, ?_⟩
  · by_cases hh : ω ∈ clkHit d g
    · have hs := clk_clkInv hh
      have hs' : d'.clk ω' (Prop59System.clkInv d g ω) = g := by rw [← h.clk _ (hle hs)]; exact hs
      exact eq_clkInv hm' hs'
    · have hh' := (not_congr hiff).1 hh
      simp only [Prop59System.clkInv, hh, hh', ↓reduceDIte]
  · by_cases hh : ω ∈ clkHit d g
    · exact hle (clk_clkInv hh)
    · simp only [Prop59System.clkInv, hh, ↓reduceDIte, zero_le]

theorem StageUpTo.farGap (h : StageUpTo d d' ω ω' T) {u : ℝ≥0} (hu : u ≤ T) :
    Prop59Stage.farGap hnL hnR j d ω u = Prop59Stage.farGap hnL hnR j d' ω' u := by
  simp only [Prop59Stage.farGap, h.W u hu, h.VL _ u hu, h.VR _ u hu]

theorem StageUpTo.swCond (h : StageUpTo d d' ω ω' T) {s : ℝ≥0} (hs : s ≤ T) :
    SwCond hnL hnR j d ω s ↔ SwCond hnL hnR j d' ω' s := by
  have hW := h.W s hs
  have hy := h.y
  have hg : (∀ u ≤ s, 0 < Prop59Stage.farGap hnL hnR j d ω u) ↔
      ∀ u ≤ s, 0 < Prop59Stage.farGap hnL hnR j d' ω' u :=
    forall₂_congr fun u hu => by rw [h.farGap (hu.trans hs)]
  simp only [SwCond, hW, hy, hg, iff_of_true (h.lt s hs).1 (h.lt s hs).2]

theorem StageUpTo.mem_swSet (h : StageUpTo d d' ω ω' T) (hm : StrictMono (d.clk ω))
    (hm' : StrictMono (d'.clk ω')) {g : ℝ≥0} (hg : g ≤ d.clk ω T) :
    ω ∈ swSet hnL hnR j d g ↔ ω' ∈ swSet hnL hnR j d' g := by
  obtain ⟨h1, h2, h3⟩ := h.clkInv hm hm' hg
  simp only [swSet, mem_ofPred_eq, h1, ← h2, h.swCond h3]

/-- The switch event at a grid point is the first grid point satisfying the switching condition. -/
theorem mem_swEv_iff {G : ℕ → ℕ → ℝ≥0} {Ω₀ : Type*} [MeasurableSpace Ω₀] {e : StageData Ω₀ (nL₀ + j) (nR₀ + j)}
    (hr : IsRegStage hnL hnR j e) {n m : ℕ} {x : Ω₀} :
    x ∈ swEv G hnL hnR j e n m ↔ x ∈ swSet hnL hnR j e (G n m) ∧ ∀ k < m, x ∉ swSet hnL hnR j e (G n k) := by
  constructor
  · rintro ⟨hs, hidx⟩
    have hsp := swIdx_spec hr hs
    simp only [mem_ofPred_eq] at hidx
    rw [hidx] at hsp
    exact hsp
  · rintro ⟨h1, h2⟩
    have hs : x ∈ succSet G hnL hnR j e n :=
      ⟨m, Prop59System.clkInv e (G n m) x, clk_clkInv h1.1, h1.2⟩
    refine ⟨hs, ?_⟩
    show sInf {k | x ∈ swSet hnL hnR j e (G n k)} = m
    refine le_antisymm (Nat.sInf_le h1) (le_of_not_gt fun hlt => h2 _ hlt ?_)
    exact Nat.sInf_mem (s := {k | x ∈ swSet hnL hnR j e (G n k)}) ⟨m, h1⟩

variable [MeasurableSpace Ω] [MeasurableSpace Ω'] {G : ℕ → ℕ → ℝ≥0}

/-- **The switch events at grid points reached by time `T` agree.** -/
theorem StageUpTo.mem_swEv (h : StageUpTo d d' ω ω' T) (hr : IsRegStage hnL hnR j d)
    (hr' : IsRegStage hnL hnR j d') (hG : ∀ n, Monotone (G n)) {n m : ℕ} (hg : G n m ≤ d.clk ω T) :
    ω ∈ swEv G hnL hnR j d n m ↔ ω' ∈ swEv G hnL hnR j d' n m := by
  rw [mem_swEv_iff hr, mem_swEv_iff hr', h.mem_swSet (hr.clk_mono ω) (hr'.clk_mono ω') hg]
  refine and_congr_right fun _ => forall₂_congr fun k hk => not_congr ?_
  exact h.mem_swSet (hr.clk_mono ω) (hr'.clk_mono ω') ((hG n hk.le).trans hg)

theorem StageUpTo.swT (h : StageUpTo d d' ω ω' T) (hr : IsRegStage hnL hnR j d)
    (hr' : IsRegStage hnL hnR j d') (hG : ∀ n, Monotone (G n)) {n m : ℕ} (hg : G n m ≤ d.clk ω T)
    (hω : ω ∈ swEv G hnL hnR j d n m) :
    Prop59Stage.swT G hnL hnR j d n ω = Prop59Stage.swT G hnL hnR j d' n ω' ∧
      Prop59Stage.swT G hnL hnR j d n ω ≤ T := by
  have hω' := (h.mem_swEv hr hr' hG hg).1 hω
  have e : Prop59Stage.swT G hnL hnR j d n ω = Prop59System.clkInv d (G n m) ω := by
    rw [swT_eq hr hω.1, show swIdx G hnL hnR j d n ω = m from hω.2]
  have e' : Prop59Stage.swT G hnL hnR j d' n ω' = Prop59System.clkInv d' (G n m) ω' := by
    rw [swT_eq hr' hω'.1, show swIdx G hnL hnR j d' n ω' = m from hω'.2]
  obtain ⟨-, h2, h3⟩ := h.clkInv (hr.clk_mono ω) (hr'.clk_mono ω') hg
  rw [e, e']
  exact ⟨h2, h3⟩

theorem StageUpTo.nextStart (h : StageUpTo d d' ω ω' T) (hr : IsRegStage hnL hnR j d)
    (hr' : IsRegStage hnL hnR j d') (hG : ∀ n, Monotone (G n)) {n m : ℕ} (hg : G n m ≤ d.clk ω T)
    (hω : ω ∈ swEv G hnL hnR j d n m) :
    Prop59Stage.nextStart G hnL hnR j d n ω = Prop59Stage.nextStart G hnL hnR j d' n ω' := by
  obtain ⟨e, hle⟩ := h.swT hr hr' hG hg hω
  simp only [Prop59Stage.nextStart, ← e, h.y, h.W _ hle, h.VL _ _ hle, h.VR _ _ hle]

end Stage

/-! ### Candidate families agreeing up to the switching times -/

section Canon

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {nL₀ nR₀ : ℕ}

/-- Two pieces agree up to the time `T`: driver, marks and clock agree on `[0, T]`, both alive there. -/
structure PieceUpTo {nL nR : ℕ} (p : Piece Ω nL nR) (p' : Piece Ω' nL nR) (ω : Ω) (ω' : Ω') (T : ℝ≥0) : Prop where
  W : ∀ u ≤ T, p.W u ω = p'.W u ω'
  VL : ∀ i, ∀ u ≤ T, p.VL i u ω = p'.VL i u ω'
  VR : ∀ k, ∀ u ≤ T, p.VR k u ω = p'.VR k u ω'
  lt : ∀ u ≤ T, (u : ℝ≥0∞) < p.ζ ω ∧ (u : ℝ≥0∞) < p'.ζ ω'
  clk : ∀ u ≤ T, p.clk ω u = p'.clk ω' u

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
theorem PieceUpTo.stageUpTo {j : ℕ} {p : Piece Ω (nL₀ + j) (nR₀ + j)} {p' : Piece Ω' (nL₀ + j) (nR₀ + j)}
    {ω : Ω} {ω' : Ω'} {T : ℝ≥0} (h : PieceUpTo p p' ω ω' T) {past : MeasurableSpace Ω}
    {past' : MeasurableSpace Ω'} {R : Set Ω} {R' : Set Ω'} {y : Ω → Start (nL₀ + j) (nR₀ + j)}
    {y' : Ω' → Start (nL₀ + j) (nR₀ + j)} (hy : y ω = y' ω') :
    StageUpTo (p.toStage past R y) (p'.toStage past' R' y') ω ω' T :=
  ⟨hy, h.W, h.VL, h.VR, h.lt, h.clk⟩

/-- **The candidate pieces of the prefixes of a list agree up to their switching times** (the piece time at which
the clock of the prefix reads the next entry). -/
def CanonUpTo (cand : CandFam Ω nL₀ nR₀) (cand' : CandFam Ω' nL₀ nR₀) (ω : Ω) (ω' : Ω') :
    (j : ℕ) → (Fin j → ℝ≥0) → Prop
  | 0, _ => True
  | j + 1, t => CanonUpTo cand cand' ω ω' j (Fin.init t) ∧
      PieceUpTo (cand j (Fin.init t)) (cand' j (Fin.init t)) ω ω' (candInv cand j (Fin.init t) (t (Fin.last j)) ω)

variable {cand : CandFam Ω nL₀ nR₀} {cand' : CandFam Ω' nL₀ nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)}
  {y₀' : Ω' → Start (nL₀ + 0) (nR₀ + 0)} {ω : Ω} {ω' : Ω'} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀}

/-- On a switch event at the grid point `G n m` the clock reads `G n m` at the switching time. -/
theorem clk_candInv_of_mem_swEv (hfam : IsRegFam cand) (hy₀ : Measurable y₀) {j : ℕ} {t : Fin j → ℝ≥0} {n m : ℕ}
    (hω : ω ∈ swEv G hnL hnR j (candStage cand (canonY cand y₀) j t) n m) :
    (cand j t).clk ω (candInv cand j t (G n m) ω) = G n m := by
  have hr := isRegStage_candStage (hnL := hnL) (hnR := hnR) hfam hy₀ j t
  have hsw := (mem_swEv_iff hr).1 hω
  exact clk_clkInv hsw.1.1

/-- **The canonical reached events and starts agree** at two samples whose candidate pieces agree up to the switching
times along the list (and whose root data agree). -/
theorem canonR_canonY_upTo (hfam : IsRegFam cand) (hfam' : IsRegFam cand') (hy₀ : Measurable y₀)
    (hy₀' : Measurable y₀') (hG : ∀ n, Monotone (G n)) (hy : y₀ ω = y₀' ω') {R₀ : Set Ω} {R₀' : Set Ω'}
    (hR : ω ∈ R₀ → ω' ∈ R₀') :
    ∀ j t, ω ∈ canonR cand G hnL hnR y₀ R₀ j t → CanonUpTo cand cand' ω ω' j t →
      ω' ∈ canonR cand' G hnL hnR y₀' R₀' j t ∧ canonY cand y₀ j t ω = canonY cand' y₀' j t ω'
  | 0, _, hω, _ => ⟨hR hω, hy⟩
  | j + 1, t, hω, hc => by
    simp only [canonR, mem_inter_iff, mem_iUnion] at hω
    obtain ⟨hω0, n, m, hnm, hsw⟩ := hω
    obtain ⟨ih1, ih2⟩ := canonR_canonY_upTo hfam hfam' hy₀ hy₀' hG hy hR j (Fin.init t) hω0 hc.1
    have hp := hc.2
    have hr := isRegStage_candStage (hnL := hnL) (hnR := hnR) hfam hy₀ j (Fin.init t)
    have hr' := isRegStage_candStage (hnL := hnL) (hnR := hnR) hfam' hy₀' j (Fin.init t)
    have hst := hp.stageUpTo (past := ⊥) (past' := ⊥) (R := ∅) (R' := ∅) ih2
    have hclk : (cand j (Fin.init t)).clk ω (candInv cand j (Fin.init t) (t (Fin.last j)) ω) = t (Fin.last j) := by
      rw [← hnm]; exact clk_candInv_of_mem_swEv hfam hy₀ hsw
    have hg : G n m ≤ (candStage cand (canonY cand y₀) j (Fin.init t)).clk ω
        (candInv cand j (Fin.init t) (t (Fin.last j)) ω) := by
      show G n m ≤ (cand j (Fin.init t)).clk ω _
      rw [hclk, hnm]
    have hsw' := (hst.mem_swEv hr hr' hG hg).1 hsw
    refine ⟨⟨ih1, mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨hnm, hsw'⟩⟩⟩⟩, ?_⟩
    have hg' : t (Fin.last j) ≤ (candStage cand (canonY cand y₀) j (Fin.init t)).clk ω
        (candInv cand j (Fin.init t) (t (Fin.last j)) ω) := hnm.symm.trans_le hg
    obtain ⟨-, hinv, hle⟩ := hst.clkInv (hr.clk_mono ω) (hr'.clk_mono ω') hg'
    have hinv' : Prop59System.clkInv ((cand j (Fin.init t)).toStage ⊥ ∅ fun _ => 0) (t (Fin.last j)) ω =
        Prop59System.clkInv ((cand' j (Fin.init t)).toStage ⊥ ∅ fun _ => 0) (t (Fin.last j)) ω' := hinv
    have hle'' : Prop59System.clkInv ((cand' j (Fin.init t)).toStage ⊥ ∅ fun _ => 0) (t (Fin.last j)) ω' ≤
        candInv cand j (Fin.init t) (t (Fin.last j)) ω := by rw [← hinv']; exact hle
    simp only [canonY, startAt]
    rw [hinv']
    generalize Prop59System.clkInv ((cand' j (Fin.init t)).toStage ⊥ ∅ fun _ => 0) (t (Fin.last j)) ω' = u at hle'' ⊢
    simp only [Piece.toStage, ih2, hp.W u hle'', hp.VL _ u hle'', hp.VR _ u hle'']

/-- **The generators of the switch σ-algebra agree** at two samples where the list is reached and the candidate
pieces agree up to the switching times. -/
theorem mem_swGen_upTo (hfam : IsRegFam cand) (hfam' : IsRegFam cand') (hy₀ : Measurable y₀)
    (hy₀' : Measurable y₀') (hG : ∀ n, Monotone (G n)) (hy : y₀ ω = y₀' ω') {R₀ : Set Ω} {R₀' : Set Ω'}
    (hR : ω ∈ R₀ → ω' ∈ R₀') {j : ℕ} {t : Fin (j + 1) → ℝ≥0}
    (hω : ω ∈ canonR cand G hnL hnR y₀ R₀ (j + 1) t) (hc : CanonUpTo cand cand' ω ω' (j + 1) t) {n m : ℕ}
    (hnm : G n m = t (Fin.last j)) (S : Set (ℝ≥0 × Start (nL₀ + (j + 1)) (nR₀ + (j + 1)))) :
    ω ∈ swEv G hnL hnR j (candStage cand (canonY cand y₀) j (Fin.init t)) n m ∩
        {ω | (Prop59Stage.swT G hnL hnR j (candStage cand (canonY cand y₀) j (Fin.init t)) n ω,
          Prop59Stage.nextStart G hnL hnR j (candStage cand (canonY cand y₀) j (Fin.init t)) n ω) ∈ S} ↔
      ω' ∈ swEv G hnL hnR j (candStage cand' (canonY cand' y₀') j (Fin.init t)) n m ∩
        {ω' | (Prop59Stage.swT G hnL hnR j (candStage cand' (canonY cand' y₀') j (Fin.init t)) n ω',
          Prop59Stage.nextStart G hnL hnR j (candStage cand' (canonY cand' y₀') j (Fin.init t)) n ω') ∈ S} := by
  have hω0 : ω ∈ canonR cand G hnL hnR y₀ R₀ j (Fin.init t) := hω.1
  obtain ⟨-, ih2⟩ := canonR_canonY_upTo hfam hfam' hy₀ hy₀' hG hy hR j (Fin.init t) hω0 hc.1
  have hp := hc.2
  have hr := isRegStage_candStage (hnL := hnL) (hnR := hnR) hfam hy₀ j (Fin.init t)
  have hr' := isRegStage_candStage (hnL := hnL) (hnR := hnR) hfam' hy₀' j (Fin.init t)
  have hst := hp.stageUpTo (past := ⊥) (past' := ⊥) (R := ∅) (R' := ∅) ih2
  -- the switch of the list happens at the grid value `t (Fin.last j)`
  have hω1 := hω.2
  simp only [mem_iUnion] at hω1
  obtain ⟨n₀, m₀, hnm₀, hsw₀⟩ := hω1
  have hclk : (cand j (Fin.init t)).clk ω (candInv cand j (Fin.init t) (t (Fin.last j)) ω) = t (Fin.last j) := by
    rw [← hnm₀]; exact clk_candInv_of_mem_swEv hfam hy₀ hsw₀
  have hg : G n m ≤ (candStage cand (canonY cand y₀) j (Fin.init t)).clk ω
      (candInv cand j (Fin.init t) (t (Fin.last j)) ω) := by
    show G n m ≤ (cand j (Fin.init t)).clk ω _
    rw [hclk, hnm]
  have hev := hst.mem_swEv hr hr' hG hg
  have heq : ω ∈ swEv G hnL hnR j (candStage cand (canonY cand y₀) j (Fin.init t)) n m →
      Prop59Stage.swT G hnL hnR j (candStage cand (canonY cand y₀) j (Fin.init t)) n ω =
        Prop59Stage.swT G hnL hnR j (candStage cand' (canonY cand' y₀') j (Fin.init t)) n ω' ∧
      Prop59Stage.nextStart G hnL hnR j (candStage cand (canonY cand y₀) j (Fin.init t)) n ω =
        Prop59Stage.nextStart G hnL hnR j (candStage cand' (canonY cand' y₀') j (Fin.init t)) n ω' :=
    fun h1 => ⟨(hst.swT hr hr' hG hg h1).1, hst.nextStart hr hr' hG hg h1⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hev.1 h1, ?_⟩
    simp only [mem_ofPred_eq] at h2 ⊢
    rw [← (heq h1).1, ← (heq h1).2]
    exact h2
  · rintro ⟨h1, h2⟩
    have h1' := hev.2 h1
    refine ⟨h1', ?_⟩
    simp only [mem_ofPred_eq] at h2 ⊢
    rw [(heq h1').1, (heq h1').2]
    exact h2

end Canon

end InteractingSLE.Sec5.CrossCond.StagedNTr
