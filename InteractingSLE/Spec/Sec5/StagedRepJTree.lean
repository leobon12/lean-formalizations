/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJGam

/-!
# Prop 5.9's tree candidates read at a sample

Packet PROVE-STAGED-REPJ. PROVE-PROP59-PIECES' tree construction (`TreeData`) is pointwise: the candidate pieces at a
sample read the tree data only at that sample. This file makes that precise for two tree data on two spaces and two
samples whose data agree (`TreeData.AgreeAt`), so that PIECES' root candidates can be compared with REP2's construction
`gamData` on `Gam` at the pair (field, history) of the sample:

* `PieceAt`: two pieces agree at two samples (driver, marks, lifetime, clock as functions of time);
* `pieceAt_arcPiece`: arc pieces of agreeing data agree; `clkInv_congr`: clock inverses of agreeing clocks agree;
* **`TreeData.AgreeAt.marks`**, **`TreeData.AgreeAt.cand`**: the tree marks and the candidate pieces agree at every
  depth.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open WangWu WangWu.ImgWord GlueCond CrossCond.Word49 LawUnique CrossRestart Prop59System Prop59Stage Prop59Pieces
open Sec7.Lemma71C (capClock)

/-! ### Pieces agreeing at two samples -/

section PieceAt

variable {Ω Ω' : Type*} {nL nR : ℕ}

/-- Two pieces agree at the samples `ω`, `ω'`: same driver, marks, lifetime and clock. -/
structure PieceAt (p : Piece Ω nL nR) (p' : Piece Ω' nL nR) (ω : Ω) (ω' : Ω') : Prop where
  W : ∀ u, p.W u ω = p'.W u ω'
  VL : ∀ i u, p.VL i u ω = p'.VL i u ω'
  VR : ∀ k u, p.VR k u ω = p'.VR k u ω'
  ζ : p.ζ ω = p'.ζ ω'
  clk : p.clk ω = p'.clk ω'

/-- **Arc pieces of data agreeing at two samples agree there.** -/
theorem pieceAt_arcPiece {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0} {A : Set Ω}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {B : ℝ≥0 → Ω → ℝ} {γ' : Ω' → ℝ → ℂ} {P' : Ω' → Set ℝ}
    {S₀' : Ω' → ℝ≥0} {A' : Set Ω'} {xL' : Ω' → Fin nL → ℝ} {xR' : Ω' → Fin nR → ℝ} {B' : ℝ≥0 → Ω' → ℝ}
    {ω : Ω} {ω' : Ω'} (hγ : γ ω = γ' ω') (hP : P ω = P' ω') (hS : S₀ ω = S₀' ω') (hA : ω ∈ A ↔ ω' ∈ A')
    (hxL : xL ω = xL' ω') (hxR : xR ω = xR' ω') :
    PieceAt (arcPiece γ P S₀ A xL xR B) (arcPiece γ' P' S₀' A' xL' xR' B') ω ω' := by
  classical
  have hW : ∀ u, arcW γ P S₀ A u ω = arcW γ' P' S₀' A' u ω' := fun u => by
    unfold arcW
    rw [hγ, hP, hS]
    by_cases h : ω ∈ A
    · simp only [h, hA.1 h, true_and]
    · simp only [h, (not_congr hA).1 h, false_and, ↓reduceIte]
  have hζ : arcζ γ P S₀ A ω = arcζ γ' P' S₀' A' ω' := by
    unfold arcζ
    rw [hγ, hP, hS]
    by_cases h : ω ∈ A
    · simp only [h, hA.1 h, ↓reduceIte]
    · simp only [h, (not_congr hA).1 h, ↓reduceIte]
  have hrW : Bessel.realPath (fun u ω => -arcW γ P S₀ A u ω) ω =
      Bessel.realPath (fun u ω => -arcW γ' P' S₀' A' u ω) ω' := by
    funext r; simp only [Bessel.realPath, hW]
  have hrW' : Bessel.realPath (arcW γ P S₀ A) ω = Bessel.realPath (arcW γ' P' S₀' A') ω' := by
    funext r; simp only [Bessel.realPath, hW]
  refine ⟨hW, fun i u => ?_, fun k u => ?_, hζ, ?_⟩
  · show arcVL γ P S₀ A xL i u ω = arcVL γ' P' S₀' A' xL' i u ω'
    simp only [arcVL, hζ, hrW, hxL]
  · show arcVR γ P S₀ A xR k u ω = arcVR γ' P' S₀' A' xR' k u ω'
    simp only [arcVR, hζ, hrW', hxR]
  · show arcClk γ P S₀ A ω = arcClk γ' P' S₀' A' ω'
    unfold arcClk
    rw [hγ, hP, hS]
    by_cases h : ω ∈ A
    · simp only [h, hA.1 h, ↓reduceIte]
    · simp only [h, (not_congr hA).1 h, ↓reduceIte]

theorem choose_congr {α : Sort*} {p q : α → Prop} (hpq : p = q) (hp : ∃ a, p a) (hq : ∃ a, q a) :
    Classical.choose hp = Classical.choose hq := by
  subst hpq; rfl

/-- **Clock inverses of agreeing clocks agree.** -/
theorem clkInv_congr {a b j a' b' j' : ℕ} {d : StageData Ω (a + j) (b + j)} {d' : StageData Ω' (a' + j') (b' + j')}
    {ω : Ω} {ω' : Ω'}
    (h : d.clk ω = d'.clk ω') (g : ℝ≥0) : clkInv d g ω = clkInv d' g ω' := by
  classical
  have hiff : ω ∈ clkHit d g ↔ ω' ∈ clkHit d' g := by
    simp only [clkHit, mem_ofPred_eq, h]
  by_cases hω : ω ∈ clkHit d g
  · have hω' := hiff.1 hω
    have e1 : clkInv d g ω = Classical.choose hω := by simp only [clkInv, hω, ↓reduceDIte]
    have e2 : clkInv d' g ω' = Classical.choose hω' := by simp only [clkInv, hω', ↓reduceDIte]
    rw [e1, e2]
    exact choose_congr (p := fun s => d.clk ω s = g) (q := fun s => d'.clk ω' s = g) (by rw [h]) hω hω'
  · have hω' := (not_congr hiff).1 hω
    simp only [clkInv, hω, hω', ↓reduceDIte]

end PieceAt

end InteractingSLE.Sec5.CrossCond.StagedRepJ

/-! ### Tree data agreeing at two samples -/

namespace InteractingSLE.Sec5.Prop59Pieces

open WangWu WangWu.ImgWord GlueCond CrossCond.Word49 LawUnique CrossRestart Prop59System Prop59Stage
open CrossCond.StagedRepJ
open Sec7.Lemma71C (capClock)

section Agree

variable {Ω Ω' : Type*} {nL₀ nR₀ : ℕ}

/-- **Two tree data agree at the samples `ω`, `ω'`**: same counterflow time, history value, dilation, membership in
the good set, paths, admissible lists and root marks (the noise is not compared). -/
structure TreeData.AgreeAt (D : TreeData Ω nL₀ nR₀) (D' : TreeData Ω' nL₀ nR₀) (ω : Ω) (ω' : Ω') : Prop where
  r : D.r = D'.r
  y : D.y ω = D'.y ω'
  lam : D.lam ω = D'.lam ω'
  G : ω ∈ D.G ↔ ω' ∈ D'.G
  α : ∀ j t, D.α j t ω = D'.α j t ω'
  valid : ∀ j t, D.valid j t ↔ D'.valid j t
  xL0 : D.xL0 ω = D'.xL0 ω'
  xR0 : D.xR0 ω = D'.xR0 ω'

variable {D : TreeData Ω nL₀ nR₀} {D' : TreeData Ω' nL₀ nR₀} {ω : Ω} {ω' : Ω'}

theorem TreeData.AgreeAt.mem_Gc (hA : D.AgreeAt D' ω ω') (j : ℕ) (t : Fin j → ℝ≥0) :
    ω ∈ D.Gc j t ↔ ω' ∈ D'.Gc j t :=
  and_congr (hA.valid j t) hA.G

theorem TreeData.AgreeAt.img (hA : D.AgreeAt D' ω ω') (j : ℕ) (t : Fin j → ℝ≥0) :
    D.img j t ω = D'.img j t ω' := by
  classical
  unfold TreeData.img tImg
  by_cases h : ω ∈ D.Gc j t
  · simp only [h, (hA.mem_Gc j t).1 h, ↓reduceIte, hA.r, hA.y, hA.lam, hA.α]
  · simp only [h, (not_congr (hA.mem_Gc j t)).1 h, ↓reduceIte]

theorem TreeData.AgreeAt.pre (hA : D.AgreeAt D' ω ω') (j : ℕ) (t : Fin j → ℝ≥0) :
    D.pre j t ω = D'.pre j t ω' := by
  classical
  unfold TreeData.pre tPre
  by_cases h : ω ∈ D.Gc j t
  · simp only [h, (hA.mem_Gc j t).1 h, ↓reduceIte, hA.r, hA.y, hA.α]
  · simp only [h, (not_congr (hA.mem_Gc j t)).1 h, ↓reduceIte]

theorem TreeData.AgreeAt.mem_alive (hA : D.AgreeAt D' ω ω') (j : ℕ) (t : Fin j → ℝ≥0) :
    ω ∈ D.alive j t ↔ ω' ∈ D'.alive j t := by
  simp only [TreeData.alive, mem_ofPred_eq, hA.mem_Gc j t, hA.pre j t]

theorem TreeData.AgreeAt.startCap (hA : D.AgreeAt D' ω ω') (j : ℕ) (t : Fin j → ℝ≥0) :
    D.startCap j t ω = D'.startCap j t ω' := by
  classical
  unfold TreeData.startCap
  by_cases h : ω ∈ D.alive j t
  · simp only [h, (hA.mem_alive j t).1 h, ↓reduceIte, hA.img j t]
  · simp only [h, (not_congr (hA.mem_alive j t)).1 h, ↓reduceIte]

/-- **The tree marks agree at every depth.** -/
theorem TreeData.AgreeAt.marks (hA : D.AgreeAt D' ω ω') :
    ∀ (j : ℕ) (t : Fin j → ℝ≥0), D.marks j t ω = D'.marks j t ω'
  | 0, _ => by simp only [TreeData.marks, hA.xL0, hA.xR0]
  | j + 1, t => by
    have hm := hA.marks j (Fin.init t)
    have hp := pieceAt_arcPiece (B := fun _ _ => (0 : ℝ)) (B' := fun _ _ => (0 : ℝ))
      (xL := fun ω => (D.marks j (Fin.init t) ω).1) (xR := fun ω => (D.marks j (Fin.init t) ω).2)
      (xL' := fun ω' => (D'.marks j (Fin.init t) ω').1) (xR' := fun ω' => (D'.marks j (Fin.init t) ω').2)
      (hA.img j (Fin.init t)) (hA.pre j (Fin.init t)) (hA.startCap j (Fin.init t)) (hA.mem_alive j (Fin.init t))
      (by rw [hm]) (by rw [hm])
    have hinv : clkInv (D.clkStage j (Fin.init t)) (t (Fin.last j)) ω =
        clkInv (D'.clkStage j (Fin.init t)) (t (Fin.last j)) ω' := clkInv_congr hp.clk _
    have hW : ∀ u, arcW (D.img j (Fin.init t)) (D.pre j (Fin.init t)) (D.startCap j (Fin.init t))
        (D.alive j (Fin.init t)) u ω = arcW (D'.img j (Fin.init t)) (D'.pre j (Fin.init t))
        (D'.startCap j (Fin.init t)) (D'.alive j (Fin.init t)) u ω' := hp.W
    have hVL : ∀ i u, arcVL (D.img j (Fin.init t)) (D.pre j (Fin.init t)) (D.startCap j (Fin.init t))
        (D.alive j (Fin.init t)) (fun ω => (D.marks j (Fin.init t) ω).1) i u ω =
        arcVL (D'.img j (Fin.init t)) (D'.pre j (Fin.init t)) (D'.startCap j (Fin.init t))
        (D'.alive j (Fin.init t)) (fun ω' => (D'.marks j (Fin.init t) ω').1) i u ω' := hp.VL
    have hVR : ∀ k u, arcVR (D.img j (Fin.init t)) (D.pre j (Fin.init t)) (D.startCap j (Fin.init t))
        (D.alive j (Fin.init t)) (fun ω => (D.marks j (Fin.init t) ω).2) k u ω =
        arcVR (D'.img j (Fin.init t)) (D'.pre j (Fin.init t)) (D'.startCap j (Fin.init t))
        (D'.alive j (Fin.init t)) (fun ω' => (D'.marks j (Fin.init t) ω').2) k u ω' := hp.VR
    simp only [TreeData.marks, hinv, hW, hVL, hVR]

/-- **The candidate pieces agree at every depth.** -/
theorem TreeData.AgreeAt.cand (hA : D.AgreeAt D' ω ω') (j : ℕ) (t : Fin j → ℝ≥0) :
    PieceAt (D.cand j t) (D'.cand j t) ω ω' :=
  pieceAt_arcPiece (hA.img j t) (hA.pre j t) (hA.startCap j t) (hA.mem_alive j t) (by rw [hA.marks j t])
    (by rw [hA.marks j t])

end Agree

end InteractingSLE.Sec5.Prop59Pieces

/-! ### Stage data agreeing at two samples: the switch data agree -/

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open Prop59System Prop59Stage Prop59Pieces StagedCand StagedAdapt

section StageAt

variable {Ω Ω' : Type*} {nL₀ nR₀ : ℕ}

/-- Two stage data agree at the samples `ω`, `ω'`. -/
structure StageAt {j : ℕ} (d : StageData Ω (nL₀ + j) (nR₀ + j)) (d' : StageData Ω' (nL₀ + j) (nR₀ + j)) (ω : Ω)
    (ω' : Ω') : Prop where
  y : d.y ω = d'.y ω'
  W : ∀ u, d.W u ω = d'.W u ω'
  VL : ∀ i u, d.VL i u ω = d'.VL i u ω'
  VR : ∀ k u, d.VR k u ω = d'.VR k u ω'
  ζ : d.ζ ω = d'.ζ ω'
  clk : d.clk ω = d'.clk ω'

variable {hnL : 0 < nL₀} {hnR : 0 < nR₀} {j : ℕ} {d : StageData Ω (nL₀ + j) (nR₀ + j)}
  {d' : StageData Ω' (nL₀ + j) (nR₀ + j)} {ω : Ω} {ω' : Ω'} (G : ℕ → ℕ → ℝ≥0)

theorem StageAt.farGap (h : StageAt d d' ω ω') (u : ℝ≥0) :
    farGap hnL hnR j d ω u = farGap hnL hnR j d' ω' u := by
  simp only [Prop59Stage.farGap, h.W, h.VL, h.VR]

theorem StageAt.swCond (h : StageAt d d' ω ω') (s : ℝ≥0) :
    SwCond hnL hnR j d ω s ↔ SwCond hnL hnR j d' ω' s := by
  simp only [SwCond, h.ζ, h.y, h.W, h.farGap]

theorem StageAt.mem_swSet (h : StageAt d d' ω ω') (g : ℝ≥0) :
    ω ∈ swSet hnL hnR j d g ↔ ω' ∈ swSet hnL hnR j d' g := by
  simp only [swSet, mem_ofPred_eq, clkHit, h.clk, clkInv_congr h.clk, h.swCond]

theorem StageAt.mem_succSet (h : StageAt d d' ω ω') (n : ℕ) :
    ω ∈ succSet G hnL hnR j d n ↔ ω' ∈ succSet G hnL hnR j d' n := by
  simp only [succSet, mem_ofPred_eq, h.clk, h.swCond]

theorem StageAt.swIdx (h : StageAt d d' ω ω') (n : ℕ) :
    swIdx G hnL hnR j d n ω = swIdx G hnL hnR j d' n ω' := by
  simp only [Prop59System.swIdx, h.mem_swSet]

theorem StageAt.mem_swEv (h : StageAt d d' ω ω') (n m : ℕ) :
    ω ∈ swEv G hnL hnR j d n m ↔ ω' ∈ swEv G hnL hnR j d' n m := by
  simp only [swEv, mem_inter_iff, h.mem_succSet G, mem_ofPred_eq, h.swIdx G]

theorem StageAt.swT [MeasurableSpace Ω] [MeasurableSpace Ω'] (h : StageAt d d' ω ω')
    (hr : IsRegStage hnL hnR j d) (hr' : IsRegStage hnL hnR j d') (n : ℕ) :
    swT G hnL hnR j d n ω = swT G hnL hnR j d' n ω' := by
  classical
  by_cases hs : ω ∈ succSet G hnL hnR j d n
  · rw [swT_eq hr hs, swT_eq hr' ((h.mem_succSet G n).1 hs), h.swIdx G, clkInv_congr h.clk]
  · have hs' := (not_congr (h.mem_succSet G n)).1 hs
    simp only [Prop59Stage.swT, hs, hs', ↓reduceDIte]

theorem StageAt.nextStart [MeasurableSpace Ω] [MeasurableSpace Ω'] (h : StageAt d d' ω ω')
    (hr : IsRegStage hnL hnR j d) (hr' : IsRegStage hnL hnR j d') (n : ℕ) :
    nextStart G hnL hnR j d n ω = nextStart G hnL hnR j d' n ω' := by
  simp only [Prop59Stage.nextStart, h.swT G hr hr' n, h.y, h.W, h.VL, h.VR]

end StageAt

/-! ### Candidate families agreeing at two samples -/

section CandAt

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {nL₀ nR₀ : ℕ} {cand : CandFam Ω nL₀ nR₀}
  {cand' : CandFam Ω' nL₀ nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {y₀' : Ω' → Start (nL₀ + 0) (nR₀ + 0)}
  {ω : Ω} {ω' : Ω'}

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **The canonical starts agree** at two samples where all candidates and the root starts agree. -/
theorem canonY_congr (hc : ∀ j t, PieceAt (cand j t) (cand' j t) ω ω') (hy : y₀ ω = y₀' ω') :
    ∀ j t, canonY cand y₀ j t ω = canonY cand' y₀' j t ω'
  | 0, _ => hy
  | j + 1, t => by
    have ih := canonY_congr hc hy j (Fin.init t)
    have hp := hc j (Fin.init t)
    have hinv : clkInv ((cand j (Fin.init t)).toStage ⊥ ∅ fun _ => 0) (t (Fin.last j)) ω =
        clkInv ((cand' j (Fin.init t)).toStage ⊥ ∅ fun _ => 0) (t (Fin.last j)) ω' := clkInv_congr hp.clk _
    simp only [canonY, startAt]
    rw [hinv]
    simp only [Piece.toStage]
    rw [ih, hp.W]
    simp only [hp.VL, hp.VR]

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
theorem stageAt_candStage (hc : ∀ j t, PieceAt (cand j t) (cand' j t) ω ω') (hy : y₀ ω = y₀' ω') (j : ℕ)
    (t : Fin j → ℝ≥0) :
    StageAt (candStage cand (canonY cand y₀) j t) (candStage cand' (canonY cand' y₀') j t) ω ω' :=
  ⟨canonY_congr hc hy j t, (hc j t).W, (hc j t).VL, (hc j t).VR, (hc j t).ζ, (hc j t).clk⟩

variable (G : ℕ → ℕ → ℝ≥0) (hnL : 0 < nL₀) (hnR : 0 < nR₀)

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **The canonical reached events agree** at two samples where all candidates and the root data agree. -/
theorem mem_canonR_congr (hc : ∀ j t, PieceAt (cand j t) (cand' j t) ω ω') (hy : y₀ ω = y₀' ω') {R₀ : Set Ω}
    {R₀' : Set Ω'} (hR : ω ∈ R₀ ↔ ω' ∈ R₀') :
    ∀ j t, ω ∈ canonR cand G hnL hnR y₀ R₀ j t ↔ ω' ∈ canonR cand' G hnL hnR y₀' R₀' j t
  | 0, _ => hR
  | j + 1, t => by
    simp only [canonR, mem_inter_iff, mem_iUnion, mem_canonR_congr hc hy hR j (Fin.init t),
      (stageAt_candStage hc hy j (Fin.init t)).mem_swEv G]

/-- **The generators of the switch σ-algebras agree.** -/
theorem mem_swGen_congr (hc : ∀ j t, PieceAt (cand j t) (cand' j t) ω ω') (hy : y₀ ω = y₀' ω')
    (hfam : IsRegFam cand) (hfam' : IsRegFam cand') (hy₀ : Measurable y₀) (hy₀' : Measurable y₀') (j : ℕ)
    (t : Fin j → ℝ≥0) (n m : ℕ) (S : Set (ℝ≥0 × Start (nL₀ + (j + 1)) (nR₀ + (j + 1)))) :
    ω ∈ swEv G hnL hnR j (candStage cand (canonY cand y₀) j t) n m ∩
        {ω | (swT G hnL hnR j (candStage cand (canonY cand y₀) j t) n ω,
          nextStart G hnL hnR j (candStage cand (canonY cand y₀) j t) n ω) ∈ S} ↔
      ω' ∈ swEv G hnL hnR j (candStage cand' (canonY cand' y₀') j t) n m ∩
        {ω' | (swT G hnL hnR j (candStage cand' (canonY cand' y₀') j t) n ω',
          nextStart G hnL hnR j (candStage cand' (canonY cand' y₀') j t) n ω') ∈ S} := by
  have hA := stageAt_candStage hc hy j t
  have hr := isRegStage_candStage (hnL := hnL) (hnR := hnR) hfam hy₀ j t
  have hr' := isRegStage_candStage (hnL := hnL) (hnR := hnR) hfam' hy₀' j t
  simp only [mem_inter_iff, hA.mem_swEv G, mem_ofPred_eq, hA.swT G hr hr', hA.nextStart G hr hr']

end CandAt

end InteractingSLE.Sec5.CrossCond.StagedRepJ
