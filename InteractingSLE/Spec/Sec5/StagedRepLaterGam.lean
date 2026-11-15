/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterGlue
import InteractingSLE.Spec.Sec5.StagedKCandWire

/-!
# Prop 5.9's root candidates as Borel functions of (field, counterflow history)

Packet PROVE-STAGED-REP2. To transfer the root stage's comparison clause from the glued space to PROVE-PROP59-PIECES'
space (STAGED7's `compClause_of_map_eq`), the candidate's start and samples must be one **Borel function** of the
pair `(field in chart Q, counterflow history)` on both spaces. PIECES' own tree data read the good set through
`toMeasurable P`, which is not a function of that pair. Here the same construction is run on the space
`Gam = DistOn × HistorySpace 0 0` itself, with a good set described by Borel conditions only:

* `gamGood`: the history is a good hitting history and every code driver of every admissible list is a good path
  (both Borel conditions; they give PIECES' `CfGood` and `IsProperArc`);
* `gamData r`: the tree data of PIECES' root experiment on `Gam` (dilation `rootLam`, root marks `rootLam · rootXL`);
* **`gamObs`** and `measurable_gamObs`: (start, samples) of the root candidate, a Borel function on `Gam`;
* `pieceSamp_arcPiece_congr`, `TreeData.pieceSamp_cand_zero_congr`: the samples of a stage-0 candidate depend only on
  the values of the tree data at the sample.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`; `h44` is R74's `Theorem12ParamCond44Statement`, used only
through PROP513C's code drivers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open Sec4 GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage Prop59Pieces StagedKCand StagedKill
open Sec7.StripWall (goodPathSet)

/-! ### Samples of a stage-0 candidate are read at the sample -/

section Congr

variable {Ω Ω' : Type*} {nL nR : ℕ}

/-- The samples of a candidate piece of a killed arc read only the values of its data at the sample. -/
theorem pieceSamp_arcPiece_congr {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0} {A : Set Ω}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {B : ℝ≥0 → Ω → ℝ} {γ' : Ω' → ℝ → ℂ} {P' : Ω' → Set ℝ}
    {S₀' : Ω' → ℝ≥0} {A' : Set Ω'} {xL' : Ω' → Fin nL → ℝ} {xR' : Ω' → Fin nR → ℝ} {B' : ℝ≥0 → Ω' → ℝ}
    {ω : Ω} {ω' : Ω'} (hγ : γ ω = γ' ω') (hP : P ω = P' ω') (hS : S₀ ω = S₀' ω') (hA : ω ∈ A ↔ ω' ∈ A')
    (hxL : xL ω = xL' ω') (hxR : xR ω = xR' ω') :
    pieceSamp (arcPiece γ P S₀ A xL xR B).W (arcPiece γ P S₀ A xL xR B).VL (arcPiece γ P S₀ A xL xR B).VR
      (arcPiece γ P S₀ A xL xR B).ζ ω =
    pieceSamp (arcPiece γ' P' S₀' A' xL' xR' B').W (arcPiece γ' P' S₀' A' xL' xR' B').VL
      (arcPiece γ' P' S₀' A' xL' xR' B').VR (arcPiece γ' P' S₀' A' xL' xR' B').ζ ω' := by
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
  simp only [pieceSamp, samp, arcPiece, arcVL, arcVR, hζ, hW, hrW, hrW', hxL, hxR]
  rfl

end Congr

/-! ### The good set and the tree data on `Gam` -/

/-- The space of (field in chart `Q`, counterflow history). -/
abbrev Gam := DistOn upperHalfPlaneOpens × HistorySpace 0 0

section Gam

variable (h44 : Theorem12ParamCond44Statement.{0}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')

/-- **The good set on `Gam`**: a good hitting history, and every code driver of every admissible list is a good
path. -/
def gamGood : Set Gam :=
  {γ | γ.2 ∈ goodHitSet ∧ ∀ j t, IsValid j t → ∀ k < (scheduleList (candSched j t)).length,
    codeFam h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) Prod.fst (candSched j t) k γ ∈ goodPathSet}

theorem measurableSet_gamGood : MeasurableSet (gamGood h44 hκ hκ4 (x₀ := x₀) hb) := by
  have h1 : MeasurableSet {γ : Gam | γ.2 ∈ goodHitSet} := measurable_snd measurableSet_goodHitSet
  have h2 : ∀ j (t : Fin j → ℝ≥0) k, MeasurableSet {γ : Gam |
      codeFam h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) Prod.fst (candSched j t) k γ ∈ goodPathSet} :=
    fun j t k => ((measurable_codeDriver h44 hκ hκ4 _ _ k).comp measurable_fst) Sec7.StripWall.measurableSet_goodPathSet
  have e : gamGood h44 hκ hκ4 (x₀ := x₀) hb = {γ : Gam | γ.2 ∈ goodHitSet} ∩
      ⋂ j, ⋂ tt : {t : Fin j → ℝ≥0 // IsValid j t}, ⋂ k : Fin (scheduleList (candSched j tt.1)).length,
        {γ : Gam | codeFam h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) Prod.fst (candSched j tt.1) k γ ∈
          goodPathSet} := by
    ext γ
    simp only [gamGood, mem_ofPred_eq, mem_inter_iff, mem_iInter, Subtype.forall]
    refine and_congr_right fun _ => ⟨fun h j t hv k => h j t hv k k.2, fun h j t hv k hk => h j t hv ⟨k, hk⟩⟩
  rw [e]
  exact h1.inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun tt => MeasurableSet.iInter fun k => h2 _ _ _)

/-- **PIECES' root tree data on `Gam`** at counterflow time `r`: the code paths of the field coordinate, the history
coordinate, the dilation `rootLam` and the dilated root marks (noise `0`; the samples do not read it). -/
def gamData (r : ℝ≥0) : TreeData Gam (rootNL (sourceWord (x₀ := x₀) hκ hb)) (rootNR (sourceWord (x₀ := x₀) hκ hb)) where
  r := r
  y := Prod.snd
  lam := fun γ => rootLam r γ.2
  G := gamGood h44 hκ hκ4 (x₀ := x₀) hb
  α := fun j t => qPath h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) Prod.fst j t
  valid := IsValid
  xL0 := fun γ i => rootLam r γ.2 * rootXL hκ hb x₀ r γ.2 i
  xR0 := fun γ j => rootLam r γ.2 * rootXR hκ hb x₀ r γ.2 j
  noise := fun _ _ _ _ => 0

theorem isReg_gamData (r : ℝ≥0) : (gamData h44 hκ hκ4 (x₀ := x₀) hb r).IsReg where
  y := measurable_snd
  lam := (measurable_rootLam r).comp measurable_snd
  lam_pos γ := rootLam_pos r γ.2
  G := measurableSet_gamGood h44 hκ hκ4 hb
  good _ hγ := ⟨cfGood_of_mem_goodHitSet hγ.1 r, fun j t hv => (isProperArc_qPath_of h44 hκ hκ4 _ _ (hγ.2 j t hv)).1⟩
  α j t u := measurable_qPath h44 hκ hκ4 _ _ measurable_fst j t u
  xL0 := measurable_pi_iff.2 fun i => ((measurable_rootLam r).comp measurable_snd).mul
    ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb r).comp measurable_snd))
  xR0 := measurable_pi_iff.2 fun j => ((measurable_rootLam r).comp measurable_snd).mul
    ((measurable_pi_apply j).comp ((measurable_rootXR hκ hb r).comp measurable_snd))
  qrat j t hv := ⟨lastO j t, (lastO_eq hv).symm⟩

/-- **The observable of the root candidate on `Gam`**: (start, samples). -/
def gamObs (r : ℝ≥0) (γ : Gam) :
    Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + 0) (rootNR (sourceWord (x₀ := x₀) hκ hb) + 0) ×
      Samp (rootNL (sourceWord (x₀ := x₀) hκ hb) + 0) (rootNR (sourceWord (x₀ := x₀) hκ hb) + 0) :=
  (((0 : ℝ), (gamData h44 hκ hκ4 (x₀ := x₀) hb r).xL0 γ, (gamData h44 hκ hκ4 (x₀ := x₀) hb r).xR0 γ),
    pieceSamp ((gamData h44 hκ hκ4 (x₀ := x₀) hb r).cand 0 Fin.elim0).W
      ((gamData h44 hκ hκ4 (x₀ := x₀) hb r).cand 0 Fin.elim0).VL
      ((gamData h44 hκ hκ4 (x₀ := x₀) hb r).cand 0 Fin.elim0).VR
      ((gamData h44 hκ hκ4 (x₀ := x₀) hb r).cand 0 Fin.elim0).ζ γ)

theorem measurable_gamObs (r : ℝ≥0) : Measurable (gamObs h44 hκ hκ4 (x₀ := x₀) hb r) :=
  (measurable_const.prodMk ((isReg_gamData h44 hκ hκ4 hb r).xL0.prodMk (isReg_gamData h44 hκ hκ4 hb r).xR0)).prodMk
    (measurable_pieceSamp_of_isRegPiece ((isReg_gamData h44 hκ hκ4 hb r).isRegFam 0 Fin.elim0))

end Gam

end InteractingSLE.Sec5.CrossCond.StagedRepLater
