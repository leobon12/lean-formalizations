/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrGlue

/-!
# Prop 5.9's node laws: the glued bound for the transfer to the node candidates

Packet PROVE-STAGED-NODETRANSFER. The comparison clause of the node candidate `(j, t)` of the node `n` is transferred
(`compClauseK_transfer`) along `gZ = (field in chart Q, counterflow history)` from the glued space. The glued side
must give, for every canonical past event `M ⊆ gamNodeR` of `Gam`, the bound
`p μ(gZ⁻¹ M) ≤ μ(gZ⁻¹ M ∩ {gamNodeObs ∘ gZ ∈ S})`. It comes from the flag word of the node flags `nodeFlag s` at the
full depth `nodeLen s + j` (list `nodePre s ++ t`), PROVE-STAGED-NODECOMP's `FlagGluedRep`, through
`compClauseK_flagGlue`, with:

* the node dilation `tf (gamNodeScale ∘ gZ)`, a function of the tip marks of the node tree (revealed past on `Gam`),
  frozen in the past — not a function of the stage start;
* the restarted word reindexed to the node's mark count (`ndVL`, `ndVR`, `ndStart`; `CompClauseK.reindex'`; the
  weights match by PROVE-STAGED-NODECOMP's `stageρL_nodeρL`);
* two glued identifications, named here as statements (the node analogues of PROVE-STAGED-REPJ's `GluePast` and
  `GlueObs`):
  - **`NodeGluePast`**: the `gZ`-preimages of `Gam`'s canonical node past events inside `gamNodeR` are, almost
    surely, events of the Galmarino filtration `candFiltF` at time `0` inside the alive event;
  - **`NodeGlueObs`**: almost surely on the alive event and `gZ⁻¹ gamNodeR`, the canonical marks of `Gam`'s node
    candidate are the dilated restarted marks, and its killed samples are those of the dilated restarted word.

**`nodeBound_of_glue`** assembles them. R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real symmDiff
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNTr

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System
open Prop59NodeTree StagedRepLater StagedKCand StagedKill StagedRep StagedRepJ StagedNComp StagedCand
open Sec4 (IsStripGFF IsStripCounterflowDriver)

/-! ### Generic tools -/

section Tools

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A measurable set almost surely equal to an event at time `0` is an event of the null augmentation at `0`. -/
theorem measurableSet_nullAugmented_of_ae {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {A D : Set Ω}
    (hA : MeasurableSet[𝓕 0] A) (hD : MeasurableSet D) (h : A =ᵐ[μ] D) :
    MeasurableSet[Ito.nullAugmented 𝓕 μ 0] D := by
  have hAm : MeasurableSet A := 𝓕.le 0 _ hA
  have hN : MeasurableSet[Ito.nullAugmented 𝓕 μ 0] (A ∆ D) :=
    Ito.measurableSet_nullAugmented_of_null (hAm.symmDiff hD) (measure_symmDiff_eq_zero_iff.2 h) 0
  have hA' : MeasurableSet[Ito.nullAugmented 𝓕 μ 0] A := Ito.le_nullAugmented 𝓕 μ 0 _ hA
  have e : D = A ∆ (A ∆ D) := (symmDiff_symmDiff_cancel_left A D).symm
  rw [e]
  exact hA'.symmDiff hN

/-- The canonical pasts contain the base. -/
theorem le_canonQ {𝓑 : MeasurableSpace Ω} {nL₀ nR₀ : ℕ} {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0}
    {hnL : 0 < nL₀} {hnR : 0 < nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} :
    ∀ j t, 𝓑 ≤ canonQ 𝓑 cand G hnL hnR y₀ j t
  | 0, _ => le_rfl
  | j + 1, t => (le_canonQ j (Fin.init t)).trans le_sup_left

variable {κ : ℝ} {𝓠 : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω} {R : Set Ω}

/-- **The comparison clause along equalities of the numbers of marks**, with the target data given by equations. -/
theorem CompClauseK.reindex' {nL nR nL' nR' : ℕ} (eL : nL = nL') (eR : nR = nR') {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ρL' : Fin nL' → ℝ}
    {ρR' : Fin nR' → ℝ} {iL' : Fin nL'} {iR' : Fin nR'} {y' : Ω → Start nL' nR'} {VL' : Fin nL' → ℝ≥0 → Ω → ℝ}
    {VR' : Fin nR' → ℝ≥0 → Ω → ℝ}
    (hρL : ∀ i, ρL' i = ρL (Fin.cast eL.symm i)) (hρR : ∀ k, ρR' k = ρR (Fin.cast eR.symm k))
    (hiL : (iL' : ℕ) = iL) (hiR : (iR' : ℕ) = iR)
    (hy : ∀ ω, y' ω = ((y ω).1, fun i => (y ω).2.1 (Fin.cast eL.symm i), fun k => (y ω).2.2 (Fin.cast eR.symm k)))
    (hVL : ∀ i, VL' i = VL (Fin.cast eL.symm i)) (hVR : ∀ k, VR' k = VR (Fin.cast eR.symm k))
    (h : CompClauseK κ P 𝓠 R ρL ρR iL iR y W VL VR ζ) : CompClauseK κ P 𝓠 R ρL' ρR' iL' iR' y' W VL' VR' ζ := by
  subst eL eR
  obtain rfl : ρL' = ρL := funext hρL
  obtain rfl : ρR' = ρR := funext hρR
  obtain rfl : iL' = iL := Fin.ext hiL
  obtain rfl : iR' = iR := Fin.ext hiR
  obtain rfl : VL' = VL := funext hVL
  obtain rfl : VR' = VR := funext hVR
  obtain rfl : y' = y := funext fun ω => (hy ω).trans rfl
  exact h

end Tools

/-! ### Reindexed starts -/

section Cast

variable {nL nR nL' nR' : ℕ}

/-- A start with its marks reindexed along equalities of the numbers of marks. -/
def castStart (eL : nL = nL') (eR : nR = nR') (y : Start nL nR) : Start nL' nR' :=
  (y.1, fun i => y.2.1 (Fin.cast eL.symm i), fun k => y.2.2 (Fin.cast eR.symm k))

theorem measurable_castStart (eL : nL = nL') (eR : nR = nR') : Measurable (castStart eL eR) :=
  measurable_fst.prodMk ((measurable_pi_iff.2 fun _ => (measurable_pi_apply _).comp measurable_snd.fst).prodMk
    (measurable_pi_iff.2 fun _ => (measurable_pi_apply _).comp measurable_snd.snd))

end Cast

/-! ### The node's restarted word on the glued space -/

section Node

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

/-- The alive event of the node flags' candidate `nodePre ++ t` (the node candidate `(j, t)`). -/
abbrev ndA (hhm : Measurable h) (n j : ℕ) (t : Fin j → ℝ≥0) (r : ℝ≥0) : Set (Ω × HistorySpace 0 0) :=
  flA x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
    (Fin.append (nodePre (scheduleAt n)) t) r

/-- The restarted driver of the node candidate `(j, t)` on the glued space. -/
abbrev ndW (hhm : Measurable h) (n j : ℕ) (t : Fin j → ℝ≥0) (r : ℝ≥0) : ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  flW x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
    (Fin.append (nodePre (scheduleAt n)) t) r

/-- The restarted left marks of the node candidate `(j, t)`, reindexed to the node's mark count. -/
abbrev ndVL (hhm : Measurable h) (n j : ℕ) (t : Fin j → ℝ≥0) (r : ℝ≥0) :
    Fin (nodeNL x₀ hκ hb n + j) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  fun i => flVL x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
    (Fin.append (nodePre (scheduleAt n)) t) r (Fin.cast (Nat.add_assoc _ _ _) i)

/-- The restarted right marks of the node candidate `(j, t)`, reindexed to the node's mark count. -/
abbrev ndVR (hhm : Measurable h) (n j : ℕ) (t : Fin j → ℝ≥0) (r : ℝ≥0) :
    Fin (nodeNR x₀ hκ hb n + j) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  fun k => flVR x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
    (Fin.append (nodePre (scheduleAt n)) t) r (Fin.cast (Nat.add_assoc _ _ _) k)

/-- The restarted lifetime of the node candidate `(j, t)`. -/
abbrev ndζ (hhm : Measurable h) (n j : ℕ) (t : Fin j → ℝ≥0) (r : ℝ≥0) : Ω × HistorySpace 0 0 → ℝ≥0∞ :=
  flζ x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
    (Fin.append (nodePre (scheduleAt n)) t) r

/-- The restarted start of the node candidate `(j, t)` (driver `0`, reindexed initial marks). -/
abbrev ndStart (hhm : Measurable h) (n j : ℕ) (t : Fin j → ℝ≥0) (r : ℝ≥0) (p : Ω × HistorySpace 0 0) :
    Start (nodeNL x₀ hκ hb n + j) (nodeNR x₀ hκ hb n + j) :=
  ((0 : ℝ), fun i => ndVL x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r i 0 p,
    fun k => ndVR x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r k 0 p)

omit [StandardBorelSpace Ω] in
theorem ndStart_eq (hhm : Measurable h) (n j : ℕ) (t : Fin j → ℝ≥0) (r : ℝ≥0) :
    ndStart x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r =
      castStart (Nat.add_assoc _ _ _).symm (Nat.add_assoc _ _ _).symm ∘
        flStart x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) r := rfl

include hκ4 in
/-- **The killed comparison clause of the node candidate's dilated restarted word on the glued space**, with the
node's weights `stageρL κ (nodeρL κ c s) j` and mark count (`compClauseK_flagGlue` reindexed). -/
theorem compClauseK_nodeGlue (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ} {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0} (hr : 0 < r)
    (hA0 : candMu x₀ (κ := κ) P h W ζ hG.1 (ndA x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r) ≠ 0)
    (hrep : FlagGluedRep x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr)
    {C : Ω × HistorySpace 0 0 → ℝ≥0}
    (hC : Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr] C)
    (hC0 : ∀ p, C p ≠ 0) {y' : Ω × HistorySpace 0 0 → Start (nodeNL x₀ hκ hb n + j) (nodeNR x₀ hκ hb n + j)}
    (hy' : Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr] y')
    (hy'e : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ ndA x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r →
      (y' p).2 = (dilV (C p) (ndStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r p)).2) :
    CompClauseK κ (candMu x₀ (κ := κ) P h W ζ hG.1)
      (flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr)
      (ndA x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r)
      (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
      (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
      (farL (Nat.lt_of_lt_of_le (nodeNL_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
      (farR (Nat.lt_of_lt_of_le (nodeNR_pos x₀ hκ hb n) (Nat.le_add_right _ j))) y'
      (fun u p => (√(C p : ℝ))⁻¹ * ndW x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r (C p * u) p)
      (fun i u p => (√(C p : ℝ))⁻¹ * ndVL x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r i (C p * u) p)
      (fun k u p => (√(C p : ℝ))⁻¹ * ndVR x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r k (C p * u) p)
      (fun p => ndζ x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r p / C p) := by
  have eL : rootNL (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j) = nodeNL x₀ hκ hb n + j :=
    (Nat.add_assoc _ _ _).symm
  have eR : rootNR (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j) = nodeNR x₀ hκ hb n + j :=
    (Nat.add_assoc _ _ _).symm
  have hyf : Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr]
      (castStart eL.symm eR.symm ∘ y') := (measurable_castStart eL.symm eR.symm).comp hy'
  have hyfe : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ ndA x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r →
      ((castStart eL.symm eR.symm ∘ y') p).2 = (dilV (C p) (flStart x₀ h44 hκ hκ4 hb P h W ζ
        (nodeFlag (scheduleAt n)) hG.1 (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r
          p)).2 := by
    filter_upwards [hy'e] with p hp hpA
    have e := hp hpA
    refine Prod.ext (funext fun i => ?_) (funext fun k => ?_)
    · exact congrFun (congrArg Prod.fst e) (Fin.cast eL i)
    · exact congrFun (congrArg Prod.snd e) (Fin.cast eR k)
  have hflag := compClauseK_flagGlue x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf hv hr hA0 hrep hC hC0
    hyf hyfe
  refine CompClauseK.reindex' eL eR (fun i => stageρL_nodeρL κ _ _ j i) (fun k => stageρR_nodeρR κ _ _ j k)
    ?_ ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hflag
  · simp only [farL]; omega
  · simp only [farR]; omega

/-- **The glued past of a node candidate** (named statement): the `gZ`-preimage of every canonical past event of
`Gam`'s node candidate `(j, t)` inside its reached event is almost surely an event of the Galmarino filtration of the
node flags' candidate `nodePre ++ t` at time `0`, inside its alive event. -/
def NodeGluePast (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0} (hr : 0 < r) :
    Prop :=
  ∀ M, MeasurableSet[gamNodeQ h44 hκ hκ4 (x₀ := x₀) hb n r j t] M → M ⊆ gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t →
    ∃ A, MeasurableSet[candFiltF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr 0] A ∧
      A ⊆ ndA x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r ∧
      A =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] gZ x₀ (κ := κ) h ⁻¹' M

/-- **The glued observable of a node candidate** (named statement): almost surely on the alive event and on
`gZ⁻¹ gamNodeR`, the canonical marks of `Gam`'s node candidate `(j, t)` are the restarted marks dilated by the node
factor `tf (gamNodeScale ∘ gZ)`, and its killed samples are the samples of the dilated restarted word. -/
def NodeGlueObs (hhm : Measurable h) (n j : ℕ) (t : Fin j → ℝ≥0) (r : ℝ≥0) : Prop :=
  ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hhm), p ∈ ndA x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r →
    gZ x₀ (κ := κ) h p ∈ gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t →
    (canonY (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) (gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n r) j t
        (gZ x₀ (κ := κ) h p)).2 =
      (dilV (tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p) : ℝ))
        (ndStart x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r p)).2 ∧
    pieceSamp (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r j t).W (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r j t).VL
        (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r j t).VR (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r j t).ζ
        (gZ x₀ (κ := κ) h p) =
      samp (fun u => (√(tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p) : ℝ) : ℝ))⁻¹ *
          ndW x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r
            (tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p) : ℝ) * u) p)
        (fun i u => (√(tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p) : ℝ) : ℝ))⁻¹ *
          ndVL x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r i
            (tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p) : ℝ) * u) p)
        (fun k u => (√(tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p) : ℝ) : ℝ))⁻¹ *
          ndVR x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r k
            (tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p) : ℝ) * u) p)
        (ndζ x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r p /
          tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p) : ℝ))

include hκ4 in
/-- **The glued bound for the transfer of a node candidate's comparison clause.** From the stopped representation of
the node flags' word (`FlagGluedRep`, needed only when the alive event is not null) and the two glued identifications
`NodeGluePast`, `NodeGlueObs`, every canonical node past event `M ⊆ gamNodeR` of `Gam` satisfies
`p μ(gZ⁻¹ M) ≤ μ(gZ⁻¹ M ∩ {gamNodeObs ∘ gZ ∈ S})` under every killed premise for the node's stage word. -/
theorem nodeBound_of_glue (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ} {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0} (hr : 0 < r)
    (hrep : candMu x₀ (κ := κ) P h W ζ hG.1 (ndA x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r) ≠ 0 →
      FlagGluedRep x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr)
    (hpast : NodeGluePast x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hr)
    (hobs : NodeGlueObs x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r) :
    ∀ S : Set (Start (nodeNL x₀ hκ hb n + j) (nodeNR x₀ hκ hb n + j) ×
      Samp (nodeNL x₀ hκ hb n + j) (nodeNR x₀ hκ hb n + j)), MeasurableSet S → ∀ p : ℝ≥0∞,
      CompPremiseFarK κ (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (farL (Nat.lt_of_lt_of_le (nodeNL_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (farR (Nat.lt_of_lt_of_le (nodeNR_pos x₀ hκ hb n) (Nat.le_add_right _ j))) univ S p →
      ∀ M, MeasurableSet[gamNodeQ h44 hκ hκ4 (x₀ := x₀) hb n r j t] M →
        M ⊆ gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t →
        p * candMu x₀ (κ := κ) P h W ζ hG.1 (gZ x₀ (κ := κ) h ⁻¹' M) ≤
          candMu x₀ (κ := κ) P h W ζ hG.1 (gZ x₀ (κ := κ) h ⁻¹' M ∩
            {p' | gamNodeObs h44 hκ hκ4 (x₀ := x₀) hb n r j t (gZ x₀ (κ := κ) h p') ∈ S}) := by
  classical
  intro S hS p hp M hM hMR
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set A := ndA x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r with hAdef
  by_cases hA0 : μ A = 0
  · obtain ⟨A', -, hAA, hAM⟩ := hpast M hM hMR
    have h0 : μ (gZ x₀ (κ := κ) h ⁻¹' M) = 0 := by
      rw [← measure_congr hAM]; exact measure_mono_null hAA hA0
    rw [h0, mul_zero]
    exact bot_le
  set 𝓐 := candFiltF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr with h𝓐
  have h𝓐𝓠 : 𝓐 0 ≤ flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr :=
    Ito.le_nullAugmented 𝓐 _ 0
  have hAm𝓐 : MeasurableSet[𝓐 0] A :=
    measurableSet_s3Alive_candFiltF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr 0
  have hAm : MeasurableSet A := 𝓐.le 0 _ hAm𝓐
  have hZm : Measurable (gZ x₀ (κ := κ) h) := measurable_gZ x₀ h hG.1
  -- a glued past event of `Gam` is an event of the null-augmented past
  have hpast₀ : ∀ M', MeasurableSet[gamNodeQ h44 hκ hκ4 (x₀ := x₀) hb n r j t] M' →
      M' ⊆ gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t →
      MeasurableSet[flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr]
        (A ∩ gZ x₀ (κ := κ) h ⁻¹' M') := by
    intro M' hM' hM'R
    obtain ⟨A', hA', hAA, hAM⟩ := hpast M' hM' hM'R
    refine measurableSet_nullAugmented_of_ae hA' (hAm.inter (hZm (gamNodeQ_le h44 hκ hκ4 hb n r j t _ hM'))) ?_
    have h1 : A' =ᵐ[μ] A ∩ gZ x₀ (κ := κ) h ⁻¹' M' := by
      filter_upwards [hAM] with p' hp'
      show (p' ∈ A') = (p' ∈ A ∧ p' ∈ gZ x₀ (κ := κ) h ⁻¹' M')
      by_cases h' : p' ∈ A'
      · have : p' ∈ gZ x₀ (κ := κ) h ⁻¹' M' := by rw [← hp']; exact h'
        have hpA : p' ∈ A := hAA h'
        simp only [h', hpA, this, and_self]
      · have : p' ∉ gZ x₀ (κ := κ) h ⁻¹' M' := by rw [← hp']; exact h'
        simp only [h', this, and_false]
    exact cond_absolutelyContinuous.ae_eq h1
  have hRQ := measurableSet_gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t
  have hD : MeasurableSet[flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr]
      (A ∩ gZ x₀ (κ := κ) h ⁻¹' gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t) := hpast₀ _ hRQ le_rfl
  -- the node dilation, frozen by the revealed past
  set C : Ω × HistorySpace 0 0 → ℝ≥0 := fun p' =>
    if p' ∈ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t then
      tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p') : ℝ) else 1 with hCdef
  have hscale : ∀ B : Set ℝ≥0, MeasurableSet B → MeasurableSet[gamNodeQ h44 hκ hκ4 (x₀ := x₀) hb n r j t]
      ((fun γ => tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r γ : ℝ)) ⁻¹' B) := by
    intro B hB
    have hm : Measurable fun m : (Fin (nodeNL x₀ hκ hb n) → ℝ) × (Fin (nodeNR x₀ hκ hb n) → ℝ) =>
        tf ((nodeLam (m.1 (farL (nodeNL_pos x₀ hκ hb n))) (m.2 (farR (nodeNR_pos x₀ hκ hb n)))).toNNReal : ℝ) :=
      measurable_tf.comp (measurable_coe_nnreal_real.comp (measurable_nodeLamNN (x₀ := x₀) hκ hb n))
    exact le_canonQ j t _ (measurableSet_gamNodeBase_marks h44 hκ hκ4 hb n r (hm hB))
  have hC : Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr] C := by
    intro B hB
    have e : C ⁻¹' B = (A ∩ gZ x₀ (κ := κ) h ⁻¹' (gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t ∩
        (fun γ => tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r γ : ℝ)) ⁻¹' B)) ∪
        ((A ∩ gZ x₀ (κ := κ) h ⁻¹' gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t)ᶜ ∩ {_p' | (1 : ℝ≥0) ∈ B}) := by
      ext p'
      by_cases hp' : p' ∈ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t
      · have hC1 : C p' = tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p') : ℝ) := by
          simp only [hCdef, hp', ↓reduceIte]
        rw [mem_preimage, hC1]
        exact ⟨fun h1 => Or.inl ⟨hp'.1, hp'.2, h1⟩,
          fun h1 => h1.elim (fun h2 => h2.2.2) fun h2 => absurd hp' h2.1⟩
      · have hC1 : C p' = 1 := by simp only [hCdef, hp', ↓reduceIte]
        rw [mem_preimage, hC1]
        exact ⟨fun h1 => Or.inr ⟨hp', h1⟩,
          fun h1 => h1.elim (fun h2 => absurd ⟨h2.1, h2.2.1⟩ hp') fun h2 => h2.2⟩
    rw [e]
    refine (hpast₀ _ (hRQ.inter (hscale B hB)) inter_subset_left).union (hD.compl.inter ?_)
    by_cases h1 : (1 : ℝ≥0) ∈ B
    · simp only [h1, ofPred_true, MeasurableSet.univ]
    · simp only [h1, ofPred_false, MeasurableSet.empty]
  have hC0 : ∀ p', C p' ≠ 0 := by
    intro p'
    simp only [hCdef]
    split_ifs
    · exact tf_ne_zero (NNReal.coe_pos.2 (gamNodeScale_pos h44 hκ hκ4 hb n r _))
    · exact one_ne_zero
  -- the start
  have hst : Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr]
      (ndStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r) := by
    rw [ndStart_eq]
    exact (measurable_castStart _ _).comp ((measurable_flStart_candFiltF x₀ h44 hκ hκ4 hb P h W ζ
      (nodeFlag (scheduleAt n)) hG hcf us hv hr).mono h𝓐𝓠 le_rfl)
  set y' : Ω × HistorySpace 0 0 → Start (nodeNL x₀ hκ hb n + j) (nodeNR x₀ hκ hb n + j) := fun p' =>
    if p' ∈ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t then
      canonY (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) (gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n r) j t
        (gZ x₀ (κ := κ) h p')
    else ((0 : ℝ), (dilV (C p') (ndStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r p')).2) with hy'def
  have hg : Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr] fun p' =>
      ((0 : ℝ), (dilV (C p') (ndStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r p')).2) :=
    measurable_const.prodMk (measurable_dilV hC hst).snd
  have hy' : Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv hr] y' := by
    intro T hT
    have e : y' ⁻¹' T = (A ∩ gZ x₀ (κ := κ) h ⁻¹' (gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t ∩
        canonY (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) (gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n r) j t ⁻¹' T)) ∪
        ((A ∩ gZ x₀ (κ := κ) h ⁻¹' gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t)ᶜ ∩
          (fun p' => ((0 : ℝ), (dilV (C p') (ndStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r p')).2)) ⁻¹' T) := by
      ext p'
      by_cases hp' : p' ∈ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t
      · have hy1 : y' p' = canonY (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r)
            (gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n r) j t (gZ x₀ (κ := κ) h p') := by
          simp only [hy'def, hp', ↓reduceIte]
        rw [mem_preimage, hy1]
        exact ⟨fun h1 => Or.inl ⟨hp'.1, hp'.2, h1⟩,
          fun h1 => h1.elim (fun h2 => h2.2.2) fun h2 => absurd hp' h2.1⟩
      · have hy1 : y' p' = ((0 : ℝ), (dilV (C p') (ndStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r p')).2) := by
          simp only [hy'def, hp', ↓reduceIte]
        rw [mem_preimage, hy1]
        exact ⟨fun h1 => Or.inr ⟨hp', h1⟩,
          fun h1 => h1.elim (fun h2 => absurd ⟨h2.1, h2.2.1⟩ hp') fun h2 => h2.2⟩
    rw [e]
    refine (hpast₀ _ ?_ inter_subset_left).union (hD.compl.inter (hg hT))
    exact measurableSet_canonR_inter_canonY (isRegFam_gamNodeCand h44 hκ hκ4 hb n r)
      (measurable_gamNodeStart h44 hκ hκ4 hb n r) (measurableSet_gamNodeBase_R0 h44 hκ hκ4 hb n r)
      (fun S' hS' => measurableSet_gamNodeBase_start h44 hκ hκ4 hb n r hS') j t T hT
  have hy'e : ∀ᵐ p' ∂μ, p' ∈ A →
      (y' p').2 = (dilV (C p') (ndStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t r p')).2 := by
    filter_upwards [hobs] with p' hp' hpA
    by_cases hR : gZ x₀ (κ := κ) h p' ∈ gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t
    · have hm : p' ∈ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t := ⟨hpA, hR⟩
      have hC1 : C p' = tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p') : ℝ) := by
        simp only [hCdef, hm, ↓reduceIte]
      simp only [hy'def, hm, ↓reduceIte]
      rw [hC1]
      exact (hp' hpA hR).1
    · have hm : p' ∉ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t := fun h' => hR h'.2
      simp only [hy'def, hm, ↓reduceIte]
  have hglue := compClauseK_nodeGlue x₀ h44 hκ hκ4 hb P h W ζ hG hcf hv hr hA0 (hrep hA0) hC hC0 hy' hy'e
  refine bound_of_compClauseK hglue (fun M' hM' hM'R => ?_) ?_ S hS p hp M hM hMR
  · obtain ⟨A', hA', hAA, hAM⟩ := hpast M' hM' hM'R
    exact ⟨A', h𝓐𝓠 _ hA', hAA, hAM⟩
  · filter_upwards [hobs] with p' hp' hpA hR
    have hm : p' ∈ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t := ⟨hpA, hR⟩
    have hC1 : C p' = tf (gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r (gZ x₀ (κ := κ) h p') : ℝ) := by
      simp only [hCdef, hm, ↓reduceIte]
    have hy1 : y' p' = canonY (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r)
        (gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n r) j t (gZ x₀ (κ := κ) h p') := by
      simp only [hy'def, hm, ↓reduceIte]
    refine Prod.ext hy1 ?_
    rw [hC1]
    exact (hp' hpA hR).2.symm

end Node

end InteractingSLE.Sec5.CrossCond.StagedNTr
