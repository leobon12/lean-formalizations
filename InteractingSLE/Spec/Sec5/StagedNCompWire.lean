/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNCompRep
import InteractingSLE.Spec.Sec5.StagedNCompArc

/-!
# Proposition 5.9's node laws from the flag word's pathwise facts and the node transfer

Packet PROVE-STAGED-NODECOMP. The comparison clause `NodeCompOn h44 (nodeObjects h44)` (the open clause of
PROVE-STAGED-NODE) is reduced to two named inputs, the node analogues of PROVE-STAGED-S7's and PROVE-STAGED-REPJ's
targets for the root:

* `FlagGluedRep` / `FlagGluedClause` (`StagedNCompRep`): the stopped representation / killed comparison clause of the
  flag candidate's restarted word on the glued space (conditioned on the alive event, past `candFiltF … 0`);
* `FlagPaths`: almost surely on the alive event the restarted start is strictly ordered, the restarted word is killed
  at its far (junction) marks with left limits, and its driver has a trace up to the restarted lifetime;
* **`NodeFlagPathsStatement`** (named input, S7's items 1 and 3 for the node candidates): `FlagPaths` for the node
  flags at every node depth `nodeLen + j`, list `nodePre ++ t`, counterflow time `q`;
* **`flagGluedRep_of_flagPaths`**, **`flagGluedClause_of_flagPaths`**: `FlagGluedRep` and `FlagGluedClause` from
  `FlagPaths` (PROVED: word entrance, threshold, stopped representation, disintegration);
* **`NodeTransferStatement`** (named input, REPJ's transfer for the node candidates): the glued representation of
  the node flags `nodeFlag (scheduleAt n)` at the node depth `nodeLen + j` (list `nodePre ++ t`, counterflow time `q`)
  gives the comparison clause of the node candidate `(j, t)` of `nodeObjects` (law transfer through the pair (field,
  counterflow history), the dilation `nodeScale` frozen by the past, the subtree reindexing, the lift to `Ω × ℝ`; the
  weights match by `stageρL_nodeρL`/`imgStageRhoL_treeIdx_node`);
* **`nodeCompOn_of_paths_transfer`**, **`nodeLawOn_nodeObjects_of_paths_transfer`**: `hNodeLaw` for `nodeObjects` from
  the two named inputs and Part A's clearance form.

Conditional helpers with distinct names; they replace no source theorem. R48: the only other named input is
`h44 : Theorem12ParamCond44Statement` (R74); nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNComp

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater Prop59NodeTree
open Prop59Stage Prop59System StagedKCand StagedKill StagedRep StagedCand StagedAdapt StagedNode Wire.Night
open Sec4 (IsStripGFF IsStripCounterflowDriver)

/-! ### The glued clause and the pathwise facts of a flag word -/

section Flag

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

/-- **The pathwise facts of the flag candidate's restarted word**, almost surely on the alive event: a strictly ordered
start, the killing at the far (junction) marks with left limits, and a trace of the driver up to the restarted
lifetime. -/
def FlagPaths (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : Prop :=
  ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hhm), p ∈ s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
      (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ) →
    (StrictAnti (fun i => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s)
        (lastO ℓ t : ℝ) i 0 p) ∧
      StrictMono (fun j => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s)
        (lastO ℓ t : ℝ) j 0 p)) ∧
    IsKilledAtFarLim (farL (Nat.lt_of_lt_of_le (rootNL_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ ℓ)))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ ℓ)))
      (fun r => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s)
        (lastO ℓ t : ℝ) r p)
      (fun i r => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s)
        (lastO ℓ t : ℝ) i r p)
      (fun j r => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s)
        (lastO ℓ t : ℝ) j r p)
      (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s)
        (lastO ℓ t : ℝ) p) ∧
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun r => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
      (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ) r p)
      (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s)
        (lastO ℓ t : ℝ) p) η

include hκ4 in
/-- **The stopped representation of a flag candidate from its pathwise facts.** -/
theorem flagGluedRep_of_flagPaths (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) (hℓ : 0 < ℓ) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : candMu x₀ (κ := κ) P h W ζ hG.1 (s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
      (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)) ≠ 0)
    (hpaths : FlagPaths x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) :
    FlagGluedRep x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs :=
  flagGluedRep_of_paths x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf hus hv hℓ hs hA0
    (hpaths.mono fun _ hp hpA => (hp hpA).1) (hpaths.mono fun _ hp hpA => (hp hpA).2.1)
    (hpaths.mono fun _ hp hpA => (hp hpA).2.2)

include hκ4 in
/-- **The glued clause of a flag candidate from its pathwise facts.** -/
theorem flagGluedClause_of_flagPaths (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) (hℓ : 0 < ℓ) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : candMu x₀ (κ := κ) P h W ζ hG.1 (s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
      (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)) ≠ 0)
    (hpaths : FlagPaths x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) :
    FlagGluedClause x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs :=
  flagGluedClause_of_rep x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf hv hs hA0
    (flagGluedRep_of_flagPaths x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf hus hv hℓ hs hA0 hpaths)

end Flag

/-! ### The named inputs and the node laws -/

/-- **PROVE-STAGED-S7's items 1 and 3 for the node candidates** (named input): in every Figure 5.1 setting, for every
node `n`, positive rational counterflow time `q` and admissible extension `nodePre ++ t` of the node prefix, the flag
candidate of the node flags has its pathwise facts (`FlagPaths`) at the counterflow time `q`. -/
def NodeFlagPathsStatement (h44 : Theorem12ParamCond44Statement.{0}) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    ∀ _hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀},
    ∀ _hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ,
    ∀ (n : ℕ) (q : ℚ), 0 < q → ∀ (j : ℕ) (t : Fin j → ℝ≥0),
      IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) →
      FlagPaths x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) _hG.1 (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) (q : ℝ).toNNReal

/-- **PROVE-STAGED-REPJ's transfer for the node candidates** (named input): in every Figure 5.1 setting, with the
stage objects `nodeObjects`, the glued representation of the node flags at the node depth (for every admissible
extension of the node prefix with non-null alive event) gives the comparison clause of the node candidate. -/
def NodeTransferStatement (h44 : Theorem12ParamCond44Statement.{0}) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    ∀ hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀},
    ∀ hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ,
    ∀ htr : (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)),
    let d := nodeObjects h44 hκ hκ4 hb P h W ζ γ hG hcf htr;
    ∀ (n : ℕ) (q : ℚ) (hq : 0 < q) (j : ℕ) (t : Fin j → ℝ≥0),
      (∀ (us : ℂ → ℝ),
        IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us →
        ∀ hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t),
        candMu x₀ (κ := κ) P h W ζ hG.1 (s3Alive (q : ℝ).toNNReal
          (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
            (Fin.append (nodePre (scheduleAt n)) t))
          (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG.1 (nodeLen (scheduleAt n) + j)
            (Fin.append (nodePre (scheduleAt n)) t) (q : ℝ).toNNReal)
          (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ)) ≠ 0 →
        FlagGluedRep x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv
          ((Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq))) →
      CompClauseK κ (P.prod d.measure)
        (canonQ (nodeBase x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise d.nodeBase n q)
          (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) ratGrid
          (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (canonR (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
          (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q)
          (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (farL (Nat.lt_of_lt_of_le (nodeNL_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (farR (Nat.lt_of_lt_of_le (nodeNR_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (canonY (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q)
          (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).W
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).VL
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).VR
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).ζ

/-- **The comparison clause of every node law** for `nodeObjects`, from the flag word's pathwise facts and the node
transfer. -/
theorem nodeCompOn_of_paths_transfer (h44 : Theorem12ParamCond44Statement.{0}) (hP : NodeFlagPathsStatement h44)
    (hT : NodeTransferStatement h44) : NodeCompOn h44 (nodeObjects h44) := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ γ hG hcf htr d n q hq j t
  refine hT hκ hκ4 hb P h W ζ γ hG hcf htr n q hq j t fun us hus hv hA0 => ?_
  have hℓ : 0 < nodeLen (scheduleAt n) + j := Nat.lt_of_lt_of_le (nodeLen_pos (s := scheduleAt n)) (Nat.le_add_right
      _ _)
  exact flagGluedRep_of_flagPaths x₀ h44 hκ hκ4 hb P h W ζ _ hG hcf hus hv hℓ _ hA0
    (hP hκ hκ4 hb P h W ζ hG hcf n q hq j t hv)

/-- **`hNodeLaw` for `nodeObjects`** from the flag word's pathwise facts, the node transfer and Part A's clearance
form (the path clause, PROVE-STAGED-NODE). -/
theorem nodeLawOn_nodeObjects_of_paths_transfer (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hP : NodeFlagPathsStatement h44) (hT : NodeTransferStatement h44) :
    NodeLawOn h44 (nodeObjects h44) :=
  nodeLawOn_nodeObjects' h44 hA (nodeCompOn_of_paths_transfer h44 hP hT)

end InteractingSLE.Sec5.CrossCond.StagedNComp
