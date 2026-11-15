/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrBound

/-!
# Prop 5.9's node laws: the comparison clause of the node candidates

Packet PROVE-STAGED-NODETRANSFER. For every node `n`, rational `q > 0` and list `t`, the killed comparison clause
(`CompClauseK`, R78) of PROVE-PROP59-NODETREE's node candidate `nodeCand … n q j t` for its canonical past (base
`nodeBase` with the trivial given past, as in `nodeObjects`), reached event and start, by the transfer
`compClauseK_transfer` along the pair `(field in chart Q, counterflow history)`:

* the target side: the node tree agrees with `gamNodeData` at almost every sample (`ae_nodeGood_pieceZ`,
  `agreeAt_nodeD_gamNodeData`), so the canonical node pasts lie in `aeComap` of `Gam`'s (`canonQ_le_aeComap`), the
  reached events agree almost surely (`canonR_ae_eq`) and the record is `gamNodeObs ∘ pieceZ` almost surely;
* the laws of the pair agree on PIECES' space and on the glued space (PROVE-STAGED-REPJ's `map_pieceZ_eq`);
* the source side: `nodeBound_of_glue` (PROVE-STAGED-NODECOMP's `FlagGluedRep` for the node flags at the full depth,
  the node dilation frozen by the past), whose remaining inputs are the glued identifications `NodeGluePast` and
  `NodeGlueObs`;
* inadmissible lists are never reached (PROVE-STAGED-NODE's `alive_of_mem_canonR`).

**`compClauseK_nodeCand`**. R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNTr

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System
open Prop59NodeTree StagedRepLater StagedKCand StagedKill StagedRep StagedRepJ StagedNComp StagedCand StagedNode
open Sec4 (IsStripGFF IsStripCounterflowDriver)

section Main

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace Ωa] (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
  (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ)

include hκ4 in
/-- **The killed comparison clause of the node candidate `(j, t)`** (the second clause of `Wire.Night.NodeLaw`, with
the base `nodeBase` of the trivial given past), from the stopped representation of the node flags' restarted word
(`FlagGluedRep`, for non-null alive events) and the two glued identifications `NodeGluePast`, `NodeGlueObs` (needed
only for admissible lists; inadmissible lists are never reached). -/
theorem compClauseK_nodeCand (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {n : ℕ} {q : ℚ} (hq : 0 < q) {j : ℕ}
    (t : Fin j → ℝ≥0)
    (hrep : ∀ us : ℂ → ℝ, IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn
        (sourceWord (x₀ := x₀) hκ hb).jumps us →
      ∀ hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t),
      candMu x₀ (κ := κ) P h W ζ hG.1 (ndA x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t (q : ℝ).toNNReal) ≠ 0 →
      FlagGluedRep x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv
        ((Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq)))
    (hpast : ∀ us : ℂ → ℝ, IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn
        (sourceWord (x₀ := x₀) hκ hb).jumps us →
      ∀ hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t),
      NodeGluePast x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv ((Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq)))
    (hobs : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) →
      NodeGlueObs x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t (q : ℝ).toNNReal) :
    CompClauseK κ (P.prod Pa)
      (canonQ (nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise (fun _ _ => ⊥) n q)
        (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid
        (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t)
      (canonR (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
        (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t)
      (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
      (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
      (farL (Nat.lt_of_lt_of_le (nodeNL_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
      (farR (Nat.lt_of_lt_of_le (nodeNR_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
      (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t)
      (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).W
      (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).VL
      (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).VR
      (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).ζ := by
  have hhm := hG.1
  have hgood := ae_nodeGood_pieceZ x₀ h44 hκ hκ4 hb P Pa h W ζ hA hG hcf (scheduleAt n)
  have hagr : ∀ᵐ ω' ∂(P.prod Pa), (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).AgreeAt
      (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (q : ℝ).toNNReal) ω'.1
      (pieceZ (Ωa := Ωa) x₀ κ h W ζ ω') := by
    filter_upwards [hgood] with ω' hω'
    exact agreeAt_nodeD_gamNodeData x₀ h44 hκ hκ4 hb P h W ζ noise n q hω'.1 hω'.2
  have hag : ∀ᵐ ω' ∂(P.prod Pa), (∀ j t, PieceAt (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t)
      (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal j t) ω' (pieceZ (Ωa := Ωa) x₀ κ h W ζ ω')) ∧
      nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q ω' =
        gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal (pieceZ (Ωa := Ωa) x₀ κ h W ζ ω') := by
    filter_upwards [hagr] with ω' h' using ⟨fun j t => pieceAt_nodeCand h' j t, nodeStart_eq_gam h'⟩
  have hR0 : ∀ᵐ ω' ∂(P.prod Pa), (ω' ∈ nodeR0 (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q ↔
      pieceZ (Ωa := Ωa) x₀ κ h W ζ ω' ∈ gamNodeR0 h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal) := by
    filter_upwards [hagr] with ω' h' using mem_nodeR0_iff_gam h'
  have hZm := measurable_pieceZ (Ωa := Ωa) x₀ hhm hcf
  have hfam := isRegFam_nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q
  have hy₀ := measurable_nodeStart (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q
  have hbase : nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise (fun _ _ => ⊥) n q ≤
      aeComap (P.prod Pa) (pieceZ (Ωa := Ωa) x₀ κ h W ζ) (gamNodeBase h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal) := by
    refine sup_le bot_le (MeasurableSpace.generateFrom_le ?_)
    rintro _ rfl
    refine ⟨gamNodeR0 h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal, measurableSet_gamNodeBase_R0 h44 hκ hκ4 hb n _,
      ?_⟩
    filter_upwards [hR0] with ω' h' using propext h'
  have hQ := canonQ_le_aeComap ratGrid (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) hfam
    (isRegFam_gamNodeCand h44 hκ hκ4 hb n (q : ℝ).toNNReal) hy₀ (measurable_gamNodeStart h44 hκ hκ4 hb n _) hag
    hbase j t
  have hRae := canonR_ae_eq ratGrid (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) hag hR0 j t
  by_cases hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)
  · obtain ⟨us, hus, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
      (Restart.BoundaryWord.isPiecewiseConstantBoundaryData (sourceWord (x₀ := x₀) hκ hb))
    have hr0 : 0 < (q : ℝ).toNNReal := (Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq)
    have hbound := nodeBound_of_glue x₀ h44 hκ hκ4 hb P h W ζ hG hcf hv hr0 (hrep us hus hv) (hpast us hus hv)
      (hobs hv)
    refine compClauseK_transfer hZm (measurable_gZ x₀ h hhm) (map_pieceZ_eq x₀ P Pa h W ζ hhm hcf)
      (gamNodeQ_le h44 hκ hκ4 hb n (q : ℝ).toNNReal j t)
      (RΓ := gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal j t)
      (measurable_gamNodeObs h44 hκ hκ4 hb n (q : ℝ).toNNReal j t) ?_ ?_ hbound
    · intro A hA hAR
      obtain ⟨M₀, hM₀, hAM⟩ := hQ A hA
      refine ⟨M₀ ∩ gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal j t,
        hM₀.inter (measurableSet_gamNodeR h44 hκ hκ4 hb n _ j t), inter_subset_right, ?_⟩
      have e : A = A ∩ canonR (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid
          (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)
          (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t :=
        (inter_eq_left.2 hAR).symm
      rw [e, preimage_inter]
      exact hAM.inter hRae
    · filter_upwards [hag] with ω' hω' _
      refine Prod.ext (canonY_congr hω'.1 hω'.2 j t) ?_
      have hc := hω'.1 j t
      simp only [gamNodeObs, pieceSamp, hc.W, hc.VL, hc.VR, hc.ζ]
  · intro S hS p hp A hA hAR
    have hempty : canonR (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid
        (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t = ∅ :=
      eq_empty_of_forall_notMem fun ω' hω' =>
        hv (alive_of_mem_canonR x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q j t ω' hω').1.1.1.1
    have h0 : (P.prod Pa) A = 0 := by
      rw [hempty] at hAR
      exact measure_mono_null hAR measure_empty
    rw [h0, mul_zero]
    exact bot_le

end Main

end InteractingSLE.Sec5.CrossCond.StagedNTr
