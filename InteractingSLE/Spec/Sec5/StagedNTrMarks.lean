/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrFinal
import InteractingSLE.Spec.Sec5.StagedRepJMarks

/-!
# Prop 5.9's node laws: the node marks identity, and `NodeTransferStatement`

Packet PROVE-STAGED-NODETRANSFER. **`nodeGlueMarks_of_good`** proves `NodeGlueMarks` (`StagedNTrObs`): at a glued sample
whose node flags' candidate `nodePre ++ t` is alive and whose pair `gZ p` is good, the tree marks of `gamNodeData` at
the full depth are the initial marks of the restarted word in tree order. This is PROVE-STAGED-REPJ's `glueMarks` for
the undilated node tree (`lam = 1`): PROVE-STAGED-REPJ's closed form of the tree marks (`TreeData.marks_eq_cfStage`, any
regular tree) with the continuous local driver of a pre-contact time beyond the last switch, the full-depth arc
identities of `StagedNTrObs`, and the switch capacities `capClock (tau t m) = capClock (candTsF m)`.

Hence (**`nodeTransferStatement_of_partA`**, **`nodeLawOn_nodeObjects_of_partA`**) PROVE-STAGED-NODECOMP's
`NodeTransferStatement h44` and Theorem 1.2's leaf `hNodeLaw` (`NodeLawOn h44 (nodeObjects h44)`) hold under the
clearance form of Part A alone.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; `h44` is
R74's input.
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
open Prop59Nodes Prop59NodeTree StagedRepLater StagedKCand StagedKill StagedRep StagedRepJ StagedNComp StagedCand
open StagedNode StagedFinal
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)

section Marks

variable {x₀ : ℝ} {h44 : Theorem12ParamCond44Statement.{0}} {κ a b a' b' : ℝ} {hκ : 0 < κ} {hκ4 : κ < 4}
  {hb : IsFig51Bounds κ a b a' b'} {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The node marks identity** at every glued sample whose node good set holds at `gZ p`. -/
theorem nodeGlueMarks_of_good {hhm : Measurable h} {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0}
    (hgam : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hhm),
      gZ x₀ (κ := κ) h p ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n)) :
    NodeGlueMarks x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r := by
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
    (Fin.append (nodePre (scheduleAt n)) t) r
  filter_upwards [hgam] with p hZ hpA _
  have hDr := isReg_gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r
  have hDt := isTree_gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r
  have hal := gamNodeData_alive hv hpA hZ
  have hγ : WangWu.IsKilledArc (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n))
      (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ
      (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p)
      (gPre r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm
      (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p) := isKilledArc_gCurve hEg p
  have hq : (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) ∈
      gPre r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm
      (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p := hpA.2
  -- a continuous driver extending the killed driver beyond the last switch
  obtain ⟨S', hS', hlt⟩ := hγ.exists_gt _ hq
  have hS'0 : 0 < S' := lt_of_le_of_lt (by exact_mod_cast lastO_nonneg hv) hlt
  have hw := (hγ.locDrv_spec hS' hS'0).1
  have hEqg := kPath_eqOn_locDrv hγ hS' hS'0 (hγ.strictMonoOn_capClock hq hS' hlt)
  have himg := gamNodeData_img_eq hv hpA.1 hZ
  have hpre := gamNodeData_pre_eq hv hpA.1 hZ
  have hEqD : EqOn (kPath ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).img (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p)) ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb
      (scheduleAt n) r).pre (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p)))
      (WangWu.locDrv (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n))
      (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ
      (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p) S')
      (Icc 0 (capClock ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).img (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p)) (qLast (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t)))) := by
    rw [himg, hpre, ← lastO_eq hv]; exact hEqg
  have hpos : ∀ k (t' : Fin (k + 1) → ℝ≥0), (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).valid (k + 1) t' →
      0 < qLast (k + 1) t' := fun _ _ hv' => qLast_pos_of_nodeValid hv'
  -- signs of the root marks
  obtain ⟨-, -, hjL, hjR, -⟩ := hEg p hpA.1
  have hF := Theorem15.isOrderedForceWord_flowLine (sourceWord (x₀ := x₀) hκ hb).fn
    (sourceWord (x₀ := x₀) hκ hb).jumps 0
  have hx0L : ∀ i, (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).xL0 (gZ x₀ (κ := κ) h p) i ≤ 0 :=
    fun i => StagedS7.imgMarkL_nonpos hF.2.1 hjL i
  have hx0R : ∀ i, 0 ≤ (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).xR0 (gZ x₀ (κ := κ) h p) i :=
    fun i => StagedS7.imgMarkR_nonneg hF.2.2.2 hjR i
  have hm := TreeData.marks_eq_cfStage hDr hDt hpos (gZ x₀ (κ := κ) h p) hx0L hx0R _ _ hal _ hw hEqD
  -- the capacities
  have hmem : ∀ m : Fin (nodeLen (scheduleAt n) + j), candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) (m + 1) ∈ gPre r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h
      (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t))
      (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) r) p := fun m =>
    hγ.icc _ hq ⟨(candTsF_bounds hv m).1, (candTsF_bounds hv m).2⟩
  have hGS := coe_s3Start_of_alive hEg hpA
  have hAg : ∀ m : Fin (nodeLen (scheduleAt n) + j),
      0 ≤ (fun m => capClock (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n))
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ
        (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) m))
        (m + 1) ∧
      (fun m => capClock (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n))
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ
        (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) m))
        (m + 1) ≤ ((s3Start r (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm
          (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r)
          (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) p : ℝ≥0) : ℝ) :=
    fun m => by
      refine ⟨hγ.capClock_nonneg (hmem m), ?_⟩
      rw [hGS]
      exact hγ.strictMonoOn_capClock.monotoneOn (hmem m) hq (candTsF_bounds hv m).2
  have hTD : capClock ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).img (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p)) (qLast (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)) =
      capClock (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n))
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ
        (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p)
        (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) := by
    rw [himg, ← lastO_eq hv]
  have hAg2 : ∀ m : Fin (nodeLen (scheduleAt n) + j),
      0 ≤ (fun m => capClock (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n))
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ
        (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) m))
        (m + 1) ∧
      (fun m => capClock (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n))
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ
        (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) m))
        (m + 1) ≤ capClock (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n))
          (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ
          (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p)
          (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) :=
    fun m => ⟨(hAg m).1, (hAg m).2.trans_eq hGS⟩
  have hAD : ∀ m : Fin (nodeLen (scheduleAt n) + j),
      (fun m => capClock ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).img (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p)) (tau (Fin.append (nodePre (scheduleAt n)) t) m))
        (m + 1) =
      (fun m => capClock (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n))
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ
        (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r) p)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) m))
        (m + 1) := fun m => by
    simp only
    rw [tau_succ, ← oTime_eq (hv.2 m).2.2, ← candTsF_succ hv m, himg]
  rw [hm]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · dsimp only
    rw [cfStageL_congr_A (A := (fun m => capClock ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).img
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p))
        (tau (Fin.append (nodePre (scheduleAt n)) t) m)))
      (A' := (fun m => capClock (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h
        (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t))
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) r) p)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) m)))
      _ _ _ hAD, hTD]
    simp only [flVL, s6VL_zero hEg (candTsF_bounds hv) p i]
    have hpA' : p ∈ s3Alive r (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r)
        (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) := hpA
    simp only [s3XL, hpA', ↓reduceIte]
    rw [hGS, imgStageVL_congr hw hEqg _ _ _ hAg2 (hγ.capClock_nonneg hq), imgStageVL_eq_cfStageL]
    rfl
  · dsimp only
    rw [cfStageR_congr_A (A := (fun m => capClock ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).img
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h p))
        (tau (Fin.append (nodePre (scheduleAt n)) t) m)))
      (A' := (fun m => capClock (gCurve r (fun _ => ⊤) (candWF x₀ h44 hκ hκ4 hb h
        (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t))
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) r) p)
        (candTsF (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) m)))
      _ _ _ hAD, hTD]
    simp only [flVR, s6VR_zero hEg (candTsF_bounds hv) p i]
    have hpA' : p ∈ s3Alive r (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)) (candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) r)
        (lastO (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) : ℝ) := hpA
    simp only [s3XR, hpA', ↓reduceIte]
    rw [hGS, imgStageVR_congr hw hEqg _ _ _ hAg2 (hγ.capClock_nonneg hq), imgStageVR_eq_cfStageR]
    rfl

end Marks

/-- **The node marks identities** (PROVED from Part A's clearance form). -/
theorem nodeGlueMarksStatement_of_partA (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) : NodeGlueMarksStatement h44 := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ hG hcf n q _ j t hv
  exact nodeGlueMarks_of_good hv (ae_gamNodeGood_glue x₀ h44 hκ hκ4 hb P h W ζ hA hG hcf _)

/-- **PROVE-STAGED-NODECOMP's `NodeTransferStatement h44`** (PROVED from Part A's clearance form). -/
theorem nodeTransferStatement_of_partA (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) : NodeTransferStatement h44 :=
  nodeTransferStatement_of_marks h44 hA (nodeGlueMarksStatement_of_partA h44 hA)

/-- **The comparison clause of every node law** for `nodeObjects` (PROVED from Part A's clearance form). -/
theorem nodeCompOn_of_partA (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance) :
    NodeCompOn h44 (nodeObjects h44) :=
  StagedNPath.nodeCompOn_of_transfer h44 (nodeTransferStatement_of_partA h44 hA)

/-- **Theorem 1.2's leaf `hNodeLaw` for `nodeObjects`** (PROVED from Part A's clearance form). -/
theorem nodeLawOn_nodeObjects_of_partA (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) : Wire.Night.NodeLawOn h44 (nodeObjects h44) :=
  StagedNPath.nodeLawOn_nodeObjects_of_transfer h44 hA (nodeTransferStatement_of_partA h44 hA)

end InteractingSLE.Sec5.CrossCond.StagedNTr
