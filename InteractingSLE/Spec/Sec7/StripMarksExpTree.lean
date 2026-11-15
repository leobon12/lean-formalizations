/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripMarksExpGood
import InteractingSLE.Spec.Sec5.Prop59SchedWire
import InteractingSLE.Spec.Sec5.StripRevVisitLaw
import InteractingSLE.Spec.Sec5.FrameQConsumers

/-!
# Proposition 5.13 from the killed laws of the concrete root and node candidates (clearance form of Part A)

Packet PROVE-STRIPMARKS. Theorem 1.2's wiring supplies Proposition 5.13 (`Wire.late_prop513_comap_of_sched`) from two
abstract experiment families (`HistExp` for the root and for every node, with regular candidate families, measurable
starts and events, and fixed-candidate killed laws). The experiments themselves are already constructed concretely in
the project: the root experiment from PROVE-PROP59-PIECES' candidate pieces with the canonical dilated marks
(`CrossCond.StagedK2.rootCandExpK`, PROVE-STAGED9) and the node experiments from the node tree
(`Prop59NodeTree.nodeCandExpF`, PROVE-PROP59-NODETREE, R75 form). Here they are used under the clearance form of Part A
and with R78's killed law (`IsStageLawFarK`):

* `rootCandExpK_of_clearance`: `rootCandExpK'` with the clearance form of Part A;
* `nodeCandExpK_of_clearance`: `nodeCandExpF` with R78's killed law (`Prop59StageLawFarKStatement`) and the clearance
    form of Part A;
* `isRegFam_nodeCand`, `measurable_nodeStart`, `measurableSet_nodeR0`: the regularity of the node candidates (the
  fields of `nodeCandExpF`);
* **`prop513_path_of_candLaws`**: Proposition 5.13 (a version of the counterflow measurable for the field) from the
  killed laws of the fixed concrete root and node candidates (PROVE-STAGEDK-CAND's target), on their canonical pasts,
  reached events and starts; the experiments, their regularity and their starts are constructed.

R48: nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the restricted
determination `h44` is R74's `Theorem12ParamCond44Statement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function Metric
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.StripMarks

open Sec5 Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec5.Prop513Target Exist.StagedLaw Exist.Staged LQGMetric
  Sec7.AdmCode Restart Sec4 Theorem14.StagedReg Sec5.GlueCond Sec5.CrossCond.Word49 WangWu LawUnique
  Sec5.Prop59System Sec5.Prop59Stage Sec5.Prop59Pieces Sec5.Prop59Nodes Sec5.Prop59NodeTree Sec5.Prop59Tips
  Sec5.CrossCond.StagedK2 Sec5.CrossCond.StagedKill Sec5.CrossCond.StagedCand Sec5.Prop59Sched Sec5.StripRevVisit
  Sec5.Prop513Asm
open Sec5.Prop513Wire (StripReverseVisitLaw)

/-! ### The root experiment -/

section Root

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa] [StandardBorelSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

/-- **The root experiment with the canonical dilated root marks** (`CrossCond.StagedK2.rootCandExpK'` with the clearance
form of Part A): only the killed staged law of the realized construction is an input. -/
def rootCandExpK_of_clearance (hA : PartAInputsSixteenDivOfClearance) (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StageLawFarKStatement κ (P.prod Pa) (rootNL_pos _) (rootNR_pos _)
      (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (base q))) :
    CandExpK κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ :=
  rootCandExpK x₀ h44 hκ hκ4 hb P Pa h W ζ E (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
    base hhm hG hcf hE hR
    (fun q => (measurable_rootLam _).comp (measurable_cfHistory_of_strip hcf))
    (fun q ω => rootLam_pos _ _)
    (fun q => measurable_pi_iff.2 fun i => ((measurable_rootLam _).comp (measurable_cfHistory_of_strip hcf)).mul
      ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb _).comp (measurable_cfHistory_of_strip hcf))))
    (fun q => measurable_pi_iff.2 fun j => ((measurable_rootLam _).comp (measurable_cfHistory_of_strip hcf)).mul
      ((measurable_pi_apply j).comp ((measurable_rootXR hκ hb _).comp (measurable_cfHistory_of_strip hcf))))
    hbase
    (fun q hq => (ae_cfHistory_mem_goodSet49_of_clearance hκ hκ4 hb hA hG hcf (r := (q : ℝ).toNNReal)
      (Real.toNNReal_pos.2 (by exact_mod_cast hq))).mono fun ω hω =>
        ⟨rootLam_mul_junL_le hκ hb hω, le_rootLam_mul_junR hκ hb hω⟩)
    hlaw

end Root

/-! ### The node experiments -/

section Node

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ)
  (E : Schedule → ℕ → Ω → Driver) (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ)
  (base : ℕ → ℚ → MeasurableSpace (Ω × Ωa))

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] [IsProbabilityMeasure Pa] in
/-- The node candidates form a regular family (the field `reg` of `nodeCandExpF`). -/
theorem isRegFam_nodeCand (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) :
    IsRegFam (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) :=
  isRegFam_liftFam (IsRegFam.scaleFam (measurable_nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q)
    (nodeScale_pos x₀ h44 hκ hκ4 hb P h W ζ noise n q)
    (Prop59Nodes.IsRegFam.subFam (isReg_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q).isRegFam _ _))

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] [IsProbabilityMeasure Pa] in
/-- The node start is measurable (the field `y₀_meas` of `nodeCandExpF`). -/
theorem measurable_nodeStart (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) :
    Measurable (nodeStart (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) := by
  obtain ⟨hL, hR⟩ := measurable_nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q
  have hc := measurable_coe_nnreal_real.comp (measurable_nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q)
  refine measurable_const.prodMk (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.2 fun i => (hc.mul ((measurable_pi_apply i).comp hL)).comp measurable_fst
  · exact measurable_pi_iff.2 fun k => (hc.mul ((measurable_pi_apply k).comp hR)).comp measurable_fst

omit [StandardBorelSpace Ω] [MeasurableSpace Ωa] [IsProbabilityMeasure P] [IsProbabilityMeasure Pa] in
/-- The node event is measurable in the node's revealed past (the field `R₀_meas` of `nodeCandExpF`). -/
theorem measurableSet_nodeR0 (n : ℕ) (q : ℚ) :
    MeasurableSet[nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise base n q]
      (nodeR0 (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) :=
  (le_sup_right : MeasurableSpace.generateFrom _ ≤ nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise base n q) _
    (MeasurableSpace.measurableSet_generateFrom (mem_singleton _))

/-- **The node experiment of the node `n` with R78's killed law** (`Prop59NodeTree.nodeCandExpF` with
`Prop59StageLawFarKStatement` and the clearance form of Part A). -/
def nodeCandExpK_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    (hbase : ∀ n q, base n q ≤ (inferInstance : MeasurableSpace (Ω × Ωa))) (n : ℕ)
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StageLawFarKStatement κ (P.prod Pa) (nodeNL_pos x₀ hκ hb n)
      (nodeNR_pos x₀ hκ hb n) (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n))
      (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n))
      (histSys (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
        (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise n q) (nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise base n q))) :
    CandExpK κ P Pa
      (nodeTarget W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n)) where
  nL _ := nodeNL x₀ hκ hb n
  nR _ := nodeNR x₀ hκ hb n
  posL _ := nodeNL_pos x₀ hκ hb n
  posR _ := nodeNR_pos x₀ hκ hb n
  rhoL _ := nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)
  rhoR _ := nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)
  grid _ := ratTimes
  mesh _ := ratMesh
  times _ := ratGrid
  grid_ok _ k := isSwitchGrid_ratGrid k
  mesh_ok _ := tendsto_ratMesh
  cand q := nodeCand x₀ h44 hκ hκ4 hb P h W ζ noise n q
  y₀ q := nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q
  R₀ q := nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise n q
  base q := nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise base n q
  image q ω' := (fun z => ((nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1 : ℝ) : ℂ) * z) ''
    ((nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).imageG
      (nodeZ (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q) (nodePre (scheduleAt n)) (descPts E n)) ω'.1)
  start q j t ω' := (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1 : ℝ) ^ 2 *
    (recStart (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).cand (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) ω'.1 -
      recStart (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).cand (nodeLen (scheduleAt n)) (nodePre (scheduleAt n))
        ω'.1)
  reg q _ := isRegFam_liftFam (IsRegFam.scaleFam (measurable_nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise hG.1 hcf n q)
    (nodeScale_pos x₀ h44 hκ hκ4 hb P h W ζ noise n q)
    (Prop59Nodes.IsRegFam.subFam (isReg_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise hG.1 hcf n q).isRegFam _ _))
  y₀_meas q _ := by
    obtain ⟨hL, hR⟩ := measurable_nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise hG.1 hcf n q
    have hc := measurable_coe_nnreal_real.comp (measurable_nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise hG.1 hcf n q)
    refine measurable_const.prodMk (Measurable.prodMk ?_ ?_)
    · exact measurable_pi_iff.2 fun i => (hc.mul ((measurable_pi_apply i).comp hL)).comp measurable_fst
    · exact measurable_pi_iff.2 fun k => (hc.mul ((measurable_pi_apply k).comp hR)).comp measurable_fst
  base_le q _ := sup_le (hbase n q) (MeasurableSpace.generateFrom_le fun t ht => by
    rw [mem_singleton_iff.1 ht]
    exact measurable_fst (measurableSet_nodeR0Ω x₀ h44 hκ hκ4 hb P h W ζ noise hG.1 hcf n q))
  R₀_meas q _ := (le_sup_right : MeasurableSpace.generateFrom _ ≤ nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise base n q) _
    (MeasurableSpace.measurableSet_generateFrom (mem_singleton _))
  init q _ := Eventually.of_forall fun ω' hω' => by
    obtain ⟨-, hL, hR⟩ := hω'
    have hl := nodeLam_mul_le hL hR
    refine ⟨rfl, ?_, ?_⟩
    · show (0 : ℝ) + (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1 : ℝ) *
        (nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1).1 (farL (nodeNL_pos x₀ hκ hb n)) ≤ -3
      rw [zero_add, nodeScale_coe]; exact hl.1
    · show 3 ≤ (0 : ℝ) + (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1 : ℝ) *
        (nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1).2 (farR (nodeNR_pos x₀ hκ hb n))
      rw [zero_add, nodeScale_coe]; exact hl.2
  chain q _ := by
    have hD := isReg_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise hG.1 hcf n q
    have hT := isTree_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q
    exact IsChainFamEx.lift ((IsChainAll.scale (TreeData.isChainAll_subFam hD hT (nodePre (scheduleAt n))
      (ae_mem_nodeZ x₀ h44 hκ hκ4 hb P h W ζ E noise hG hcf hE hR n q))
      (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q) (nodeScale_pos x₀ h44 hκ hκ4 hb P h W ζ noise n q)).isChainFamEx
      (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n))
  pieceLaw := hlaw
  initialWord _ _ := isStageInit_nodeρ hκ hκ4 (isStageInit_sourceWord hκ hb) (scheduleAt n)
  image_bdd q _ ω' hDb := isBounded_image_mul _ (isBounded_nodeImage x₀ h44 hκ hκ4 hb n q ω'.1 hDb)
  active q hq := by
    have hq' : (0 : ℝ≥0) < (q : ℝ).toNNReal := Real.toNNReal_pos.2 (by exact_mod_cast hq)
    have hΩ : ∀ᵐ ω ∂P, ω ∈ nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n) q →
        ω ∈ nodeR0Ω x₀ h44 hκ hκ4 hb P h W ζ noise n q := by
      filter_upwards [ae_alive_of_nodeActive_of_clearance x₀ h44 hκ hκ4 hb hA hG hcf htr hE hR hVisit n q
          (fun ω => rootXL hκ hb x₀ (q : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω))
          (fun ω => rootXR hκ hb x₀ (q : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω)) (noise n q),
        ae_farGaps_nodeData_of_clearance x₀ h44 hκ hκ4 hb (s := scheduleAt n) hA hG hcf hq' (noise n q)]
        with ω h1 h2 hact
      exact ⟨h1 hact, h2 (h1 hact)⟩
    exact (measurePreserving_fst (μ := P) (ν := Pa)).quasiMeasurePreserving.ae hΩ

end Node

/-! ### Proposition 5.13 -/

/-- **Proposition 5.13 from the killed laws of the fixed concrete candidates** (clearance form of Part A): the root
experiment (`rootCandExpK_of_clearance`) and the node experiments (`nodeCandExpK_of_clearance`) are constructed; their
realized killed staged laws come from the killed laws of their fixed candidates on the canonical candidate trees
(`CrossCond.StagedK2.prop59StageLawFarKStatement_rootCand`, `…_histSys_canon`); the target schedules, their staged
histories and regularity and the reverse-visit law are those of `Wire.late_prop513_comap_of_sched`; the tips feed the
clearance assembly `Prop513Wire.prop513_path_of_partA_reverseVisit_of_clearance`. -/
theorem prop513_path_of_candLaws
    (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hFH : StagedPrefixFirstHitStatement.{0})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {Ωa : Type} [MeasurableSpace Ωa] [StandardBorelSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (noise₀ : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base₀ : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase₀ : ∀ q, base₀ q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw₀ : ∀ q : ℚ, 0 < q → ∀ j t, IsStageLawFarK κ (P.prod Pa)
      (canonQ (base₀ q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise₀ (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) j t)
      (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise₀ (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ j t)
      (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) j) (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) j)
      (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ j)))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ j)))
      (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise₀ (Ωa := Ωa) q) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) q) j t)
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise₀
        (Ωa := Ωa) q j t).W
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise₀
        (Ωa := Ωa) q j t).VL
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise₀
        (Ωa := Ωa) q j t).VR
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise₀
        (Ωa := Ωa) q j t).B
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise₀
        (Ωa := Ωa) q j t).ζ)
    (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℕ → ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ n q, base n q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : ∀ (n : ℕ) (q : ℚ), 0 < q → ∀ j t, IsStageLawFarK κ (P.prod Pa)
      (canonQ (nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise base n q) (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise
          n q) ratGrid
        (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t)
      (canonR (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
        (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise
            n q) j t)
      (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
      (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
      (farL (Nat.lt_of_lt_of_le (nodeNL_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
      (farR (Nat.lt_of_lt_of_le (nodeNR_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
      (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)
          j t)
      (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).W (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ
          noise n q j t).VL
      (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).VR (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ
          noise n q j t).B
      (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).ζ) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  have hE := isStagedHistory_targetSched h44 hκ hκ4 hb hG
  have hR := stagedPiecesRegular_targetSched h44 hκ hκ4 hb hG
  have hVisit := stripReverseVisitLaw_of_stagedPrefixFirstHit h44 hA hFH hκ hκ4 hb hG hcf htr hE hR
  have hhm : Measurable h := hG.1
  have hcfm := measurable_cfHistory_of_strip hcf
  refine Prop513Wire.prop513_path_of_partA_reverseVisit_of_clearance h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit
    (fun n => ?_) ?_
  · exact tipUnboundedStatement_of_prodExpK hκ hκ4
      (nodeCandExpK_of_clearance x₀ h44 hκ hκ4 hb P Pa h W ζ γ _ noise base hA hG hcf htr hE hR hVisit hbase n
        fun q hq => prop59StageLawFarKStatement_histSys_canon
          (isRegFam_nodeCand x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q)
          (measurable_nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q)
          (measurableSet_nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise base n q) (hlaw n q hq)).toProdExpK
  · exact tip0UnboundedStatement_of_prodExpK hκ hκ4
      (rootCandExpK_of_clearance x₀ h44 hκ hκ4 hb P Pa h W ζ _ hA hhm hG hcf hE hR noise₀ base₀ hbase₀
        fun q hq => prop59StageLawFarKStatement_rootCand x₀ h44 hκ hκ4 hb hhm hcf
          (fun _ => (measurable_rootLam _).comp hcfm) (fun _ _ => rootLam_pos _ _)
          (fun _ => measurable_pi_iff.2 fun i => ((measurable_rootLam _).comp hcfm).mul
            ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb _).comp hcfm)))
          (fun _ => measurable_pi_iff.2 fun j => ((measurable_rootLam _).comp hcfm).mul
            ((measurable_pi_apply j).comp ((measurable_rootXR hκ hb _).comp hcfm))) q base₀ (hlaw₀ q hq)).toProdExpK

end InteractingSLE.Sec7.StripMarks
