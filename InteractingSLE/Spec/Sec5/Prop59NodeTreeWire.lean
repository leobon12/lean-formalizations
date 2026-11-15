/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodeTreeExp
import InteractingSLE.Spec.Sec5.Prop59NodesFarRoot

/-!
# Proposition 5.13 from the root and node experiments with the killed law

Packet PROVE-PROP59-NODETREE. Specification §5.2, proof of Proposition 5.13 (p. 151: "The extreme-angle version of
Proposition 5.9 gives `L_z = η'([0, T_z])`"). For every node `n` (the extreme-angle schedule `scheduleAt n`) and every
positive rational counterflow time `q`, the node experiment is PROVE-PROP59-NODES' `CandExpF` built from:

* the node tree (`nodeD`): the node's schedule, then the alternating angles (`+π/2` first), in the joint chart of the
  revealed counterflow, with the root marks of the counterflow chart (`Prop59NodeTreeData`);
* its subtree after the node prefix (PROVE-PROP59-NODES' `subFam`), dilated by the factor `nodeScale` chosen from the
  far marks at the node tip (`nodeLam`, p. 143: `z₋ ≤ −3`, `z₊ ≥ 3`), lifted to the product extension (`nodeCand`);
* the initial start `nodeStart` (the dilated marks at the node tip), the initial event `nodeR0` (the node prefix is
  pre-contact and the far gaps are positive), the revealed past `nodeBase` (any given past, enlarged by `nodeR0`);
* the node word `nodeρL`/`nodeρR` (`Prop59NodeTreeWord`), the image set `nodeImage` (dilated joint-chart images of the
  node prefix and descendant points), the start capacities `nodeStartF`.

Every field is proved except the killed staged law of the realized construction (ruling R75's named input):

* **`nodeCandExpF`**; **`tipUnboundedStatement_of_nodeTree`** (Proposition 5.13's `htip` at node `n`);
* **`prop513_path_of_partA_reverseVisit_nodeTree`**: Proposition 5.13 from the killed staged laws of the root
  experiment (PROVE-PROP59-NODES' `rootCandExpF'`) and of the node experiments alone.

Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Prop59NodeTree

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec4 Theorem14.StagedReg GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage Prop59Pieces
open Prop59Nodes
open Prop513Wire (StripReverseVisitLaw)

section Defs

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
  (E : Schedule → ℕ → Ω → Driver) (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ)

/-- The number of left marks of the node experiment of `n`. -/
abbrev nodeNL (n : ℕ) : ℕ := rootNL (sourceWord (x₀ := x₀) hκ hb) + nodeLen (scheduleAt n)

/-- The number of right marks of the node experiment of `n`. -/
abbrev nodeNR (n : ℕ) : ℕ := rootNR (sourceWord (x₀ := x₀) hκ hb) + nodeLen (scheduleAt n)

theorem nodeNL_pos (n : ℕ) : 0 < nodeNL x₀ hκ hb n := Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ _)

theorem nodeNR_pos (n : ℕ) : 0 < nodeNR x₀ hκ hb n := Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ _)

/-- **The node tree of the node `n`** at the counterflow time `q`, with the root marks of the counterflow chart. -/
def nodeD (n : ℕ) (q : ℚ) :
    TreeData Ω (rootNL (sourceWord (x₀ := x₀) hκ hb)) (rootNR (sourceWord (x₀ := x₀) hκ hb)) :=
  nodeData x₀ h44 hκ hκ4 hb P h W ζ (scheduleAt n) (q : ℝ).toNNReal
    (fun ω => rootXL hκ hb x₀ (q : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω))
    (fun ω => rootXR hκ hb x₀ (q : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω)) (noise n q)

/-- The (undilated) marks at the node tip. -/
def nodeMarks (n : ℕ) (q : ℚ) (ω : Ω) : (Fin (nodeNL x₀ hκ hb n) → ℝ) × (Fin (nodeNR x₀ hκ hb n) → ℝ) :=
  (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).marks (nodeLen (scheduleAt n)) (nodePre (scheduleAt n)) ω

/-- **The dilation of the node experiment** from the far marks at the node tip. -/
def nodeScale (n : ℕ) (q : ℚ) (ω : Ω) : ℝ≥0 :=
  (nodeLam ((nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω).1 (farL (nodeNL_pos x₀ hκ hb n)))
    ((nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω).2 (farR (nodeNR_pos x₀ hκ hb n)))).toNNReal

/-- **The candidate pieces of the node experiment**: the dilated subtree after the node prefix, on `Ω × Ωa`. -/
def nodeCand (n : ℕ) (q : ℚ) : CandFam (Ω × Ωa) (nodeNL x₀ hκ hb n) (nodeNR x₀ hκ hb n) :=
  liftFam (scaleFam (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q)
    (subFam (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).cand (nodeLen (scheduleAt n)) (nodePre (scheduleAt n))))

/-- **The initial start of the node experiment**: the driver at `0` and the dilated marks at the node tip. -/
def nodeStart (n : ℕ) (q : ℚ) (ω' : Ω × Ωa) : Start (nodeNL x₀ hκ hb n + 0) (nodeNR x₀ hκ hb n + 0) :=
  (0, fun i => (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1 : ℝ) *
      (nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1).1 i,
    fun k => (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1 : ℝ) *
      (nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω'.1).2 k)

/-- The samples where the node prefix is pre-contact and both far gaps at the node tip are positive. -/
def nodeR0Ω (n : ℕ) (q : ℚ) : Set Ω :=
  {ω | ω ∈ (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).alive (nodeLen (scheduleAt n)) (nodePre (scheduleAt n)) ∧
    (nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω).1 (farL (nodeNL_pos x₀ hκ hb n)) < 0 ∧
    0 < (nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω).2 (farR (nodeNR_pos x₀ hκ hb n))}

/-- **The initial event of the node experiment** (on the product extension). -/
def nodeR0 (n : ℕ) (q : ℚ) : Set (Ω × Ωa) := Prod.fst ⁻¹' nodeR0Ω x₀ h44 hκ hκ4 hb P h W ζ noise n q

/-- **The revealed past of the node experiment**: a given past, enlarged by the initial event. -/
@[instance_reducible]
def nodeBase (base : ℕ → ℚ → MeasurableSpace (Ω × Ωa)) (n : ℕ) (q : ℚ) : MeasurableSpace (Ω × Ωa) :=
  base n q ⊔ MeasurableSpace.generateFrom {nodeR0 (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q}

end Defs

/-! ### The node experiment -/

section Exp

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ)
  (E : Schedule → ℕ → Ω → Driver) (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ)
  (base : ℕ → ℚ → MeasurableSpace (Ω × Ωa))

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem isReg_nodeD (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) :
    (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).IsReg :=
  isReg_nodeData x₀ h44 hκ hκ4 hb hhm hcf
    ((measurable_rootXL (x₀ := x₀) hκ hb ((q : ℝ).toNNReal)).comp (measurable_cfHistory_of_strip hcf))
    ((measurable_rootXR (x₀ := x₀) hκ hb ((q : ℝ).toNNReal)).comp (measurable_cfHistory_of_strip hcf))

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem isTree_nodeD (n : ℕ) (q : ℚ) : (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).IsTree :=
  isTree_nodeData x₀ h44 hκ hκ4 hb

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurable_nodeMarks (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) :
    (Measurable fun ω => (nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω).1) ∧
      Measurable fun ω => (nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω).2 :=
  (isReg_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q).measurable_marks _ _

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem nodeScale_coe (n : ℕ) (q : ℚ) (ω : Ω) :
    (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω : ℝ) =
      nodeLam ((nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω).1 (farL (nodeNL_pos x₀ hκ hb n)))
        ((nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise n q ω).2 (farR (nodeNR_pos x₀ hκ hb n))) :=
  Real.coe_toNNReal _ (nodeLam_pos _ _).le

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem nodeScale_pos (n : ℕ) (q : ℚ) (ω : Ω) : 0 < nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q ω :=
  Real.toNNReal_pos.2 (nodeLam_pos _ _)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurable_nodeScale (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) :
    Measurable (nodeScale x₀ h44 hκ hκ4 hb P h W ζ noise n q) := by
  obtain ⟨hL, hR⟩ := measurable_nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q
  exact measurable_real_toNNReal.comp (measurable_nodeLam ((measurable_pi_apply _).comp hL)
    ((measurable_pi_apply _).comp hR))

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurableSet_nodeR0Ω (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) :
    MeasurableSet (nodeR0Ω x₀ h44 hκ hκ4 hb P h W ζ noise n q) := by
  obtain ⟨hL, hR⟩ := measurable_nodeMarks x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q
  have hD := isReg_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q
  exact (hD.measurableSet_alive _ _).inter ((measurableSet_lt ((measurable_pi_apply _).comp hL) measurable_const).inter
    (measurableSet_lt measurable_const ((measurable_pi_apply _).comp hR)))

/-- The subtree positions at positive rational times are node points (for alive subtree candidates). -/
theorem ae_mem_nodeZ (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) (n : ℕ) (q : ℚ) :
    ∀ᵐ ω ∂P, ∀ j t, ω ∈ (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).alive (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) → ∀ q' : ℚ, 0 < (q' : ℝ) →
      (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q).α (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) ω q' ∈
          nodeZ (nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q) (nodePre (scheduleAt n)) (descPts E n) ω := by
  classical
  have hhm : Measurable h := hG.1
  have hD := isReg_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise hhm hcf n q
  have hT := isTree_nodeD x₀ h44 hκ hκ4 hb P h W ζ noise n q
  filter_upwards [ae_qPathF_mem_descPts x₀ h44 hκ hκ4 hb hG hE hR n] with ω hω j t hA q' hq'
  have hA0 := TreeData.IsTree.alive_append hD hT (nodePre (scheduleAt n)) j t hA
  have hv : NodeValid (scheduleAt n) (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) :=
    hA.1.1
  by_cases hle : (q' : ℝ) ≤ qLast (nodeLen (scheduleAt n)) (nodePre (scheduleAt n))
  · left
    simp only [hA0, ↓reduceIte]
    exact ⟨q', hq', hle, TreeData.IsTree.α_append hT (nodePre (scheduleAt n)) j t hv ω q' hq'.le hle⟩
  · right
    show nodeAlpha x₀ h44 hκ hκ4 hb h (scheduleAt n) (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) ω q' ∈ descPts E n ω
    rw [nodeAlpha_append]
    refine hω j t hv.1 q' ?_
    have hτ : qLast (nodeLen (scheduleAt n)) (nodePre (scheduleAt n)) = (terminalRat (scheduleAt n) : ℝ) := by
      rw [← lastO_eq isValid_nodePre, lastO_nodePre]
    rw [← hτ]
    exact not_le.1 hle

/-- **The node experiment of the node `n`** (`CandExpF`): every field is proved, except the killed staged law of the
realized construction (`hlaw`, ruling R75's named input). -/
def nodeCandExpF (hA : PartAInputsSixteenDiv)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    (hbase : ∀ n q, base n q ≤ (inferInstance : MeasurableSpace (Ω × Ωa))) (n : ℕ)
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StageLawFarStatement κ (P.prod Pa) (nodeNL_pos x₀ hκ hb n)
      (nodeNR_pos x₀ hκ hb n) (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n))
      (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n))
      (histSys (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
        (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise n q) (nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise base n q))) :
    CandExpF κ P Pa
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
      filter_upwards [ae_alive_of_nodeActive x₀ h44 hκ hκ4 hb hA hG hcf htr hE hR hVisit n q
          (fun ω => rootXL hκ hb x₀ (q : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω))
          (fun ω => rootXR hκ hb x₀ (q : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω)) (noise n q),
        ae_farGaps_nodeData x₀ h44 hκ hκ4 hb (s := scheduleAt n) hA hG hcf hq' (noise n q)] with ω h1 h2 hact
      exact ⟨h1 hact, h2 (h1 hact)⟩
    exact (measurePreserving_fst (μ := P) (ν := Pa)).quasiMeasurePreserving.ae hΩ

/-- **Proposition 5.13's tip assertion at the node `n` from the node experiment** (`htip n` of
`Prop513Wire.prop513_path_of_partA_reverseVisit`): from the killed staged law of the realized node construction
alone. -/
theorem tipUnboundedStatement_of_nodeTree (hA : PartAInputsSixteenDiv)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    (hbase : ∀ n q, base n q ≤ (inferInstance : MeasurableSpace (Ω × Ωa))) (n : ℕ)
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StageLawFarStatement κ (P.prod Pa) (nodeNL_pos x₀ hκ hb n)
      (nodeNR_pos x₀ hκ hb n) (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n))
      (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n))
      (histSys (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
        (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise n q) (nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise base n q))) :
    Prop59Tips.TipUnboundedStatement P W γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n)
      (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n) :=
  tipUnboundedStatement_of_prodExpF hκ hκ4
    (nodeCandExpF x₀ h44 hκ hκ4 hb P Pa h W ζ γ E noise base hA hG hcf htr hE hR hVisit hbase n hlaw).toProdExpF

end Exp

/-! ### Proposition 5.13 -/

/-- **Proposition 5.13 from the killed staged laws of the root experiment and of the node experiments**: the root
experiment is PROVE-PROP59-NODES' `rootCandExpF'`, the node experiments are `nodeCandExpF`; the only inputs beyond
PROVE-PROP513C's setting are the killed staged laws `hlaw₀` (root) and `hlaw` (nodes) of the realized constructions
(ruling R75). -/
theorem prop513_path_of_partA_reverseVisit_nodeTree
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDiv)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    {Ωa : Type} [MeasurableSpace Ωa] [StandardBorelSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (noise₀ : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base₀ : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase₀ : ∀ q, base₀ q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw₀ : ∀ q : ℚ, 0 < q → Prop59StageLawFarStatement κ (P.prod Pa) (rootNL_pos _) (rootNR_pos _)
      (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        noise₀ (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (base₀ q)))
    (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℕ → ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ n q, base n q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : ∀ (n : ℕ) (q : ℚ), 0 < q → Prop59StageLawFarStatement κ (P.prod Pa) (nodeNL_pos x₀ hκ hb n)
      (nodeNR_pos x₀ hκ hb n) (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n))
      (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n))
      (histSys (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
        (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)
        (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise n q) (nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise base n q))) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  prop513_path_of_partA_reverseVisit_candExpF h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit
    (rootCandExpF' x₀ h44 hκ hκ4 hb P Pa h W ζ E hA hG.1 hG hcf hE hR noise₀ base₀ hbase₀ hlaw₀)
    fun n => nodeCandExpF x₀ h44 hκ hκ4 hb P Pa h W ζ γ E noise base hA hG hcf htr hE hR hVisit hbase n (hlaw n)

end InteractingSLE.Sec5.Prop59NodeTree
