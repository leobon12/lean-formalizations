/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedK2Wire
import InteractingSLE.Spec.Sec5.Prop59NodesFarRoot
import InteractingSLE.Spec.Sec5.Prop59NodesSub

/-!
# The root experiment and the node experiments with the killed law in the trace-up-to-the-kill form (ruling R78)

Packet PROVE-STAGED9. PROVE-PROP59-NODES' root experiment from PROVE-PROP59-PIECES' concrete pieces
(`Prop59NodesFarRoot`) and its node experiments as subtrees (`Prop59NodesSub`), with the piece law
`Prop59StageLawFarKStatement`; proofs unchanged (they pass the law through).

* `rootCandExpK`, `rootCandExpK'`, **`tip0UnboundedStatement_of_concretePiecesK'`**: Proposition 5.13's `htip0` from
  the killed staged law of the realized construction in the trace-up-to-the-kill form;
* `SubExpK`, `SubExpK.toCandExpK`, **`prop513_path_of_partA_reverseVisit_subExpK`**.

Conditional helpers with distinct names; they replace no source theorem. R48: the only named input is
`Theorem12ParamCond44Statement` (R74), passed through to PROVE-PROP59-PIECES and PROVE-PROP513C.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedK2

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec4 Theorem14.StagedReg GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage Prop59Pieces
open Prop59Tips Prop59Nodes

section Assembly

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa] [StandardBorelSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

/-- **The root experiment from the concrete candidate pieces with the killed law in the trace-up-to-the-kill form**
(`CandExpK`): as PROVE-PROP59-PIECES' `rootCandExpEx`, with `hlaw` the killed staged law of the realized construction.
-/
def rootCandExpK (lam : ℚ → Ω → ℝ) (xL0 : ℚ → Ω → Fin (rootNL (sourceWord (x₀ := x₀) hκ hb)) → ℝ)
    (xR0 : ℚ → Ω → Fin (rootNR (sourceWord (x₀ := x₀) hκ hb)) → ℝ)
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (hlam : ∀ q, Measurable (lam q)) (hpos : ∀ q ω, 0 < lam q ω) (hxL : ∀ q, Measurable (xL0 q))
    (hxR : ∀ q, Measurable (xR0 q)) (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hinit : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, xL0 q ω (farL (rootNL_pos _)) ≤ -3 ∧ 3 ≤ xR0 q ω (farR (rootNR_pos _)))
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StageLawFarKStatement κ (P.prod Pa) (rootNL_pos _) (rootNR_pos _)
      (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q))) :
    CandExpK κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ where
  nL _ := rootNL (sourceWord (x₀ := x₀) hκ hb)
  nR _ := rootNR (sourceWord (x₀ := x₀) hκ hb)
  posL _ := rootNL_pos _
  posR _ := rootNR_pos _
  rhoL _ := rootρL κ (sourceWord (x₀ := x₀) hκ hb)
  rhoR _ := rootρR κ (sourceWord (x₀ := x₀) hκ hb)
  grid _ := ratTimes
  mesh _ := ratMesh
  times _ := ratGrid
  grid_ok _ n := isSwitchGrid_ratGrid n
  mesh_ok _ := tendsto_ratMesh
  cand q := rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise q
  y₀ q := rootStart x₀ hκ hb xL0 xR0 q
  R₀ _ := univ
  base := base
  image q ω' := (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (lam q) (xL0 q) (xR0 q) (noise q)).imageG
    (nodeSet E) ω'.1
  start q j t ω' := recStart (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (lam q) (xL0 q) (xR0 q)
    (noise q)).cand j t ω'.1
  reg q _ := isRegFam_liftFam (isRegFam_rootData x₀ h44 hκ hκ4 hb hhm hcf (hlam q) (hpos q) (hxL q) (hxR q))
  y₀_meas q _ := measurable_const.prodMk (((hxL q).comp measurable_fst).prodMk ((hxR q).comp measurable_fst))
  base_le q _ := hbase q
  R₀_meas _ _ := MeasurableSet.univ
  init q hq := by
    have h1 := (measurePreserving_fst (μ := P) (ν := Pa)).quasiMeasurePreserving.ae (hinit q hq)
    filter_upwards [h1] with ω' hω' _
    refine ⟨rfl, ?_, ?_⟩
    · simp only [rootStart, zero_add]; exact hω'.1
    · simp only [rootStart, zero_add]; exact hω'.2
  chain q _ := IsChainFamEx.lift (TreeData.isChainFamEx_imageG
    (isChainFamEx_rootData x₀ h44 hκ hκ4 hb hhm hG hcf hE hR (hlam q) (hpos q) (hxL q) (hxR q) _ _))
  pieceLaw := hlaw
  initialWord _ _ := isStageInit_sourceWord hκ hb
  image_bdd q _ ω' hD := isBounded_rootImage x₀ h44 hκ hκ4 hb q ω'.1 hD
  active _ _ := Eventually.of_forall fun _ _ => mem_univ _

/-- **The root experiment with the canonical dilated root marks and the killed law** (`CandExpK`): only the killed
staged law of the realized construction remains an input. -/
def rootCandExpK' (hA : PartAInputsSixteenDiv) (hhm : Measurable h)
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
    (fun q hq => (ae_cfHistory_mem_goodSet49 hA hκ hκ4 hb hG hcf (r := (q : ℝ).toNNReal)
      (Real.toNNReal_pos.2 (by exact_mod_cast hq))).mono fun ω hω =>
        ⟨rootLam_mul_junL_le hκ hb hω, le_rootLam_mul_junR hκ hb hω⟩)
    hlaw

omit [StandardBorelSpace Ωa] in
/-- **Proposition 5.13's root tip assertion from the concrete candidate pieces with the killed law in the
trace-up-to-the-kill form**: `htip0` of `Prop513Wire.prop513_path_of_partA_reverseVisit` follows from the killed staged
law of the realized construction alone (valid for every `κ ∈ (0, 4)`; PROVE-PROP59-PIECES'
`tip0UnboundedStatement_of_concretePieces'` needs the unkilled piece law, which fails for `κ ∈ (2, 4)`). -/
theorem tip0UnboundedStatement_of_concretePiecesK' (hA : PartAInputsSixteenDiv) (hhm : Measurable h)
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
    Prop59Tips.Tip0UnboundedStatement P W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime) :=
  tip0UnboundedStatement_of_prodExpK hκ hκ4
    (rootCandExpK' x₀ h44 hκ hκ4 hb P Pa h W ζ E hA hhm hG hcf hE hR noise base hbase hlaw).toProdExpK

end Assembly

/-! ### Node experiments from subtrees -/

section Exp

variable {κ : ℝ} {Ω Ωa : Type} [MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω} [IsProbabilityMeasure P]
  {Pa : Measure Ωa} [IsProbabilityMeasure Pa]

/-- **A node experiment as a subtree** (at every positive rational counterflow time, on `Ω × Ωa`): a tree of candidate
pieces `cand r` with regularity and gap-free chain data in the image set `image r`, read after the deterministic prefix
`pre` of `m` switches (the node's own schedule); the node's initial start, event and revealed history; the killed
staged law of the realized node construction; the node's initial word; bounded images for bounded targets; and the
initial event. -/
structure SubExpK (κ : ℝ) (P : Measure Ω) (Pa : Measure Ωa) (D : ℚ → Ω → Set ℂ) (A : ℚ → Set Ω) where
  nL : ℚ → ℕ
  nR : ℚ → ℕ
  /-- The length of the node prefix. -/
  m : ℕ
  /-- The switching clock values of the node prefix. -/
  pre : Fin m → ℝ≥0
  posL : ∀ r, 0 < nL r + m
  posR : ∀ r, 0 < nR r + m
  rhoL : (r : ℚ) → Fin (nL r + m) → ℝ
  rhoR : (r : ℚ) → Fin (nR r + m) → ℝ
  grid : ℚ → Set ℝ≥0
  mesh : ℚ → ℕ → ℝ≥0
  times : ℚ → ℕ → ℕ → ℝ≥0
  grid_ok : ∀ r n, IsSwitchGrid (grid r) (mesh r n) (times r n)
  mesh_ok : ∀ r, Tendsto (mesh r) atTop (𝓝 0)
  /-- The tree of candidate pieces (in the dilated joint chart of the root). -/
  cand : (r : ℚ) → CandFam (Ω × Ωa) (nL r) (nR r)
  /-- The node's initial start. -/
  y₀ : (r : ℚ) → Ω × Ωa → Start (nL r + m + 0) (nR r + m + 0)
  R₀ : ℚ → Set (Ω × Ωa)
  base : ℚ → MeasurableSpace (Ω × Ωa)
  /-- The image set (node prefix and descendants) in the chart of the tree. -/
  image : ℚ → Ω × Ωa → Set ℂ
  start : (r : ℚ) → (j : ℕ) → (Fin j → ℝ≥0) → Ω × Ωa → ℝ
  reg : ∀ r : ℚ, 0 < r → IsRegFam (cand r)
  chain : ∀ r : ℚ, 0 < r → IsChainAll (P.prod Pa) (cand r) (image r) (start r)
  start_pre : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), 0 ≤ start r m pre ω'
  y₀_meas : ∀ r : ℚ, 0 < r → Measurable (y₀ r)
  base_le : ∀ r : ℚ, 0 < r → base r ≤ (inferInstance : MeasurableSpace (Ω × Ωa))
  R₀_meas : ∀ r : ℚ, 0 < r → MeasurableSet[base r] (R₀ r)
  init : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω' ∈ R₀ r → (y₀ r ω').1 = 0 ∧
    (y₀ r ω').1 + (y₀ r ω').2.1 (farL (by have := posL r; omega : 0 < nL r + m + 0)) ≤ -3 ∧
    3 ≤ (y₀ r ω').1 + (y₀ r ω').2.2 (farR (by have := posR r; omega : 0 < nR r + m + 0))
  /-- **The killed staged law of the realized node construction.** -/
  pieceLaw : ∀ r : ℚ, 0 < r → Prop59StageLawFarKStatement κ (P.prod Pa) (posL r) (posR r) (rhoL r) (rhoR r)
    (histSys (subFam (cand r) m pre) (times r) (posL r) (posR r) (y₀ r) (R₀ r) (base r))
  initialWord : ∀ r : ℚ, 0 < r → IsStageInit κ (rhoL r) (rhoR r)
  image_bdd : ∀ r : ℚ, 0 < r → ∀ ω' : Ω × Ωa, Bornology.IsBounded (D r ω'.1) → Bornology.IsBounded (image r ω')
  active : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A r → ω' ∈ R₀ r

/-- **A subtree experiment is a candidate experiment** (`IsChainAll.subFam`, `IsRegFam.subFam`). -/
def SubExpK.toCandExpK {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω} (X : SubExpK κ P Pa D A) : CandExpK κ P Pa D A where
  nL r := X.nL r + X.m
  nR r := X.nR r + X.m
  posL := X.posL
  posR := X.posR
  rhoL := X.rhoL
  rhoR := X.rhoR
  grid := X.grid
  mesh := X.mesh
  times := X.times
  grid_ok := X.grid_ok
  mesh_ok := X.mesh_ok
  cand r := subFam (X.cand r) X.m X.pre
  y₀ := X.y₀
  R₀ := X.R₀
  base := X.base
  image := X.image
  start r j t ω' := X.start r (X.m + j) (Fin.append X.pre t) ω' - X.start r X.m X.pre ω'
  reg r hr := IsRegFam.subFam (X.reg r hr) X.m X.pre
  y₀_meas := X.y₀_meas
  base_le := X.base_le
  R₀_meas := X.R₀_meas
  init := X.init
  chain r hr := (X.chain r hr).subFam X.m X.pre (X.start_pre r hr) (X.posL r) (X.posR r)
  pieceLaw := X.pieceLaw
  initialWord := X.initialWord
  image_bdd := X.image_bdd
  active := X.active

end Exp

/-! ### Proposition 5.13 from the root experiment and the node subtrees -/

open Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Prop513Wire Restart
open LQGMetric Exist Exist.Staged Exist.StagedLaw

/-- **Proposition 5.13 from the killed-law root experiment and the node subtree experiments.** -/
theorem prop513_path_of_partA_reverseVisit_subExpK
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
    (X₀ : CandExpK κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (X : ∀ n, SubExpK κ P Pa
      (nodeTarget W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n))) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  prop513_path_of_partA_reverseVisit_candExpK h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit X₀
    fun n => (X n).toCandExpK

end InteractingSLE.Sec5.CrossCond.StagedK2
