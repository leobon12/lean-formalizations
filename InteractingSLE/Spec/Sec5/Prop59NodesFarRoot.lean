/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodesFarWire

/-!
# Proposition 5.9's root experiment with the killed stage law

Packet PROVE-PROP59-NODES. PROVE-PROP59-PIECES' root experiment (`rootCandExpEx`, `rootCandExpEx'`) with the piece law
replaced by the killed staged law `Prop59StageLawFarStatement` of the realized construction: the concrete pieces are
killed at their first contact with the revealed counterflow, which is exactly the lifetime the killed law describes,
for every `κ ∈ (0, 4)` (`Prop59NodesFar`).

* `rootCandExpF` (any root marks with the initial dilation), `rootCandExpF'` (the canonical dilated root marks);
* **`tip0UnboundedStatement_of_concretePiecesF'`**: Proposition 5.13's `htip0` from the killed staged law alone.

Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Prop59Nodes

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec4 Theorem14.StagedReg GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage Prop59Pieces

section Assembly

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa] [StandardBorelSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

/-- **The root experiment from the concrete candidate pieces with the killed law** (`CandExpF`): as
PROVE-PROP59-PIECES' `rootCandExpEx`, with `hlaw` the killed staged law of the realized construction. -/
def rootCandExpF (lam : ℚ → Ω → ℝ) (xL0 : ℚ → Ω → Fin (rootNL (sourceWord (x₀ := x₀) hκ hb)) → ℝ)
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
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StageLawFarStatement κ (P.prod Pa) (rootNL_pos _) (rootNR_pos _)
      (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q))) :
    CandExpF κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
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

/-- **The root experiment with the canonical dilated root marks and the killed law** (`CandExpF`): only the killed
staged law of the realized construction remains an input. -/
def rootCandExpF' (hA : PartAInputsSixteenDiv) (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StageLawFarStatement κ (P.prod Pa) (rootNL_pos _) (rootNR_pos _)
      (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (base q))) :
    CandExpF κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ :=
  rootCandExpF x₀ h44 hκ hκ4 hb P Pa h W ζ E (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
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
/-- **Proposition 5.13's root tip assertion from the concrete candidate pieces with the killed law**: `htip0` of
`Prop513Wire.prop513_path_of_partA_reverseVisit` follows from the killed staged law of the realized construction
alone (valid for every `κ ∈ (0, 4)`; PROVE-PROP59-PIECES' `tip0UnboundedStatement_of_concretePieces'` needs the
unkilled piece law, which fails for `κ ∈ (2, 4)`). -/
theorem tip0UnboundedStatement_of_concretePiecesF' (hA : PartAInputsSixteenDiv) (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StageLawFarStatement κ (P.prod Pa) (rootNL_pos _) (rootNR_pos _)
      (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (base q))) :
    Prop59Tips.Tip0UnboundedStatement P W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime) :=
  tip0UnboundedStatement_of_prodExpF hκ hκ4
    (rootCandExpF' x₀ h44 hκ hκ4 hb P Pa h W ζ E hA hhm hG hcf hE hR noise base hbase hlaw).toProdExpF

end Assembly

end InteractingSLE.Sec5.Prop59Nodes
