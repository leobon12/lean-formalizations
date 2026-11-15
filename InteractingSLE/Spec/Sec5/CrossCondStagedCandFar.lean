/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedCandRoot
import InteractingSLE.Spec.Sec5.Prop59NodesFarRoot

/-!
# Proposition 5.9: the killed stage law of the adaptive construction from the killed laws of its fixed candidates

Packet PROVE-STAGED7, redirected by ruling R75 to the **killed** stage law `Prop59Nodes.Prop59StageLawFarStatement`
(PROVE-PROP59-NODES: each piece compared with integrated evolutions stopped at their first contact with a far mark;
true for every `κ ∈ (0, 4)`, while the threshold form fails for `κ ∈ (2, 4)`).

* `isStageLawFar_iff_isCompLaw`: `IsStageLawFar` is the generic comparison-form law `IsCompLaw` with the local-solution
  clause `farPath` and the killed premise `CompPremiseFar … univ` (definitional);
* **`prop59StageLawFarStatement_histSys`**: the killed law of `histSys` from a consistent candidate tree (`IsCandTree`)
  and the killed laws of the fixed candidates (PROVE-STAGED6's induction and mixture, via `isCompLaw_histSys`);
* **`prop59StageLawFarStatement_histSys_canon`**: the same on the canonical candidate tree (`canonQ`, `canonR`,
  `canonY`), whose consistency is proved (`isCandTree_canon`): only the per-candidate killed laws remain;
* **`prop59StageLawFarStatement_rootCand`**: for PROVE-PROP59-PIECES' root experiment (any measurable marks);
* **`tip0UnboundedStatement_of_candLawsF`**: Proposition 5.13's root tip assertion `htip0` from the killed laws of the
  fixed candidates of the root experiment with the canonical dilated root marks (through PROVE-PROP59-NODES'
  `tip0UnboundedStatement_of_concretePiecesF'`).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; `Theorem12ParamCond44Statement` (R74) enters only
through PROVE-PROP59-PIECES' code drivers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedCand

open Prop59Stage Prop59System StagedAdapt Prop59Pieces Prop59Nodes Prop513TreeExtract Prop513Target Sec7.AdmCode
open Restart Sec4 Exist.StagedLaw Theorem14.StagedReg Prop513Schedule

/-! ### The killed law as a comparison-form law -/

section Bridge

variable {Ω : Type*} {nL nR : ℕ}

/-- The pathwise clause of the killed law: an ordered start with distinct marks and a local solution of
Definition 2.1's equations before the lifetime. -/
def farPath (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (x : StageRec nL nR) : Prop :=
  IsOrderedForceWord x.1.2.1 x.1.2.2 ∧ StrictAnti x.1.2.1 ∧ StrictMono x.1.2.2 ∧
    Sec2.IsSLEPathUpTo κ x.1.2.1 x.1.2.2 ρL ρR x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2

/-- The premise of the killed law (every integrated evolution, killed at its first far contact). -/
def farPrem (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR)
    (S : Set (Start nL nR × Samp nL nR)) (p : ℝ≥0∞) : Prop :=
  CompPremiseFar κ ρL ρR iL iR univ S p

variable {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **`IsStageLawFar` is a generic comparison-form law.** -/
theorem isStageLawFar_iff_isCompLaw {κ : ℝ} {P : Measure Ω} {R : Set Ω} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {iL : Fin nL} {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} :
    @IsStageLawFar κ Ω mΩ P 𝓠 R nL nR ρL ρR iL iR y W VL VR B ζ ↔
      IsCompLaw P 𝓠 R (farPath κ ρL ρR) stageObsRec (farPrem κ ρL ρR iL iR) (stageRec y W VL VR B ζ) :=
  Iff.rfl

end Bridge

/-! ### The killed law of the adaptive construction -/

section Law

variable {κ : ℝ} {Ω : Type*} {𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ}
  {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ} {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀}
  {hnR : 0 < nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}
  {𝓠c : (j : ℕ) → (Fin j → ℝ≥0) → MeasurableSpace Ω} {Rc : (j : ℕ) → (Fin j → ℝ≥0) → Set Ω}
  {yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j)}

/-- **The killed stage law of the adaptive construction from the killed laws of its fixed candidates** along a
consistent candidate tree (R73 (2.2) and the countable mixture; PROVE-STAGED6's argument for the killed law). -/
theorem prop59StageLawFarStatement_histSys (hT : IsCandTree P cand G hnL hnR 𝓠c Rc yc)
    (hlaw : ∀ j t, IsStageLawFar κ P (𝓠c j t) (Rc j t) (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
      (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right nL₀ j)))
      (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right nR₀ j)))
      (yc j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ)
    (h𝓑 : 𝓑 ≤ 𝓠c 0 Fin.elim0) (hR₀ : MeasurableSet[𝓑] R₀)
    (hbase : ∀ᵐ ω ∂P, ω ∈ R₀ → ω ∈ Rc 0 Fin.elim0 ∧ y₀ ω = yc 0 Fin.elim0 ω)
    (hhist : ∀ r j, Measurable (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist) :
    Prop59StageLawFarStatement κ P hnL hnR ρL₀ ρR₀ (histSys cand G hnL hnR y₀ R₀ 𝓑) := fun r j =>
  isCompLaw_histSys (Φ := fun j => farPath κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)) (g := fun _ => stageObsRec)
    (Prem := fun j => farPrem κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
      (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right nL₀ j)))
      (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right nR₀ j))))
    hT hlaw h𝓑 hR₀ hbase hhist r j

/-- **The killed stage law of the adaptive construction from the per-candidate killed laws on the canonical candidate
tree**: if every fixed candidate `cand j t` obeys `IsStageLawFar` (stage word, far marks the last indices) for its
canonical past `canonQ`, reached event `canonR` and start `canonY`, then `Prop59StageLawFarStatement` holds for
`histSys cand G … y₀ R₀ 𝓑`. -/
theorem prop59StageLawFarStatement_histSys_canon (hfam : IsRegFam cand) (hy₀ : Measurable y₀)
    (hR₀ : MeasurableSet[𝓑] R₀)
    (hlaw : ∀ j t, IsStageLawFar κ P (canonQ 𝓑 cand G hnL hnR y₀ j t) (canonR cand G hnL hnR y₀ R₀ j t)
      (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
      (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right nL₀ j)))
      (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right nR₀ j)))
      (canonY cand y₀ j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ) :
    Prop59StageLawFarStatement κ P hnL hnR ρL₀ ρR₀ (histSys cand G hnL hnR y₀ R₀ 𝓑) :=
  prop59StageLawFarStatement_histSys (isCandTree_canon hfam hy₀ hR₀) hlaw le_rfl hR₀
    (Eventually.of_forall fun _ h => ⟨h, rfl⟩) fun r j => (measurable_hstate hfam hy₀ r j).2

end Law

/-! ### The root experiment -/

section Root

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω} {Pa : Measure Ωa}
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {lam : ℚ → Ω → ℝ} {xL0 : ℚ → Ω → Fin (rootNL (sourceWord (x₀ := x₀) hκ hb)) → ℝ}
  {xR0 : ℚ → Ω → Fin (rootNR (sourceWord (x₀ := x₀) hκ hb)) → ℝ}
  {noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ}

include h44 hκ4 in
/-- **The killed stage law of PROVE-PROP59-PIECES' root experiment from the killed laws of its fixed candidates**
(any measurable positive dilation and measurable root marks; root past `base q`, root event `univ`). -/
theorem prop59StageLawFarStatement_rootCand (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (hlam : ∀ q, Measurable (lam q))
    (hpos : ∀ q ω, 0 < lam q ω) (hxL : ∀ q, Measurable (xL0 q)) (hxR : ∀ q, Measurable (xR0 q)) (q : ℚ)
    (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hlaw : ∀ j t, IsStageLawFar κ (P.prod Pa)
      (canonQ (base q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid
        (rootNL_pos _) (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) j t)
      (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid
        (rootNL_pos _) (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ j t)
      (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) j) (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) j)
      (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ j)))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ j)))
      (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q)
        (rootStart x₀ hκ hb xL0 xR0 q) j t)
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q j t).W
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q j t).VL
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q j t).VR
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q j t).B
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q j t).ζ) :
    Prop59StageLawFarStatement κ (P.prod Pa) (rootNL_pos _) (rootNR_pos _)
      (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q)) :=
  prop59StageLawFarStatement_histSys_canon (isRegFam_rootCand x₀ h44 hκ hκ4 hb hhm hcf hlam hpos hxL hxR q)
    (measurable_rootStart x₀ hκ hb hxL hxR q) MeasurableSet.univ hlaw

end Root

section Tip

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa] [StandardBorelSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

omit [StandardBorelSpace Ωa] in
/-- **Proposition 5.13's root tip assertion from the killed laws of the fixed candidates** of the root experiment
with the canonical dilated root marks (`canonLam`, `canonXL`, `canonXR`): `htip0` of
`Prop513Wire.prop513_path_of_partA_reverseVisit` holds as soon as, for every rational counterflow time `q > 0`, every
fixed candidate obeys the killed stage law for its canonical past, reached event and start (root past `base q`). -/
theorem tip0UnboundedStatement_of_candLawsF (hA : PartAInputsSixteenDiv) (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : ∀ q : ℚ, 0 < q → ∀ j t, IsStageLawFar κ (P.prod Pa)
      (canonQ (base q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) j t)
      (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ j t)
      (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) j) (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) j)
      (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ j)))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ j)))
      (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) q) j t)
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q j t).W
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q j t).VL
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q j t).VR
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q j t).B
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q j t).ζ) :
    Prop59Tips.Tip0UnboundedStatement P W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime) := by
  have hcfm := measurable_cfHistory_of_strip hcf
  refine tip0UnboundedStatement_of_concretePiecesF' x₀ h44 hκ hκ4 hb P Pa h W ζ E hA hhm hG hcf hE hR noise base
    hbase fun q hq => prop59StageLawFarStatement_rootCand x₀ h44 hκ hκ4 hb hhm hcf
      (fun _ => (measurable_rootLam _).comp hcfm) (fun _ _ => rootLam_pos _ _)
      (fun _ => measurable_pi_iff.2 fun i => ((measurable_rootLam _).comp hcfm).mul
        ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb _).comp hcfm)))
      (fun _ => measurable_pi_iff.2 fun j => ((measurable_rootLam _).comp hcfm).mul
        ((measurable_pi_apply j).comp ((measurable_rootXR hκ hb _).comp hcfm))) q base (hlaw q hq)

end Tip

end InteractingSLE.Sec5.CrossCond.StagedCand
