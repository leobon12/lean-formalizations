/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedK2Root
import InteractingSLE.Spec.Sec5.CrossCondStagedCandFar

/-!
# Prop 5.9's candidate tree with the killed law in the trace-up-to-the-kill form (ruling R78)

Packet PROVE-STAGED9. PROVE-STAGED7's reduction of the staged law of the adaptive construction to the per-candidate
laws (`CrossCondStagedCandFar`), for `IsStageLawFarK`: it is a generic comparison-form law (`IsCompLaw`, premise
`farPremK`) by `Iff.rfl`, so STAGED7's tree consistency and mixture (`isCompLaw_histSys`, `isCompLaw_of_mix`) apply
with no new proof.

* `farPremK`, **`isStageLawFarK_iff_isCompLaw`**, `isStageLawFarK_of_mix`;
* **`prop59StageLawFarKStatement_histSys`**, **`prop59StageLawFarKStatement_histSys_canon`** (any regular family),
  **`prop59StageLawFarKStatement_rootCand`** (PROVE-PROP59-PIECES' root experiment);
* **`tip0UnboundedStatement_of_candLawsK`**: Proposition 5.13's `htip0` from the per-candidate laws `IsStageLawFarK`
  of the fixed candidates of the root experiment with the canonical dilated root marks.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; `Theorem12ParamCond44Statement` (R74) enters only
through PROVE-PROP59-PIECES' code drivers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedK2

open Prop59Stage Prop59System StagedAdapt Prop59Pieces Prop59Nodes Prop513TreeExtract Prop513Target Sec7.AdmCode
open Restart Sec4 Exist.StagedLaw Theorem14.StagedReg Prop513Schedule StagedCand StagedKill

/-! ### `IsStageLawFarK` as a comparison-form law -/

section Bridge

variable {Ω : Type*} {nL nR : ℕ}

/-- The premise of `IsStageLawFarK` (every integrated evolution traced up to its first far contact, killed there). -/
def farPremK (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR)
    (S : Set (Start nL nR × Samp nL nR)) (p : ℝ≥0∞) : Prop :=
  CompPremiseFarK κ ρL ρR iL iR univ S p

variable {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **`IsStageLawFarK` is a generic comparison-form law.** -/
theorem isStageLawFarK_iff_isCompLaw {κ : ℝ} {P : Measure Ω} {R : Set Ω} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {iL : Fin nL} {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} :
    @IsStageLawFarK κ Ω mΩ P 𝓠 R nL nR ρL ρR iL iR y W VL VR B ζ ↔
      IsCompLaw P 𝓠 R (farPath κ ρL ρR) stageObsRec (farPremK κ ρL ρR iL iR) (stageRec y W VL VR B ζ) :=
  Iff.rfl

end Bridge

/-! ### A countable mixture -/

section Mix

variable {κ : ℝ} {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {K : Type*}
  [Countable K] {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR}

/-- **The killed stage law (trace-up-to-the-kill form) of a countable mixture** (hypotheses exactly as
PROVE-PROP59-NODES' `isStageLawFar_of_mix`; proof by STAGED7's `isCompLaw_of_mix`). -/
theorem isStageLawFarK_of_mix {R : Set Ω} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (I : Ω → K) (hI : ∀ k, MeasurableSet[mΩ] {ω | I ω = k}) (𝓠k : K → MeasurableSpace Ω) (Rk : K → Set Ω)
    (yk : K → Ω → Start nL nR) (Wk : K → ℝ≥0 → Ω → ℝ) (VLk : K → Fin nL → ℝ≥0 → Ω → ℝ)
    (VRk : K → Fin nR → ℝ≥0 → Ω → ℝ) (Bk : K → ℝ≥0 → Ω → ℝ) (ζk : K → Ω → ℝ≥0∞)
    (hlaw : ∀ k, @IsStageLawFarK κ Ω mΩ P (𝓠k k) (Rk k) nL nR ρL ρR iL iR (yk k) (Wk k) (VLk k) (VRk k) (Bk k)
      (ζk k))
    (hRk : ∀ k, MeasurableSet[𝓠k k] (Rk k))
    (hpt : ∀ k ω, I ω = k → (fun u => W u ω) = (fun u => Wk k u ω) ∧
      (fun i u => VL i u ω) = (fun i u => VLk k i u ω) ∧ (fun i u => VR i u ω) = (fun i u => VRk k i u ω) ∧
      (fun u => B u ω) = (fun u => Bk k u ω) ∧ ζ ω = ζk k ω)
    (hRy : ∀ k, ∀ᵐ ω ∂P, ω ∈ R → I ω = k → ω ∈ Rk k ∧ y ω = yk k ω)
    (htr : ∀ k A, MeasurableSet[𝓠] A → A ⊆ R →
      ∃ A', MeasurableSet[𝓠k k] A' ∧ A ∩ {ω | I ω = k} =ᵐ[P] A') :
    @IsStageLawFarK κ Ω mΩ P 𝓠 R nL nR ρL ρR iL iR y W VL VR B ζ := by
  refine isStageLawFarK_iff_isCompLaw.2 (isCompLaw_of_mix I hI 𝓠k Rk
    (fun k => stageRec (yk k) (Wk k) (VLk k) (VRk k) (Bk k) (ζk k))
    (fun k => isStageLawFarK_iff_isCompLaw.1 (hlaw k)) hRk (fun k => ?_) htr)
  filter_upwards [hRy k] with ω hω hR hIk
  obtain ⟨h1, h2⟩ := hω hR hIk
  obtain ⟨e1, e2, e3, e4, e5⟩ := hpt k ω hIk
  refine ⟨h1, ?_⟩
  simp only [stageRec]
  rw [h2, e1, e2, e3, e4, e5]

end Mix

/-! ### The killed law of the adaptive construction -/

section Law

variable {κ : ℝ} {Ω : Type*} {𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ}
  {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ} {cand : CandFam Ω nL₀ nR₀} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀}
  {hnR : 0 < nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)} {R₀ : Set Ω}
  {𝓠c : (j : ℕ) → (Fin j → ℝ≥0) → MeasurableSpace Ω} {Rc : (j : ℕ) → (Fin j → ℝ≥0) → Set Ω}
  {yc : (j : ℕ) → (Fin j → ℝ≥0) → Ω → Start (nL₀ + j) (nR₀ + j)}

/-- **The killed stage law (trace-up-to-the-kill form) of the adaptive construction from the killed laws of its fixed
candidates** along a consistent candidate tree (R73 (2.2) and the countable mixture; PROVE-STAGED6's argument for the
killed law). -/
theorem prop59StageLawFarKStatement_histSys (hT : IsCandTree P cand G hnL hnR 𝓠c Rc yc)
    (hlaw : ∀ j t, IsStageLawFarK κ P (𝓠c j t) (Rc j t) (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
      (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right nL₀ j)))
      (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right nR₀ j)))
      (yc j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ)
    (h𝓑 : 𝓑 ≤ 𝓠c 0 Fin.elim0) (hR₀ : MeasurableSet[𝓑] R₀)
    (hbase : ∀ᵐ ω ∂P, ω ∈ R₀ → ω ∈ Rc 0 Fin.elim0 ∧ y₀ ω = yc 0 Fin.elim0 ω)
    (hhist : ∀ r j, Measurable (hstate cand G hnL hnR y₀ R₀ 𝓑 r j).hist) :
    Prop59StageLawFarKStatement κ P hnL hnR ρL₀ ρR₀ (histSys cand G hnL hnR y₀ R₀ 𝓑) := fun r j =>
  isCompLaw_histSys (Φ := fun j => farPath κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)) (g := fun _ => stageObsRec)
    (Prem := fun j => farPremK κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
      (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right nL₀ j)))
      (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right nR₀ j))))
    hT hlaw h𝓑 hR₀ hbase hhist r j

/-- **The killed stage law (trace-up-to-the-kill form) of the adaptive construction from the per-candidate killed laws
on the canonical candidate tree**: if every fixed candidate `cand j t` obeys `IsStageLawFar` (stage word, far marks the
last indices) for its canonical past `canonQ`, reached event `canonR` and start `canonY`, then
`Prop59StageLawFarKStatement` holds for `histSys cand G … y₀ R₀ 𝓑`. -/
theorem prop59StageLawFarKStatement_histSys_canon (hfam : IsRegFam cand) (hy₀ : Measurable y₀)
    (hR₀ : MeasurableSet[𝓑] R₀)
    (hlaw : ∀ j t, IsStageLawFarK κ P (canonQ 𝓑 cand G hnL hnR y₀ j t) (canonR cand G hnL hnR y₀ R₀ j t)
      (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
      (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right nL₀ j)))
      (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right nR₀ j)))
      (canonY cand y₀ j t) (cand j t).W (cand j t).VL (cand j t).VR (cand j t).B (cand j t).ζ) :
    Prop59StageLawFarKStatement κ P hnL hnR ρL₀ ρR₀ (histSys cand G hnL hnR y₀ R₀ 𝓑) :=
  prop59StageLawFarKStatement_histSys (isCandTree_canon hfam hy₀ hR₀) hlaw le_rfl hR₀
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
/-- **The killed stage law (trace-up-to-the-kill form) of PROVE-PROP59-PIECES' root experiment from the killed laws of
its fixed candidates** (any measurable positive dilation and measurable root marks; root past `base q`, root event
`univ`). -/
theorem prop59StageLawFarKStatement_rootCand (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (hlam : ∀ q, Measurable (lam q))
    (hpos : ∀ q ω, 0 < lam q ω) (hxL : ∀ q, Measurable (xL0 q)) (hxR : ∀ q, Measurable (xR0 q)) (q : ℚ)
    (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hlaw : ∀ j t, IsStageLawFarK κ (P.prod Pa)
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
    Prop59StageLawFarKStatement κ (P.prod Pa) (rootNL_pos _) (rootNR_pos _)
      (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q)) :=
  prop59StageLawFarKStatement_histSys_canon (isRegFam_rootCand x₀ h44 hκ hκ4 hb hhm hcf hlam hpos hxL hxR q)
    (measurable_rootStart x₀ hκ hb hxL hxR q) MeasurableSet.univ hlaw

end Root

section Tip

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa] [StandardBorelSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

omit [StandardBorelSpace Ωa] in
/-- **Proposition 5.13's root tip assertion from the killed laws (trace-up-to-the-kill form) of the fixed candidates**
of the root experiment with the canonical dilated root marks (`canonLam`, `canonXL`, `canonXR`): `htip0` of
`Prop513Wire.prop513_path_of_partA_reverseVisit` holds as soon as, for every rational counterflow time `q > 0`, every
fixed candidate obeys the killed stage law (trace-up-to-the-kill form) for its canonical past, reached event and start
(root past `base q`). -/
theorem tip0UnboundedStatement_of_candLawsK (hA : PartAInputsSixteenDiv) (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : ∀ q : ℚ, 0 < q → ∀ j t, IsStageLawFarK κ (P.prod Pa)
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
  refine tip0UnboundedStatement_of_concretePiecesK' x₀ h44 hκ hκ4 hb P Pa h W ζ E hA hhm hG hcf hE hR noise base
    hbase fun q hq => prop59StageLawFarKStatement_rootCand x₀ h44 hκ hκ4 hb hhm hcf
      (fun _ => (measurable_rootLam _).comp hcfm) (fun _ _ => rootLam_pos _ _)
      (fun _ => measurable_pi_iff.2 fun i => ((measurable_rootLam _).comp hcfm).mul
        ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb _).comp hcfm)))
      (fun _ => measurable_pi_iff.2 fun j => ((measurable_rootLam _).comp hcfm).mul
        ((measurable_pi_apply j).comp ((measurable_rootXR hκ hb _).comp hcfm))) q base (hlaw q hq)

end Tip

end InteractingSLE.Sec5.CrossCond.StagedK2
