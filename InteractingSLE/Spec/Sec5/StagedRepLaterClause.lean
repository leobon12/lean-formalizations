/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterMain
import InteractingSLE.Spec.Sec5.StagedRepLaterPath
import InteractingSLE.Spec.Sec5.StagedRepLaterStart
import InteractingSLE.Spec.Sec5.CrossCondStagedK2Cand

/-!
# Prop 5.9's root stage: the killed stage law of PIECES' root candidate

Packet PROVE-STAGED-REP2.

* `rootNoise`: the noise of PIECES' candidates chosen as their **recovered noise** (PIECES left it a free parameter);
* `TreeData.cand_zero_W` …: at good samples a stage-0 candidate's processes are those of the killed word of its arc;
* **`clause1_rootCand`**: clause 1 of the killed stage law (pathwise) for the stage-0 root candidate, almost surely —
  the killed word solves Definition 2.1's equations with its recovered noise (`IsKilledWord.isSLEPathUpTo_recNoise`),
  the start is an ordered strict non-threshold word (`StagedRepLaterStart`);
* **`isStageLawFarK_rootCand_zero`**: `IsStageLawFarK` of the stage-0 candidate in the exact form of the `hlaw` of
  `StagedK2.tip0UnboundedStatement_of_candLawsK` at `j = 0` (with `base := rootBase W ζ`, `noise := rootNoise`).

Named inputs: PROVE-KILLARC's deterministic `StagedRep.KilledArcSwallowStatement` and R74's `h44`. R48: nothing here
uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open Sec4 GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage Prop59Pieces StagedKCand StagedKill
open StagedRep StagedCand WangWu.ImgWord WangWu.ImgDrv

/-! ### Stage-0 candidates are killed words, pointwise -/

section Point

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

theorem TreeData.cand_zero_eq (D : TreeData Ω nL₀ nR₀) (t : Fin 0 → ℝ≥0) {ω : Ω}
    (hγ : IsKilledArc (D.img 0 t ω) (D.pre 0 t ω)) (hω : ω ∈ D.G) (hv : D.valid 0 t) :
    (fun u => (D.cand 0 t).W u ω) = kW (D.img 0 t ω) (D.pre 0 t ω) ∧
      (fun i u => (D.cand 0 t).VL i u ω) = (fun i => kVL (D.img 0 t ω) (D.pre 0 t ω) (D.xL0 ω) i) ∧
      (fun k u => (D.cand 0 t).VR k u ω) = (fun k => kVR (D.img 0 t ω) (D.pre 0 t ω) (D.xR0 ω) k) ∧
      (D.cand 0 t).ζ ω = (kLife (D.img 0 t ω) (D.pre 0 t ω) : ℝ≥0∞) := by
  classical
  have hA : ω ∈ D.alive 0 t := ⟨⟨hv, hω⟩, by simpa [qLast] using hγ.zero_mem⟩
  have hS : D.startCap 0 t ω = 0 := by
    simp only [TreeData.startCap, hA, ↓reduceIte, qLast, hγ.capClock_zero, Real.toNNReal_zero]
  have hW : ∀ u, arcW (D.img 0 t) (D.pre 0 t) (D.startCap 0 t) (D.alive 0 t) u ω = kW (D.img 0 t ω) (D.pre 0 t ω) u :=
    fun u => by
      unfold arcW
      simp only [hS, zero_add, hA, true_and]
      by_cases hu : (u : WithTop ℝ≥0) < kLife (D.img 0 t ω) (D.pre 0 t ω)
      · simp only [hu, ↓reduceIte, hγ.kW_zero, sub_zero]
      · simp only [hu, ↓reduceIte, kW]
  have hζ : arcζ (D.img 0 t) (D.pre 0 t) (D.startCap 0 t) (D.alive 0 t) ω =
      (kLife (D.img 0 t ω) (D.pre 0 t ω) : ℝ≥0∞) := by
    simp only [arcζ, hA, ↓reduceIte, hS, ENNReal.coe_zero, tsub_zero]
    rfl
  have hrW : Bessel.realPath (fun u ω => -arcW (D.img 0 t) (D.pre 0 t) (D.startCap 0 t) (D.alive 0 t) u ω) ω =
      fun r => -kPath (D.img 0 t ω) (D.pre 0 t ω) r := by
    funext r; simp only [Bessel.realPath, hW, kPath]
  have hrW' : Bessel.realPath (arcW (D.img 0 t) (D.pre 0 t) (D.startCap 0 t) (D.alive 0 t)) ω =
      kPath (D.img 0 t ω) (D.pre 0 t ω) := by
    funext r; simp only [Bessel.realPath, hW, kPath]
  refine ⟨funext hW, funext fun i => funext fun u => ?_, funext fun k => funext fun u => ?_, hζ⟩
  · show arcVL _ _ _ _ _ i u ω = _
    simp only [arcVL, hζ, hrW, kVL, kVLr, kImg]
    by_cases hu : ((u : ℝ≥0) : ℝ≥0∞) < (kLife (D.img 0 t ω) (D.pre 0 t ω) : ℝ≥0∞)
    · have hu' : (u : WithTop ℝ≥0) < kLife (D.img 0 t ω) (D.pre 0 t ω) := hu
      simp only [hu, hu', ↓reduceIte]
    · have hu' : ¬ (u : WithTop ℝ≥0) < kLife (D.img 0 t ω) (D.pre 0 t ω) := hu
      simp only [hu, hu', ↓reduceIte]
  · show arcVR _ _ _ _ _ k u ω = _
    simp only [arcVR, hζ, hrW', kVR, kVRr, kImg]
    by_cases hu : ((u : ℝ≥0) : ℝ≥0∞) < (kLife (D.img 0 t ω) (D.pre 0 t ω) : ℝ≥0∞)
    · have hu' : (u : WithTop ℝ≥0) < kLife (D.img 0 t ω) (D.pre 0 t ω) := hu
      simp only [hu, hu', ↓reduceIte]
    · have hu' : ¬ (u : WithTop ℝ≥0) < kLife (D.img 0 t ω) (D.pre 0 t ω) := hu
      simp only [hu, hu', ↓reduceIte]

end Point

/-! ### The recovered noise of PIECES' candidates and clause 1 at stage 0 -/

section Clause

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)

/-- PIECES' root tree data at the counterflow time `q` with the canonical dilated marks and the noise `0`. -/
abbrev rootData0 (q : ℚ) : TreeData Ω (rootNL (sourceWord (x₀ := x₀) hκ hb)) (rootNR (sourceWord (x₀ := x₀) hκ hb)) :=
  rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
    (canonXR x₀ hκ hb W ζ q) (fun _ _ _ _ => 0)

/-- **The recovered noise of PIECES' candidates** (the candidate's processes do not read the noise parameter). -/
def rootNoise (q : ℚ) (j : ℕ) (t : Fin j → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  recNoise κ (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) j)
    (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) j)
    ((rootData0 x₀ h44 hκ hκ4 hb P h W ζ q).marks j t ω).1 ((rootData0 x₀ h44 hκ hκ4 hb P h W ζ q).marks j t ω).2
    (fun s => ((rootData0 x₀ h44 hκ hκ4 hb P h W ζ q).cand j t).W s ω)
    (fun i s => ((rootData0 x₀ h44 hκ hκ4 hb P h W ζ q).cand j t).VL i s ω)
    (fun k s => ((rootData0 x₀ h44 hκ hκ4 hb P h W ζ q).cand j t).VR k s ω) u

/-- **Clause 1 of the killed stage law of PIECES' root candidate at a good sample.** -/
theorem clause1_rootCand_of_good (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {q : ℚ} (t : Fin 0 → ℝ≥0) {ω : Ω}
    (h1 : ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal)
    (h2 : Cond44Ref.cfHistory W ζ ω ∈ goodSet49 (q : ℝ).toNNReal) :
    IsOrderedForceWord (canonXL x₀ hκ hb W ζ q ω) (canonXR x₀ hκ hb W ζ q ω) ∧
      StrictAnti (canonXL x₀ hκ hb W ζ q ω) ∧ StrictMono (canonXR x₀ hκ hb W ζ q ω) ∧
      Sec2.IsSLEPathUpTo κ (canonXL x₀ hκ hb W ζ q ω) (canonXR x₀ hκ hb W ζ q ω)
        (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
        (fun u => ((rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
          (canonXR x₀ hκ hb W ζ q) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ q)).cand 0 t).W u ω)
        (fun i u => ((rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
          (canonXR x₀ hκ hb W ζ q) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ q)).cand 0 t).VL i u ω)
        (fun k u => ((rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
          (canonXR x₀ hκ hb W ζ q) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ q)).cand 0 t).VR k u ω)
        (fun u => ((rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
          (canonXR x₀ hκ hb W ζ q) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ q)).cand 0 t).B u ω)
        (((rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
          (canonXR x₀ hκ hb W ζ q) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ q)).cand 0 t).ζ ω) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set r : ℝ≥0 := (q : ℝ).toNNReal with hr
  set D := rootData x₀ h44 hκ hκ4 hb P h W ζ r (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
    (canonXR x₀ hκ hb W ζ q) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ q) with hD
  have hcfm := measurable_cfHistory_of_strip hcf
  have hlamm : Measurable (canonLam W ζ q) := (measurable_rootLam _).comp hcfm
  have hxLm : Measurable (canonXL x₀ hκ hb W ζ q) := measurable_pi_iff.2 fun i =>
    ((measurable_rootLam _).comp hcfm).mul ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb _).comp hcfm))
  have hxRm : Measurable (canonXR x₀ hκ hb W ζ q) := measurable_pi_iff.2 fun j =>
    ((measurable_rootLam _).comp hcfm).mul ((measurable_pi_apply j).comp ((measurable_rootXR hκ hb _).comp hcfm))
  have hReg := isReg_rootData x₀ h44 hκ hκ4 hb hhm hcf hlamm (fun ω => rootLam_pos _ _) hxLm hxRm (r := r)
    (noise := rootNoise x₀ h44 hκ hκ4 hb P h W ζ q)
  have hv : D.valid 0 t := isValid_zero t
  have hγ := (hReg.isKilledFamily 0 t).arc ω
  obtain ⟨hW, hVL, hVR, hζ⟩ := TreeData.cand_zero_eq D t hγ h1 hv
  have hlam : 0 < canonLam W ζ q ω := rootLam_pos _ _
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hxLs : StrictAnti (flowLineXL c.fn c.jumps 0) := fun i j hij => Theorem14.GW0.flowLineXL_lt c.fn c.jumps 0 hij
  have hxRs : StrictMono (flowLineXR c.fn c.jumps 0) := fun i j hij => Theorem14.GW0.flowLineXR_lt c.fn c.jumps 0 hij
  have hord := histStart_ordered_dil hlam hF h2 (s := r)
  have hstr := histStart_strict_dil hlam hF hxLs hxRs h2 (s := r)
  have h44' : Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 (π / 2)) (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) :=
    cond44_upper hκ (sourceWord_extreme hκ hb)
  have hthr := not_threshold_histStart_dil hlam hκ hF h44' h2 (s := r)
  -- the killed word of the arc, as a one-point family
  have hK := isKilledWord_kW (Ω := Unit) (γ := fun _ => D.img 0 t ω) (P := fun _ => D.pre 0 t ω) (fun _ => hγ)
    (xL := fun _ => D.xL0 ω) (xR := fun _ => D.xR0 ω) (fun _ i => hord.2.1 i) (fun _ j => hord.2.2.2 j)
    (fun _ => hord.1) (fun _ => hord.2.2.1)
  have hL0 : (fun i => kVL (D.img 0 t ω) (D.pre 0 t ω) (D.xL0 ω) i 0) = D.xL0 ω := funext fun i => by
    rw [kVL_of_lt _ _ (by simpa using hγ.zero_lt_kLife)]
    exact Prop49Exit.kVLr_zero_of_killed hγ _ hord.2.1 i
  have hR0 : (fun j => kVR (D.img 0 t ω) (D.pre 0 t ω) (D.xR0 ω) j 0) = D.xR0 ω := funext fun j => by
    rw [kVR_of_lt _ _ (by simpa using hγ.zero_lt_kLife)]
    exact Prop49Exit.kVRr_zero_of_killed hγ _ hord.2.2.2 j
  have hthr0 : ¬ ForceWord.ThresholdCondition (rootρL κ c) (rootρR κ c) (kW (D.img 0 t ω) (D.pre 0 t ω) 0)
      (fun i => kVL (D.img 0 t ω) (D.pre 0 t ω) (D.xL0 ω) i 0)
      (fun j => kVR (D.img 0 t ω) (D.pre 0 t ω) (D.xR0 ω) j 0) := by
    rw [hγ.kW_zero, hL0, hR0]
    exact hthr
  have hp := hK.isSLEPathUpTo_recNoise (fun _ => hγ.zero_lt_kLife) hκ (rootρL κ c) (rootρR κ c) () hthr0
  simp only [hL0, hR0] at hp
  refine ⟨hord, hstr.1, hstr.2, ?_⟩
  have hB : (fun u => (D.cand 0 t).B u ω) = recNoise κ (rootρL κ c) (rootρR κ c) (D.xL0 ω) (D.xR0 ω)
      (kW (D.img 0 t ω) (D.pre 0 t ω)) (fun i => kVL (D.img 0 t ω) (D.pre 0 t ω) (D.xL0 ω) i)
      (fun k => kVR (D.img 0 t ω) (D.pre 0 t ω) (D.xR0 ω) k) := by
    funext u
    show rootNoise x₀ h44 hκ hκ4 hb P h W ζ q 0 t u ω = _
    simp only [rootNoise]
    rw [show (fun s => ((rootData0 x₀ h44 hκ hκ4 hb P h W ζ q).cand 0 t).W s ω) =
        fun s => (D.cand 0 t).W s ω from rfl, hW,
      show (fun i s => ((rootData0 x₀ h44 hκ hκ4 hb P h W ζ q).cand 0 t).VL i s ω) =
        fun i s => (D.cand 0 t).VL i s ω from rfl, hVL,
      show (fun k s => ((rootData0 x₀ h44 hκ hκ4 hb P h W ζ q).cand 0 t).VR k s ω) =
        fun k s => (D.cand 0 t).VR k s ω from rfl, hVR]
    rfl
  rw [hW, hVL, hVR, hB, hζ]
  exact hp

end Clause

/-! ### The killed stage law of the stage-0 root candidate -/

section Law

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

/-- **Proposition 5.9's killed stage law of the stage-0 root candidate** (R78), in the exact form of the `hlaw` of
`StagedK2.tip0UnboundedStatement_of_candLawsK` at `j = 0`, with the root past `rootBase W ζ` and the recovered noise
`rootNoise`. -/
theorem isStageLawFarK_rootCand_zero (hsw : KilledArcSwallowStatement) (hA : PartAInputsSixteenDiv)
    (hhm : Measurable h) (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) {q : ℚ} (hq : 0 < q) (t : Fin 0 → ℝ≥0) :
    IsStageLawFarK κ (P.prod Pa)
      (canonQ (rootBase W ζ (Ωa := Ωa) q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) 0 t)
      (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ 0 t)
      (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) 0) (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) 0)
      (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ 0)))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ 0)))
      (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) 0 t)
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q 0 t).W
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q 0 t).VL
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q 0 t).VR
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q 0 t).B
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q 0 t).ζ := by
  have hfl : farL (Nat.lt_of_lt_of_le (rootNL_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ 0)) =
      Fin.last (flowLineNL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) := Fin.ext rfl
  have hfr : farR (Nat.lt_of_lt_of_le (rootNR_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ 0)) =
      Fin.last (flowLineNR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) := Fin.ext rfl
  rw [hfl, hfr]
  refine isStageLawFarK_of_compClauseK ?_
    (compClauseK_rootCand x₀ h44 hκ hκ4 hb P Pa h W ζ E hsw hA hhm hG hcf hE hR
      (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) hq t)
  have hr : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 (by exact_mod_cast hq)
  obtain ⟨γ, htr⟩ := exists_cfTrace hκ hb hG hcf
  have h0 : ∀ᵐ ω ∂P, ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal ∧
      Cond44Ref.cfHistory W ζ ω ∈ goodSet49 (q : ℝ).toNNReal := by
    filter_upwards [ae_mem_rootGood x₀ h44 hκ hκ4 hb hA hG hcf htr hE hR (r := (q : ℝ).toNNReal),
      ae_cfHistory_mem_goodSet49 hA hκ hκ4 hb hG hcf hr] with ω h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h0] with ω' hω' _
  exact clause1_rootCand_of_good x₀ h44 hκ hκ4 hb P h W ζ hhm hcf t hω'.1 hω'.2

end Law

/-! ### Prop 5.13's root tip from the later stages only -/

section Tip

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

/-- **Proposition 5.13's root tip assertion from the killed laws of the later stages only**: PROVE-STAGED9's
`tip0UnboundedStatement_of_candLawsK` with the root past `rootBase W ζ`, the recovered noise `rootNoise`, and its
`hlaw` at `j = 0` discharged by `isStageLawFarK_rootCand_zero`; the remaining hypothesis `hlaw` is the per-candidate
killed law at every depth `j + 1 ≥ 1`. -/
theorem tip0UnboundedStatement_of_laterLaws (hsw : KilledArcSwallowStatement) (hA : PartAInputsSixteenDiv)
    (hhm : Measurable h) (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (hlaw : ∀ q : ℚ, 0 < q → ∀ (j : ℕ) (t : Fin (j + 1) → ℝ≥0), IsStageLawFarK κ (P.prod Pa)
      (canonQ (rootBase W ζ (Ωa := Ωa) q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t)
      (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (j + 1) t)
      (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
      (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
      (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ (j + 1))))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ (j + 1))))
      (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t)
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).W
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).VL
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).VR
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).B
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (Ωa := Ωa) q (j + 1) t).ζ) :
    Prop59Tips.Tip0UnboundedStatement P W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime) := by
  have hbase : ∀ q : ℚ, rootBase W ζ (Ωa := Ωa) q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)) := fun q => by
    rintro s ⟨u, hu, rfl⟩
    exact ((measurable_cfStop _).comp ((measurable_cfHistory_of_strip hcf).comp measurable_fst)) hu
  refine StagedK2.tip0UnboundedStatement_of_candLawsK x₀ h44 hκ hκ4 hb P Pa h W ζ E hA hhm hG hcf hE hR
    (rootNoise x₀ h44 hκ hκ4 hb P h W ζ) (rootBase W ζ) hbase fun q hq j t => ?_
  match j, t with
  | 0, t => exact isStageLawFarK_rootCand_zero x₀ h44 hκ hκ4 hb P Pa h W ζ E hsw hA hhm hG hcf hE hR hq t
  | j + 1, t => exact hlaw q hq j t

end Tip

end InteractingSLE.Sec5.CrossCond.StagedRepLater
