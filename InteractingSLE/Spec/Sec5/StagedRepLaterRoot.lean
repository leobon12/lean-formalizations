/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterGam
import InteractingSLE.Spec.Sec5.StagedRepLaterScale
import InteractingSLE.Spec.Sec5.Prop59SchedReal
import InteractingSLE.Spec.Sec7.R7OuterAvoid
import InteractingSLE.Spec.Sec5.FrameQChart
import InteractingSLE.Spec.Sec5.Prop513ScheduleData

/-!
# Prop 5.9's root stage on PROVE-PROP59-PIECES' space: the setting

Packet PROVE-STAGED-REP2. The θ-template of Proposition 4.9 (PROVE-CROSSCOND-THETA, PROVE-STAGED-REP) is run with
PIECES' own probability space as the flow space:

* `qDrv_zero`: the stage-0 candidate path of PIECES is the trace of the field-determined angle-`π/2` code driver
  `rootDrv` of the field in chart `Q` (`admDrv (π/2)`);
* **`exists_rootCoupling`**: `rootDrv` is the driver of an optional hull coupling with the flow field
  `qField + (π/2)χ` of the root flow word, its lifetime infinite almost surely
  (`Prop59Sched.isOptionalHullCoupling_admCode`,
  R74's `h44`);
* `cfField_rootField`: the counterflow field of that coupling field is `qField` itself, the field of PIECES'
  counterflow (`isCenteredCounterflowDriver_of_strip`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; `h44`
is R74's `Theorem12ParamCond44Statement`.
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

/-! ### The stage-0 code path -/

section Code

variable (h44 : Theorem12ParamCond44Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : BoundaryWord)

theorem isValid_zero (t : Fin 0 → ℝ≥0) : IsValid 0 t := ⟨fun i => i.elim0, fun i => i.elim0⟩

theorem scheduleList_candSched_zero (t : Fin 0 → ℝ≥0) :
    scheduleList (candSched 0 t) = [(π / 2, (1 : ℝ≥0))] := by
  rw [candSched, scheduleList_mkSched (isValid_zero t) (by simp [lastO])]
  simp [entries, stageFlag, lastO]

theorem instrAngle_candSched_zero (t : Fin 0 → ℝ≥0) : instrAngle (scheduleSpec (candSched 0 t)) 0 = π / 2 := by
  simp only [scheduleSpec]
  rw [candSched, scheduleList_mkSched (isValid_zero t) (by simp [lastO])]
  simp [entries, stageFlag, lastO, instrAngle, scheduleProgram]

/-- **The stage-0 candidate driver is the angle-`π/2` code driver of the field.** -/
theorem qDrv_zero {Ω : Type*} (F : Ω → DistOn upperHalfPlaneOpens) (t : Fin 0 → ℝ≥0) (ω : Ω) :
    qDrv h44 hκ hκ4 c F 0 t ω = (admDrv h44 hκ hκ4 (π / 2) (c, F ω)).1 := by
  have hpi : ¬ π / 2 < 0 := not_lt.2 (by positivity)
  simp only [qDrv, scheduleList_candSched_zero, continuedDriver, codeFam, codeDriver,
    instrAngle_candSched_zero, codeContext, stageDriver, hpi, ↓reduceIte]

end Code

/-! ### The root coupling on PIECES' space -/

section Coupling

variable (h44 : Theorem12ParamCond44Statement.{0}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The root code driver**: the angle-`π/2` flow-line driver determined by the field in chart `Q`. -/
def rootDrv (h : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  admDrv h44 hκ hκ4 (π / 2) (sourceWord (x₀ := x₀) hκ hb, qField x₀ κ h ω)

/-- The coupling field of the root flow line: `qField + (π/2)χ`. -/
def rootField (h : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) : DistOn upperHalfPlaneOpens :=
  Exist.flowField 0 (π / 2 * chiC κ) (qField x₀ κ h ω)

omit mΩ [IsProbabilityMeasure P] in
theorem cfField_rootField (ω : Ω) : Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω) = qField x₀ κ h ω :=
  Sec7.R7Outer.cfField_flowField_half κ _

theorem measurable_rootDrv (hhm : Measurable h) : Measurable (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h) :=
  (measurable_admDrv h44 hκ hκ4 _).comp (measurable_const.prodMk
    ((measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm))

theorem measurable_rootField (hhm : Measurable h) : Measurable (rootField (κ := κ) (x₀ := x₀) h) :=
  (Exist.measurable_flowField 0 _).comp ((measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm)

/-- **The root flow line as an optional hull coupling** on PIECES' space: the field-determined angle-`π/2` code
driver of `qField` drives a coupling with `qField + (π/2)χ` for the root flow word; its lifetime is infinite almost
surely. -/
theorem exists_rootCoupling (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀}) :
    (∀ᵐ ω ∂P, (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2 = ⊤) ∧
      ∃ (𝓕 : Filtration ℝ≥0 mΩ)
        (VL : Fin (flowLineNL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) →
          ℝ≥0 → Ω → ℝ)
        (VR : Fin (flowLineNR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) →
          ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
          (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
          (flowLineRhoL κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0 (π / 2))
          (flowLineRhoR κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0 (π / 2))
          P 𝓕 (fun t ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).1 t) VL VR B
          (fun ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2) (rootField (κ := κ) (x₀ := x₀) h) := by
  set c := sourceWord (x₀ := x₀) hκ hb
  have hgff := Exist.isGFFWithBoundaryData_flowField hκ c.isPiecewiseConstantBoundaryData 0 (π / 2)
    (sourceWord_gff hκ hb hG)
  exact Prop59Sched.isOptionalHullCoupling_admCode h44 hκ hκ4 (Theorem15.isOrderedForceWord_flowLine _ _ 0)
    (cond44_upper hκ (sourceWord_extreme hκ hb)) hgff (measurable_rootDrv h44 hκ hκ4 hb hhm)
    (Eventually.of_forall fun ω => admDrv_eq h44 hκ hκ4 (π / 2) c (qField x₀ κ h ω))

omit [IsProbabilityMeasure P] in
/-- PIECES' strip counterflow is a centered counterflow of `qField`. -/
theorem isCenteredCounterflowDriver_of_strip (hκ : 0 < κ)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    IsCenteredCounterflowDriver κ P (qField x₀ κ h) W ζ :=
  (FrameQ.isStripCounterflowDriver_iff_centered hκ (Real.exp_pos _)).1 hcf

end Coupling

/-! ### Stage-0 candidates are the killed words of their image curves -/

section Ident

variable {Ω : Type*} {nL nR : ℕ}

/-- **A stage-0 candidate piece is the killed word of its killed arc** (start capacity `0`, alive). -/
theorem pieceSamp_arcPiece_zero {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0} {A : Set Ω}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hγ : IsKilledArc (γ ω) (P ω))
    (hA : ω ∈ A) (hS : S₀ ω = 0) :
    pieceSamp (arcPiece γ P S₀ A xL xR B).W (arcPiece γ P S₀ A xL xR B).VL (arcPiece γ P S₀ A xL xR B).VR
      (arcPiece γ P S₀ A xL xR B).ζ ω =
    samp (ImgWord.kW (γ ω) (P ω)) (fun i => ImgWord.kVL (γ ω) (P ω) (xL ω) i)
      (fun k => ImgWord.kVR (γ ω) (P ω) (xR ω) k) (ImgWord.kLife (γ ω) (P ω)) := by
  classical
  have hW : ∀ u, arcW γ P S₀ A u ω = ImgWord.kW (γ ω) (P ω) u := fun u => by
    unfold arcW
    simp only [hS, zero_add, hA, true_and]
    by_cases hu : (u : WithTop ℝ≥0) < ImgWord.kLife (γ ω) (P ω)
    · simp only [hu, ↓reduceIte, hγ.kW_zero, sub_zero]
    · simp only [hu, ↓reduceIte, ImgWord.kW]
  have hζ : arcζ γ P S₀ A ω = (ImgWord.kLife (γ ω) (P ω) : ℝ≥0∞) := by
    simp only [arcζ, hA, ↓reduceIte, hS, ENNReal.coe_zero, tsub_zero]
    rfl
  have hrW : Bessel.realPath (fun u ω => -arcW γ P S₀ A u ω) ω = fun r => -ImgWord.kPath (γ ω) (P ω) r := by
    funext r; simp only [Bessel.realPath, hW, ImgWord.kPath]
  have hrW' : Bessel.realPath (arcW γ P S₀ A) ω = ImgWord.kPath (γ ω) (P ω) := by
    funext r; simp only [Bessel.realPath, hW, ImgWord.kPath]
  simp only [pieceSamp, samp, arcPiece, arcVL, arcVR, hζ, hW, hrW, hrW', ImgWord.kVL, ImgWord.kVR,
    ImgWord.kVLr, ImgWord.kVRr, ImgWord.kImg]
  refine Prod.ext rfl (funext fun q => ?_)
  by_cases hq : ((q : ℝ≥0) : ℝ≥0∞) < (ImgWord.kLife (γ ω) (P ω) : ℝ≥0∞)
  · have hq' : ((q : ℝ≥0) : WithTop ℝ≥0) < ImgWord.kLife (γ ω) (P ω) := hq
    simp only [hq, hq', ↓reduceIte]
  · simp only [hq, ↓reduceIte]

variable {nL₀ nR₀ : ℕ}

/-- **The stage-0 candidate of tree data** at a good sample is the killed word of its image curve with the root
marks. -/
theorem TreeData.pieceSamp_cand_zero (D : TreeData Ω nL₀ nR₀) (t : Fin 0 → ℝ≥0) {ω : Ω}
    (hγ : IsKilledArc (D.img 0 t ω) (D.pre 0 t ω)) (hω : ω ∈ D.G) (hv : D.valid 0 t) :
    pieceSamp (D.cand 0 t).W (D.cand 0 t).VL (D.cand 0 t).VR (D.cand 0 t).ζ ω =
    samp (ImgWord.kW (D.img 0 t ω) (D.pre 0 t ω)) (fun i => ImgWord.kVL (D.img 0 t ω) (D.pre 0 t ω) (D.xL0 ω) i)
      (fun k => ImgWord.kVR (D.img 0 t ω) (D.pre 0 t ω) (D.xR0 ω) k)
      (ImgWord.kLife (D.img 0 t ω) (D.pre 0 t ω)) := by
  classical
  have hA : ω ∈ D.alive 0 t := ⟨⟨hv, hω⟩, by simpa [qLast] using hγ.zero_mem⟩
  have hS : D.startCap 0 t ω = 0 := by
    simp only [TreeData.startCap, hA, ↓reduceIte, qLast, hγ.capClock_zero, Real.toNNReal_zero]
  exact pieceSamp_arcPiece_zero hγ hA hS

end Ident

end InteractingSLE.Sec5.CrossCond.StagedRepLater
