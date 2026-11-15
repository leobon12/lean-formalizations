/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.WordSafeSystem
import InteractingSLE.Spec.Sec7.StripDetMain

/-!
# The field-determined drivers of the two-angle paths `η^{t₀,∞}_{θ₀,θ}` (R48-safe)

Packet PROVE-TWOANGLE. Theorems 1.2–1.3's leaf `hWordT` asks for a two-angle strip system
(`Sec7.WordSafe.IsTwoAngleStripSystem`): staged histories of the strip field for the constant-angle programs
`constSpec θ` and the two-angle programs `twoAngleSpec θ₀ t₀ θ`. PROVE-STRIPSYS-SAFE built the constant-angle half
(`StripSafe.constFam`). Here the two-angle drivers are *defined* as Borel functions of the field, by a two-stage version
of PROVE-PROP59-SCHED's schedule recursion (`Prop513Schedule.codeDriver`), whose stage step handles only `±π/2`:

* the first piece is the field-determined angle-`θ₀` flow line `admDrv θ₀` of the field (`drv₀`);
* the continuation is read in the record chart of the first piece at own time `t₀` (`ctx₁`: the stop word
  `stopWord κ (c₀, θ₀, r)` and the field `recField κ r h`, `r = recOf t₀ (drv₀ h)`), and is the field-determined
  angle-`θ` flow line of that conditional field, **directly** (`admDrv θ`) when `θ₀ ≤ θ`, and **after the reflection
  `z ↦ −z̄`** (`negDrv ∘ admDrv (−θ) ∘ (reflWord, reflField)`) when `θ < θ₀` (`recStage`). This is the record-angle
  rule of PROVE-STRIPSYS-SAFE §4: the first piece's sides are exposed at heights `−λ − θ₀χ` / `λ − θ₀χ`, so the new
  word satisfies (4.4) directly iff `θ ≥ θ₀` and after the reflection iff `θ ≤ θ₀` (`StripDet.cond44_flowLine_stopWord`,
  `cond44_reflWord_stopWord`).

* **`recStage`**, **`drv₀`**, **`ctx₁`**, **`drv₁`**, **`twoFam`** (the two-angle drivers), **`twoAngleFam`** (the whole
  family: two-angle drivers on two-instruction programs, `StripSafe.constFam` otherwise), with measurability and
  regularity at every sample;
* **`isFlowLineDriver_recStage`**: the record-angle stage driver of a GFF is its angle-`θ` flow-line driver when the
  word satisfies (4.4) in the chosen orientation.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the only
named input is `Theorem12ParamCond44Statement` (`h44`, R74).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.TwoAngle

open LQGMetric (DistOn)
open QuantumZipper (chiC)
open Restart Exist Exist.Staged Exist.StagedLaw Exist.StagedLaw.BoundaryWord
open Sec7 Sec7.AdmCode Sec7.StripWall Sec7.StripDet Prop513Schedule

section Defs

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

/-- **The record-angle stage driver**: the field-determined angle-`θ` flow line of a context, directly when the new
angle is at least the previous one (`θ₀ ≤ θ`), and through the reflection `z ↦ −z̄` otherwise. -/
def recStage (θ₀ θ : ℝ) (c : Context) : Driver :=
  if θ₀ ≤ θ then admDrv h44 hκ hκ4 θ c
  else negDrv (admDrv h44 hκ hκ4 (-θ) (reflWord c.1, FlowReflect.reflField c.2))

theorem measurable_recStage (θ₀ θ : ℝ) : Measurable (recStage h44 hκ hκ4 θ₀ θ) := by
  unfold recStage
  split_ifs
  · exact measurable_admDrv h44 hκ hκ4 θ
  · exact measurable_negDrv.comp ((measurable_admDrv h44 hκ hκ4 (-θ)).comp
      ((measurable_reflWord.comp measurable_fst).prodMk
        (FlowReflect.measurable_reflField.comp measurable_snd)))

theorem recStage_regular (θ₀ θ : ℝ) (c : Context) : IsRegularDriver (recStage h44 hκ hκ4 θ₀ θ c) := by
  unfold recStage
  split_ifs
  · exact admDrv_regular h44 hκ hκ4 _ _
  · exact isRegularDriver_negDrv (admDrv_regular h44 hκ hκ4 _ _)

/-- The first piece: the field-determined angle-`θ₀` flow line of the field (word `shiftW 0 c₀`, the stage-`0` witness
of `StripDet.stageWitness_zero`). -/
def drv₀ (c₀ : BoundaryWord) (θ₀ : ℝ) (f : DistOn upperHalfPlaneOpens) : Driver :=
  admDrv h44 hκ hκ4 θ₀ (shiftW 0 c₀, flowField 0 0 f)

theorem measurable_drv₀ (c₀ : BoundaryWord) (θ₀ : ℝ) : Measurable (drv₀ h44 hκ hκ4 c₀ θ₀) :=
  (measurable_admDrv h44 hκ hκ4 θ₀).comp (measurable_const.prodMk (measurable_flowField 0 0))

theorem drv₀_regular (c₀ : BoundaryWord) (θ₀ : ℝ) (f : DistOn upperHalfPlaneOpens) :
    IsRegularDriver (drv₀ h44 hκ hκ4 c₀ θ₀ f) :=
  admDrv_regular h44 hκ hκ4 _ _

/-- The context of the continuation: the stop word of the first piece at own time `t₀` and the field read in its
record chart. -/
def ctx₁ (c₀ : BoundaryWord) (θ₀ : ℝ) (t₀ : ℝ≥0∞) (f : DistOn upperHalfPlaneOpens) : Context :=
  (word₁ κ θ₀ c₀ (recOf t₀ (drv₀ h44 hκ hκ4 c₀ θ₀ f)), field₁ κ (recOf t₀ (drv₀ h44 hκ hκ4 c₀ θ₀ f)) f)

theorem measurable_ctx₁ (c₀ : BoundaryWord) (θ₀ : ℝ) (t₀ : ℝ≥0∞) : Measurable (ctx₁ h44 hκ hκ4 c₀ θ₀ t₀) := by
  have hr : Measurable fun f => recOf t₀ (drv₀ h44 hκ hκ4 c₀ θ₀ f) :=
    measurable_recOf (measurable_drv₀ h44 hκ hκ4 c₀ θ₀) (drv₀_regular h44 hκ hκ4 c₀ θ₀) t₀
  have h1 : Measurable fun f => word₁ κ θ₀ c₀ (recOf t₀ (drv₀ h44 hκ hκ4 c₀ θ₀ f)) :=
    (measurable_word₁ κ θ₀ c₀).comp hr
  have h2 : Measurable fun f => field₁ κ (recOf t₀ (drv₀ h44 hκ hκ4 c₀ θ₀ f)) f :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => field₁ κ p.1 p.2)
      (f := fun f => (recOf t₀ (drv₀ h44 hκ hκ4 c₀ θ₀ f), f)) (measurable_field₁ κ) (hr.prodMk measurable_id)
  exact h1.prodMk h2

/-- The continuation: the record-angle stage driver of the context `ctx₁`. -/
def drv₁ (c₀ : BoundaryWord) (θ₀ : ℝ) (t₀ : ℝ≥0∞) (θ : ℝ) (f : DistOn upperHalfPlaneOpens) : Driver :=
  recStage h44 hκ hκ4 θ₀ θ (ctx₁ h44 hκ hκ4 c₀ θ₀ t₀ f)

theorem measurable_drv₁ (c₀ : BoundaryWord) (θ₀ : ℝ) (t₀ : ℝ≥0∞) (θ : ℝ) :
    Measurable (drv₁ h44 hκ hκ4 c₀ θ₀ t₀ θ) :=
  (measurable_recStage h44 hκ hκ4 θ₀ θ).comp (measurable_ctx₁ h44 hκ hκ4 c₀ θ₀ t₀)

theorem drv₁_regular (c₀ : BoundaryWord) (θ₀ : ℝ) (t₀ : ℝ≥0∞) (θ : ℝ) (f : DistOn upperHalfPlaneOpens) :
    IsRegularDriver (drv₁ h44 hκ hκ4 c₀ θ₀ t₀ θ f) :=
  recStage_regular h44 hκ hκ4 _ _ _

/-- **The two-angle drivers** of `η^{t₀,∞}_{θ₀,θ}`: the first piece at instruction `0`, the continuation at every later
instruction (only instruction `1` launches). -/
def twoFam (c₀ : BoundaryWord) (θ₀ : ℝ) (t₀ : ℝ≥0∞) (θ : ℝ) {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) :
    ℕ → Ω → Driver :=
  fun j ω => if j = 0 then drv₀ h44 hκ hκ4 c₀ θ₀ (h ω) else drv₁ h44 hκ hκ4 c₀ θ₀ t₀ θ (h ω)

theorem twoFam_zero (c₀ : BoundaryWord) (θ₀ : ℝ) (t₀ : ℝ≥0∞) (θ : ℝ) {Ω : Type*}
    (h : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) :
    twoFam h44 hκ hκ4 c₀ θ₀ t₀ θ h 0 ω = drv₀ h44 hκ hκ4 c₀ θ₀ (h ω) :=
  ite_eq_left rfl

theorem twoFam_succ (c₀ : BoundaryWord) (θ₀ : ℝ) (t₀ : ℝ≥0∞) (θ : ℝ) {Ω : Type*}
    (h : Ω → DistOn upperHalfPlaneOpens) (k : ℕ) (ω : Ω) :
    twoFam h44 hκ hκ4 c₀ θ₀ t₀ θ h (k + 1) ω = drv₁ h44 hκ hκ4 c₀ θ₀ t₀ θ (h ω) :=
  ite_eq_right (Nat.succ_ne_zero k)

theorem measurable_twoFam (c₀ : BoundaryWord) (θ₀ : ℝ) (t₀ : ℝ≥0∞) (θ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (j : ℕ) :
    Measurable (twoFam h44 hκ hκ4 c₀ θ₀ t₀ θ h j) := by
  rcases j with _ | j
  · rw [show twoFam h44 hκ hκ4 c₀ θ₀ t₀ θ h 0 = fun ω => drv₀ h44 hκ hκ4 c₀ θ₀ (h ω) from
      funext (twoFam_zero h44 hκ hκ4 c₀ θ₀ t₀ θ h)]
    exact (measurable_drv₀ h44 hκ hκ4 c₀ θ₀).comp hh
  · rw [show twoFam h44 hκ hκ4 c₀ θ₀ t₀ θ h (j + 1) = fun ω => drv₁ h44 hκ hκ4 c₀ θ₀ t₀ θ (h ω) from
      funext (twoFam_succ h44 hκ hκ4 c₀ θ₀ t₀ θ h j)]
    exact (measurable_drv₁ h44 hκ hκ4 c₀ θ₀ t₀ θ).comp hh

theorem twoFam_regular (c₀ : BoundaryWord) (θ₀ : ℝ) (t₀ : ℝ≥0∞) (θ : ℝ) {Ω : Type*}
    (h : Ω → DistOn upperHalfPlaneOpens) (j : ℕ) (ω : Ω) :
    IsRegularDriver (twoFam h44 hκ hκ4 c₀ θ₀ t₀ θ h j ω) := by
  rcases j with _ | j
  · rw [twoFam_zero]; exact drv₀_regular h44 hκ hκ4 _ _ _
  · rw [twoFam_succ]; exact drv₁_regular h44 hκ hκ4 _ _ _ _ _

/-- **The whole family**: the two-angle drivers (angles and switch time read from the program) on the two-instruction
programs, the constant-angle drivers `StripSafe.constFam` on every other program. -/
def twoAngleFam (c₀ : BoundaryWord) {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) :
    ExplSpec → ℕ → Ω → Driver :=
  fun spec => if spec.2.2.length = 2 then
      twoFam h44 hκ hκ4 c₀ (instrAngle spec 0) (instrTime spec 0) (instrAngle spec 1) h
    else StripSafe.constFam h44 hκ hκ4 c₀ h spec

theorem twoAngleFam_twoAngleSpec (c₀ : BoundaryWord) {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) (θ₀ : ℝ)
    (t₀ : ℝ≥0) (θ : ℝ) :
    twoAngleFam h44 hκ hκ4 c₀ h (StripSys.twoAngleSpec θ₀ t₀ θ) = twoFam h44 hκ hκ4 c₀ θ₀ (t₀ : ℝ≥0∞) θ h :=
  ite_eq_left rfl

theorem twoAngleFam_constSpec (c₀ : BoundaryWord) {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) (θ : ℝ) :
    twoAngleFam h44 hκ hκ4 c₀ h (R7Aux131.constSpec θ) = StripSafe.constFam h44 hκ hκ4 c₀ h (R7Aux131.constSpec θ) :=
  ite_eq_right (by simp [R7Aux131.constSpec])

theorem twoAngleFam_regular (c₀ : BoundaryWord) {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) (spec : ExplSpec)
    (j : ℕ) (ω : Ω) : IsRegularDriver (twoAngleFam h44 hκ hκ4 c₀ h spec j ω) := by
  unfold twoAngleFam
  split_ifs
  · exact twoFam_regular h44 hκ hκ4 _ _ _ _ _ _ _
  · exact StripSafe.constFam_regular h44 hκ hκ4 _ _ _ _ _

end Defs

/-! ### The record-angle stage is a flow line -/

section Flow

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

/-- **The record-angle stage driver is a flow-line driver** of a GFF with the data of a word `c`, when the angle-`θ`
flow-line word of `c` satisfies (4.4) (case `θ₀ ≤ θ`), resp. the angle-`(−θ)` flow-line word of the mirror word
`reflWord c` does (case `θ < θ₀`); its lifetime is infinite almost surely. -/
theorem isFlowLineDriver_recStage {θ₀ θ : ℝ} {c : BoundaryWord}
    (hup : θ₀ ≤ θ → Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ))
    (hdown : θ < θ₀ → Sec4.Cond44 κ (flowLineRhoL κ (reflWord c).fn (reflWord c).jumps 0 (-θ))
      (flowLineRhoR κ (reflWord c).fn (reflWord c).jumps 0 (-θ)))
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : IsGFFWithBoundaryData Q Y c.fn c.jumps)
    {E : Ω → Driver} (hEm : Measurable E) (hE : ∀ᵐ ω ∂Q, E ω = recStage h44 hκ hκ4 θ₀ θ (c, Y ω)) :
    (∀ᵐ ω ∂Q, (E ω).2 = ⊤) ∧
      IsFlowLineDriver κ c.fn c.jumps θ Q Y (fun t ω => (E ω).1 t) (fun ω => (E ω).2) := by
  by_cases hθ : θ₀ ≤ θ
  · refine Prop59Sched.isFlowLineDriver_admDrv h44 hκ hκ4 θ c (hup hθ) hY hEm ?_
    filter_upwards [hE] with ω hω
    rw [hω]
    simp only [recStage, hθ, ↓reduceIte]
  · have hE' : ∀ᵐ ω ∂Q, negDrv (E ω) =
        admDrv h44 hκ hκ4 (-θ) (reflWord c, FlowReflect.reflField (Y ω)) := by
      filter_upwards [hE] with ω hω
      rw [hω]
      simp only [recStage, hθ, ↓reduceIte, negDrv, neg_neg]
    obtain ⟨htop, hfl⟩ := Prop59Sched.isFlowLineDriver_admDrv h44 hκ hκ4 (-θ) (reflWord c)
      (hdown (not_le.1 hθ)) (Prop59Sched.isGFFWithBoundaryData_reflWord hY) (measurable_negDrv.comp hEm) hE'
    have hfl' := isFlowLineDriver_reflect (reflWord c).isPiecewiseConstantBoundaryData hfl
    simp only [FlowReflect.reflField_reflField, neg_neg] at hfl'
    have e : (-fun t ω => ((negDrv ∘ E) ω).1 t) = fun t ω => (E ω).1 t := by
      funext t ω
      simp only [Function.comp_apply, negDrv, Pi.neg_apply, neg_neg]
    rw [e] at hfl'
    exact ⟨htop, isFlowLineDriver_word hκ hY
      (FlowReflect.isPiecewiseConstantBoundaryData_reflData (reflWord c).isPiecewiseConstantBoundaryData) hfl'⟩

end Flow

end InteractingSLE.Sec5.TwoAngle
