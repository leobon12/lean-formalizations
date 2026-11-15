/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfDownRec
import InteractingSLE.Spec.Sec5.QSchedChart
import InteractingSLE.Spec.Sec5.QSchedWire

/-!
# The restart law at a switch for pieces at the mirror-image heights, by reflection

Packet PROVE-CFDOWN. `QSched.CounterflowGivenPrefix44Statement` (the restart law at a switch used by the schedule
induction of Theorem 1.2's `hQ0`) has two height alternatives: the (4.4) heights of the data at the prefix angle
`θ₀` and at `π/2`, or those of the mirror-image data `y ↦ −b(−y)` at `−θ₀` and `π/2` (needed for pieces of angle
`−π/2`). The second alternative is the reflection `σ(z) = −z̄` of the first: the reflected field `−h ∘ σ` is a GFF
with the mirror-image data, its centred counterflow is driven by `−W′`, the reflected piece `−D` is its flow line of
angle `−θ₀`, the record of `−D` is the reflected record (generating the same σ-algebra), and the field read in its
chart is the reflected field read in the record chart (`CfDownRec`). So the first alternative's conditional law,
reflected back, is the second's:

* `PrefixLaw`: the conclusion of `CounterflowGivenPrefix44Statement`;
* `prefixLaw_up`: the first alternative from `QSched.CfGivenChart44UpStatement` (as
  `QSched.counterflowGivenPrefix44Statement_of_chart44`);
* **`prefixLaw_reflect`**: the reflection step (the first alternative for the reflected data gives the second);
* **`counterflowGivenPrefix44Statement_of_up`**: the restart law at a switch from the up chart form alone;
* **`qScheduleFirstHitStatement_of_up_leaves`**: `QSched.qScheduleFirstHitStatement_of_leaves` without the
  mirror-image chart input `CfGivenChart44DownStatement`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfDown

open Exist Exist.Staged Exist.StagedLaw CfGiven QSched
open LP (reflectC reflectC_reflectC)
open WangWu (negInv)
open Sec7.FlowReflect (reflField reflData reflJumps)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.StripWall (negDrv)

/-- **The conclusion of the restart law at a switch** (`QSched.CounterflowGivenPrefix44Statement`): under the
regular conditional law given the record of `D` stopped at `t₀`, `W″` drives the centred counterflow of the field read
in the record chart, with infinite lifetime; pathwise a continuous increasing clock `ℓ` carries the image counterflow
`η″` to the physical one `η`. -/
def PrefixLaw (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (t₀ : ℝ≥0)
    (η : Ω → ℝ≥0 → ℂ) : Prop :=
  ∃ (W'' : ℝ≥0 → Ω → ℝ) (ζ'' : Ω → ℝ≥0∞) (η'' : Ω → ℝ≥0 → ℂ),
    (∀ᵐ ω₀ ∂P,
      IsCenteredCounterflowDriver κ
          (condExpKernel P (MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance) ω₀)
          (fun ω => recField κ (recOf (t₀ : ℝ≥0∞) (D ω₀)) (h ω)) W'' ζ'' ∧
        ∀ᵐ ω ∂(condExpKernel P (MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance) ω₀),
          ζ'' ω = ⊤) ∧
    ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧
      ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
        ∀ u : ℝ≥0, 0 < u → negInv (η'' ω u) ∈ H ∧
          negInv (η ω (ℓ u)) = (recChart (recOf (t₀ : ℝ≥0∞) (D ω))).2.1 (negInv (η'' ω u))

/-- Conditional kernels given equal σ-algebras agree. -/
theorem condExpKernel_apply_congr {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] (e : m₁ = m₂) (ω₀ : Ω) :
    condExpKernel P m₁ ω₀ = condExpKernel P m₂ ω₀ := by
  subst e
  rfl

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {θ₀ : ℝ} {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {η : Ω → ℝ≥0 → ℂ}

/-- **The restart law at a switch at the heights of the prefix angle, from the up chart form**
(`QSched.counterflowGivenPrefix44Statement_of_chart44`'s argument:
`CfGiven.ae_isCenteredCounterflowDriver_of_hasSafeLaw`
and `CfGiven.hasSafeLaw_imgField_of_chartConst` use no heights). -/
theorem prefixLaw_up (hU : CfGivenChart44UpStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (h1 : IsHeightBounded44 κ b J θ₀) (h2 : IsHeightBounded44 κ b J (π / 2))
    (hDm : Measurable D) (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)) (t₀ : ℝ≥0)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) : PrefixLaw κ P h D t₀ η := by
  obtain ⟨𝓐, nL, nR, ρL, ρR, xL, xR, W'', η'', h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hW0, hWc, hWa, hthr, htype,
    hint, hchart, hmem, hpath⟩ := hU κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ' θ₀ hθ₀ h1 h2 D hDm hDreg hD t₀ η hη
  have hRm : Measurable fun ω => recOf (t₀ : ℝ≥0∞) (D ω) := measurable_recOf hDm hDreg _
  refine ⟨W'', fun _ => ⊤, η'', ?_, hpath⟩
  filter_upwards [ae_isCenteredCounterflowDriver_of_hasSafeLaw hκ hh.1 hRm h𝒢 hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc
    hWa hint hthr htype (hasSafeLaw_imgField_of_chartConst hκ hh.1 h𝒢 hW0 hWc hchart) hmem] with ω₀ hω₀
  exact ⟨hω₀, ae_of_all _ fun _ => rfl⟩

/-- **The reflection step.** The restart law for the reflected configuration (field `−h ∘ σ`, piece `−D`, counterflow
trace `σ ∘ η`) gives the restart law for the original one: negate the image driver, reflect the image counterflow. -/
theorem prefixLaw_reflect (hκ : 0 < κ) (t₀ : ℝ≥0)
    (hL : PrefixLaw κ P (fun ω => reflField (h ω)) (fun ω => negDrv (D ω)) t₀ (fun ω t => reflectC (η ω t))) :
    PrefixLaw κ P h D t₀ η := by
  obtain ⟨W₃, ζ₃, η₃, hlaw, hpath⟩ := hL
  refine ⟨-W₃, ζ₃, fun ω t => reflectC (η₃ ω t), ?_, ?_⟩
  · filter_upwards [hlaw] with ω₀ hω₀
    obtain ⟨hcf₀, hζ₀⟩ := hω₀
    have ek := condExpKernel_apply_congr (P := P) (comap_negRec (fun ω => recOf (t₀ : ℝ≥0∞) (D ω))) ω₀
    have hcf₁ : IsCenteredCounterflowDriver κ
        (condExpKernel P (MeasurableSpace.comap (fun ω => negRec (recOf (t₀ : ℝ≥0∞) (D ω))) inferInstance) ω₀)
        (fun ω => recField κ (negRec (recOf (t₀ : ℝ≥0∞) (D ω₀))) (reflField (h ω))) W₃ ζ₃ := hcf₀
    have hζ₁ : ∀ᵐ ω ∂(condExpKernel P
        (MeasurableSpace.comap (fun ω => negRec (recOf (t₀ : ℝ≥0∞) (D ω))) inferInstance) ω₀), ζ₃ ω = ⊤ := hζ₀
    rw [ek] at hcf₁ hζ₁
    simp only [recField_negRec] at hcf₁
    have hr := Sec7.R7Outer.isCenteredCounterflowDriver_reflect hκ hcf₁
    simp only [Sec7.FlowReflect.reflField_reflField] at hr
    exact ⟨hr, hζ₁⟩
  · filter_upwards [hpath] with ω hω
    obtain ⟨hg, ℓ, hc, hm, h0, hl⟩ := hω
    refine ⟨LP.isGeneratingTrace_reflect hg, ℓ, hc, hm, h0, fun u hu => ?_⟩
    obtain ⟨hH, he⟩ := hl u hu
    rw [recOf_negDrv, recChart_negRec_inv _ hH, Sec7.R7Outer.negInv_reflectC] at he
    refine ⟨?_, ?_⟩
    · rw [Sec7.R7Outer.negInv_reflectC]
      exact LP.reflectC_mem_H_iff.2 hH
    · rw [Sec7.R7Outer.negInv_reflectC]
      exact LP.reflectC_injective he

/-- **The restart law at a switch at the mirror-image heights, from the up chart form**, by reflection. -/
theorem prefixLaw_down (hU : CfGivenChart44UpStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (h1 : IsHeightBounded44 κ (reflData b) (reflJumps J) (-θ₀))
    (h2 : IsHeightBounded44 κ (reflData b) (reflJumps J) (π / 2))
    (hDm : Measurable D) (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2)) (t₀ : ℝ≥0)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) : PrefixLaw κ P h D t₀ η := by
  have hθ' : -θ₀ ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hθ₀.2], by linarith [hθ₀.1]⟩
  have hD' : IsFlowLineDriver κ (reflData b) (reflJumps J) (-θ₀) P (fun ω => reflField (h ω))
      (fun t ω => (negDrv (D ω)).1 t) (fun ω => (negDrv (D ω)).2) := Sec7.StripWall.isFlowLineDriver_reflect hb hD
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W') t ω) ⊤ (fun t => reflectC (η ω t)) :=
    hη.mono fun ω hω => LP.isGeneratingTrace_reflect hω
  exact prefixLaw_reflect hκ t₀ (prefixLaw_up hU hκ hκ4 (Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb)
    (Sec7.FlowReflect.IsGFFWithBoundaryData.reflect hh) (Sec7.R7Outer.isCenteredCounterflowDriver_reflect hκ hcf)
    hζ' hθ' h1 h2 (Sec7.StripWall.measurable_negDrv.comp hDm)
    (fun ω => Sec7.StripWall.isRegularDriver_negDrv (hDreg ω)) hD' t₀ hη')

/-- **The restart law at a switch (`QSched.CounterflowGivenPrefix44Statement`) from the up chart form alone**: the
first height alternative directly, the second by reflection. -/
theorem counterflowGivenPrefix44Statement_of_up (hU : CfGivenChart44UpStatement.{u}) :
    CounterflowGivenPrefix44Statement.{u} := by
  intro κ b J Ω _ _ P _ h W' ζ' hκ hκ4 hb hh hcf hζ' θ₀ hθ₀ hhgt D hDm hDreg hD t₀ η hη
  rcases hhgt with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact prefixLaw_up hU hκ hκ4 hb hh hcf hζ' hθ₀ h1 h2 hDm hDreg hD t₀ hη
  · exact prefixLaw_down hU hκ hκ4 hb hh hcf hζ' hθ₀ h1 h2 hDm hDreg hD t₀ hη

/-- **The restart law at a switch from the four chart leaves in their (4.4) form**, with Part A and the §4.2
reference (`QSched.counterflowGivenPrefix44Statement_of_leaves` without the mirror-image chart input). -/
theorem counterflowGivenPrefix44Statement_of_up_leaves (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hInt : Converted44IntegrableOn.{u})
    (hRed : Converted44ReductionOn (positiveChartBase44Statement hA href))
    (hLoc : Converted44LocalOn (positiveChartBase44Statement hA href)) (hZero : ZeroChart44Statement.{u}) :
    CounterflowGivenPrefix44Statement.{u} :=
  counterflowGivenPrefix44Statement_of_up (cfGivenChart44Up_of_converted _ hInt hRed hLoc hZero)

/-- **Lemma 5.7 for the finite extreme-angle schedules in the Q frame (Theorem 1.2's `hQ0`) from Lemma 4.7, `h44`,
Part A, the §4.2 reference and the four chart leaves in their (4.4) form** —
`QSched.qScheduleFirstHitStatement_of_leaves`
without its input `CfGivenChart44DownStatement`. -/
theorem qScheduleFirstHitStatement_of_up_leaves (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (h47 : Prop411Q.Lemma47QHitStatement.{u}) (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hInt : Converted44IntegrableOn.{u})
    (hRed : Converted44ReductionOn (positiveChartBase44Statement hA href))
    (hLoc : Converted44LocalOn (positiveChartBase44Statement hA href)) (hZero : ZeroChart44Statement.{u}) :
    FrameQ.QScheduleFirstHitStatement.{u} :=
  qScheduleFirstHitStatement_of_input h44 h47 href
    (counterflowGivenPrefix44Statement_of_up_leaves hA href hInt hRed hLoc hZero)

end InteractingSLE.Sec5.CfDown
