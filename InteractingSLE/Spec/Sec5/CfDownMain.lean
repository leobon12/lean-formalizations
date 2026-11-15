/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfDownSafe
import InteractingSLE.Spec.Sec5.CfDownLaw

/-!
# The mirror-image restart chart `QSched.CfGivenChart44DownStatement` from the up chart by reflection

Packet PROVE-CFDOWN. **`cfGivenChart44Down_of_up`**: the chart form of Lemma 4.7's conditional law at the
mirror-image heights (needed for the pieces of angle `−π/2` of Theorem 1.2's restart schedules) follows from the
chart form at the heights of the prefix angle (`QSched.CfGivenChart44UpStatement`), applied to the reflected
configuration: the field `−h ∘ σ` (a GFF with the data `y ↦ −b(−y)`, `FlowReflect.IsGFFWithBoundaryData.reflect`), its
centred counterflow `−W′` (`R7Outer.isCenteredCounterflowDriver_reflect`), the reflected piece `−D` (its flow line of
angle `−θ₀`, `StripWall.isFlowLineDriver_reflect`) and the reflected trace `σ ∘ η`. The conclusion is reflected back:

* filtration unchanged, record σ-algebras equal (`comap_negRec`);
* image word `(−xR; −xL)`, `(ρR; ρL)` (`thr_neg`, `isFlowType_reflWord`), image driver `−W″`;
* integrability and member identities of the image field (`imgField_negRec`, `hasSafeMembers_reflect`);
* the chart coupling clause (`isChartCouplingCharFunConst_reflect`, `a = πk` for `(a, k) = (−πχ, −χ)`);
* image counterflow `σ ∘ η″`, same clock (`recChart_negRec_inv`, `R7Outer.negInv_reflectC`).

Wirings: **`cfGivenChart44Statement_of_up`** (both alternatives), **`counterflowGivenPrefix44Statement_of_leaves'`**
and **`qScheduleFirstHitStatement_of_leaves'`** (`QSched.counterflowGivenPrefix44Statement_of_leaves` /
`qScheduleFirstHitStatement_of_leaves` with their input `hDn` discharged).

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
open Sec7.FlowReflect (reflField reflData reflJumps reflTest)
open Sec7.StripWall (negDrv)

/-- **The mirror-image restart chart from the up chart, by reflection** (`QSched.CfGivenChart44DownStatement`). -/
theorem cfGivenChart44Down_of_up (hU : CfGivenChart44UpStatement.{u}) : CfGivenChart44DownStatement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W' ζ' hκ hκ4 hb hh hcf hζ θ₀ hθ₀ h1 h2 D hDm hDreg hD t₀ η hη
  have hθ' : -θ₀ ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [hθ₀.2], by linarith [hθ₀.1]⟩
  have hD' : IsFlowLineDriver κ (reflData b) (reflJumps J) (-θ₀) P (fun ω => reflField (h ω))
      (fun t ω => (negDrv (D ω)).1 t) (fun ω => (negDrv (D ω)).2) := Sec7.StripWall.isFlowLineDriver_reflect hb hD
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W') t ω) ⊤ (fun t => reflectC (η ω t)) :=
    hη.mono fun ω hω => LP.isGeneratingTrace_reflect hω
  obtain ⟨𝓐, nL, nR, ρL, ρR, xL, xR, W₃, η₃, h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hW0, hWc, hWa, hthr, htype,
    hint, hchart, hmem, hpath⟩ := hU κ (reflData b) (reflJumps J) P (fun ω => reflField (h ω)) (-W') ζ' hκ hκ4
      (Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb)
      (Sec7.FlowReflect.IsGFFWithBoundaryData.reflect hh) (Sec7.R7Outer.isCenteredCounterflowDriver_reflect hκ hcf)
      hζ (-θ₀) hθ' h1 h2 (fun ω => negDrv (D ω)) (Sec7.StripWall.measurable_negDrv.comp hDm)
      (fun ω => Sec7.StripWall.isRegularDriver_negDrv (hDreg ω)) hD' t₀ (fun ω t => reflectC (η ω t)) hη'
  -- the record σ-algebras
  have hc := comap_negRec (fun ω => recOf (t₀ : ℝ≥0∞) (D ω))
  have h𝒢' : MeasurableSpace.comap (fun ω => negRec (recOf (t₀ : ℝ≥0∞) (D ω))) inferInstance ≤ 𝓐 0 := h𝒢
  have hxL' : Measurable[MeasurableSpace.comap (fun ω => negRec (recOf (t₀ : ℝ≥0∞) (D ω))) inferInstance] xL := hxL
  have hxR' : Measurable[MeasurableSpace.comap (fun ω => negRec (recOf (t₀ : ℝ≥0∞) (D ω))) inferInstance] xR := hxR
  rw [hc] at h𝒢' hxL' hxR'
  -- the outputs restated through the reflected record `negRec (recOf t₀ (D ω))`
  have hint' : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => imgField κ (negRec (recOf (t₀ : ℝ≥0∞) (D ω))) (reflField (h ω)) φ) P := hint
  have hchart' : Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 W₃
      (Sec7.PocketTraversal.geomLW W₃ xL) (Sec7.PocketTraversal.geomRW W₃ xR) (fun _ => ⊤)
      (fun ω => cfChart (negRec (recOf (t₀ : ℝ≥0∞) (D ω)))) (-(π * chiC κ)) (-chiC κ)
      (fun ω => -reflField (h ω)) := hchart
  have hmem' : Restart.DomainMarkov.K2.HasSafeMembers P 𝓐 univ (fun _ => ⊤) W₃
      (fun ω => imgField κ (negRec (recOf (t₀ : ℝ≥0∞) (D ω))) (reflField (h ω))) := hmem
  have hpath' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W₃ t ω) ⊤ (η₃ ω) ∧
      ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
        ∀ u : ℝ≥0, 0 < u → negInv (η₃ ω u) ∈ H ∧
          negInv (reflectC (η ω (ℓ u))) = (recChart (negRec (recOf (t₀ : ℝ≥0∞) (D ω)))).2.1 (negInv (η₃ ω u)) :=
    hpath
  have himg : (fun ω => imgField κ (negRec (recOf (t₀ : ℝ≥0∞) (D ω))) (reflField (h ω))) =
      fun ω => reflField (imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω)) :=
    funext fun ω => imgField_negRec hκ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω)
  rw [himg] at hmem'
  have hak : -(π * chiC κ) = π * -chiC κ := by ring
  refine ⟨𝓐, nR, nL, ρR, ρL, fun ω i => -xR ω i, fun ω j => -xL ω j, -W₃, fun ω t => reflectC (η₃ ω t), h𝒢',
    hxR'.neg, hxL'.neg, fun ω i => neg_nonpos.2 (hxR0 ω i), fun ω j => neg_nonneg.2 (hxL0 ω j),
    fun ω => (hxRm ω).neg, fun ω => (hxLa ω).neg, fun ω => by simp [hW0 ω], fun ω => (hWc ω).neg,
    fun t => (hWa t).neg, ?_, ?_, ?_,
    isChartCouplingCharFunConst_reflect (R := fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) (h := h) hak hchart',
    hasSafeMembers_reflect hmem', ?_⟩
  · filter_upwards [hthr] with ω hω
    exact (thr_neg ρL ρR W₃ xL xR ω).trans hω
  · filter_upwards [htype] with ω hω
    obtain ⟨c, hc⟩ := hω
    exact ⟨Sec7.StripWall.reflWord c, isFlowType_reflWord hc⟩
  · intro φ
    have e : (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω) φ) =
        fun ω => -imgField κ (negRec (recOf (t₀ : ℝ≥0∞) (D ω))) (reflField (h ω)) (reflTest φ) :=
      funext fun ω => imgField_apply_eq hκ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω) φ
    rw [e]
    exact (hint' (reflTest φ)).neg
  · filter_upwards [hpath'] with ω hω
    obtain ⟨hg, ℓ, hcl, hm, h0, hl⟩ := hω
    refine ⟨LP.isGeneratingTrace_reflect hg, ℓ, hcl, hm, h0, fun u hu => ?_⟩
    obtain ⟨hH, he⟩ := hl u hu
    rw [recChart_negRec_inv _ hH, Sec7.R7Outer.negInv_reflectC] at he
    refine ⟨?_, ?_⟩
    · rw [Sec7.R7Outer.negInv_reflectC]
      exact LP.reflectC_mem_H_iff.2 hH
    · rw [Sec7.R7Outer.negInv_reflectC]
      exact LP.reflectC_injective he

/-- **The chart form under the (4.4) heights, both alternatives, from the up chart form.** -/
theorem cfGivenChart44Statement_of_up (hU : CfGivenChart44UpStatement.{u}) : CfGivenChart44Statement.{u} :=
  cfGivenChart44Statement_of_up_down hU (cfGivenChart44Down_of_up hU)

/-- **The restart law at a switch from the four chart leaves in their (4.4) form**, Part A and the §4.2 reference
(`QSched.counterflowGivenPrefix44Statement_of_leaves` with its mirror-image input discharged). -/
theorem counterflowGivenPrefix44Statement_of_leaves' (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hInt : Converted44IntegrableOn.{u})
    (hRed : Converted44ReductionOn (positiveChartBase44Statement hA href))
    (hLoc : Converted44LocalOn (positiveChartBase44Statement hA href)) (hZero : ZeroChart44Statement.{u}) :
    CounterflowGivenPrefix44Statement.{u} :=
  counterflowGivenPrefix44Statement_of_leaves hA href hInt hRed hLoc hZero
    (cfGivenChart44Down_of_up (cfGivenChart44Up_of_converted _ hInt hRed hLoc hZero))

/-- **Theorem 1.2's `hQ0` (`FrameQ.QScheduleFirstHitStatement`) from Lemma 4.7, `h44`, Part A, the §4.2 reference and
the four chart leaves in their (4.4) form** (`QSched.qScheduleFirstHitStatement_of_leaves` with `hDn` discharged). -/
theorem qScheduleFirstHitStatement_of_leaves' (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (h47 : Prop411Q.Lemma47QHitStatement.{u}) (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hInt : Converted44IntegrableOn.{u})
    (hRed : Converted44ReductionOn (positiveChartBase44Statement hA href))
    (hLoc : Converted44LocalOn (positiveChartBase44Statement hA href)) (hZero : ZeroChart44Statement.{u}) :
    FrameQ.QScheduleFirstHitStatement.{u} :=
  qScheduleFirstHitStatement_of_leaves h44 h47 hA href hInt hRed hLoc hZero
    (cfGivenChart44Down_of_up (cfGivenChart44Up_of_converted _ hInt hRed hLoc hZero))

end InteractingSLE.Sec5.CfDown
