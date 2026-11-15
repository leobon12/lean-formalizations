/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61NjGerm
import InteractingSLE.Spec.Sec5.Aux61WndCapNorm

/-!
# Component comparisons from pinch-free accesses, and the fibre cover

Packet PROVE-AUX61-NOJUMP (ruling R103). The component comparisons `Aux61GPrime.ZeroComparisons`
of the normalized source — the `C`/`Cm` input of `Aux61Wnd.dyCover_of_normalized_capture` and
`Aux61WndCap.dyCover_of_finiteRestrict_capture` — from the access hypothesis **without fibre
clauses**: almost surely on each selected record every window point is an own collar point
(`OwnCollarPointNP`) or a counterflow collar access (`CfAccessNP`). Compared with COMPARE's
`Aux61Cmp.normalizedComparisons`, the clause "every physical preimage of the landing point lies in the
collar" is dropped on both sides, so pinch points of the counterflow hull (and of the own hull) need
not be excluded: that half of R103's open step is not needed.

* `source_componentComparisons_of_germs`: every field of the component record from the actual source
  coupling and retained references (as `Aux61GChoice16.source_comparisons_of_past_germs`), with the
  component germ cover as the only input;
* `componentGermCover_of_access`: that cover from the pinch-free accesses (`Aux61NjGerm`);
* **`normalizedComparisonsNP`**: the `C` input for the normalized source;
* **`dyCover_of_finiteRestrict_capture_access`**: the Theorem-top fibre leaf from restart choices,
  their window data, the installed seed heights, the pinch-free access hypothesis and the existential
  capture.

Conditional on the access hypothesis (R101/R103) and the capture; R48: no Theorem 1.2/1.3 input;
R77: no post-contact kernel. Nothing here replaces a source statement.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Nj
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61GChoice16 Aux61ULoc Aux61Marks
open LawUnique GlueCond LocalSets WholeField Aux61Asm2 Aux61SlitWX Aux61FibData Aux61Cmp Aux61ChLoc
open InteractingSLE.Theorem14.SB.FinRel
universe u

/-- **The component comparison record from component germs**: every mean and marked-union field is
constructed from the actual source coupling and the retained references exactly as in
`Aux61GChoice16.source_comparisons_of_past_germs`; the cover is the component germ cover. -/
theorem source_componentComparisons_of_germs
    (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι) (q : ℚ) (hq : F.start i = rationalTime q)
    (hsets : Measurable[(S.marksData F).baseMarks i 0, hittingSigma]
      ((S.marksData F).baseSets i 0))
    (hretained : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)))
    (hgerms : ∀ᵐ x ∂S.μ, (S.marksData F).Z i x ∈ (S.marksData F).B i →
      ∀ b ∈ ((S.marksData F).data i).O₀,
      ∃ (j : SourceReferenceIndex) (z₀ : ℂ),
        z₀ ∈ sourceReferenceSet S (pastReferenceIndex q j) x ∪ {z : ℂ | z.im = 0} ∧
        (∃ r > 0, ∀ᶠ z in 𝓝[H] (b : ℂ), ((S.marksData F).chart i x).2.1 z ∈
          freeNear ((S.marksData F).baseSets i 0 x) (sourceReferenceSet S (pastReferenceIndex q j) x)
            z₀ r) ∧
        Tendsto ((S.marksData F).chart i x).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
        Tendsto (fun z => sourceReferenceMean S (pastReferenceIndex q j) x
          (((S.marksData F).chart i x).2.1 z) + (S.marksData F).scale +
          (S.marksData F).constant * ((S.marksData F).chart i x).2.2
            (((S.marksData F).chart i x).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
          (𝓝[H] (b : ℂ)) (𝓝 0)) :
    Nonempty (Aux61GPrime.ZeroComparisons (S.marksData F) i) := by
  obtain ⟨g, hg, hh, hp⟩ := exists_source_reference_family S F i
  exact ⟨{
    index := SourceReferenceIndex
    countable := inferInstance
    patch := fun j => sourceReferenceSet S (pastReferenceIndex q j)
    patchMean := fun j => g (pastReferenceIndex q j)
    physicalMean := fun j => sourceReferenceMean S (pastReferenceIndex q j)
    union := pastReferenceUnion S F i q
    unionMarks := fun _ => (S.marksData F).baseMarks i 0
    event := fun _ => univ
    patch_measurable := fun j => measurable_sourceReferenceSet S (pastReferenceIndex q j)
    patch_closed := fun j => ae_of_all _ (sourceReferenceSet_closed S (pastReferenceIndex q j))
    patch_unbounded := fun j => ae_of_all _ (sourceReferenceSet_unbounded S (pastReferenceIndex q j))
    patch_mean := fun j => hg (pastReferenceIndex q j)
    physical_harmonic := fun j => hh (pastReferenceIndex q j)
    represents := fun j => hp (pastReferenceIndex q j)
    union_marks_le := fun _ => nullMarks_le
    union_measurable := fun j => past_union_recorded S F hR i q hq hsets j
    union_closed := fun j => past_union_closed S F hR i q j
    union_local := fun j => past_union_local S F hR i q hq hsets hretained j
    marks_le := fun _ => le_rfl
    set_recorded := fun _ => hsets
    set_subset := fun _ _ => inter_subset_left.trans subset_union_left
    patch_recorded := fun j => past_reference_recorded S F hR.chart_measurable i q hq j
    patch_subset := fun _ _ => inter_subset_left.trans subset_union_right
    event_measurable := fun _ => MeasurableSet.univ
    union_eq := fun j => by
      filter_upwards [past_union_eq S F hR i q hq hretained j] with x hx _
      exact hx
    cover := by
      filter_upwards [hgerms] with x hx he b hb
      obtain ⟨j, z, hz, hr, hl, hm⟩ := hx he b hb
      exact ⟨j, z, mem_univ _, hz, hr, hl, hm⟩ }⟩

variable {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}

/-- **The component germ cover from pinch-free accesses.** -/
theorem componentGermCover_of_access
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι) (q : ℚ) (hq : F.start i = rationalTime q)
    (hleft : PiecewiseConstantBoundaryData.leftLim (F.data i).bR 0 = -sleLambda (F.data i).κ)
    (hright : PiecewiseConstantBoundaryData.rightLim (F.data i).bR 0 = sleLambda (F.data i).κ)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (hcf : ∀ᵐ p ∂S.μ, cfW S p 0 = 0 ∧ ∃ γ : ℝ → ℂ, IsLoewnerTrace (cfW S p) γ)
    (haccess : ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i →
      ∀ b ∈ ((S.marksData F).data i).O₀, OwnCollarPointNP S F i p b ∨ CfAccessNP S F i p b) :
    ∀ᵐ x ∂S.μ, (S.marksData F).Z i x ∈ (S.marksData F).B i →
      ∀ b ∈ ((S.marksData F).data i).O₀,
      ∃ (j : SourceReferenceIndex) (z₀ : ℂ),
        z₀ ∈ sourceReferenceSet S (pastReferenceIndex q j) x ∪ {z : ℂ | z.im = 0} ∧
        (∃ r > 0, ∀ᶠ z in 𝓝[H] (b : ℂ), ((S.marksData F).chart i x).2.1 z ∈
          freeNear ((S.marksData F).baseSets i 0 x) (sourceReferenceSet S (pastReferenceIndex q j) x)
            z₀ r) ∧
        Tendsto ((S.marksData F).chart i x).2.1 (𝓝[H] (b : ℂ)) (𝓝 z₀) ∧
        Tendsto (fun z => sourceReferenceMean S (pastReferenceIndex q j) x
          (((S.marksData F).chart i x).2.1 z) + (S.marksData F).scale +
          (S.marksData F).constant * ((S.marksData F).chart i x).2.2
            (((S.marksData F).chart i x).2.1 z) - Aux61GlueK.refMean0 ((S.marksData F).data i) z)
          (𝓝[H] (b : ℂ)) (𝓝 0) := by
  filter_upwards [haccess, ownComponentGerm_of_access hR i q hq hleft hright hgeometry,
    cfComponentGerm_of_access hR i hgeometry hcf] with p hacc hown hcfg hB b hb
  rcases hacc hB b hb with h | h
  · obtain ⟨z₀, h₁, h₂, h₃, h₄⟩ := hown hB b h
    exact ⟨.inl q, z₀, h₁, h₂, h₃, h₄⟩
  · obtain ⟨z₀, h₁, h₂, h₃, h₄⟩ := hcfg hB b h
    exact ⟨.inr (), z₀, h₁, h₂, h₃, h₄⟩

/-! ### The normalized source -/

variable (D : R1Restart S) (h : D.HasChart) (R : ReaderFacts D)

include R in
/-- **Component comparisons for the normalized source from pinch-free accesses.** -/
theorem normalized_componentComparisons_of_access (hTip : OwnTipForwardLimit S)
    (V : WindowData D h) (hExit : PhysicalExit D h)
    (hleft : ∀ i, PiecewiseConstantBoundaryData.leftLim (D.data i).bR 0 = -sleLambda (D.data i).κ)
    (hright : ∀ i, PiecewiseConstantBoundaryData.rightLim (D.data i).bR 0 = sleLambda (D.data i).κ)
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource D h)).Z i p ∈ (S.marksData (normSource D h)).B i →
      ∀ b ∈ ((S.marksData (normSource D h)).data i).O₀,
        OwnCollarPointNP S (normSource D h) i p b ∨ CfAccessNP S (normSource D h) i p b)
    (i : (normSource D h).ι) :
    Nonempty (Aux61GPrime.ZeroComparisons (S.marksData (normSource D h)) i) := by
  have hR := Aux61GCaptureNext.normalized_cut_restart D h R hTip V hExit
  have hTa := Aux61GCaptureNext.normalized_contact_rule D h R
  have hTam := fun i => measurable_contactRule
    (measurable_infDist_retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
    (rationalTime (D.q i))
  have hTaG := fun i => isGalmarinoRule_contactRule
    (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (rationalTime (D.q i))
  have hgeo : ∀ᵐ p ∂S.μ, p ∈ (normSource D h).event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1)
        (fun t => S.path p.1 t.toNNReal) (cfHullQ (rationalTime S.s) p.2)
        ((normSource D h).start i)
        (sourceChart (normSource D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
    filter_upwards [R.ae_geometry h i] with p hp he
    exact hp he.1
  have hretained : ∀ᵐ p ∂S.μ, p ∈ (normSource D h).event i →
      (((S.marksData (normSource D h)).chart i p).dom : Set ℂ) ⊆ H \ (cfHullQ (rationalTime S.s) p.2 ∪
        (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 ((normSource D h).start i : ℝ)) := by
    filter_upwards [hgeo] with p hp he
    exact (hp he).retained
  exact source_componentComparisons_of_germs S (normSource D h) hR i (D.q i) rfl
    (sets_marks_cut_of hR hTam hTaG hTa i 0) hretained
    (componentGermCover_of_access hR i (D.q i) rfl (hleft i) (hright i) hgeo (ae_cfW_trace S)
      (haccess i))

/-- **The `C` input of `Aux61Wnd.dyCover_of_normalized_capture` from pinch-free accesses**: the
installed words' seed heights and, almost surely on each selected record, every window point an own
collar point or a counterflow collar access, **without** the fibre clauses of
`Aux61Cmp.normalizedComparisons`. -/
def normalizedComparisonsNP (hTip : OwnTipForwardLimit S) (V : WindowData D h)
    (hExit : PhysicalExit D h)
    (hleft : ∀ i, PiecewiseConstantBoundaryData.leftLim (D.data i).bR 0 = -sleLambda (D.data i).κ)
    (hright : ∀ i, PiecewiseConstantBoundaryData.rightLim (D.data i).bR 0 = sleLambda (D.data i).κ)
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource D h)).Z i p ∈ (S.marksData (normSource D h)).B i →
      ∀ b ∈ ((S.marksData (normSource D h)).data i).O₀,
        OwnCollarPointNP S (normSource D h) i p b ∨ CfAccessNP S (normSource D h) i p b) :
    ∀ i, Aux61GPrime.ZeroComparisons (S.marksData (cutSource S (source D h))) i := fun i =>
  Classical.choice
    (normalized_componentComparisons_of_access D h R hTip V hExit hleft hright haccess i)

/-! ### The fibre cover -/

open Aux61R1C Aux61SlitWX Aux61WndCap in
/-- **The Theorem-top fibre leaf from pinch-free accesses** (`Aux61WndCap.dyCover_of_finiteRestrict_capture`
with its component comparisons `Cm` supplied by `normalizedComparisonsNP`): for restart choices `C`
with Borel selections, their window data, the installed words' seed heights `∓λ`, the pinch-free
access hypothesis on the finite-buffer restriction, and the existential capture. -/
theorem dyCover_of_finiteRestrict_capture_access (C : ∀ S : SourceSetting.{u}, RestartChoices S)
    (hsel : ∀ S, ∀ i, MeasurableSet ((C S).selected i))
    (V : ∀ S : SourceSetting.{u}, WindowData (finiteRestart (C S))
      (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)
    (hleft : ∀ S : SourceSetting.{u}, ∀ i,
      PiecewiseConstantBoundaryData.leftLim ((finiteRestart (C S)).data i).bR 0 =
        -sleLambda ((finiteRestart (C S)).data i).κ)
    (hright : ∀ S : SourceSetting.{u}, ∀ i,
      PiecewiseConstantBoundaryData.rightLim ((finiteRestart (C S)).data i).bR 0 =
        sleLambda ((finiteRestart (C S)).data i).κ)
    (haccess : ∀ S : SourceSetting.{u}, ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource (finiteRestart (C S))
        (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)).Z i p ∈
        (S.marksData (normSource (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)).B i →
      ∀ b ∈ ((S.marksData (normSource (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart)).data i).O₀,
        OwnCollarPointNP S (normSource (finiteRestart (C S))
            (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart) i p b ∨
          CfAccessNP S (normSource (finiteRestart (C S))
            (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart) i p b)
    (hcaptured_cover : ∀ S : SourceSetting.{u}, ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, Aux61GRec.completedCapture
        (S.marksData (cutSource S (source (finiteRestart (C S))
          (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart))) i p) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_finiteRestrict_capture C hsel V
    (fun S => normalizedComparisonsNP (finiteRestart (C S))
      (Aux61SlitWAC.restrictChoices (C S) (finiteRestrict (C S))).hasChart
      (Aux61SlitWZ.readers _ (selected_measurable_finiteRestrict (C S) (hsel S)))
      (Aux61SlitWY.ownTipForwardLimit S) (V S) (physicalExit_finiteRestrict (C S) (hsel S))
      (hleft S) (hright S) (haccess S))
    hcaptured_cover

end InteractingSLE.Sec5.Aux61Nj
