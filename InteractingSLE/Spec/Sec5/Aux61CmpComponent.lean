/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CmpCover
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextNormalized

/-! # Component comparisons for the normalized R1 source (ruling R102)

`Aux61Wnd.dyCover_of_normalized_capture` takes component comparisons
`Aux61GPrime.ZeroComparisons` for every index of the normalized cut source
`cutSource S (source D h)`.

* `toComponent`: a full-ball comparison record is a component one, as soon as
  the inverse chart avoids the zero-time marked set (the record's own
  `union_eq`/`patch_subset` put every patch inside that set, so the free
  component of a full-ball-contained landing never meets it).
* `normalized_fullBall_of_access`: the full-ball records for the normalized
  source from collar accesses, with every restart, geometry and
  marked-measurability prerequisite taken from the landed normalized-capture
  facts (`normalized_cut_restart`, `ReaderFacts.ae_geometry`, `sets_marks_cut_of`).
* `normalizedComparisons_of_access`: the exact `C` input of
  `dyCover_of_normalized_capture` from the seed heights and the access
  hypothesis (every window point an own collar point or a counterflow germ).

Conditional on the access hypothesis (R101); no source statement is replaced.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cmp
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61GChoice16 Aux61ChLoc
open Aux61Asm2 Aux61SlitWX Aux61FibData Aux61Marks Aux61ULoc LawUnique GlueCond
universe u v

/-- **Full-ball comparisons are component comparisons** once the inverse
chart maps `ℍ` off the zero-time marked set on the selected records. -/
def toComponent {X : Type v} [mX : MeasurableSpace X] {μ : Measure X} {D : MarksData μ} {i : D.ι}
    (C : Aux61GAlign.ZeroComparisons D i)
    (hdom : ∀ᵐ x ∂μ, D.Z i x ∈ D.B i → ∀ z ∈ H,
      (D.chart i x).2.1 z ∈ H ∧ (D.chart i x).2.1 z ∉ D.baseSets i 0 x) :
    Aux61GPrime.ZeroComparisons D i where
  index := C.index
  countable := C.countable
  patch := C.patch
  patchMean := C.patchMean
  physicalMean := C.physicalMean
  union := C.union
  unionMarks := C.unionMarks
  event := C.event
  patch_measurable := C.patch_measurable
  patch_closed := C.patch_closed
  patch_unbounded := C.patch_unbounded
  patch_mean := C.patch_mean
  physical_harmonic := C.physical_harmonic
  represents := C.represents
  union_marks_le := C.union_marks_le
  union_measurable := C.union_measurable
  union_closed := C.union_closed
  union_local := C.union_local
  marks_le := C.marks_le
  set_recorded := C.set_recorded
  set_subset := C.set_subset
  patch_recorded := C.patch_recorded
  patch_subset := C.patch_subset
  event_measurable := C.event_measurable
  union_eq := C.union_eq
  cover := by
    have : Countable C.index := C.countable
    have hu : ∀ᵐ x ∂μ, ∀ j, x ∈ C.event j → C.union j x = D.baseSets i 0 x :=
      ae_all_iff.2 C.union_eq
    filter_upwards [C.cover, hdom, hu] with x hx hd hu' hB b hb
    obtain ⟨j, z₀, hev, hz₀, ⟨r, hr, hsub⟩, hland, hgerm⟩ := hx hB b hb
    refine ⟨j, z₀, hev, hz₀, ⟨r, hr, ?_⟩, hland, hgerm⟩
    have hball : ∀ᶠ z in 𝓝[H] (b : ℂ), (D.chart i x).2.1 z ∈ ball z₀ r :=
      hland (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hball, self_mem_nhdsWithin] with z hzb hzH
    obtain ⟨hcH, hcA⟩ := hd hB z hzH
    have hnp : (D.chart i x).2.1 z ∉ C.patch j x := fun hp =>
      hcA (by rw [← hu' j hev]; exact C.patch_subset j x ⟨hp, hcH⟩)
    refine ⟨⟨⟨hcH, hnp⟩, hzb⟩, ?_⟩
    rw [Set.disjoint_left]
    intro w hw hwA
    have hw' := connectedComponentIn_subset _ _ hw
    exact hw'.1.2 (hsub ⟨hwA, hw'.2⟩)

variable {S : SourceSetting.{u}} (D : R1Restart S) (h : D.HasChart) (R : ReaderFacts D)

/-- The normalized cut source. -/
abbrev normSource (D : R1Restart S) (h : D.HasChart) : SourceRestartData S.Ω S.nL S.nR :=
  cutSource S (source D h)

include R in
/-- On the selected records of the normalized source the inverse chart maps
`ℍ` into the complement of the zero-time marked set. -/
theorem normalized_inverse_avoids (hTip : OwnTipForwardLimit S) (V : WindowData D h)
    (hExit : PhysicalExit D h) (i : (normSource D h).ι) :
    ∀ᵐ x ∂S.μ, (S.marksData (normSource D h)).Z i x ∈ (S.marksData (normSource D h)).B i →
      ∀ z ∈ H, ((S.marksData (normSource D h)).chart i x).2.1 z ∈ H ∧
        ((S.marksData (normSource D h)).chart i x).2.1 z ∉
          (S.marksData (normSource D h)).baseSets i 0 x := by
  have hR := Aux61GCaptureNext.normalized_cut_restart D h R hTip V hExit
  filter_upwards [hR.physical_stop i, source_zero_alive_iff S (normSource D h) hR i]
    with x hstop halive hB z hz
  have hsel : sourceRecord (normSource D h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i x ∈
      (normSource D h).selected i := hB
  have hc : ((S.marksData (normSource D h)).chart i x).IsConformal := (hR.spec i).conf x (hstop hsel).1
  have hlive : x ∈ liveEv ((S.marksData (normSource D h)).Z i) ((S.marksData (normSource D h)).B i)
      ((S.marksData (normSource D h)).code i) 0 :=
    ⟨hB, by rw [ENNReal.coe_zero]; exact halive.2 hsel⟩
  rw [baseSets_zero_eq S (normSource D h) hc hlive]
  have hd : ((S.marksData (normSource D h)).chart i x).2.1 z ∈
      ((S.marksData (normSource D h)).chart i x).dom := by
    rw [← SetLike.mem_coe, hc.coe_dom]
    exact mem_image_of_mem _ hz
  exact ⟨hc.2.1 hz, fun h' => h'.2 hd⟩

include R in
/-- **Full-ball comparison records for the normalized source from collar
accesses.** All prerequisites come from the landed normalized-capture facts. -/
theorem normalized_fullBall_of_access (hTip : OwnTipForwardLimit S) (V : WindowData D h)
    (hExit : PhysicalExit D h)
    (hleft : ∀ i, PiecewiseConstantBoundaryData.leftLim (D.data i).bR 0 = -sleLambda (D.data i).κ)
    (hright : ∀ i, PiecewiseConstantBoundaryData.rightLim (D.data i).bR 0 = sleLambda (D.data i).κ)
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource D h)).Z i p ∈ (S.marksData (normSource D h)).B i →
      ∀ b ∈ ((S.marksData (normSource D h)).data i).O₀,
        OwnCollarPoint S (normSource D h) i p b ∨ CounterGerm S (normSource D h) i p b)
    (i : (normSource D h).ι) :
    Nonempty (Aux61GAlign.ZeroComparisons (S.marksData (normSource D h)) i) := by
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
  exact source_comparisons_of_past_germs S (normSource D h) hR i (D.q i) rfl
    (sets_marks_cut_of hR hTam hTaG hTa i 0) hretained
    (pastGermCover_of_access hR i (D.q i) rfl (hleft i) (hright i) hgeo (haccess i))

/-- **The `C` input of `Aux61Wnd.dyCover_of_normalized_capture`** (ruling R102)
from the canonical seed heights of the installed words and the access
hypothesis on the selected records. -/
def normalizedComparisons_of_access (hTip : OwnTipForwardLimit S) (V : WindowData D h)
    (hExit : PhysicalExit D h)
    (hleft : ∀ i, PiecewiseConstantBoundaryData.leftLim (D.data i).bR 0 = -sleLambda (D.data i).κ)
    (hright : ∀ i, PiecewiseConstantBoundaryData.rightLim (D.data i).bR 0 = sleLambda (D.data i).κ)
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (normSource D h)).Z i p ∈ (S.marksData (normSource D h)).B i →
      ∀ b ∈ ((S.marksData (normSource D h)).data i).O₀,
        OwnCollarPoint S (normSource D h) i p b ∨ CounterGerm S (normSource D h) i p b) :
    ∀ i, Aux61GPrime.ZeroComparisons (S.marksData (cutSource S (source D h))) i := fun i =>
  toComponent (Classical.choice
    (normalized_fullBall_of_access D h R hTip V hExit hleft hright haccess i))
    (normalized_inverse_avoids D h R hTip V hExit i)

end InteractingSLE.Sec5.Aux61Cmp
