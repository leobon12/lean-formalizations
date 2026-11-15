/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Extension
import InteractingSLE.Spec.Sec5.Aux61SlitWABSeedData

/-! # Uniform Borel seed pieces for the canonical chart

The recorded old boundary and inverse extension are already constructed.
Positive seed clearance is localized by the existing collar-piece theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61FibData Aux61GInst LawUnique
universe u

/-- The actual model distance on certified retained records. -/
def recordDistance (S : SourceSetting.{u}) (t : GoodTime S)
    (a : ℝ) (y : certifiedRecords S t) : ℝ :=
  infDist (boundedInverse (recordChart S t y.1) (a : ℂ))
    (Aux61SlitWAB.recordBoundary (rationalTime S.s) y.1.1)

theorem measurable_recordDistance (S : SourceSetting.{u}) (t : GoodTime S) (a : ℝ) :
    Measurable (recordDistance S t a) := by
  have hm : Measurable (fun y : certifiedRecords S t =>
      boundedInverse (recordChart S t y.1) (a : ℂ)) := by
    have h := (measurable_recordChart_inverse S t a).comp
      (measurable_subtype_coe : Measurable (Subtype.val : certifiedRecords S t → SourceRecord S.nL S.nR))
    have heq : (fun y : certifiedRecords S t => (certifiedRecords S t).indicator
        (fun y => boundedInverse (recordChart S t y) (a : ℂ)) y.1) =
        (fun y : certifiedRecords S t => boundedInverse (recordChart S t y.1) (a : ℂ)) :=
      funext fun y => indicator_of_mem y.2 _
    change Measurable (fun y : certifiedRecords S t => (certifiedRecords S t).indicator
      (fun y => boundedInverse (recordChart S t y) (a : ℂ)) y.1) at h
    rwa [heq] at h
  exact measurable_comp_of_continuous_of_measurable
    (u := fun z (y : certifiedRecords S t) =>
      infDist z (Aux61SlitWAB.recordBoundary (rationalTime S.s) y.1.1))
    (fun _ => continuous_infDist_pt _)
    (Aux61SlitWAB.measurable_infDist_recordBoundary (baseChoices S t.1) (baseIndex S t)) hm

theorem continuous_recordDistance (S : SourceSetting.{u}) (t : GoodTime S)
    (y : certifiedRecords S t) : Continuous (fun a => recordDistance S t a y) :=
  (continuous_infDist_pt _).comp ((recordChart_extension S t y.2).2.comp_continuous
    Complex.continuous_ofReal (fun a => by change 0 ≤ (a : ℂ).im; simp only [Complex.ofReal_im, le_refl]))

/-- Certified records with positive distance at the normalized seed. -/
def seedRecords (S : SourceSetting.{u}) (t : GoodTime S) : Set (SourceRecord S.nL S.nR) :=
  Subtype.val '' {y : certifiedRecords S t | 0 < recordDistance S t 0 y}

/-- A fixed Borel record piece with a fixed free closed seed collar. -/
def seedPiece (S : SourceSetting.{u}) (t : GoodTime S) (k : ℕ × ℕ) :
    Set (SourceRecord S.nL S.nR) :=
  Subtype.val '' collarPiece {y : certifiedRecords S t | 0 < recordDistance S t 0 y}
    (fun y a => recordDistance S t a y) k.1 k.2

theorem measurableSet_seedPiece (S : SourceSetting.{u}) (t : GoodTime S) (k : ℕ × ℕ) :
    MeasurableSet (seedPiece S t k) :=
  (measurableSet_certifiedRecords S t).subtype_image
    (measurableSet_collarPiece (measurableSet_lt measurable_const (measurable_recordDistance S t 0))
      (measurable_recordDistance S t) (fun y _ => continuous_recordDistance S t y) k.1 k.2)

theorem seedPieces_cover (S : SourceSetting.{u}) (t : GoodTime S) :
    seedRecords S t = ⋃ k, seedPiece S t k := by
  have hcov := collarPieces_cover
    (E := {y : certifiedRecords S t | 0 < recordDistance S t 0 y})
    (g := fun y a => recordDistance S t a y)
    (fun y _ => continuous_recordDistance S t y) (fun y hy => ?_)
  · unfold seedRecords seedPiece
    conv_lhs => rw [hcov, image_iUnion]
  · have ho : IsOpen {a : ℝ | 0 < recordDistance S t a y} :=
      isOpen_lt continuous_const (continuous_recordDistance S t y)
    obtain ⟨δ, hδ, hf⟩ := Metric.isOpen_iff.1 ho 0 hy
    exact ⟨δ, hδ, fun a ha => hf (by simpa only [mem_ball, Real.dist_eq, sub_zero] using ha)⟩

theorem seedPiece_subset (S : SourceSetting.{u}) (t : GoodTime S) (k : ℕ × ℕ) :
    seedPiece S t k ⊆ seedRecords S t := by
  rintro y ⟨z, hz, rfl⟩
  exact ⟨z, hz.1, rfl⟩

/-- Membership gives the actual uniform collar, with no geometric premise. -/
theorem seedPiece_free (S : SourceSetting.{u}) (t : GoodTime S) (k : ℕ × ℕ)
    {y : SourceRecord S.nL S.nR} (hy : y ∈ seedPiece S t k) {a : ℝ}
    (ha : |a| ≤ collarRadius k.1) :
    boundedInverse (recordChart S t y) (a : ℂ) ∉
      Aux61SlitWAB.recordBoundary (rationalTime S.s) y.1 := by
  obtain ⟨z, hz, rfl⟩ := hy
  have hp := positive_on_collarPiece hz ha
  intro hm
  exact hp.ne' (infDist_zero_of_mem hm)

end InteractingSLE.Sec5.Aux61GWindow17
