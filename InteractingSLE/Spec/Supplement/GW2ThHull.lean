/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TgLoc

/-!
# The explored curve and hull at a root `x` are marked local (time-ordered histories)

Packet PROVE-GW2-RELDET, the explored half of the stage layer at a nonzero root (ruling R113; PROVE-GW2-ROOTX's
decision D8 lists "RELDET locality at every root" under its option (A)). The physical explored set from the root `x`
is the translate `x + (explored trace)` (`GW2TfAsm.exists_schedPhysCurveX_of_timeOrdered`), in the ORIGINAL field.
The statements here are about these physical sets; they do not depend on the chart in which the stage is read.

* Translation by a real number: it preserves `ℍ` (`image_add_H`, `H_diff_image_add`), boundedness
  (`isBounded_image_add_iff`), fillings (**`isFilling_image_add`**) and turns avoidance events of a translate into
  avoidance events of the preimage of the open set (`disjoint_image_add_iff`).
* `schedCurveSX`, `schedHullX`: the sampled explored curve and the filled explored hull, translated to the root, on
  `oldSuccess`; `ℍ` off it. At root `0` they are round 19's `schedCurveS` and round 18's `schedHullL`.
* **`exists_schedCurveX_local`**, **`exists_schedHullX_local`**: both are marked local, with marks reading the
  history records, the explored path on `[0, q]` and the null sets, all field-determined. From Theorem 1.3, for every
  root and every time-ordered history.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField Supp8 GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 Sec5.Prop513Schedule

section Translate

variable (x : ℝ)

theorem mem_H_add_iff {z : ℂ} : (x : ℂ) + z ∈ H ↔ z ∈ H := by
  change 0 < ((x : ℂ) + z).im ↔ 0 < z.im
  rw [Complex.add_im, Complex.ofReal_im, zero_add]

theorem image_add_H : (fun z => (x : ℂ) + z) '' H = H := by
  ext w
  refine ⟨?_, fun hw => ⟨w - x, ?_, by ring⟩⟩
  · rintro ⟨z, hz, rfl⟩
    exact (mem_H_add_iff x).2 hz
  · rw [← mem_H_add_iff x]
    simpa only [add_sub_cancel] using hw

theorem H_diff_image_add (B : Set ℂ) :
    H \ (fun z => (x : ℂ) + z) '' B = (fun z => (x : ℂ) + z) '' (H \ B) := by
  rw [image_sdiff (add_right_injective (x : ℂ)) H B, image_add_H]

theorem isBounded_image_add_iff {S : Set ℂ} :
    Bornology.IsBounded ((fun z => (x : ℂ) + z) '' S) ↔ Bornology.IsBounded S := by
  have h1 : ∀ (a : ℂ) (T : Set ℂ), Bornology.IsBounded T → Bornology.IsBounded ((fun z => a + z) '' T) :=
    fun a T hT => by
      rw [← singleton_add]
      exact Bornology.isBounded_singleton.add hT
  refine ⟨fun h => ?_, h1 _ _⟩
  have e : S = (fun z => -(x : ℂ) + z) '' ((fun z => (x : ℂ) + z) '' S) := by
    rw [image_image]
    simp only [neg_add_cancel_left, image_id']
  rw [e]
  exact h1 _ _ h

/-- **Translation by a real number preserves fillings.** -/
theorem isFilling_image_add {K A : Set ℂ} (hKA : IsFilling K A) :
    IsFilling ((fun z => (x : ℂ) + z) '' K) ((fun z => (x : ℂ) + z) '' A) := by
  obtain ⟨⟨z, hz, hcc⟩, hunb⟩ := hKA
  have hzA : z ∈ H \ A := connectedComponentIn_nonempty_iff.1 ⟨z, hcc ▸ hz⟩
  refine ⟨⟨(x : ℂ) + z, ?_, ?_⟩, ?_⟩
  · rw [H_diff_image_add]
    exact mem_image_of_mem _ hz
  · rw [H_diff_image_add, H_diff_image_add, ← hcc]
    exact ((Homeomorph.addLeft (x : ℂ)).image_connectedComponentIn hzA).symm
  · rw [H_diff_image_add, isBounded_image_add_iff]
    exact hunb

theorem disjoint_image_add_iff {B U : Set ℂ} :
    Disjoint ((fun z => (x : ℂ) + z) '' B) U ↔ Disjoint B ((fun z => (x : ℂ) + z) ⁻¹' U) := by
  constructor
  · intro h
    exact disjoint_left.2 fun b hb hbU => disjoint_left.1 h ⟨b, hb, rfl⟩ hbU
  · intro h
    refine disjoint_left.2 ?_
    rintro _ ⟨b, hb, rfl⟩ hbU
    exact disjoint_left.1 h hb hbU

theorem isOpen_preimage_add {U : Set ℂ} (hU : IsOpen U) : IsOpen ((fun z => (x : ℂ) + z) ⁻¹' U) :=
  hU.preimage (continuous_const.add continuous_id)

theorem preimage_add_subset_H {U : Set ℂ} (hUH : U ⊆ H) : (fun z => (x : ℂ) + z) ⁻¹' U ⊆ H :=
  fun _ hz => (mem_H_add_iff x).1 (hUH hz)

end Translate

section Defs

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

open scoped Classical in
/-- The sampled explored curve on `[0, q]` translated to the root, where the history succeeded; `ℍ` elsewhere. -/
def schedCurveSX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  if oldSuccess c r l ω then (fun z => (rootPt r.1 : ℂ) + z) '' schedSamples c r l a q ω else H

open scoped Classical in
/-- The filled explored hull at `q` translated to the root, where the history succeeded; `ℍ` elsewhere. -/
def schedHullX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  if oldSuccess c r l ω then (fun z => (rootPt r.1 : ℂ) + z) '' schedHull c r l a q ω else H

end Defs

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The sampled explored curve at the root `x` is marked local** (time-ordered histories, Theorem 1.3). -/
theorem exists_schedCurveX_local (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hord : TimeOrdered 0 (historyProgram c r l))
    (u₀ : ℂ → ℝ) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀) (q : ℝ≥0) (hq : historyTime c r l ≤ q) :
    ∃ 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets c.P ≤ 𝓜.1 ∧
      (∀ t ≤ q, Measurable[𝓜.1] (schedW c r l a t)) ∧
      (∀ j : Fin ((entryList l).length + 1),
        Measurable[𝓜.1] (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j)) ∧
      𝓜.1 ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P ∧
      (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (schedCurveSX c r l a q ω) U}) ∧
      IsHistoryAvoidanceLocal 𝓜.1 (schedCurveSX c r l a q) (centredField c.h u₀) c.P := by
  classical
  obtain ⟨𝓜, hnull, hW, hrec, hd, S, hSm, hloc, hST⟩ :=
    exists_schedPhysCurveX_of_timeOrdered h13 c r l a hord u₀ hu₀ q hq
  set x : ℝ := rootPt r.1 with hx
  have hhm := measurable_centredField c.hh.1 u₀
  have hE : MeasurableSet[𝓜.1] {ω | oldSuccess c r l ω} := measurableSet_oldSuccess_of_records c r l 𝓜 hrec
  have hev0 : ∀ U : Opens ℂ, (U : Set ℂ) = ∅ → ∀ X : Ω → Set ℂ, {ω | Disjoint (X ω) U} = univ := by
    intro U hU X
    ext ω
    simp only [hU, mem_ofPred_eq, disjoint_empty, mem_univ]
  have hCm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[𝓜.1] {ω | Disjoint (schedCurveSX c r l a q ω) U} := by
    intro U hUH
    by_cases hU : (U : Set ℂ) = ∅
    · rw [hev0 U hU]
      exact MeasurableSet.univ
    · obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hU
      have e : {ω | Disjoint (schedCurveSX c r l a q ω) U} = {ω | oldSuccess c r l ω} ∩
          {ω | Disjoint (schedSamples c r l a q ω) ((fun z => (x : ℂ) + z) ⁻¹' (U : Set ℂ))} := by
        ext ω
        by_cases hω : oldSuccess c r l ω
        · simp only [schedCurveSX, hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, true_and]
          exact disjoint_image_add_iff x
        · simp only [schedCurveSX, hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, false_and, iff_false]
          exact fun hd' => disjoint_left.1 hd' (hUH hz) hz
      rw [e]
      exact hE.inter (measurableSet_disjoint_schedSamples c r l a 𝓜 hW (isOpen_preimage_add x U.isOpen))
  obtain ⟨hAm, hAloc⟩ := isHistoryAvoidanceLocal_ite_H hhm hloc hSm hd hE
  refine ⟨𝓜, hnull, hW, hrec, hd, hCm, isHistoryAvoidanceLocal_of_superset_marks hhm hAloc hAm hCm hd ?_⟩
  filter_upwards [hST, ae_schedSamples_eq c r l a h13 q] with ω hω hsω
  by_cases hωE : oldSuccess c r l ω
  · have h1 : (if oldSuccess c r l ω then S ω else H) = S ω := by
      simp only [hωE, ↓reduceIte]
    have h2 : schedCurveSX c r l a q ω = (fun s => (x : ℂ) + schedTr c r l a ω s) '' Icc 0 q := by
      simp only [schedCurveSX, hωE, ↓reduceIte, hsω, image_image]
      rfl
    rw [h1, h2]
    exact hω hωE
  · have h1 : (if oldSuccess c r l ω then S ω else H) = H := by
      simp only [hωE, ↓reduceIte]
    have h2 : schedCurveSX c r l a q ω = H := by simp only [schedCurveSX, hωE, ↓reduceIte]
    rw [h1, h2]
    exact inter_subset_left

/-- **The filled explored hull at the root `x` is marked local** (time-ordered histories, Theorem 1.3). -/
theorem exists_schedHullX_local (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hord : TimeOrdered 0 (historyProgram c r l))
    (u₀ : ℂ → ℝ) (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀) (q : ℝ≥0) (hq : historyTime c r l ≤ q) :
    ∃ 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets c.P ≤ 𝓜.1 ∧
      (∀ t ≤ q, Measurable[𝓜.1] (schedW c r l a t)) ∧
      (∀ j : Fin ((entryList l).length + 1),
        Measurable[𝓜.1] (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j)) ∧
      𝓜.1 ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P ∧
      (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (schedHullX c r l a q ω) U}) ∧
      IsHistoryAvoidanceLocal 𝓜.1 (schedHullX c r l a q) (centredField c.h u₀) c.P := by
  obtain ⟨𝓜, hnull, hW, hrec, hd, hSm, hloc⟩ := exists_schedCurveX_local h13 c r l a hord u₀ hu₀ q hq
  set x : ℝ := rootPt r.1 with hx
  have hE : MeasurableSet[𝓜.1] {ω | oldSuccess c r l ω} := measurableSet_oldSuccess_of_records c r l 𝓜 hrec
  have hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P :=
    isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hKm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet {ω | Disjoint ((fun z => (x : ℂ) + z) '' schedHull c r l a q ω) U} := by
    intro U hUH
    have e : {ω | Disjoint ((fun z => (x : ℂ) + z) '' schedHull c r l a q ω) U} =
        schedHull c r l a q ⁻¹' {K : Set ℂ | Disjoint K ((fun z => (x : ℂ) + z) ⁻¹' (U : Set ℂ))} := by
      ext ω
      exact disjoint_image_add_iff x
    rw [e]
    exact measurable_schedHull_of c r l a ⟨mΩ, le_rfl⟩ (fun t _ => measurable_schedW c r l a t)
      (measurableSet_avoid (isOpen_preimage_add x U.isOpen) (preimage_add_subset_H x hUH))
  have hgood : ∀ᵐ ω ∂c.P, ω ∈ {ω | oldSuccess c r l ω} →
      IsFilling ((fun z => (x : ℂ) + z) '' schedHull c r l a q ω) (schedCurveSX c r l a q ω) ∧
        IsOpen (H \ schedCurveSX c r l a q ω) ∧
        ∃ R : ℝ, {w : ℂ | R < w.im} ⊆ H \ (fun z => (x : ℂ) + z) '' schedHull c r l a q ω := by
    filter_upwards [ae_schedW_trace c r l a h13, ae_schedSamples_eq c r l a h13 q] with ω hω hsω hωE
    have hS : schedCurveSX c r l a q ω = (fun z => (x : ℂ) + z) '' schedSamples c r l a q ω := by
      simp only [schedCurveSX, show oldSuccess c r l ω from hωE, ↓reduceIte]
      rfl
    rw [hS]
    refine ⟨isFilling_image_add x ?_, ?_, ?_⟩
    · rw [hsω]
      exact hω.1.2.2 q ENNReal.coe_lt_top
    · rw [H_diff_image_add]
      exact isOpenMap_add_left (x : ℂ) _ (QuantumZipper.isOpen_H.sdiff isClosed_closure)
    · obtain ⟨R, hR⟩ :=
        exists_halfIm_subset_compl_fwdHull ((continuous_schedW c r l a ω).comp continuous_real_toNNReal) q
      refine ⟨R, fun w hw => ?_⟩
      rw [H_diff_image_add]
      refine ⟨w - x, hR ?_, by ring⟩
      change R < (w - x).im
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact hw
  obtain ⟨hAm, hAloc⟩ := isHistoryAvoidanceLocal_fill_on_ae (measurable_centredField c.hh.1 u₀) hh 𝓜.2 hnull hloc
    hSm hKm hd hE hgood
  exact ⟨𝓜, hnull, hW, hrec, hd, hAm, hAloc⟩

end InteractingSLE.Theorem14.GW2Rd
