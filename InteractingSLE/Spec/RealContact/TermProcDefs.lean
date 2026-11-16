/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermRecMeas
import InteractingSLE.Spec.Supplement.AStopProcFstMain

/-!
# The processes of the first path against the completed second path: definitions and good samples

Packet PROVE-RC-TERM, second run (ruling R124). For an own time `N` of the second path, a driver family `E` of the
second path, a capped version `ηc₂` of the second path and a measurable version `η₁'` of the first path:

* `pRec`, `pU`, `pT`: the record of the second driver at own time `N`, its driver and its time;
* `pRho₂`, `pRho₁`: the two paths recentred at their seeds; `pPath`, `pStop`: the chart path (`Term.kPath`) and the
  physical stop (`Term.kStop`) of the sample;
* `IsTermGood`: the pathwise facts at a sample (second lifetime `≤ N`, the hypotheses `IsKSample`, a good first path,
  the second version frozen after the lifetime);
* `IsTermGood.isAGood`, **`IsTermGood.pStop_eq`** (the stop is the first contact of the first version with
  `η₁'([0, 0]) ∪ ηc₂([0, N])`, the form of `RLC.AStopProc.measurableSet_lt_contStopA_of_prefix`);
* `exists_subset_isTermGood`: an almost surely good event of the retained σ-algebra has an everywhere good
  measurable sub-event of full relative measure.

R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open Restart Restart.RetAux79 Supp7 Exist.Staged Exist.StagedLaw Sec2.Assembly Sec7.Lemma76F RLC.AStopProc

section Defs

variable {Ω : Type*}

/-- The record of the second driver at own time `N`. -/
def pRec (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : RecData := recOf (N : ℝ≥0∞) (E ω)

/-- The record driver. -/
def pU (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : ℝ → ℝ := rdrv (pRec N E ω)

/-- The record time. -/
def pT (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : ℝ≥0 := (pRec N E ω).2.1.toNNReal

/-- The second path recentred at its seed, in real time. -/
def pRho₂ (ηc₂ : Ω → ℝ≥0 → ℂ) (x₂ : ℝ) (ω : Ω) : ℝ → ℂ := fun s => ηc₂ ω s.toNNReal - (x₂ : ℂ)

/-- The first path recentred at its seed. -/
def pRho₁ (η₁' : Ω → ℝ≥0 → ℂ) (x₁ : ℝ) (ω : Ω) : ℝ≥0 → ℂ := fun t => η₁' ω t - (x₁ : ℂ)

/-- The chart path of the sample. -/
def pPath (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ηc₂ η₁' : Ω → ℝ≥0 → ℂ) (ζ₁ : Ω → ℝ≥0∞) (x₁ x₂ : ℝ) (ω : Ω) :
    ℝ≥0 → ℂ :=
  kPath (pU N E ω) (pRho₂ ηc₂ x₂ ω) (pT N E ω) (x₁ - x₂) (pRho₁ η₁' x₁ ω) (ζ₁ ω)

/-- The physical stop of the sample. -/
def pStop (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ηc₂ η₁' : Ω → ℝ≥0 → ℂ) (ζ₁ : Ω → ℝ≥0∞) (x₁ x₂ : ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  kStop (pRho₂ ηc₂ x₂ ω) (pT N E ω) (x₁ - x₂) (pRho₁ η₁' x₁ ω) (ζ₁ ω)

theorem rtime_pRec (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : rtime (pRec N E ω) = (pT N E ω : ℝ) := rfl

/-- **A good sample** (see the module docstring). -/
structure IsTermGood (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ηc₂ η₁' : Ω → ℝ≥0 → ℂ) (ζ₁ : Ω → ℝ≥0∞)
    (x₁ x₂ : ℝ) (ω : Ω) : Prop where
  life : (E ω).2 ≤ N
  sample : ∃ (q : ℝ) (w : ℝ≥0 → ℝ), q < 0 ∧
    IsKSample (pU N E ω) (pT N E ω) (pRho₂ ηc₂ x₂ ω) q (x₁ - x₂) w (ζ₁ ω) (pRho₁ η₁' x₁ ω)
  path : IsPathGood (η₁' ω) (ζ₁ ω) x₁
  frozen : ∀ s : ℝ≥0, pT N E ω ≤ s → ηc₂ ω s = ηc₂ ω (pT N E ω)
  cont : Continuous (ηc₂ ω)

namespace IsTermGood

variable {N : ℝ≥0} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ηc₂ η₁' : Ω → ℝ≥0 → ℂ} {ζ₁ : Ω → ℝ≥0∞} {x₁ x₂ : ℝ} {ω : Ω}
  (g : IsTermGood N E ηc₂ η₁' ζ₁ x₁ x₂ ω)
include g

omit g in
theorem pT_le : pT N E ω ≤ N := by
  have h1 : (pRec N E ω).2.1 ≤ (N : ℝ≥0∞) := by
    change min (N : ℝ≥0∞) (E ω).2 ≤ N
    exact min_le_left _ _
  have h2 := ENNReal.toNNReal_mono ENNReal.coe_ne_top h1
  rwa [ENNReal.toNNReal_coe] at h2

theorem isAGood : IsAGood (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) ω := by
  obtain ⟨q, w, -, hs⟩ := g.sample
  exact (hs.isAGood (Ω := Ω) ω).congr rfl rfl

/-- The second version up to `N` is its image up to the record time. -/
theorem image_Icc_N : ηc₂ ω '' Icc 0 N = ηc₂ ω '' Icc 0 (pT N E ω) := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    rcases le_total s (pT N E ω) with h | h
    · exact ⟨s, ⟨hs.1, h⟩, rfl⟩
    · exact ⟨pT N E ω, ⟨zero_le, le_rfl⟩, (g.frozen s h).symm⟩
  · exact image_mono (Icc_subset_Icc_right pT_le)

/-- **The physical stop is the first contact of the first version with the retained union at `(0, N)`.** -/
theorem pStop_eq : pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω =
    contStop (η₁' ω) (ζ₁ ω) 0 (η₁' ω '' Icc 0 0 ∪ ηc₂ ω '' Icc 0 N) := by
  have hinj := g.path.1
  have hset : contSet (fun t => reflectC (pRho₁ η₁' x₁ ω t)) (ζ₁ ω) 0
      (retSet (fun s => reflectC (pRho₂ ηc₂ x₂ ω s)) (pT N E ω) (x₁ - x₂)) =
      contSet (η₁' ω) (ζ₁ ω) 0 (η₁' ω '' Icc 0 0 ∪ ηc₂ ω '' Icc 0 N) := by
    ext t
    refine and_congr_right fun _ => and_congr_right fun htζ => forall_congr' fun t' =>
      forall_congr' fun ht'0 => forall_congr' fun ht't => not_congr ?_
    have hmem := mem_retSet_iff (η₁' ω) (ηc₂ ω) x₁ x₂ (pT N E ω) t'
    refine hmem.trans ?_
    rw [g.image_Icc_N]
    constructor
    · exact fun h => Or.inr h
    · rintro (⟨s, hs, hse⟩ | h)
      · exfalso
        have hs0 : s = 0 := le_antisymm hs.2 hs.1
        rw [hs0] at hse
        have ht'ζ : (t' : ℝ≥0∞) ≤ ζ₁ ω := (ENNReal.coe_le_coe.2 ht't.le).trans htζ
        exact ht'0.ne' (hinj ht'ζ (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ ω from zero_le) hse.symm)
      · exact h
  show contStop _ _ _ _ = contStop _ _ _ _
  unfold contStop
  rw [hset]

theorem pStop_pos : 0 < pStop N E ηc₂ η₁' ζ₁ x₁ x₂ ω := g.isAGood.pos

end IsTermGood

end Defs

section Sub

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **An almost surely good event of the retained σ-algebra has an everywhere good measurable sub-event** of full
relative measure. -/
theorem exists_subset_of_ae {u r : ℝ≥0} {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] M)
    {p : Ω → Prop} (hp : ∀ᵐ ω ∂P, ω ∈ M → p ω) :
    ∃ M' ⊆ M, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] M' ∧ (∀ᵐ ω ∂P, ω ∈ M → ω ∈ M') ∧ ∀ ω ∈ M', p ω := by
  classical
  set Good : Set Ω := {ω | ω ∈ M → p ω} with hGood
  set G' : Set Ω := (toMeasurable P Goodᶜ)ᶜ with hG'
  have hG'sub : G' ⊆ Good := fun ω hω => by
    by_contra h'
    exact hω (subset_toMeasurable P _ h')
  have hG'm : MeasurableSet G' := (measurableSet_toMeasurable P _).compl
  have hG'ae : ∀ᵐ ω ∂P, ω ∈ G' := by
    rw [ae_iff]
    have : {ω | ¬ ω ∈ G'} = toMeasurable P Goodᶜ := by ext ω; simp [hG']
    rw [this, measure_toMeasurable]
    exact ae_iff.1 hp
  have hG'R : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] G' := by
    apply measurableSet_retSigma76_congr hG'm (@MeasurableSet.univ Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r))
    filter_upwards [hG'ae] with ω hω
    exact propext ⟨fun _ => trivial, fun _ => hω⟩
  refine ⟨M ∩ G', inter_subset_left, hM.inter hG'R, ?_, fun ω hω => hG'sub hω.2 hω.1⟩
  filter_upwards [hG'ae] with ω hω hM
  exact ⟨hM, hω⟩

end Sub

end Term

end InteractingSLE.RealContact
