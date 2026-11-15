/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Process.Filtration
import Mathlib.Order.Filter.CountableInter

/-!
# Proposition 5.9 at depth `ℓ`, step S3: the Galmarino filtration

Packet PROVE-STAGED-S3. The restarted image word after the last switch is observed in a filtration whose events, on
each pre-contact window `E i r` (the dyadic own time `i` is before contact and the restarted image time `r` is
before its capacity), agree almost surely with an event of the marks `𝓜 i` of S2 at the own time `i`. Defining the
filtration by this property makes the marks transfer of S3 (CROSSCOND-THETA's `ImgMarksThetaStatement`) hold by
construction; what remains is that the observed processes are adapted to it.

* `galSet`, **`galSigma`** (a σ-algebra when every window is itself a.s. an `𝓜 i`-event), `galSigma_le`,
  **`galFilt`** (a filtration when the windows shrink in `r`), `measurableSet_galFilt_iff`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace InteractingSLE.Sec5.CrossCond.StagedS3

variable {X : Type*} [mX : MeasurableSpace X] {ι : Type*}

/-- **A Galmarino event**: measurable, and on each window `E i` almost surely equal to an `𝓜 i`-event. -/
def galSet (μ : Measure X) (𝓜 : ι → MeasurableSpace X) (E : ι → Set X) (A : Set X) : Prop :=
  MeasurableSet A ∧ ∀ i, ∃ B, MeasurableSet[𝓜 i] B ∧ B =ᵐ[μ] (A ∩ E i : Set X)

/-- **The Galmarino σ-algebra** of the windows `E i` and the marks `𝓜 i` (each window a.s. an `𝓜 i`-event). -/
@[instance_reducible]
def galSigma (μ : Measure X) (𝓜 : ι → MeasurableSpace X) (E : ι → Set X)
    (hE : ∀ i, ∃ B, MeasurableSet[𝓜 i] B ∧ B =ᵐ[μ] E i) : MeasurableSpace X where
  MeasurableSet' := galSet μ 𝓜 E
  measurableSet_empty := ⟨MeasurableSet.empty, fun i => ⟨∅, @MeasurableSet.empty X (𝓜 i), by simp⟩⟩
  measurableSet_compl A hA := by
    refine ⟨hA.1.compl, fun i => ?_⟩
    obtain ⟨B, hB, hBe⟩ := hA.2 i
    obtain ⟨C, hC, hCe⟩ := hE i
    refine ⟨C \ B, hC.diff hB, (hCe.diff hBe).trans ?_⟩
    refine Eventually.of_forall fun x => ?_
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, eq_iff_iff]
    tauto
  measurableSet_iUnion f hf := by
    refine ⟨MeasurableSet.iUnion fun n => (hf n).1, fun i => ?_⟩
    choose B hB hBe using fun n => (hf n).2 i
    refine ⟨⋃ n, B n, MeasurableSet.iUnion hB, (EventuallyEqSet.countable_iUnion hBe).trans ?_⟩
    rw [iUnion_inter]

theorem measurableSet_galSigma_iff {μ : Measure X} {𝓜 : ι → MeasurableSpace X} {E : ι → Set X}
    {hE : ∀ i, ∃ B, MeasurableSet[𝓜 i] B ∧ B =ᵐ[μ] E i} {A : Set X} :
    MeasurableSet[galSigma μ 𝓜 E hE] A ↔ galSet μ 𝓜 E A := Iff.rfl

theorem galSigma_le {μ : Measure X} {𝓜 : ι → MeasurableSpace X} {E : ι → Set X}
    (hE : ∀ i, ∃ B, MeasurableSet[𝓜 i] B ∧ B =ᵐ[μ] E i) : galSigma μ 𝓜 E hE ≤ mX := fun _ hA => hA.1

/-- **The Galmarino filtration** of windows `E i r` shrinking in `r`. -/
def galFilt (μ : Measure X) (𝓜 : ι → MeasurableSpace X) (E : ι → ℝ≥0 → Set X)
    (hE : ∀ i r, ∃ B, MeasurableSet[𝓜 i] B ∧ B =ᵐ[μ] E i r) (hmono : ∀ i, Antitone (E i)) :
    Filtration ℝ≥0 mX where
  seq r := galSigma μ 𝓜 (fun i => E i r) fun i => hE i r
  mono' r r' hrr' A hA := by
    refine ⟨hA.1, fun i => ?_⟩
    obtain ⟨B, hB, hBe⟩ := hA.2 i
    obtain ⟨C, hC, hCe⟩ := hE i r'
    refine ⟨B ∩ C, hB.inter hC, (hBe.inter hCe).trans (Eventually.of_forall fun x => ?_)⟩
    have hsub := hmono i hrr'
    simp only [mem_inter_iff, eq_iff_iff]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hsub h.2⟩, h.2⟩⟩
  le' r := galSigma_le fun i => hE i r

theorem measurableSet_galFilt_iff {μ : Measure X} {𝓜 : ι → MeasurableSpace X} {E : ι → ℝ≥0 → Set X}
    {hE : ∀ i r, ∃ B, MeasurableSet[𝓜 i] B ∧ B =ᵐ[μ] E i r} {hmono : ∀ i, Antitone (E i)} {r : ℝ≥0}
    {A : Set X} :
    MeasurableSet[galFilt μ 𝓜 E hE hmono r] A ↔
      MeasurableSet A ∧ ∀ i, ∃ B, MeasurableSet[𝓜 i] B ∧ B =ᵐ[μ] (A ∩ E i r : Set X) := Iff.rfl

end InteractingSLE.Sec5.CrossCond.StagedS3
