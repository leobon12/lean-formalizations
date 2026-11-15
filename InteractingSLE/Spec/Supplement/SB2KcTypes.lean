/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3StopCount
import InteractingSLE.Spec.Supplement.GW1ActiveStage

/-!
# Countable force types for the finite histories in SB2

The number of marks and the height array form a word's profile. Recentering
preserves this profile. A stopped word's profile depends only on its incoming
force type and angle, even though its mark positions depend on the whole record.
These facts give countable profiles, and hence countable force types, by finite
induction. The type and weight APIs are reused from `Supp8.Q3Stop`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist.Staged Exist.StagedLaw
open Supp8.Q3Stop

/-- A boundary word's mark count and height array, without its mark positions. -/
abbrev WordProfile := ℕ × (ℕ → ℝ)

/-- The profile of a word. -/
def wordProfile (c : BoundaryWord) : WordProfile := (c.1, c.2.2)

/-- Recentering changes only the positions of a word. -/
theorem wordProfile_shiftW (a : ℝ) (c : BoundaryWord) :
    wordProfile (BoundaryWord.shiftW a c) = wordProfile c := rfl

/-- The countable-height version of the zero-padding lemma used in GB6. -/
theorem countable_padded_of_countable {D : Set ℝ} (hD : D.Countable) (N : ℕ) :
    {a : ℕ → ℝ | (∀ i, a i ∈ D) ∧ ∀ i, N ≤ i → a i = 0}.Countable := by
  have : Countable D := hD.to_subtype
  refine (countable_range fun f : Fin N → D =>
    fun i : ℕ => if h : i < N then (f ⟨i, h⟩ : ℝ) else 0).mono ?_
  rintro a ⟨ha, ha0⟩
  refine ⟨fun i => ⟨a i, ha i⟩, funext fun i => ?_⟩
  by_cases hi : i < N
  · simp only [hi, ↓reduceDIte]
  · simp only [hi, ↓reduceDIte]
    exact (ha0 i (not_lt.1 hi)).symm

/-- Countably many heights give countably many bounded force types. -/
theorem countable_typeSet_of_countable (κ : ℝ) {Hs : Set ℝ}
    (hHs : Hs.Countable) (N : ℕ) : (typeSet κ Hs N).Countable := by
  have hD : (weightSet κ Hs).Countable :=
    (((hHs.image _).union (hHs.image _)).union (hHs.image2 hHs _)).insert 0
  have hA := countable_padded_of_countable hD N
  refine ((finite_Iic N).countable.prod
    ((finite_Iic N).countable.prod (hA.prod hA))).mono ?_
  rintro w ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, ⟨h3, h4⟩, ⟨h5, h6⟩⟩

/-- All force types permitted by a family of word profiles. -/
def profileTypes (κ : ℝ) (S : Set WordProfile) : Set WordType :=
  ⋃ p ∈ S, typeSet κ (range p.2) (p.1 + 1)

/-- A countable family of profiles allows only countably many force types. -/
theorem countable_profileTypes (κ : ℝ) {S : Set WordProfile}
    (hS : S.Countable) : (profileTypes κ S).Countable := by
  exact hS.biUnion fun p _ =>
    countable_typeSet_of_countable κ (countable_range p.2) (p.1 + 1)

/-- A word with a permitted profile has a permitted force type. -/
theorem wordType_mem_profileTypes (κ : ℝ) {S : Set WordProfile} {c : BoundaryWord}
    (hc : wordProfile c ∈ S) : wordType κ c ∈ profileTypes κ S := by
  refine mem_iUnion.2 ⟨wordProfile c, mem_iUnion.2 ⟨hc, ?_⟩⟩
  exact wordType_mem_typeSet κ c (H := range c.2.2) (fun j => ⟨j, rfl⟩) le_rfl

/-- The profile after a stop, expressed using the incoming force type. -/
def stoppedProfile (κ θ : ℝ) (w : WordType) : WordProfile :=
  (w.1 + 1 + w.2.1,
    wordHeight κ w.1
      (fun i => w.2.2.1 i - if i = 0 then θ * QuantumZipper.chiC κ / sleLambda κ else 0)
      (fun j => w.2.2.2 j + if j = 0 then θ * QuantumZipper.chiC κ / sleLambda κ else 0)
      (θ * QuantumZipper.chiC κ))

/-- Stopping changes the profile independently of the geometric record. -/
theorem wordProfile_stopWord (κ θ : ℝ) (c : BoundaryWord) (r : RecData) :
    wordProfile (stopWord κ (c, θ, r)) = stoppedProfile κ θ (wordType κ c) := by
  have he := padFL_weights κ θ c.fn c.jumps
  change (flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0,
    wordHeight κ (flowLineNL c.fn c.jumps 0)
      (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2
      (θ * QuantumZipper.chiC κ)) = _
  rw [congrArg Prod.fst he, congrArg Prod.snd he]
  rfl

/-- The profiles obtained by stopping a word with one of the given profiles. -/
def stoppedProfiles (κ θ : ℝ) (S : Set WordProfile) : Set WordProfile :=
  stoppedProfile κ θ '' profileTypes κ S

theorem countable_stoppedProfiles (κ θ : ℝ) {S : Set WordProfile}
    (hS : S.Countable) : (stoppedProfiles κ θ S).Countable :=
  (countable_profileTypes κ hS).image _

/-- A stop and any subsequent real connector preserve the countable profile cover. -/
theorem wordProfile_shift_stop_mem (κ θ a : ℝ) {S : Set WordProfile}
    {c : BoundaryWord} (hc : wordProfile c ∈ S) (r : RecData) :
    wordProfile (BoundaryWord.shiftW a (stopWord κ (c, θ, r))) ∈
      stoppedProfiles κ θ S := by
  rw [wordProfile_shiftW, wordProfile_stopWord]
  exact ⟨wordType κ c, wordType_mem_profileTypes κ hc, rfl⟩

end InteractingSLE.Theorem14.SB.Lv
