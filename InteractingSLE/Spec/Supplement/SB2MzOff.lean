/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzRec

/-!
# The offset of the relative walk as a finite formula in the entry events

Packet PROVE-SB2-LCMEAN, round 15 (item 4, gluing over the offset). LIFTSET's offset `Lk.relOff` is the even stage of
the start configuration: the first entry of `R` into the walk's physical part (`Lk.entryStage`), halved down to even,
plus `2` at a restart mark. On the event that `R` has entered by stage `o + 1`, the event `relOff = o` is a finite
formula in the entry events `Ent n` (`R` in the physical part after `n + 1` instructions) for `n ≤ o + 1`, and in the
mark test at stage `2 ⌊e / 2⌋ + 1`. Hence it depends only on the runs up to `o + 2`:

* `Ent`, `relOffEvent` (`relOff = o` and `R` entered by `o + 1`), `relOffOf`;
* **`relOffEvent_iff`**: the formula;
* **`relOffEvent_congr`**: walks whose runs agree up to `o + 2` have the same offset event.

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Mz

open Exist Exist.Staged Exist.StagedLaw GW1Bookkeep

variable (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ)

/-- The entry event: `R` lies in the walk's physical part after `n + 1` instructions. -/
def Ent (R : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) : Prop :=
  (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D (n + 1))

/-- **The offset event**: the offset is `o` and `R` has entered by stage `o + 1`. -/
def relOffEvent (R : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (o : ℕ) : Prop :=
  Lk.relOff κ θ b₁ J₁ R D = o ∧ ∃ e ≤ o + 1, Ent κ θ b₁ J₁ R D e

open Classical in
/-- The offset when the first entry is at stage `e`. -/
def relOffOf (R : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (e : ℕ) : ℕ :=
  2 * (e / 2) + if e % 2 = 1 ∧
    R ∈ GW1W.restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D (2 * (e / 2) + 1))
  then 2 else 0

/-- The offset is `relOffOf` at the entry stage. -/
theorem relOff_eq_relOffOf (R : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    Lk.relOff κ θ b₁ J₁ R D = relOffOf κ θ b₁ J₁ R D (Lk.entryStage κ θ b₁ J₁ R D) := by
  classical
  unfold Lk.relOff relOffOf Lk.MarkEntry Lk.ArcEntry Lk.startOff
  by_cases hm : Lk.entryStage κ θ b₁ J₁ R D % 2 = 1 ∧ R ∈ GW1W.restartSet κ b₁ J₁
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D (2 * (Lk.entryStage κ θ b₁ J₁ R D / 2) + 1))
  · rw [ite_eq_left hm, ite_eq_left hm]
  · rw [ite_eq_right hm, ite_eq_right hm]

/-- **The offset event as a finite formula**: a first entry at some `e ≤ o + 1` with `relOffOf e = o`. -/
theorem relOffEvent_iff (R : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (o : ℕ) :
    relOffEvent κ θ b₁ J₁ R D o ↔ ∃ e ≤ o + 1, (Ent κ θ b₁ J₁ R D e ∧ ∀ n < e, ¬ Ent κ θ b₁ J₁ R D n) ∧
      relOffOf κ θ b₁ J₁ R D e = o := by
  classical
  constructor
  · rintro ⟨hrel, e', he', hent⟩
    have hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D (n + 1)) := ⟨e', hent⟩
    obtain ⟨hspec, hmin⟩ := Lk.entryStage_spec κ θ b₁ J₁ hex
    have hle : Lk.entryStage κ θ b₁ J₁ R D ≤ e' := by
      by_contra hlt
      exact hmin e' (lt_of_not_ge hlt) hent
    refine ⟨Lk.entryStage κ θ b₁ J₁ R D, hle.trans he', ⟨hspec, fun n hn => hmin n hn⟩, ?_⟩
    rw [← relOff_eq_relOffOf]
    exact hrel
  · rintro ⟨e, he, ⟨hent, hmin⟩, hrel⟩
    have hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D (n + 1)) := ⟨e, hent⟩
    have heq : Lk.entryStage κ θ b₁ J₁ R D = e := by
      have h1 : Lk.entryStage κ θ b₁ J₁ R D = Nat.find hex := by
        unfold Lk.entryStage
        simp only [hex, ↓reduceDIte]
      rw [h1, Nat.find_eq_iff]
      exact ⟨hent, fun n hn => hmin n hn⟩
    refine ⟨?_, e, he, hent⟩
    rw [relOff_eq_relOffOf, heq]
    exact hrel

/-- **Walks whose runs agree up to `o + 2` have the same offset event.** -/
theorem relOffEvent_congr (R : ℝ) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (o : ℕ)
    (h : ∀ n ≤ o + 2, ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D n =
      ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D' n) :
    relOffEvent κ θ b₁ J₁ R D o ↔ relOffEvent κ θ b₁ J₁ R D' o := by
  have hent : ∀ n ≤ o + 1, Ent κ θ b₁ J₁ R D n ↔ Ent κ θ b₁ J₁ R D' n := by
    intro n hn
    unfold Ent
    rw [h (n + 1) (by omega)]
  have hof : ∀ e ≤ o + 1, relOffOf κ θ b₁ J₁ R D e = relOffOf κ θ b₁ J₁ R D' e := by
    intro e he
    unfold relOffOf
    rw [h (2 * (e / 2) + 1) (by omega)]
  rw [relOffEvent_iff, relOffEvent_iff]
  constructor
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, he, ⟨(hent e he).1 h1, fun n hn h4 => h2 n hn ((hent n (by omega)).2 h4)⟩, (hof e he) ▸ h3⟩
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, he, ⟨(hent e he).2 h1, fun n hn h4 => h2 n hn ((hent n (by omega)).1 h4)⟩, (hof e he).symm ▸ h3⟩

end InteractingSLE.Theorem14.SB.Mz
