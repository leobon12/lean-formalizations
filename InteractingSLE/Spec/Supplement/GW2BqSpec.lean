/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BqRead

/-!
# The near family's exit cell contains its buffer and its initial state

Packet PROVE-GW2-BUF (round 14). **`cellOf_spec`**: suppose the record's shape and padded positions are those of a
near crossing family `f`. Then the record's exit cell buffer contains `nearBuffer f n`, and it contains the initial
comparison state `(0, f.xL, f.xR)`. The controlled initial gaps are at least `min 3 f.η > 0`, by the family's
orientation clause and the label bounds `hxL`/`hxR`. So an admissible level exists, and the least one is admissible.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw GW2TipSystem GW2TipSystem.RootN4 GW2JDetR11 Supp12.DSReach

variable {κ : ℝ} (f : NearCrossingFamily.{u} κ) (n : ℕ) {shape : RecData → NearShape} {posL posR : RecData → ℕ → ℝ}
  {y : RecData}

/-- **Every controlled initial gap of a near family is at least `min 3 η`.** -/
theorem ctrl_gaps (hsh : famShapeB f = shape y) :
    (∀ i : Fin f.nL, ctrlL (shape y) i → min 3 f.η ≤ -f.xL i) ∧
      ∀ j : Fin f.nR, ctrlR (shape y) j → min 3 f.η ≤ f.xR j := by
  rw [← hsh]
  rcases f.horientation with ⟨hg, hmR, hxRpos, _, hxLc, _, _⟩ | ⟨hg, hmL, hxLneg, _, hxRc, _, _⟩
  · refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · simp only [ctrlL, famShapeB, hg, ↓reduceIte] at hi
      have := hxLc i hi
      exact (min_le_left _ _).trans (by linarith)
    · simp only [ctrlR, famShapeB, hg, ↓reduceIte] at hj
      have hj' : j = ⟨f.nR - 1, Nat.sub_lt f.hnR one_pos⟩ :=
        Fin.ext (le_antisymm (by show (j : ℕ) ≤ f.nR - 1; have := j.2; omega) hj)
      rw [hj']
      exact (min_le_right _ _).trans (f.hxR _ (ne_of_gt hxRpos))
  · refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · simp only [ctrlL, famShapeB, hg, Bool.false_eq_true, ↓reduceIte] at hi
      have hi' : i = ⟨f.nL - 1, Nat.sub_lt f.hnL one_pos⟩ :=
        Fin.ext (le_antisymm (by show (i : ℕ) ≤ f.nL - 1; have := i.2; omega) hi)
      rw [hi']
      have := f.hxL _ (ne_of_lt hxLneg)
      exact (min_le_right _ _).trans (by linarith)
    · simp only [ctrlR, famShapeB, hg, Bool.false_eq_true, ↓reduceIte] at hj
      have := hxRc j hj
      exact (min_le_left _ _).trans this

theorem exists_levOK (hsh : famShapeB f = shape y) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) : ∃ k, LevOK n shape posL posR k y := by
  have hδ : 0 < min (min 3 f.η) (1 / ((n : ℝ) + 1)) := lt_min (lt_min (by norm_num) f.hη) (by positivity)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  have hk1 : (1 / 2 : ℝ) ^ k < min 3 f.η := hk.trans_le (min_le_left _ _)
  have hk2 : (1 / 2 : ℝ) ^ k < 1 / ((n : ℝ) + 1) := hk.trans_le (min_le_right _ _)
  obtain ⟨hgL, hgR⟩ := ctrl_gaps f hsh
  have hnL : (shape y).1 = f.nL := (congrArg (fun K : NearShape => K.1) hsh).symm
  have hnR : (shape y).2.1 = f.nR := (congrArg (fun K : NearShape => K.2.1) hsh).symm
  refine ⟨k, hk2.le, fun i hi hc => ?_, fun j hj hc => ?_⟩
  · have hi' : i < f.nL := hnL ▸ hi
    have h1 := hgL ⟨i, hi'⟩ hc
    rw [hL] at h1
    linarith
  · have hj' : j < f.nR := hnR ▸ hj
    have h1 := hgR ⟨j, hj'⟩ hc
    rw [hR] at h1
    linarith

/-- **The near family's exit cell contains its buffer and its initial state.** -/
theorem cellOf_spec (hsh : famShapeB f = shape y) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) :
    bufOfShape (famShapeB f) n ⊆ cellBuf (famShapeB f, radOf n shape posL posR y, levOf n shape posL posR y) ∧
      ((0 : ℝ), f.xL, f.xR) ∈ cellBuf (famShapeB f, radOf n shape posL posR y, levOf n shape posL posR y) := by
  classical
  have hex := exists_levOK f n hsh hL hR
  have hlev : LevOK n shape posL posR (levOf n shape posL posR y) y := by
    simp only [levOf, hex, ↓reduceDIte]
    exact Nat.find_spec hex
  have hnL : (shape y).1 = f.nL := (congrArg (fun K : NearShape => K.1) hsh).symm
  have hnR : (shape y).2.1 = f.nR := (congrArg (fun K : NearShape => K.2.1) hsh).symm
  set R := radOf n shape posL posR y with hRdef
  set k := levOf n shape posL posR y with hkdef
  set S := ∑ i ∈ Finset.range (shape y).1, |posL y i| + ∑ j ∈ Finset.range (shape y).2.1, |posR y j| with hS
  have hRS : S < (R : ℝ) := by
    have h1 : S ≤ (⌈S⌉₊ : ℝ) := Nat.le_ceil S
    have h2 : (R : ℝ) = (n : ℝ) + 1 + (⌈S⌉₊ : ℝ) := by rw [hRdef, radOf]; push_cast; ring
    rw [h2]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hS0L : ∑ i ∈ Finset.range (shape y).1, |posL y i| ≤ S :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => abs_nonneg _)
  have hS0R : ∑ j ∈ Finset.range (shape y).2.1, |posR y j| ≤ S :=
    le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hboxL : ∀ i : Fin f.nL, |f.xL i| < (R : ℝ) := fun i => by
    rw [hL]
    have hi : (i : ℕ) ∈ Finset.range (shape y).1 := Finset.mem_range.2 (by rw [hnL]; exact i.2)
    have := Finset.single_le_sum (f := fun i => |posL y i|) (fun _ _ => abs_nonneg _) hi
    linarith
  have hboxR : ∀ j : Fin f.nR, |f.xR j| < (R : ℝ) := fun j => by
    rw [hR]
    have hj : (j : ℕ) ∈ Finset.range (shape y).2.1 := Finset.mem_range.2 (by rw [hnR]; exact j.2)
    have := Finset.single_le_sum (f := fun j => |posR y j|) (fun _ _ => abs_nonneg _) hj
    linarith
  have hR0 : (0 : ℝ) < R := lt_of_le_of_lt (by positivity) hRS
  have hnR' : n ≤ R := by rw [hRdef, radOf]; omega
  refine ⟨bufOfShape_subset_cellBuf _ hnR' hlev.1, ?_⟩
  obtain ⟨-, hlevL, hlevR⟩ := hlev
  have hgL : ∀ i : Fin f.nL, ctrlL (shape y) i → (1 / 2 : ℝ) ^ k < 0 - f.xL i := fun i hc => by
    rw [zero_sub, hL]
    exact hlevL i (by rw [hnL]; exact i.2) hc
  have hgR : ∀ j : Fin f.nR, ctrlR (shape y) j → (1 / 2 : ℝ) ^ k < f.xR j - 0 := fun j hc => by
    rw [sub_zero, hR]
    exact hlevR j (by rw [hnR]; exact j.2) hc
  have hbox : InBox (R : ℝ) ((0 : ℝ), f.xL, f.xR) := ⟨by simpa using hR0, hboxL, hboxR⟩
  unfold cellBuf
  rw [← hsh] at hgL hgR
  by_cases hg : f.goLeft = true
  · simp only [famShapeB, hg, ↓reduceIte]
    refine ⟨hbox, fun j hj => hgR j ?_, fun i hi => hgL i ?_⟩
    · simp only [ctrlR, famShapeB, hg, ↓reduceIte]; exact hj
    · simp only [ctrlL, famShapeB, hg, ↓reduceIte]; exact hi
  · simp only [famShapeB, hg, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hbox, fun j hj => hgR j ?_, fun i hi => hgL i ?_⟩
    · simp only [ctrlR, famShapeB, hg, Bool.false_eq_true, ↓reduceIte]; exact hj
    · simp only [ctrlL, famShapeB, hg, Bool.false_eq_true, ↓reduceIte]; exact hi

end InteractingSLE.Theorem14.GW2Bh
