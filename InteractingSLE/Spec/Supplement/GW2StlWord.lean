/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2StlInt
import InteractingSLE.Spec.Supplement.GW2JDetR5Stages

/-!
# GW2's stage lines, part 3: the stage word map has countably many types

Packet PROVE-GW2-STAGEMEAN, stage-lines round (targets `measurable_β`, `countable_wordType`, `isSorted` of
PROVE-GW2-SDE's `GW2Sde.StageInst.Good`). The stage word of stage `n` is the root word flowed through the stopped
pieces `0, …, n − 1` (each piece contributes `stopWord κ (·, θ_j, record_j)`, R5's `GW2JDetR5.stageWord`) and raised by
the angle of the stage piece (`GW2Rd.upW`). Its word type must range over a countable set. A word's type only reads
its boundary function and jumps, and a flow through a stopped piece produces finitely many heights from finitely many
heights, independently of the piece record:

* `HasShape H N c` (heights at the indices `≤ c.1` in `H`, at most `N` positions) and the clamped word `clampW c` (same
  boundary function and jumps, every height in `H`); **`wordType_mem_typeSet_of_shape`**,
  **`countable_range_wordType_of_shape`**;
* `finite_padded`, `padFL_fst_mem`, `padFL_snd_mem`, `padFL_fst_eq_zero`, `padFL_snd_eq_zero`: the padded flow-line
  weights at any angle of a word of shape `(H, N)` lie in a finite set and vanish from `N + 1` on;
* **`exists_hasShape_stopWord`**: for a finite `H`, the words `stopWord κ (c, θ, r)` of all `c` of shape `(H, N)` and
  all records `r` have one common shape `(H', 2N + 3)` with `H'` finite; `hasShape_upW`;
* **`exists_hasShape_stageWord`**: the stage words `GW2JDetR5.stageWord W₀ θ n x` of a root word map of bounded shape
  have, for every `n`, one common finite shape;
* **`stageWordMap_targets`**: for `β y = upW e (stageWord W₀ θ n (dec y))` with measurable decoder and root word map,
  sorted root words and bounded root shapes: `Measurable β`, countably many word types, every word sorted.

Deterministic. Conditional helper with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Stl

open Restart Exist.Staged Exist.StagedLaw Supp8.Q3Stop GW2Rd

/-! ### Shapes and word types -/

/-- **The shape of a word**: its heights at the indices `≤ c.1` lie in `H` and it has at most `N` positions. -/
def HasShape (H : Set ℝ) (N : ℕ) (c : BoundaryWord) : Prop :=
  (∀ j ≤ c.1, c.2.2 j ∈ H) ∧ c.1 ≤ N

/-- The word with its heights frozen from the last index on. -/
def clampW (c : BoundaryWord) : BoundaryWord := (c.1, c.2.1, fun j => c.2.2 (min j c.1))

theorem clampW_fn (c : BoundaryWord) : (clampW c).fn = c.fn := funext fun y => by
  change c.2.2 (min ((clampW c).index y) c.1) = c.2.2 (c.index y)
  have e : (clampW c).index y = c.index y := rfl
  rw [e, min_eq_left (c.index_le y)]

theorem clampW_jumps (c : BoundaryWord) : (clampW c).jumps = c.jumps := rfl

theorem wordType_clampW (κ : ℝ) (c : BoundaryWord) : wordType κ (clampW c) = wordType κ c := by
  simp only [wordType, clampW_fn, clampW_jumps]

/-- **A word of shape `(H, N)` has a type in `typeSet κ H (N + 1)`.** -/
theorem wordType_mem_typeSet_of_shape (κ : ℝ) {H : Set ℝ} {N : ℕ} {c : BoundaryWord} (hc : HasShape H N c) :
    wordType κ c ∈ typeSet κ H (N + 1) := by
  rw [← wordType_clampW]
  exact wordType_mem_typeSet κ (clampW c) (fun j => hc.1 _ (min_le_right _ _)) hc.2

/-- **Words of one finite shape take countably many types.** -/
theorem countable_range_wordType_of_shape (κ : ℝ) {X : Type*} {β : X → BoundaryWord} {H : Set ℝ} (hH : H.Finite)
    {N : ℕ} (hβ : ∀ x, HasShape H N (β x)) : (range fun x => wordType κ (β x)).Countable :=
  (countable_typeSet κ hH (N + 1)).mono (by rintro _ ⟨x, rfl⟩; exact wordType_mem_typeSet_of_shape κ (hβ x))

/-- Raising a word raises its shape. -/
theorem hasShape_upW {H : Set ℝ} {N : ℕ} {c : BoundaryWord} (hc : HasShape H N c) (a : ℝ) :
    HasShape ((fun x => x + a) '' H) N (upW a c) :=
  ⟨fun j hj => ⟨c.2.2 j, hc.1 j hj, rfl⟩, hc.2⟩

/-! ### The padded weights of a word of bounded shape -/

/-- Zero-padded sequences with values in a finite set form a finite set. -/
theorem finite_padded {D : Set ℝ} (hD : D.Finite) (N : ℕ) :
    {a : ℕ → ℝ | (∀ i, a i ∈ D) ∧ ∀ i, N ≤ i → a i = 0}.Finite := by
  have : Finite D := hD.to_subtype
  refine (Set.finite_range fun f : Fin N → D => fun i : ℕ => if h : i < N then (f ⟨i, h⟩ : ℝ) else 0).subset ?_
  rintro a ⟨ha, ha0⟩
  refine ⟨fun i => ⟨a i, ha i⟩, funext fun i => ?_⟩
  by_cases h : i < N
  · simp only [h, ↓reduceDIte]
  · simp only [h, ↓reduceDIte]
    exact (ha0 i (not_lt.1 h)).symm

/-- The angle-`0` left weights of a word of shape `(H, N)` lie in `weightSet κ H`. -/
theorem padFL_zero_fst_mem (κ : ℝ) {H : Set ℝ} {N : ℕ} {c : BoundaryWord} (hc : HasShape H N c) (i : ℕ) :
    (padFL κ 0 c.fn c.jumps).2.1 i ∈ weightSet κ H := by
  rw [← clampW_fn c, ← clampW_jumps c]
  simp only [padFL]
  split_ifs with h
  · exact flowLineRhoL_mem_weightSet κ (clampW c) (fun j => hc.1 _ (min_le_right _ _)) ⟨i, h⟩
  · exact mem_insert 0 _

/-- The angle-`0` right weights of a word of shape `(H, N)` lie in `weightSet κ H`. -/
theorem padFL_zero_snd_mem (κ : ℝ) {H : Set ℝ} {N : ℕ} {c : BoundaryWord} (hc : HasShape H N c) (j : ℕ) :
    (padFL κ 0 c.fn c.jumps).2.2 j ∈ weightSet κ H := by
  rw [← clampW_fn c, ← clampW_jumps c]
  simp only [padFL]
  split_ifs with h
  · exact flowLineRhoR_mem_weightSet κ (clampW c) (fun j => hc.1 _ (min_le_right _ _)) ⟨j, h⟩
  · exact mem_insert 0 _

/-- The possible left weights at angle `θ`. -/
def weightSetL (κ θ : ℝ) (H : Set ℝ) : Set ℝ :=
  image2 (fun a b => a - b) (weightSet κ H) {0, θ * QuantumZipper.chiC κ / sleLambda κ}

/-- The possible right weights at angle `θ`. -/
def weightSetR (κ θ : ℝ) (H : Set ℝ) : Set ℝ :=
  image2 (fun a b => a + b) (weightSet κ H) {0, θ * QuantumZipper.chiC κ / sleLambda κ}

theorem finite_weightSetL (κ θ : ℝ) {H : Set ℝ} (hH : H.Finite) : (weightSetL κ θ H).Finite :=
  (finite_weightSet κ hH).image2 _ (toFinite _)

theorem finite_weightSetR (κ θ : ℝ) {H : Set ℝ} (hH : H.Finite) : (weightSetR κ θ H).Finite :=
  (finite_weightSet κ hH).image2 _ (toFinite _)

theorem padFL_fst_mem (κ θ : ℝ) {H : Set ℝ} {N : ℕ} {c : BoundaryWord} (hc : HasShape H N c) (i : ℕ) :
    (padFL κ θ c.fn c.jumps).2.1 i ∈ weightSetL κ θ H := by
  rw [padFL_weights]
  refine ⟨_, padFL_zero_fst_mem κ hc i, _, ?_, rfl⟩
  split_ifs
  · exact mem_insert_of_mem _ rfl
  · exact mem_insert _ _

theorem padFL_snd_mem (κ θ : ℝ) {H : Set ℝ} {N : ℕ} {c : BoundaryWord} (hc : HasShape H N c) (j : ℕ) :
    (padFL κ θ c.fn c.jumps).2.2 j ∈ weightSetR κ θ H := by
  rw [padFL_weights]
  refine ⟨_, padFL_zero_snd_mem κ hc j, _, ?_, rfl⟩
  split_ifs
  · exact mem_insert_of_mem _ rfl
  · exact mem_insert _ _

theorem padFL_fst_eq_zero (κ θ : ℝ) {H : Set ℝ} {N : ℕ} {c : BoundaryWord} (hc : HasShape H N c) {i : ℕ}
    (hi : N + 1 ≤ i) : (padFL κ θ c.fn c.jumps).2.1 i = 0 := by
  have h := flowLineNL_le c
  have h2 := hc.2
  simp only [padFL]
  split_ifs with h'
  · omega
  · rfl

theorem padFL_snd_eq_zero (κ θ : ℝ) {H : Set ℝ} {N : ℕ} {c : BoundaryWord} (hc : HasShape H N c) {j : ℕ}
    (hj : N + 1 ≤ j) : (padFL κ θ c.fn c.jumps).2.2 j = 0 := by
  have h := flowLineNR_le c
  have h2 := hc.2
  simp only [padFL]
  split_ifs with h'
  · omega
  · rfl

/-! ### Flowing through a stopped piece -/

/-- **The words after a stopped piece have one finite shape**, uniformly in the input word of shape `(H, N)` and the
piece record. -/
theorem exists_hasShape_stopWord (κ θ : ℝ) {H : Set ℝ} (hH : H.Finite) (N : ℕ) :
    ∃ H' : Set ℝ, H'.Finite ∧ ∀ c : BoundaryWord, HasShape H N c → ∀ r : RecData,
      HasShape H' (2 * N + 3) (stopWord κ (c, θ, r)) := by
  set AL : Set (ℕ → ℝ) := {a | (∀ i, a i ∈ weightSetL κ θ H) ∧ ∀ i, N + 1 ≤ i → a i = 0} with hAL
  set AR : Set (ℕ → ℝ) := {a | (∀ i, a i ∈ weightSetR κ θ H) ∧ ∀ i, N + 1 ≤ i → a i = 0} with hAR
  have hALf : AL.Finite := finite_padded (finite_weightSetL κ θ hH) (N + 1)
  have hARf : AR.Finite := finite_padded (finite_weightSetR κ θ hH) (N + 1)
  set S : Set (ℕ × (ℕ → ℝ) × (ℕ → ℝ) × ℕ) := Iic (N + 1) ×ˢ AL ×ˢ AR ×ˢ Iic (2 * N + 3) with hS
  have hSf : S.Finite := (finite_Iic _).prod (hALf.prod (hARf.prod (finite_Iic _)))
  refine ⟨(fun p : ℕ × (ℕ → ℝ) × (ℕ → ℝ) × ℕ =>
    wordHeight κ p.1 p.2.1 p.2.2.1 (θ * QuantumZipper.chiC κ) p.2.2.2) '' S, hSf.image _, fun c hc r => ?_⟩
  have hL := flowLineNL_le c
  have hR := flowLineNR_le c
  have h1 : (stopWord κ (c, θ, r)).1 = flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0 := rfl
  have hN1 : (stopWord κ (c, θ, r)).1 ≤ 2 * N + 3 := by rw [h1]; have := hc.2; omega
  refine ⟨fun j hj => ?_, hN1⟩
  refine ⟨(flowLineNL c.fn c.jumps 0, (padFL κ θ c.fn c.jumps).2.1, (padFL κ θ c.fn c.jumps).2.2, j),
    ⟨?_, ⟨padFL_fst_mem κ θ hc, fun i hi => padFL_fst_eq_zero κ θ hc hi⟩,
      ⟨padFL_snd_mem κ θ hc, fun i hi => padFL_snd_eq_zero κ θ hc hi⟩, ?_⟩, rfl⟩
  · change flowLineNL c.fn c.jumps 0 ≤ N + 1
    have := hc.2
    omega
  · change j ≤ 2 * N + 3
    exact hj.trans hN1

/-- **R5's stage words of a root word map of bounded shape have, at every stage, one finite shape.** -/
theorem exists_hasShape_stageWord (κ : ℝ) {S : Type*} {W₀ : S → BoundaryWord} {H₀ : Set ℝ} (hH₀ : H₀.Finite)
    {N₀ : ℕ} (hW₀ : ∀ x, HasShape H₀ N₀ (W₀ x)) (θ : ℕ → ℝ) :
    ∀ n, ∃ H : Set ℝ, H.Finite ∧ ∃ N : ℕ, ∀ x, HasShape H N (GW2JDetR5.stageWord (κ := κ) W₀ θ n x)
  | 0 => ⟨H₀, hH₀, N₀, hW₀⟩
  | n + 1 => by
    obtain ⟨H, hH, N, hN⟩ := exists_hasShape_stageWord κ hH₀ hW₀ θ n
    obtain ⟨H', hH', hst⟩ := exists_hasShape_stopWord κ (θ n) hH N
    exact ⟨H', hH', 2 * N + 3, fun x => hst _ (hN x.1) x.2⟩

/-- **The targets `measurable_β`, `countable_wordType`, `isSorted` for a raised stage word map** read through a
measurable decoder of the record. -/
theorem stageWordMap_targets (κ : ℝ) {S : Type*} [MeasurableSpace S] {W₀ : S → BoundaryWord}
    (hW₀m : Measurable W₀) (hW₀s : ∀ x, (W₀ x).IsSorted) {H₀ : Set ℝ} (hH₀ : H₀.Finite) {N₀ : ℕ}
    (hW₀ : ∀ x, HasShape H₀ N₀ (W₀ x)) (θ : ℕ → ℝ) (n : ℕ) (e : ℝ) {dec : RecData → GW2JDetR5.Past S n}
    (hdec : Measurable dec) (k : ℝ) :
    Measurable (fun y => upW e (GW2JDetR5.stageWord (κ := κ) W₀ θ n (dec y))) ∧
      (range fun y => wordType k (upW e (GW2JDetR5.stageWord (κ := κ) W₀ θ n (dec y)))).Countable ∧
      ∀ y, (upW e (GW2JDetR5.stageWord (κ := κ) W₀ θ n (dec y))).IsSorted := by
  refine ⟨(measurable_upW e).comp ((GW2JDetR5.measurable_stageWord hW₀m θ n).comp hdec), ?_,
    fun y => isSorted_upW e (GW2JDetR5.isSorted_stageWord hW₀s θ n _)⟩
  obtain ⟨H, hH, N, hN⟩ := exists_hasShape_stageWord κ hH₀ hW₀ θ n
  exact countable_range_wordType_of_shape k (hH.image _) fun y => hasShape_upW (hN (dec y)) e

end InteractingSLE.Theorem14.GW2Stl
