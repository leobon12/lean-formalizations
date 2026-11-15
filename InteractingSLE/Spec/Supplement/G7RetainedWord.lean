/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7RetainedMeas
import InteractingSLE.Spec.Supplement.S9DW2

/-!
# Lemma G7: re-indexing kernels, and a word that also records a position

Packet PROVE-G7. Two measure-theoretic tools for passing from a two-path retained-pair kernel (datum
`(c, w) : BoundaryWord × ℝ`, `w` the chart position of the first tip) to the one-path carrier of Lemma G7 (datum a
`BoundaryWord`):

* `map_prodMap_compProd`: if `g ∘ f = id`, then `(μ ⊗ₘ κ).map (f × id) = μ.map f ⊗ₘ κ.comap g`;
* `wordEnc : BoundaryWord × ℝ ≃ᵐ BoundaryWord`: a measurable equivalence that stores `w` in the position slot `n`
  of the word (the slots from `n` on are shifted by one). Positions and heights at indices `< n` (positions) and
  `≤ n` (heights) are unchanged, so the boundary function and the jump set are those of `c`
  (`fn_wordEnc`, `jumps_wordEnc`). Conditioning on `wordEnc (c, w)` is conditioning on `(c, w)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

open Restart

/-! ### Re-indexing a disintegration -/

/-- **Re-indexing a composition-product along a map with a measurable left inverse.** -/
theorem map_prodMap_compProd {α γ β : Type*} [MeasurableSpace α] [MeasurableSpace γ] [MeasurableSpace β]
    {μ : Measure α} [IsFiniteMeasure μ] {κ : Kernel α β} [IsMarkovKernel κ] {f : α → γ} {g : γ → α}
    (hf : Measurable f) (hg : Measurable g) (hgf : ∀ a, g (f a) = a) :
    (μ ⊗ₘ κ).map (Prod.map f id) = μ.map f ⊗ₘ κ.comap g hg := by
  refine Measure.ext_prod fun {s} {t} hs ht => ?_
  rw [Measure.map_apply (hf.prodMap measurable_id) (hs.prod ht),
    show Prod.map f id ⁻¹' (s ×ˢ t) = (f ⁻¹' s) ×ˢ t from rfl, Measure.compProd_apply_prod (hf hs) ht,
    Measure.compProd_apply_prod hs ht, setLIntegral_map hs (Kernel.measurable_coe _ ht) hf]
  simp only [Kernel.comap_apply, hgf]

/-! ### Words recording a position -/

/-- Insert `w` at index `n` (shifting the later entries up). -/
def insertAt (n : ℕ) (w : ℝ) (p : ℕ → ℝ) (i : ℕ) : ℝ := if i < n then p i else if i = n then w else p (i - 1)

/-- Remove the entry at index `n` (shifting the later entries down). -/
def removeAt (n : ℕ) (p : ℕ → ℝ) (i : ℕ) : ℝ := if i < n then p i else p (i + 1)

theorem removeAt_insertAt (n : ℕ) (w : ℝ) (p : ℕ → ℝ) : removeAt n (insertAt n w p) = p := by
  funext i
  unfold removeAt insertAt
  by_cases hi : i < n
  · simp [hi]
  · have h1 : ¬ i + 1 < n := by omega
    have h2 : i + 1 ≠ n := by omega
    simp [hi, h1, h2]

theorem insertAt_removeAt (n : ℕ) (p : ℕ → ℝ) : insertAt n (p n) (removeAt n p) = p := by
  funext i
  unfold removeAt insertAt
  by_cases hi : i < n
  · simp [hi]
  · by_cases hin : i = n
    · simp [hin]
    · have h1 : ¬ i - 1 < n := by omega
      have h2 : i - 1 + 1 = i := by omega
      simp [hi, hin, h1, h2]

theorem insertAt_of_lt {n i : ℕ} (hi : i < n) (w : ℝ) (p : ℕ → ℝ) : insertAt n w p i = p i := by
  simp [insertAt, hi]

theorem measurable_insertAt_apply (i : ℕ) :
    Measurable fun c : BoundaryWord × ℝ => insertAt c.1.1 c.2 c.1.2.1 i := by
  unfold insertAt
  have hs : ∀ P : ℕ → Prop, MeasurableSet {c : BoundaryWord × ℝ | P c.1.1} := fun P =>
    (measurable_fst.fst) (MeasurableSet.of_discrete (s := {n : ℕ | P n}))
  refine Measurable.ite (hs fun n => i < n) ((measurable_pi_apply i).comp measurable_fst.snd.fst) ?_
  exact Measurable.ite (hs fun n => i = n) measurable_snd ((measurable_pi_apply (i - 1)).comp measurable_fst.snd.fst)

theorem measurable_removeAt_apply (i : ℕ) :
    Measurable fun c : BoundaryWord => removeAt c.1 c.2.1 i := by
  unfold removeAt
  have hs : MeasurableSet {c : BoundaryWord | i < c.1} :=
    measurable_fst (MeasurableSet.of_discrete (s := {n : ℕ | i < n}))
  exact Measurable.ite hs ((measurable_pi_apply i).comp measurable_snd.fst)
    ((measurable_pi_apply (i + 1)).comp measurable_snd.fst)

theorem measurable_eval_index : Measurable fun c : BoundaryWord => c.2.1 c.1 := by
  have h : Measurable fun q : (ℕ → ℝ) × ℕ => q.1 q.2 :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  exact h.comp (measurable_snd.fst.prodMk measurable_fst)

/-- **The word recording a position**: `(c, w) ↦ c` with `w` stored in its position slot `n`. -/
def wordEnc : BoundaryWord × ℝ ≃ᵐ BoundaryWord where
  toFun c := (c.1.1, insertAt c.1.1 c.2 c.1.2.1, c.1.2.2)
  invFun c := ((c.1, removeAt c.1 c.2.1, c.2.2), c.2.1 c.1)
  left_inv c := by
    obtain ⟨⟨n, p, q⟩, w⟩ := c
    simp only [removeAt_insertAt]
    simp [insertAt]
  right_inv c := by
    obtain ⟨n, p, q⟩ := c
    simp only [insertAt_removeAt]
  measurable_toFun := measurable_fst.fst.prodMk
    ((measurable_pi_iff.2 fun i => measurable_insertAt_apply i).prodMk measurable_fst.snd.snd)
  measurable_invFun := (measurable_fst.prodMk ((measurable_pi_iff.2 fun i => measurable_removeAt_apply i).prodMk
    measurable_snd.snd)).prodMk measurable_eval_index

theorem wordEnc_apply (c : BoundaryWord × ℝ) : wordEnc c = (c.1.1, insertAt c.1.1 c.2 c.1.2.1, c.1.2.2) := rfl

theorem index_wordEnc (c : BoundaryWord × ℝ) (y : ℝ) : (wordEnc c).index y = c.1.index y := by
  simp only [BoundaryWord.index, wordEnc_apply]
  congr 1
  exact Finset.filter_congr fun i hi => by rw [insertAt_of_lt (Finset.mem_range.1 hi)]

theorem fn_wordEnc (c : BoundaryWord × ℝ) : (wordEnc c).fn = c.1.fn := by
  funext y
  simp only [BoundaryWord.fn, index_wordEnc]
  rfl

theorem jumps_wordEnc (c : BoundaryWord × ℝ) : (wordEnc c).jumps = c.1.jumps := by
  simp only [BoundaryWord.jumps, wordEnc_apply]
  exact Finset.image_congr fun i hi => insertAt_of_lt (Finset.mem_range.1 hi) _ _

end Supp7

end InteractingSLE
