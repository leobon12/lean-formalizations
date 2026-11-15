/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.PartialSums
import InteractingSLE.Spec.Sec4.ChartHeights
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# Lemmas 4.3 and 4.5: the noncollision part, conditional on Aux. lemma 6

Packet PROVE-SEC4-A (specification §4.1, `source/spec/p097-144.md` L211–L215 and L245–L280).

The first case of Lemma 4.3 (`a ≤ −Λ`) and Lemma 4.5 map the strip to `ℍ` (by `e^{πz} − 1` and by
`ψ = stripQ q`), check that every actual side partial sum of the half-plane force word is at least `c = k/2 − 2`,
and apply the noncolliding results of §2.2. Aux. lemma 6 (noncollision from ordered partial sums,
`source/spec/p001-048.md` L739–L765) is not yet in Lean (no packet has proved it; its proof needs Aux. lemma 5, the
localized repulsion criterion, via Itô's formula). It is stated here, with the source's exact content, as the
proposition `Aux6Statement` and used only as a named hypothesis of the two conditional helpers:

* `noncollision_of_aux6_expChart` (Lemma 4.3, `a ≤ −Λ`): the half-plane evolution has infinite lifetime and every
  force point (including the image `−1` of the left strip end) is separated from the driver at every positive time;
* `noncollision_of_aux6_stripQ` (Lemma 4.5): the same for the chart `ψ`, whose marks include the images `−1/q`, `1`
  of the strip ends.

What these helpers do not give, and why, is recorded in `planning/handoffs/PROVE-SEC4-A.md`: avoidance of the
upper boundary uses dense passive marks (an evolution of the word with added zero-weight marks), and the limits at
the target need Aux. lemma 7 ([Zha10, Theorems 4.2, 7.7]) and a continuous trace (Remark 2.3).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped NNReal ENNReal Real
open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace Sec4

/-- **Aux. lemma 6** (Specification §2.2, `source/spec/p001-048.md` L739–L740; noncollision from ordered partial
sums), as a proposition: for `c = k/2 − 2`, an integrated `SLE_k(ρ)` evolution of an ordered force word whose
amalgamated nonempty side partial sums are all at least `c` has infinite continuation threshold, and every force
point is strictly separated from the driver at every positive time. Either side may be empty; groups may start at
`0⁻` or `0⁺`. Not proved in Lean yet; used only as a named hypothesis. -/
def Aux6Statement (k : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞),
    IsOrderedForceWord xL xR → HasAdmissiblePartialSums k ρL ρR xL xR →
      IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω

/-! ### Boundary arcs of the two charts are covered by the images of boundary lines -/

/-- Every `y < −1` is `e^{π(x+i)} − 1` for some `x`. -/
theorem exists_expChart_upper {y : ℝ} (hy : y < -1) : ∃ x : ℝ, -Real.exp (π * x) - 1 = y := by
  refine ⟨Real.log (-y - 1) / π, ?_⟩
  rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log (by linarith)]; ring

/-- Every `y < −1/q` is the image of a point `x + i` of the upper line left of `z₀`, and every `y > 1` of a point
right of `z₀`: `y = (e^{πx} + 1)/(e^{πx} − q)` with `e^{πx} = (qy + 1)/(y − 1)`. -/
theorem exists_stripQ_upper {q y : ℝ} (hq : 0 < q) (hy : y < -(1 / q) ∨ 1 < y) :
    ∃ x : ℝ, (Real.exp (π * x) + 1) / (Real.exp (π * x) - q) = y ∧
      (y < -(1 / q) → Real.exp (π * x) < q) ∧ (1 < y → q < Real.exp (π * x)) := by
  have hy1 : y - 1 ≠ 0 := by
    rcases hy with h | h
    · have : 0 < 1 / q := by positivity
      linarith
    · linarith
  set e := (q * y + 1) / (y - 1) with he
  have hepos : 0 < e := by
    rcases hy with h | h
    · have hqy : q * y + 1 < 0 := by
        have := (lt_div_iff₀ hq).1 (show y < -1 / q by rwa [neg_div])
        nlinarith
      exact div_pos_of_neg_of_neg hqy (by linarith [show 0 < 1 / q from by positivity])
    · exact div_pos (by nlinarith) (by linarith)
  refine ⟨Real.log e / π, ?_, ?_, ?_⟩
  · rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hepos, he]
    have : (q * y + 1) / (y - 1) - q = (q + 1) / (y - 1) := by field_simp; ring
    rw [this, div_add_one hy1, div_div_div_cancel_right₀ hy1]
    rw [div_eq_iff (by linarith)]
    ring
  · intro h
    rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hepos, he]
    have hy1' : y - 1 < 0 := by linarith [show 0 < 1 / q from by positivity]
    rw [div_lt_iff_of_neg hy1']
    linarith
  · intro h
    rw [mul_div_cancel₀ _ Real.pi_pos.ne', Real.exp_log hepos, he, lt_div_iff₀ (by linarith)]
    linarith

/-! ### The conditional helpers -/

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **Lemma 4.3, first case (`a ≤ −Λ`), noncollision part, conditional on Aux. lemma 6.** In the chart
`ψ(z) = e^{πz} − 1` (right end as target, left end at `−1`), let the half-plane boundary data `F` of the force word
be the transported strip data off a finite set `E`: the constant upper height `a` becomes `a + X · arg ψ'` on
`(−∞, −1)`; on `(−1, 0)` and `[0, ∞)` the lower data satisfies Remark 4.1 wherever a mark separates the point from the
seed (in the basic figure there are no lower marks, and the condition is empty). Then every evolution of the word
has infinite lifetime and no force point meets the driver at a positive time. -/
theorem noncollision_of_aux6_expChart (hk : 0 < k) (h6 : Aux6Statement.{u} k)
    (hword : IsOrderedForceWord xL xR) (E : Finset ℝ) {a : ℝ} (ha : a ≤ -sleLambda k)
    (hup : ∀ x : ℝ, -Real.exp (π * x) - 1 ∉ E →
      forceBoundaryData k ρL ρR xL xR (-Real.exp (π * x) - 1) =
        a + chiC k * (derivLogExpChart (x + I)).im)
    (hlowL : ∀ y : ℝ, -1 < y → y < 0 → y ∉ E → (∃ i, y < xL i) →
      forceBoundaryData k ρL ρR xL xR y ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ y : ℝ, 0 ≤ y → y ∉ E → (∃ i, xR i ≤ y) →
      sleLambda k - π * chiC k ≤ forceBoundaryData k ρL ρR xL xR y)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω := by
  refine h6 xL xR ρL ρR P 𝓕 W VL VR B ζ hword ?_ hE
  refine hasAdmissiblePartialSums_of_forall_not_mem hk (insert (-1) E) (fun y hy hyE hmark => ?_)
    (fun y hy hyE hmark => hlowR y hy (fun h => hyE (Finset.mem_insert_of_mem h)) hmark)
  have hy1 : y ≠ -1 := fun h => hyE (h ▸ Finset.mem_insert_self _ _)
  have hyE' : y ∉ E := fun h => hyE (Finset.mem_insert_of_mem h)
  rcases lt_or_gt_of_ne hy1 with h | h
  · obtain ⟨x, rfl⟩ := exists_expChart_upper h
    rw [hup x hyE', neg_sleLambda_add_pi_mul_chiC' hk]
    exact expChart_upper_height_le hk ha x
  · exact hlowL y h hy hyE' hmark


/-- **Lemma 4.5, noncollision part, conditional on Aux. lemma 6.** In the chart `ψ = stripQ q`, `q = e^{π x₀}`
(target `z₀ = x₀ + i` at `∞`, strip ends at `−1/q` and `1`), let the half-plane boundary data `F` be the transported
strip data off a finite set `E`: the upper heights `up` (at most `−Λ` left of `z₀`, at least `Λ` right of `z₀`)
become `up + X · arg ψ'` on `(−∞, −1/q)` and `(1, ∞)`; on `(−1/q, 0)` and `[0, 1)` the lower data satisfies
Remark 4.1 wherever a mark separates the point from the seed. Then every evolution of the word has infinite lifetime
and no force point (in particular neither strip-end image) meets the driver at a positive time. -/
theorem noncollision_of_aux6_stripQ (hk : 0 < k) (h6 : Aux6Statement.{u} k)
    (hword : IsOrderedForceWord xL xR) (E : Finset ℝ) {q : ℝ} (hq : 0 < q) {up : ℝ → ℝ}
    (hup_le : ∀ x : ℝ, Real.exp (π * x) < q → up x ≤ -sleLambda k)
    (hup_ge : ∀ x : ℝ, q < Real.exp (π * x) → sleLambda k ≤ up x)
    (htr : ∀ x : ℝ, Real.exp (π * x) ≠ q →
      (Real.exp (π * x) + 1) / (Real.exp (π * x) - q) ∉ E →
      forceBoundaryData k ρL ρR xL xR ((Real.exp (π * x) + 1) / (Real.exp (π * x) - q)) =
        up x + chiC k * (derivLogStripQ q (x + I)).im)
    (hlowL : ∀ y : ℝ, -(1 / q) < y → y < 0 → y ∉ E → (∃ i, y < xL i) →
      forceBoundaryData k ρL ρR xL xR y ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ y : ℝ, 0 ≤ y → y < 1 → y ∉ E → (∃ i, xR i ≤ y) →
      sleLambda k - π * chiC k ≤ forceBoundaryData k ρL ρR xL xR y)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω := by
  refine h6 xL xR ρL ρR P 𝓕 W VL VR B ζ hword ?_ hE
  refine hasAdmissiblePartialSums_of_forall_not_mem hk (insert (-(1 / q)) (insert 1 E))
    (fun y hy hyE hmark => ?_) (fun y hy hyE hmark => ?_)
  · have hy1 : y ≠ -(1 / q) := fun h => hyE (h ▸ Finset.mem_insert_self _ _)
    have hyE' : y ∉ E := fun h => hyE (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rcases lt_or_gt_of_ne hy1 with h | h
    · obtain ⟨x, hx, hxl, -⟩ := exists_stripQ_upper hq (Or.inl h)
      have hxq := hxl h
      rw [← hx, htr x hxq.ne (hx ▸ hyE')]
      exact stripQ_upper_left_height_le hxq (hup_le x hxq)
    · exact hlowL y h hy hyE' hmark
  · have hy1 : y ≠ 1 := fun h => hyE (Finset.mem_insert_of_mem (h ▸ Finset.mem_insert_self _ _))
    have hyE' : y ∉ E := fun h => hyE (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rcases lt_or_gt_of_ne hy1 with h | h
    · exact hlowR y hy h hyE' hmark
    · obtain ⟨x, hx, -, hxr⟩ := exists_stripQ_upper hq (Or.inr h)
      have hxq := hxr h
      rw [← hx, htr x hxq.ne' (hx ▸ hyE')]
      exact stripQ_upper_right_height_ge hxq (hup_ge x hxq)

end Sec4

end InteractingSLE
