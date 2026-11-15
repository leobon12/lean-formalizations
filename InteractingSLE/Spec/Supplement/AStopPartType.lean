/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofSplit
import InteractingSLE.Spec.Exist.StagedLawData
import InteractingSLE.Spec.Supplement.RetChartWord

/-!
# Theorem 1.5's leaf 3: finite force types from bounded comparison words

Packet PROVE-T15-ASTOP-PART (item 1 of `RLC.OrdModel.AStopSourceInputs`: the type partition). Deterministic part.

A word whose boundary function agrees, off a finite set, with a word of bounded length and heights in a fixed finite
palette has one of finitely many force types (`RetAux79.BoundedForceTypes`), and so has every translate of it
(`shiftW τ`). Hence a measurable word that almost surely on an event `G` has such a comparison word gives a finite
measurable cover of `G` by type events:

* `IsBoundedWord N heights c`: length at most `N`, heights in `heights`;
* `isBoundedWord_wordM`, `isBoundedWord_wordT`: Lemma 7.6's zone word and Aux. lemma 85's touching word (the word
  builder `zbuild`) are bounded, at every sample, with the fixed palette `retainedHeightPalette`;
* **`word_forces_eq_of_fn_eq`**, **`hasBoundedForceType_of_fn_eq`**: the force data depend only on the boundary function
  off a finite set (RETPLUMB's mean-pairing version, `RetAux79.word_forces_eq_of_mean_integrals`, with the finite set
  explicit, so that translates are covered);
* **`exists_typeCover`**, **`exists_typeCover_shiftW`**: the finite measurable type covers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopPart

open Restart Restart.RetAux79 PiecewiseConstantBoundaryData
open Exist.StagedLaw.BoundaryWord (shiftW fn_shiftW measurable_shiftW)

/-! ### Bounded words -/

/-- A word of length at most `N` whose heights `c.2.2 j`, `j ≤ c.1`, lie in the finite palette `heights`. -/
def IsBoundedWord (N : ℕ) (heights : Finset ℝ) (c : BoundaryWord) : Prop :=
  c.1 ≤ N ∧ ∀ j ≤ c.1, c.2.2 j ∈ heights

/-- A translate of a bounded word is bounded (the translation moves only the positions). -/
theorem IsBoundedWord.shiftW {N : ℕ} {heights : Finset ℝ} {c : BoundaryWord} (hc : IsBoundedWord N heights c)
    (τ : ℝ) : IsBoundedWord N heights (shiftW τ c) :=
  hc

/-- The word builder of the zone words is bounded. -/
theorem isBoundedWord_zbuild (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) {k₁ k₂ k₃ k₄ : ℕ} (h₁ : k₁ ≤ c₀.1)
    (h₂ : k₂ ≤ c₀.1) (h₃ : k₃ ≤ c₀.1) (h₄ : k₄ ≤ c₀.1) (Tp : ℕ → ℝ) (L₂ R₂ L₁ M₁ R₁ : ℝ) :
    IsBoundedWord (3 * c₀.1 + 6) (retainedHeightPalette c₀ g₁ g₂ g₃ g₄)
      (Sec7.Lemma76G.zbuild c₀ g₁ g₂ g₃ g₄ k₁ k₂ k₃ k₄ Tp L₂ R₂ L₁ M₁ R₁) :=
  zbuild_length_heights c₀ g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄ Tp L₂ R₂ L₁ M₁ R₁

theorem cntLt_le (c₀ : BoundaryWord) (y : ℝ) : Sec7.Lemma76G.cntLt c₀ y ≤ c₀.1 :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem cntLe_le (c₀ : BoundaryWord) (y : ℝ) : Sec7.Lemma76G.cntLe c₀ y ≤ c₀.1 :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

section Words

variable {Ω : Type*}

/-- **Lemma 7.6's measurable zone word is bounded at every sample.** -/
theorem isBoundedWord_wordM (d : Supp7.RetData Ω) (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) (ω : Ω) :
    IsBoundedWord (3 * c₀.1 + 6) (retainedHeightPalette c₀ g₁ g₂ g₃ g₄)
      (Sec7.Lemma76G.wordM d c₀ g₁ g₂ g₃ g₄ ω) :=
  isBoundedWord_zbuild c₀ g₁ g₂ g₃ g₄ (cntLt_le _ _) (cntLe_le _ _) (cntLt_le _ _) (cntLe_le _ _) _ _ _ _ _ _

/-- **Aux. lemma 85's measurable touching word is bounded at every sample.** -/
theorem isBoundedWord_wordT (d : Supp7.RetData Ω) (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) (ω : Ω) :
    IsBoundedWord (3 * c₀.1 + 6) (retainedHeightPalette c₀ g₁ g₂ g₃ g₄)
      (RetChart.wordT d c₀ g₁ g₂ g₃ g₄ ω) :=
  isBoundedWord_zbuild c₀ g₁ g₂ g₃ g₄ (cntLt_le _ _) (cntLe_le _ _) (cntLt_le _ _) (cntLe_le _ _) _ _ _ _ _ _

end Words

/-! ### Force data depend only on the boundary function off a finite set -/

/-- A definitional adapter exposing the three boundary-data arguments of the padded flow word (as in
`RetAux79.word_forces_eq_of_mean_integrals`), so that congruence in the jump set is ordinary rewriting. -/
private def forcePadOf (κ θ : ℝ) (S : Finset ℝ) (L R : ℝ → ℝ) : Exist.Staged.PadWord :=
  (((fun i => if h : i < (S.filter (· < 0)).card + 1 then
      Fin.cons (α := fun _ => ℝ) 0
        (fun j => (S.filter (· < 0)).orderEmbOfFin rfl (Fin.rev j) - 0) ⟨i, h⟩ else 0),
    fun j => if h : j < (S.filter (0 < ·)).card + 1 then
      Fin.cons (α := fun _ => ℝ) 0
        (fun k => (S.filter (0 < ·)).orderEmbOfFin rfl k - 0) ⟨j, h⟩ else 0),
    ((fun i => if h : i < (S.filter (· < 0)).card + 1 then
      Fin.cons (α := fun _ => ℝ) (-(L 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
        (fun j => let y := (S.filter (· < 0)).orderEmbOfFin rfl (Fin.rev j)
          (R y - L y) / sleLambda κ) ⟨i, h⟩ else 0),
    fun j => if h : j < (S.filter (0 < ·)).card + 1 then
      Fin.cons (α := fun _ => ℝ) ((R 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
        (fun k => let y := (S.filter (0 < ·)).orderEmbOfFin rfl k
          (R y - L y) / sleLambda κ) ⟨j, h⟩ else 0))

/-- **Two words whose boundary functions agree off a finite set have the same force data** (numbers of marks and
padded flow word): the one-sided limits agree everywhere, hence so do the genuine jump sets. -/
theorem word_forces_eq_of_fn_eq {c d : BoundaryWord} (κ θ : ℝ) {S : Finset ℝ}
    (hf : ∀ y ∉ S, c.fn y = d.fn y) :
    flowLineNL c.fn c.jumps 0 = flowLineNL d.fn d.jumps 0 ∧
      flowLineNR c.fn c.jumps 0 = flowLineNR d.fn d.jumps 0 ∧
        flowPad κ θ (c, 0) = flowPad κ θ (d, 0) := by
  have hL : leftLim c.fn = leftLim d.fn := leftLim_congr hf
  have hR : rightLim c.fn = rightLim d.fn := rightLim_congr hf
  have hS : jumpSet c.fn c.jumps = jumpSet d.fn d.jumps := by
    rw [← Exist.StagedLaw.jumpSet_eq_of_subset c.isPiecewiseConstantBoundaryData
        (show c.jumps ⊆ c.jumps ∪ d.jumps from Finset.subset_union_left),
      ← Exist.StagedLaw.jumpSet_eq_of_subset d.isPiecewiseConstantBoundaryData
        (show d.jumps ⊆ c.jumps ∪ d.jumps from Finset.subset_union_right)]
    unfold jumpSet
    rw [hL, hR]
  refine ⟨by simp only [flowLineNL, hS], by simp only [flowLineNR, hS], ?_⟩
  change forcePadOf κ θ (jumpSet c.fn c.jumps) (leftLim c.fn) (rightLim c.fn) =
    forcePadOf κ θ (jumpSet d.fn d.jumps) (leftLim d.fn) (rightLim d.fn)
  rw [hS, hL, hR]

/-- **The bounded-type property transfers along agreement of the boundary functions off a finite set.** -/
theorem hasBoundedForceType_of_fn_eq {c d : BoundaryWord} {κ θ : ℝ} {N : ℕ} {weights S : Finset ℝ}
    (hf : ∀ y ∉ S, c.fn y = d.fn y) (hb : HasBoundedForceType κ θ N weights c) :
    HasBoundedForceType κ θ N weights d := by
  obtain ⟨hL, hR, hpad⟩ := word_forces_eq_of_fn_eq κ θ hf
  unfold HasBoundedForceType at hb ⊢
  rw [← hL, ← hR, ← hpad]
  exact hb

/-- **A word that agrees with a bounded word off a finite set has one of finitely many force types.** -/
theorem exists_mem_forceTypeSet_of_fn_eq {κ θ : ℝ} {N : ℕ} {heights S : Finset ℝ} {c e : BoundaryWord}
    (he : IsBoundedWord N heights e) (hf : ∀ y ∉ S, c.fn y = e.fn y) :
    ∃ i : BoundedForceTypes (N + 1) (flowWeightPalette κ θ heights),
      c ∈ forceTypeSet κ θ (boundedForceType (N + 1) (flowWeightPalette κ θ heights) i) :=
  exists_boundedForceType (hasBoundedForceType_of_fn_eq (fun y hy => (hf y hy).symm)
    (hasBoundedForceType_of_heights he.1 he.2))

/-- Agreement off a finite set passes to translates. -/
theorem fn_shiftW_eq_of_fn_eq {c e : BoundaryWord} {S : Finset ℝ} (hf : ∀ y ∉ S, c.fn y = e.fn y) (τ : ℝ) :
    ∀ y ∉ S.image (· - τ), (shiftW τ c).fn y = (shiftW τ e).fn y := by
  intro y hy
  rw [fn_shiftW, fn_shiftW]
  refine hf _ fun hmem => hy (Finset.mem_image.2 ⟨y + τ, hmem, by ring⟩)

/-! ### Finite measurable type covers -/

section Cover

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {m : MeasurableSpace Ω}

/-- **The finite type cover.** A word `c`, measurable for a σ-algebra `m`, that almost surely on `G` agrees off a
finite set with a word of length at most `N` and heights in `heights`: finitely many `m`-measurable events cover `G`
almost surely, each of one force type at every point. -/
theorem exists_typeCover {κ θ : ℝ} {N : ℕ} {heights : Finset ℝ} {c : Ω → BoundaryWord} (hc : Measurable[m] c)
    {G : Ω → Prop}
    (hG : ∀ᵐ ω ∂P, G ω → ∃ (e : BoundaryWord) (S : Finset ℝ), IsBoundedWord N heights e ∧
      ∀ y ∉ S, (c ω).fn y = e.fn y) :
    ∃ (n : ℕ) (a : Fin n → ForceWordType) (M : Fin n → Set Ω), (∀ i, MeasurableSet[m] (M i)) ∧
      (∀ᵐ ω ∂P, G ω → ∃ i, ω ∈ M i) ∧
      ∀ i, ∀ ω ∈ M i, c ω ∈ FCDet.typeSet κ θ (a i).nL (a i).nR (a i).rhoL (a i).rhoR := by
  classical
  set W := flowWeightPalette κ θ heights with hW
  let e := Fintype.equivFin (BoundedForceTypes (N + 1) W)
  let a : Fin (Fintype.card (BoundedForceTypes (N + 1) W)) → ForceWordType :=
    fun i => boundedForceType (N + 1) W (e.symm i)
  refine ⟨Fintype.card (BoundedForceTypes (N + 1) W), a, fun i => c ⁻¹' forceTypeSet κ θ (a i),
    fun i => hc (measurableSet_forceTypeSet κ θ (a i)), ?_, fun i ω hω => hω⟩
  filter_upwards [hG] with ω hω hGω
  obtain ⟨w, S, hw, hf⟩ := hω hGω
  obtain ⟨j, hj⟩ := exists_mem_forceTypeSet_of_fn_eq (κ := κ) (θ := θ) hw hf
  refine ⟨e j, ?_⟩
  show c ω ∈ forceTypeSet κ θ (boundedForceType (N + 1) W (e.symm (e j)))
  rw [Equiv.symm_apply_apply]
  exact hj

/-- **The finite type cover of translates.** As `exists_typeCover`, for the translated words `shiftW (τ ω) (c ω)`
with an `m`-measurable translation `τ`. -/
theorem exists_typeCover_shiftW {κ θ : ℝ} {N : ℕ} {heights : Finset ℝ} {c : Ω → BoundaryWord}
    (hc : Measurable[m] c) {τ : Ω → ℝ} (hτ : Measurable[m] τ) {G : Ω → Prop}
    (hG : ∀ᵐ ω ∂P, G ω → ∃ (e : BoundaryWord) (S : Finset ℝ), IsBoundedWord N heights e ∧
      ∀ y ∉ S, (c ω).fn y = e.fn y) :
    ∃ (n : ℕ) (a : Fin n → ForceWordType) (M : Fin n → Set Ω), (∀ i, MeasurableSet[m] (M i)) ∧
      (∀ᵐ ω ∂P, G ω → ∃ i, ω ∈ M i) ∧
      ∀ i, ∀ ω ∈ M i, shiftW (τ ω) (c ω) ∈ FCDet.typeSet κ θ (a i).nL (a i).nR (a i).rhoL (a i).rhoR := by
  have hsc : Measurable[m] fun ω => shiftW (τ ω) (c ω) := measurable_shiftW.comp (hτ.prodMk hc)
  refine exists_typeCover (mΩ := mΩ) (m := m) (P := P) (N := N) (heights := heights) hsc ?_
  filter_upwards [hG] with ω hω hGω
  obtain ⟨w, S, hw, hf⟩ := hω hGω
  exact ⟨shiftW (τ ω) w, S.image (· - τ ω), hw.shiftW (τ ω), fn_shiftW_eq_of_fn_eq hf (τ ω)⟩

end Cover

end InteractingSLE.RLC.AStopPart
