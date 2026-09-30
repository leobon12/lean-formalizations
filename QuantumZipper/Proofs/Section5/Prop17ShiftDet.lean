import QuantumZipper.Proofs.Section5.Prop17ShiftDetBasic

/-!
# Proposition 1.7, SHIFT-DET (part 2): deterministic locality of the shift map

Sheffield, arXiv:1012.4797, proof of Proposition 1.7 (p. 26), blueprint D5 "the shift-by-`L`
map is local on `{y_L < R}`". Own elementary argument (the paper gives none), from the locality
lemmas of `Prop17ShiftDetBasic.lean`.

**Correction of the good set.** `Prop17ShiftDetStmt γ L` (`Prop17StatLocal.lean`) asks for an
exhausting family covering all of `GoodC γ`. On good vectors whose translate at the length point
has *empty* scale set (the quantum area of `ℍ` never reaches `1`; allowed by `GoodC`, which only
constrains the boundary length) `scaleParam = sInf ∅ = 0` is a junk value, and such a vector is
locally indistinguishable from good vectors with arbitrarily large scale, so no locally
determined `B n` can contain it while keeping the shifted coordinates local. We therefore cover
only `GoodCS γ L = GoodC γ ∩ {0 < scale of the translate}`, which has full measure under the
reference wedge law (`prop17ScalePosStmt_holds`); locality is still asserted on all of `GoodC γ`.
This is all that the consumer `map_eq_self_of_local` uses (it only needs the covering a.s.).

* `shiftB γ L n = {lenG ≤ n, 0 < scale of the translate ≤ n}`;
* `shiftDet_key`: for good `c, c'` agreeing on `locFull (shiftR n i)`, `c ∈ shiftB n` implies
  `c' ∈ shiftB n` and equality of the `i`-th shifted coordinates;
* `Prop17ShiftDetStmt'` and `prop17ShiftDetStmt'_holds` (unconditional).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull

/-- Good vectors whose translate at the length-`L` point has positive scale parameter. -/
def GoodCS (γ L : ℝ) : Set (ℕ → ℝ) :=
  GoodC γ ∩ {c | 0 < scaleG γ (tcoords γ L (proj c))}

theorem measurable_scaleG_tcoords_proj (γ L : ℝ) :
    Measurable fun c : ℕ → ℝ => scaleG γ (tcoords γ L (proj c)) :=
  (measurable_scaleG γ).comp ((measurable_tcoords γ L).comp measurable_proj)

theorem measurable_lenG_proj (γ L : ℝ) :
    Measurable fun c : ℕ → ℝ => lenG γ L (reconstruct (proj c)) :=
  (measurable_lenG γ L).comp (measurable_reconstruct.comp measurable_proj)

theorem measurableSet_goodCS (γ L : ℝ) : MeasurableSet (GoodCS γ L) :=
  (measurableSet_goodC γ).inter
    (measurableSet_lt measurable_const (measurable_scaleG_tcoords_proj γ L))

/-- The exhausting family: length point `≤ n` and scale of the translate in `(0, n]`. -/
def shiftB (γ L : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {c | lenG γ L (reconstruct (proj c)) ≤ n ∧ 0 < scaleG γ (tcoords γ L (proj c)) ∧
    scaleG γ (tcoords γ L (proj c)) ≤ n}

theorem measurableSet_shiftB (γ L : ℝ) (n : ℕ) : MeasurableSet (shiftB γ L n) :=
  (measurableSet_le (measurable_lenG_proj γ L) measurable_const).inter
    ((measurableSet_lt measurable_const (measurable_scaleG_tcoords_proj γ L)).inter
      (measurableSet_le (measurable_scaleG_tcoords_proj γ L) measurable_const))

theorem monotone_shiftB (γ L : ℝ) : Monotone (shiftB γ L) := fun a b hab c hc => by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact ⟨hc.1.trans hab', hc.2.1, hc.2.2.trans hab'⟩

theorem goodCS_subset_iUnion_shiftB (γ L : ℝ) : GoodCS γ L ⊆ ⋃ n, shiftB γ L n := by
  intro c hc
  refine mem_iUnion.2 ⟨⌈max (lenG γ L (reconstruct (proj c)))
    (scaleG γ (tcoords γ L (proj c)))⌉₊, ?_, hc.2, ?_⟩
  · exact (le_max_left _ _).trans (Nat.le_ceil _)
  · exact (le_max_right _ _).trans (Nat.le_ceil _)

/-- The radius used for level `n` and coordinate `i`. -/
def shiftR (n i : ℕ) : ℕ :=
  ⌈2 * (n : ℝ) + 2 + n * (‖(fullIndex i).1‖ + (fullIndex i).2)⌉₊ + 1

theorem shiftDet_key {γ L : ℝ} {n i : ℕ} {c c' : ℕ → ℝ} (hc : c ∈ GoodC γ) (hc' : c' ∈ GoodC γ)
    (he : locFull (shiftR n i) c = locFull (shiftR n i) c') (hB : c ∈ shiftB γ L n) :
    c' ∈ shiftB γ L n ∧ shiftCoords γ L c i = shiftCoords γ L c' i := by
  set R := shiftR n i with hRdef
  set ρ := ‖(fullIndex i).1‖ + (fullIndex i).2 with hρdef
  have hρ : 0 ≤ ρ := add_nonneg (norm_nonneg _) (fullIndex_radius_pos i).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hR : 2 * (n : ℝ) + 2 + n * ρ < R := by
    have h1 := Nat.le_ceil (2 * (n : ℝ) + 2 + n * ρ)
    rw [hRdef, shiftR]
    push_cast
    linarith
  have hnρ : 0 ≤ (n : ℝ) * ρ := mul_nonneg hn0 hρ
  have hx : IsLQGGood γ (reconstruct (proj c)) := hc.1
  have hx' : IsLQGGood γ (reconstruct (proj c')) := hc'.1
  have hag := agreeNear_of_locFull he
  obtain ⟨hlen, hspos, hsle⟩ := hB
  have hy : lenG γ L (reconstruct (proj c')) = lenG γ L (reconstruct (proj c)) :=
    lenG_eq_of_agreeNear hx hx' hag (n := n) (by linarith) hc.2 hlen
  set y := lenG γ L (reconstruct (proj c)) with hydef
  have hy0 : 0 ≤ y := lenG_nonneg _ _ _
  have ht : tcoords γ L (proj c) = coords (translate (reconstruct (proj c)) (y : ℂ)) := rfl
  have ht' : tcoords γ L (proj c') = coords (translate (reconstruct (proj c')) (y : ℂ)) := by
    show coords (translate (reconstruct (proj c')) (lenG γ L (reconstruct (proj c')) : ℂ)) = _
    rw [hy]
  have hagT : D3Plus.AgreeNear (reconstruct (tcoords γ L (proj c)))
      (reconstruct (tcoords γ L (proj c'))) (R - n) := by
    rw [ht, ht']
    refine agreeNear_reconstruct fun j hj => coords_translate_eq_of_agreeNear hag ?_
    rw [abs_of_nonneg hy0]
    linarith
  have hT : IsLQGGood γ (reconstruct (tcoords γ L (proj c))) := by
    rw [ht]; exact (GoodSample.isLQGGood_iff_reconstruct γ _).2 (hx.translate y)
  have hT' : IsLQGGood γ (reconstruct (tcoords γ L (proj c'))) := by
    rw [ht']; exact (GoodSample.isLQGGood_iff_reconstruct γ _).2 (hx'.translate y)
  have hsG : scaleG γ (tcoords γ L (proj c)) =
      scaleParam γ (reconstruct (tcoords γ L (proj c))) := if_pos hT
  have hsG' : scaleG γ (tcoords γ L (proj c')) =
      scaleParam γ (reconstruct (tcoords γ L (proj c'))) := if_pos hT'
  have hs : scaleG γ (tcoords γ L (proj c')) = scaleG γ (tcoords γ L (proj c)) := by
    rw [hsG, hsG']
    refine scaleParam_eq_of_agreeNear hT hT'
      (agreeNear_mono_shiftDet hagT (r' := n + 1) (by linarith)) (by rw [← hsG]; exact hspos)
      (by rw [← hsG]; linarith)
  refine ⟨⟨by rw [hy]; exact hlen, by rw [hs]; exact hspos, by rw [hs]; exact hsle⟩, ?_⟩
  show rescale (reconstruct (tcoords γ L (proj c))) (Qc γ) (scaleG γ (tcoords γ L (proj c)))
      (foldedCircle (fullIndex i).1 (fullIndex i).2) =
    rescale (reconstruct (tcoords γ L (proj c'))) (Qc γ) (scaleG γ (tcoords γ L (proj c')))
      (foldedCircle (fullIndex i).1 (fullIndex i).2)
  rw [hs]
  refine D3Plus.rescale_congr hagT hspos (s := ρ) ?_ ?_
  · exact measure_mono_null (compl_subset_compl.2 inter_subset_left)
      (CircleFubini.foldedCircle_support (fullIndex_radius_pos i).le le_rfl)
  · have := mul_le_mul_of_nonneg_right hsle hρ
    linarith

/-- **Locality of the shift, determination form, with the corrected good set** (see the module
docstring): as `Prop17ShiftDetStmt γ L`, but the family only has to cover `GoodCS γ L`. -/
def Prop17ShiftDetStmt' (γ L : ℝ) : Prop :=
  ∃ B : ℕ → Set (ℕ → ℝ), Monotone B ∧ (∀ n, MeasurableSet (B n)) ∧ GoodCS γ L ⊆ ⋃ n, B n ∧
    ∀ n i : ℕ, ∃ R : ℕ, ∀ c ∈ GoodC γ, ∀ c' ∈ GoodC γ, locFull R c = locFull R c' →
      (c ∈ B n ↔ c' ∈ B n) ∧ (c ∈ B n → shiftCoords γ L c i = shiftCoords γ L c' i)

/-- **SHIFT-DET, unconditional.** -/
theorem prop17ShiftDetStmt'_holds (γ L : ℝ) : Prop17ShiftDetStmt' γ L :=
  ⟨shiftB γ L, monotone_shiftB γ L, measurableSet_shiftB γ L, goodCS_subset_iUnion_shiftB γ L,
    fun n i => ⟨shiftR n i, fun c hc c' hc' he =>
      ⟨⟨fun h => (shiftDet_key hc hc' he h).1, fun h => (shiftDet_key hc' hc he.symm h).1⟩,
        fun h => (shiftDet_key hc hc' he h).2⟩⟩⟩

end Raw
end FieldLaw
end S5
end QuantumZipper
