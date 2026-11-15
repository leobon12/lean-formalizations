/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S8Schedule

/-!
# Lemma GB9a: the Tonelli step and the assembled selection

Packet PROVE-T14-TIP (specification supplement §8.9, **Lemma GB9a**, `source/spec/p481-528.md` L1107–L1120, p. 527;
used again in DS4, p. 555, CS3, p. 593, and Lemma GW2, p. 621: "The ordered-time-vector Tonelli argument of GB9a
applies … It therefore supplies one deterministic dense countable `Q`").

The proof of GB9a has two measure-theoretic steps around one probabilistic input:

* **input** (Lemma 2.5 for the concatenated finite-force flow): *pathwise*, the set of bad time vectors (a switching
  or terminal tip on the original boundary) is Lebesgue-null;
* **(i) Tonelli** ("Tonelli, first over the field and then over the earlier times, proves that the set of bad
  ordered vectors has Lebesgue measure zero"): for Lebesgue-almost every time vector the field gives the bad event
  probability zero (`ae_measure_section_eq_zero`);
* **(ii) selection** (landed: `Supp8.exists_seq_forall_null`, `Supp8.gb9a_exists_dense`): one deterministic
  sequence avoids all countably many bad sets.

**`gb9a_of_pathwise_null`** assembles (i) and (ii): for countably many measurable bad sets `B j ⊆ Ω × (S j → ℝ)` whose
`ω`-sections are Lebesgue-null for every `ω`, there is a deterministic dense `Q = range q ⊂ (0, ∞)` such that for every
`j` the field gives probability zero to the bad event at the time vector `q|S j`. The source's ordered vectors and
angle lists are among the `j` (one index set, one ordering and one angle list per `j`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace InteractingSLE

namespace Supp8

/-- **GB9a (i), Tonelli**: if every `ω`-section of a measurable set `B ⊆ Ω × Y` is `ν`-null, then for `ν`-almost every
`y` the `y`-section is `P`-null. -/
theorem ae_measure_section_eq_zero {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω)
    (ν : Measure Y) [SFinite P] [SFinite ν] {B : Set (Ω × Y)} (hB : MeasurableSet B)
    (hpath : ∀ ω, ν {y | (ω, y) ∈ B} = 0) : ∀ᵐ y ∂ν, P {ω | (ω, y) ∈ B} = 0 := by
  have h1 : (P.prod ν) B = 0 := (Measure.measure_prod_null hB).2 (Eventually.of_forall hpath)
  have h2 : (ν.prod P) (Prod.swap ⁻¹' B) = 0 := by
    rw [← Measure.prod_swap, Measure.map_apply measurable_swap (measurable_swap hB)]
    convert h1 using 2
    ext ⟨a, b⟩; simp
  have h3 := (Measure.measure_prod_null (measurable_swap hB)).1 h2
  filter_upwards [h3] with y hy
  exact hy

/-- **GB9a, assembled** ((i) Tonelli and (ii) selection): countably many measurable bad sets with pathwise
Lebesgue-null sections are avoided, with probability one each, at the time vectors drawn from one deterministic
countable set `Q = range q ⊂ (0, ∞)` dense in `(0, ∞)`. -/
theorem gb9a_of_pathwise_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] {ι : Type*}
    [Countable ι] (S : ι → Finset ℕ) (B : (j : ι) → Set (Ω × (S j → ℝ))) (hB : ∀ j, MeasurableSet (B j))
    (hpath : ∀ j ω, (Measure.pi fun _ : S j => (volume : Measure ℝ)) {y | (ω, y) ∈ B j} = 0) :
    ∃ q : ℕ → ℝ, (∀ m, 0 < q m) ∧ Ioi 0 ⊆ closure (range q) ∧
      ∀ j, P {ω | (ω, (S j).restrict q) ∈ B j} = 0 :=
  gb9a_exists_dense P S B fun j => ae_measure_section_eq_zero P _ (hB j) (hpath j)

end Supp8

end InteractingSLE
