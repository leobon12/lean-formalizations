/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Supplement §8.9: Lemma GB9a, a deterministic dense schedule

Packet PROVE-SUPP8 (specification supplement §8.9, `source/spec/p481-528.md` L1104–L1120, p. 527).

**Lemma GB9a** chooses a deterministic countable dense set `Q ⊂ (0, ∞)` of switching times such that, almost surely,
no switching or terminal tip of any finite extreme-angle schedule with distinct times in `Q` lies on the boundary.
Its proof has two parts: (i) for each finite angle list, Lemma 2.5 and Tonelli show that the set of bad ordered time
vectors is Lebesgue-null, i.e. for Lebesgue-a.e. time vector `y` the field gives probability zero to a bad tip at
`y`; (ii) the selection: on an auxiliary space take independent uniform `U_m` on an enumeration `I_m` of the bounded
rational open subintervals of `(0, ∞)`; every finite family of distinct indices has an absolutely continuous joint law,
so by (i) and Tonelli, for almost every auxiliary sequence the field gives probability zero to a bad tip of that
family; intersect over the countably many families and angle lists and fix one sequence.

This file proves part (ii), the selection, for arbitrary countably many bad sets:

* `exists_seq_forall_null`: given a measure `P` on `Ω`, intervals `a m < b m`, finite index sets `S j ⊆ ℕ` (`j` in a
  countable type) and sets `B j ⊆ Ω × (S j → ℝ)` whose sections satisfy `P (B j)^y = 0` for Lebesgue-a.e. `y`, there is
  `q` with `q m ∈ (a m, b m)` and `P (B j)^{q|S j} = 0` for every `j`;
* `gb9a_exists_dense`: with `(a m, b m)` enumerating the rational open intervals of `(0, ∞)`, `Q = range q` is a
  countable subset of `(0, ∞)` dense in it.

A finite vector of distinct elements of `Q` is `q` restricted to a finite index set (one index per value), so the
bad events of all finite schedules with distinct times in `Q` are among the `B j` (one per index set, ordering and
angle list). Part (i) is the input `hnull` (it uses Lemma 2.5 for the concatenated finite-force flow).

Auxiliary: `uniformIoo a b`, the uniform law on `(a, b)`, and `pi_uniformIoo_absolutelyContinuous` (a finite product
of uniform laws is absolutely continuous with respect to Lebesgue measure).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ENNReal

namespace InteractingSLE

namespace Supp8

/-- The uniform law on `(a, b)`. -/
def uniformIoo (a b : ℝ) : Measure ℝ := (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Ioo a b)

theorem uniformIoo_apply_univ {a b : ℝ} (hab : a < b) : uniformIoo a b univ = 1 := by
  rw [uniformIoo, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioo, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne' ENNReal.ofReal_ne_top

theorem isProbabilityMeasure_uniformIoo {a b : ℝ} (hab : a < b) : IsProbabilityMeasure (uniformIoo a b) :=
  ⟨uniformIoo_apply_univ hab⟩

theorem uniformIoo_ae_mem (a b : ℝ) : ∀ᵐ x ∂(uniformIoo a b), x ∈ Ioo a b := by
  rw [uniformIoo]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioo) _

/-- A finite product of uniform laws is the scaled restriction of Lebesgue measure to the box. -/
theorem pi_uniformIoo_eq {ι : Type*} [Fintype ι] {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    Measure.pi (fun i => uniformIoo (a i) (b i)) =
      (∏ i, (ENNReal.ofReal (b i - a i))⁻¹) •
        (Measure.pi fun _ : ι => (volume : Measure ℝ)).restrict (univ.pi fun i => Ioo (a i) (b i)) := by
  have := fun i => isProbabilityMeasure_uniformIoo (hab i)
  rw [Measure.restrict_pi_pi]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  rfl

/-- A finite product of uniform laws is absolutely continuous with respect to Lebesgue measure. -/
theorem pi_uniformIoo_absolutelyContinuous {ι : Type*} [Fintype ι] {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    Measure.pi (fun i => uniformIoo (a i) (b i)) ≪ Measure.pi fun _ : ι => (volume : Measure ℝ) := by
  rw [pi_uniformIoo_eq hab]
  intro N hN
  rw [Measure.smul_apply, smul_eq_mul]
  have : (Measure.pi fun _ : ι => (volume : Measure ℝ)).restrict (univ.pi fun i => Ioo (a i) (b i)) N = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 Measure.restrict_le_self N).trans hN.le)
  rw [this, mul_zero]

/-- **GB9a, selection.** Countably many bad sets `B j ⊆ Ω × (S j → ℝ)`, each with `P`-null sections at Lebesgue-almost
every time vector, are avoided by one deterministic sequence `q` with `q m ∈ (a m, b m)`: for every `j`, the field
gives probability zero to `(ω, q|S j) ∈ B j`. -/
theorem exists_seq_forall_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*} [Countable ι]
    (S : ι → Finset ℕ) (B : (j : ι) → Set (Ω × (S j → ℝ)))
    (hnull : ∀ j, ∀ᵐ y ∂(Measure.pi fun _ : S j => (volume : Measure ℝ)), P {ω | (ω, y) ∈ B j} = 0)
    {a b : ℕ → ℝ} (hab : ∀ m, a m < b m) :
    ∃ q : ℕ → ℝ, (∀ m, q m ∈ Ioo (a m) (b m)) ∧ ∀ j, P {ω | (ω, (S j).restrict q) ∈ B j} = 0 := by
  have : ∀ m, IsProbabilityMeasure (uniformIoo (a m) (b m)) := fun m =>
    isProbabilityMeasure_uniformIoo (hab m)
  set μ := Measure.infinitePi fun m => uniformIoo (a m) (b m) with hμ
  have h1 : ∀ j, ∀ᵐ u ∂μ, P {ω | (ω, (S j).restrict (π := fun _ => ℝ) u) ∈ B j} = 0 := by
    intro j
    have hlaw : μ.map ((S j).restrict (π := fun _ => ℝ)) =
        Measure.pi fun i : S j => uniformIoo (a i) (b i) :=
      Measure.infinitePi_map_restrict _
    have h := (pi_uniformIoo_absolutelyContinuous (a := fun i : S j => a i) (b := fun i : S j => b i)
      (fun i => hab i)).ae_le (hnull j)
    rw [← hlaw] at h
    exact ae_of_ae_map (Finset.measurable_restrict _).aemeasurable h
  have h2 : ∀ m, ∀ᵐ u ∂μ, u m ∈ Ioo (a m) (b m) := by
    intro m
    have hlaw : μ.map (fun u => u m) = uniformIoo (a m) (b m) := Measure.infinitePi_map_eval _ m
    have h := uniformIoo_ae_mem (a m) (b m)
    rw [← hlaw] at h
    exact ae_of_ae_map (measurable_pi_apply m).aemeasurable h
  obtain ⟨q, hq1, hq2⟩ := ((ae_all_iff.2 h2).and (ae_all_iff.2 h1)).exists
  exact ⟨q, hq1, hq2⟩

/-- **Lemma GB9a** (selection part): there is a countable set `Q = range q ⊂ (0, ∞)`, dense in `(0, ∞)`, such that for
every `j` the field gives probability zero to the bad event `B j` at the time vector `q|S j`. The hypothesis `hnull`
is the null-set statement of part (i) of the source proof. -/
theorem gb9a_exists_dense {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*} [Countable ι]
    (S : ι → Finset ℕ) (B : (j : ι) → Set (Ω × (S j → ℝ)))
    (hnull : ∀ j, ∀ᵐ y ∂(Measure.pi fun _ : S j => (volume : Measure ℝ)), P {ω | (ω, y) ∈ B j} = 0) :
    ∃ q : ℕ → ℝ, (∀ m, 0 < q m) ∧ Ioi 0 ⊆ closure (range q) ∧
      ∀ j, P {ω | (ω, (S j).restrict q) ∈ B j} = 0 := by
  set R : Set (ℚ × ℚ) := {p | 0 < p.1 ∧ p.1 < p.2} with hR
  have hRne : R.Nonempty := ⟨(1, 2), by norm_num [hR]⟩
  obtain ⟨e, he⟩ := (Set.to_countable R).exists_eq_range hRne
  have heR : ∀ m, e m ∈ R := fun m => he ▸ mem_range_self m
  obtain ⟨q, hq, hnull'⟩ := exists_seq_forall_null P S B hnull (a := fun m => ((e m).1 : ℝ))
    (b := fun m => ((e m).2 : ℝ)) fun m => by exact_mod_cast (heR m).2
  refine ⟨q, fun m => lt_trans (by exact_mod_cast (heR m).1) (hq m).1, fun x hx => ?_, hnull'⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hx0 : (0 : ℝ) < x := hx
  obtain ⟨r₁, hr₁⟩ := exists_rat_btwn (show max (x - ε) (x / 2) < x from
    max_lt (by linarith) (by linarith))
  obtain ⟨r₂, hr₂⟩ := exists_rat_btwn (show x < x + ε by linarith)
  have hmem : (r₁, r₂) ∈ R := by
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) < r₁ := lt_of_le_of_lt (le_max_of_le_right (by linarith)) hr₁.1
      exact_mod_cast this
    · have : (r₁ : ℝ) < r₂ := hr₁.2.trans hr₂.1
      exact_mod_cast this
  rw [he] at hmem
  obtain ⟨m, hm⟩ := hmem
  have hqm := hq m
  simp only [hm] at hqm
  refine ⟨q m, mem_range_self m, ?_⟩
  rw [Real.dist_eq, abs_lt]
  have h1 := le_max_left (x - ε) (x / 2)
  constructor <;> linarith [hqm.1, hqm.2, hr₁.1, hr₂.2]

end Supp8

end InteractingSLE
