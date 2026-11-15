/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB9CapStages

/-!
# The probabilistic skeleton of the exhaustion experiment (follow-up note A.5)

Packet PROVE-T14-TIP7, ruling R53 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt`, A.5, lines 197–251):

> From this prefix alternate the near-extreme stages just constructed, with `Σ_j ε_j ≤ ε`. Conditional union bounds
> give probability at least `1 − ε` of perpetual success. […] The uniform Lemma 5.10 […] gives `p₀ > 0`, fixed after
> the initial conditioning, such that every reached even stage `j ≥ 4` has conditional probability at least `p₀` to
> abort or consume at least one unit of relative capacity. […] For `n ≥ m ≥ 2`, iterating this conditional bound shows
> that the probability of success through stage `2n` and increments less than one at all even stages `2m, …, 2n` is at
> most `(1 − p₀)^{n−m+1}`. Let `n → ∞`, then take the union over `m`. On perpetual success infinitely many increments
> are at least one. Relative capacity is therefore unbounded.

This file assembles PROVE-T14-TIP6's abstract estimates (`Supp8.GB9Cap.le_measureReal_inter_iInter_Ico_sum`,
`Supp8.GB9Cap.measure_liminf_eq_zero_of_lower`) into the conclusion of the experiment, for an abstract stage filtration:

* **`le_measureReal_iInter_inter_frequently`**: with stage success events `S_j` (bounds `(1 − ε_j)`, `Σ ε_j ≤ ε`), abort
  events `Ab_j` disjoint from `S_j`, unit-capacity events `U_j` and the lower bound `p₀` at the even stages
  `2k + 4`: `P(⋂_j S_j ∩ {U_{2k+4} for infinitely many k}) ≥ 1 − ε`;
* **`tendsto_atTop_of_frequently_add_one_le`**: a nondecreasing capacity with infinitely many unit increments tends to
  infinity (deterministic).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2TipSkel

/-! ### Perpetual success has probability at least `1 − ε` -/

section Measure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **All stages succeed with probability at least `1 − ε`** ("Conditional union bounds give probability at least
`1 − ε` of perpetual success"). -/
theorem le_measureReal_iInter [IsProbabilityMeasure P] {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : Monotone 𝓕)
    (h𝓕le : ∀ j, 𝓕 j ≤ mΩ) {S : ℕ → Set Ω} (hS : ∀ j, MeasurableSet[𝓕 (j + 1)] (S j)) {ε : ℕ → ℝ}
    (hε0 : ∀ j, 0 ≤ ε j) (hε1 : ∀ j, ε j ≤ 1) {ε₀ : ℝ} (hsum : ∀ n, ∑ j ∈ range n, ε j ≤ ε₀)
    (hstep : ∀ j A, MeasurableSet[𝓕 j] A → (1 - ε j) * P.real A ≤ P.real (A ∩ S j)) :
    1 - ε₀ ≤ P.real (⋂ j, S j) := by
  set D : ℕ → Set Ω := fun n => ⋂ j ∈ Finset.range n, S j with hD
  have hDm : ∀ n, MeasurableSet (D n) := fun n =>
    Finset.measurableSet_biInter _ fun j _ => h𝓕le (j + 1) _ (hS j)
  have hDanti : Antitone D := fun n n' h => biInter_subset_biInter_left fun j hj =>
    Finset.mem_range.2 ((Finset.mem_range.1 hj).trans_le h)
  have hlow : ∀ n, 1 - ε₀ ≤ P.real (D n) := fun n => by
    have h := Supp8.GB9Cap.le_measureReal_inter_iInter_Ico_sum h𝓕 hS hε0 hε1 hstep 0 MeasurableSet.univ n
    rw [zero_add, ← Finset.range_eq_Ico, univ_inter, probReal_univ, mul_one] at h
    exact (sub_le_sub_left (hsum n) 1).trans h
  have hlim : Tendsto (fun n => P (D n)) atTop (𝓝 (P (⋂ n, D n))) :=
    tendsto_measure_iInter_atTop (fun n => (hDm n).nullMeasurableSet) hDanti ⟨0, measure_ne_top P _⟩
  have hlimR : Tendsto (fun n => P.real (D n)) atTop (𝓝 (P.real (⋂ n, D n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top P _)).comp hlim
  have hiInter : (⋂ n, D n) = ⋂ j, S j := by
    ext ω
    simp only [hD, mem_iInter, Finset.mem_range]
    exact ⟨fun h j => h (j + 1) j (Nat.lt_succ_self j), fun h n j _ => h j⟩
  rw [← hiInter]
  exact ge_of_tendsto hlimR (Eventually.of_forall hlow)

/-- **The experiment's conclusion** (A.5): perpetual success and infinitely many unit-capacity even stages, with
probability at least `1 − ε`. Stage `j` succeeds on `S_j ∈ 𝓕_{j+1}` with conditional probability at least
`1 − ε_j` (`Σ ε_j ≤ ε`); at an even stage `2k + 4` it aborts (`Ab`, disjoint from `S`) or consumes a unit of relative
capacity (`U`) with conditional probability at least `p₀`. -/
theorem le_measureReal_iInter_inter_frequently [IsProbabilityMeasure P] {𝓕 : ℕ → MeasurableSpace Ω}
    (h𝓕 : Monotone 𝓕) (h𝓕le : ∀ j, 𝓕 j ≤ mΩ) {S Ab U : ℕ → Set Ω} (hS : ∀ j, MeasurableSet[𝓕 (j + 1)] (S j))
    (hU : ∀ j, MeasurableSet[𝓕 (j + 1)] (U j)) (hSAb : ∀ j, Disjoint (S j) (Ab j)) {ε : ℕ → ℝ}
    (hε0 : ∀ j, 0 ≤ ε j) (hε1 : ∀ j, ε j ≤ 1) {ε₀ : ℝ} (hsum : ∀ n, ∑ j ∈ range n, ε j ≤ ε₀)
    (hstep : ∀ j A, MeasurableSet[𝓕 j] A → (1 - ε j) * P.real A ≤ P.real (A ∩ S j)) {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hp₀1 : p₀ ≤ 1)
    (hlow : ∀ k A, MeasurableSet[𝓕 (2 * k + 4)] A →
      p₀ * P.real A ≤ P.real (A ∩ (Ab (2 * k + 4) ∪ U (2 * k + 4)))) :
    1 - ε₀ ≤ P.real ((⋂ j, S j) ∩ {ω | ∃ᶠ k in atTop, ω ∈ U (2 * k + 4)}) := by
  -- the even stages as a filtration of their own
  set 𝓖 : ℕ → MeasurableSpace Ω := fun k => 𝓕 (2 * k + 4) with h𝓖
  have h𝓖m : Monotone 𝓖 := fun k k' h => h𝓕 (by omega)
  set F : ℕ → Set Ω := fun k => S (2 * k + 4) ∩ (U (2 * k + 4))ᶜ with hF
  set G : ℕ → Set Ω := fun k => Ab (2 * k + 4) ∪ U (2 * k + 4) with hG
  have hFm : ∀ k, MeasurableSet[𝓖 (k + 1)] (F k) := fun k =>
    (h𝓕 (by omega : 2 * k + 4 + 1 ≤ 2 * (k + 1) + 4) _ (hS _)).inter
      (h𝓕 (by omega : 2 * k + 4 + 1 ≤ 2 * (k + 1) + 4) _ (hU _)).compl
  have hGF : ∀ k, Disjoint (G k) (F k) := fun k => by
    refine Set.disjoint_left.2 fun ω hG' hF' => ?_
    rcases hG' with hab | hu
    · exact Set.disjoint_left.1 (hSAb _) hF'.1 hab
    · exact hF'.2 hu
  have hnull : P (⋃ m, ⋂ k ≥ m, F k) = 0 :=
    Supp8.GB9Cap.measure_liminf_eq_zero_of_lower h𝓖m (fun k => h𝓕le _) hFm hGF hp₀ hp₀1 hlow
  have hsub : (⋂ j, S j) ⊆ ((⋂ j, S j) ∩ {ω | ∃ᶠ k in atTop, ω ∈ U (2 * k + 4)}) ∪ ⋃ m, ⋂ k ≥ m, F k := by
    intro ω hω
    by_cases hfr : ∃ᶠ k in atTop, ω ∈ U (2 * k + 4)
    · exact Or.inl ⟨hω, hfr⟩
    · right
      rw [not_frequently, eventually_atTop] at hfr
      obtain ⟨m, hm⟩ := hfr
      simp only [mem_iUnion, mem_iInter]
      exact ⟨m, fun k hk => ⟨mem_iInter.1 hω _, hm k hk⟩⟩
  have h1 := le_measureReal_iInter h𝓕 h𝓕le hS hε0 hε1 hsum hstep (P := P)
  have h2 : P.real (⋂ j, S j) ≤
      P.real ((⋂ j, S j) ∩ {ω | ∃ᶠ k in atTop, ω ∈ U (2 * k + 4)}) + P.real (⋃ m, ⋂ k ≥ m, F k) :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have h3 : P.real (⋃ m, ⋂ k ≥ m, F k) = 0 := by rw [measureReal_def, hnull, ENNReal.toReal_zero]
  linarith

end Measure

/-! ### Unbounded relative capacity -/

/-- **A nondecreasing capacity with infinitely many unit increments tends to infinity** ("On perpetual success
infinitely many increments are at least one. Relative capacity is therefore unbounded"). -/
theorem tendsto_atTop_of_frequently_add_one_le {c : ℕ → ℝ} (hc : Monotone c)
    (hfr : ∃ᶠ k in atTop, c k + 1 ≤ c (k + 1)) : Tendsto c atTop atTop := by
  have hN : ∀ N : ℕ, ∃ j, c 0 + N ≤ c j := by
    intro N
    induction N with
    | zero => exact ⟨0, by simp⟩
    | succ N ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨k, hkj, hk⟩ := (frequently_atTop.1 hfr) j
      refine ⟨k + 1, ?_⟩
      have := hc hkj
      push_cast
      linarith
  refine tendsto_atTop_atTop_of_monotone hc fun b => ?_
  obtain ⟨N, hN'⟩ := exists_nat_ge (b - c 0)
  obtain ⟨j, hj⟩ := hN N
  exact ⟨j, by linarith⟩

end GW2TipSkel

end Theorem14

end InteractingSLE
