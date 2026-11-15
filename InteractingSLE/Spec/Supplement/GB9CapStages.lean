/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB9Stop
import InteractingSLE.Spec.Supplement.GB9Cap

/-!
# GB9 and Lemma 1.2: the selected stopping rule succeeds, and the stages succeed together

Packet PROVE-T14-TIP6. The probabilistic part of Lemma 1.2 of the shortcut note (ruling R52,
`source/external/AstraIG1/ig1_shortcuts_audited.txt` §1.1) and of "Choosing the switches" (§1.2), on top of
PROVE-T14-TIP3's measurable integer selection `GB9Stop.selIndex`:

* `le_measure_inter_selected` (Lemma 1.2, "Its success event is `E_{m(z)}`, which has the stated conditional
  probability"): if a kernel `K` from the stage-start states is a version of the conditional law given the stage-start
  state `Z` (in the integrated form `P(Z⁻¹C ∩ B) = ∫_{Z⁻¹C} K(Z ω)(B) dP`), and the increasing events `E_m` exhaust the
  conditional law (`K(Z ω)(⋃ E_m) = 1` almost surely, "Thus `E_m ↑ Ω` up to the canonical null set"), then the event of
  the rule that inspects `q₁, …, q_{m(Z)}` — the selected event `E_{m(Z)}` — has probability at least `(1 − ε) P(Z⁻¹C)`
  on every event `Z⁻¹C` of the stage-start state;
* `le_measureReal_inter_iInter_Ico` (§1.2, "Conditional union bounds give `P[all stages succeed | initial retained
  datum] ≥ 1 − ε`"; GB9, p. 526: "Take `ε_j = ε 2^{−j}`, so all stages succeed with conditional probability at least
  `1 − ε`"): stage-wise conditional success bounds `(1 − ε_j) P(A) ≤ P(A ∩ S_j)` for `A ∈ 𝓕 j`, `S_j ∈ 𝓕 (j + 1)`,
  multiply along the stages, and `∏ (1 − ε_j) ≥ 1 − Σ ε_j` (`le_measureReal_inter_iInter_Ico_sum`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace GB9Cap

open GB9Stop

/-! ### Lemma 1.2: the success probability of the selected rule -/

section Selected

variable {𝒵 Ω : Type*} [MeasurableSpace 𝒵] [MeasurableSpace Ω] {P : Measure Ω}

/-- **Lemma 1.2, the selected rule succeeds with conditional probability at least `1 − ε`.** -/
theorem le_measure_inter_selected {K : Kernel 𝒵 Ω} {Z : Ω → 𝒵} (hZ : Measurable Z) {E : ℕ → Set Ω}
    (hE : ∀ m, MeasurableSet (E m)) (hmono : Monotone E) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hK : ∀ C B, MeasurableSet C → MeasurableSet B → P (Z ⁻¹' C ∩ B) = ∫⁻ ω in Z ⁻¹' C, K (Z ω) B ∂P)
    (hone : ∀ᵐ ω ∂P, K (Z ω) (⋃ m, E m) = 1) {C : Set 𝒵} (hC : MeasurableSet C) :
    (1 - ε) * P (Z ⁻¹' C) ≤ P (Z ⁻¹' C ∩ {ω | ω ∈ E (selIndex K E ε (Z ω))}) := by
  classical
  set sel : 𝒵 → ℕ := selIndex K E ε with hsel
  have hselm : Measurable sel := measurable_selIndex K hE ε
  set A : ℕ → Set Ω := fun m => Z ⁻¹' (C ∩ sel ⁻¹' {m}) with hA
  have hAm : ∀ m, MeasurableSet (A m) := fun m => hZ (hC.inter (hselm (measurableSet_singleton m)))
  have hAd : Pairwise (Function.onFun Disjoint A) := by
    intro m n hmn
    refine Set.disjoint_left.2 fun ω h1 h2 => hmn ?_
    have e1 : sel (Z ω) = m := h1.2
    have e2 : sel (Z ω) = n := h2.2
    rw [← e1, ← e2]
  have hUA : (⋃ m, A m) = Z ⁻¹' C := by
    ext ω
    simp only [hA, mem_iUnion, mem_preimage, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨sel (Z ω), h, rfl⟩⟩
  have hset : Z ⁻¹' C ∩ {ω | ω ∈ E (sel (Z ω))} = ⋃ m, (A m ∩ E m) := by
    ext ω
    simp only [hA, mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_iUnion, mem_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨sel (Z ω), ⟨h1, rfl⟩, h2⟩, fun ⟨m, ⟨h1, h2⟩, h3⟩ => ⟨h1, by rw [h2]; exact h3⟩⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun m => A m ∩ E m) := fun m n hmn =>
    (hAd hmn).mono inter_subset_left inter_subset_left
  -- the selected events, stage by stage
  have hterm : ∀ m, P (A m ∩ E m) = ∫⁻ ω in A m, K (Z ω) (E (sel (Z ω))) ∂P := by
    intro m
    rw [show A m = Z ⁻¹' (C ∩ sel ⁻¹' {m}) from rfl, hK _ _ (hC.inter (hselm (measurableSet_singleton m))) (hE m)]
    refine setLIntegral_congr_fun (hAm m) fun ω hω => ?_
    have : sel (Z ω) = m := hω.2
    rw [this]
  have hsel_ae : ∀ᵐ ω ∂P, 1 - ε ≤ K (Z ω) (E (sel (Z ω))) := by
    filter_upwards [hone] with ω hω
    exact selIndex_spec K E ε (exists_index_of_tendsto K hmono hω hε)
  calc (1 - ε) * P (Z ⁻¹' C) = ∫⁻ _ in Z ⁻¹' C, (1 - ε) ∂P := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ ω in Z ⁻¹' C, K (Z ω) (E (sel (Z ω))) ∂P := setLIntegral_mono_ae' (hZ hC) (hsel_ae.mono
        fun ω hω _ => hω)
    _ = ∑' m, ∫⁻ ω in A m, K (Z ω) (E (sel (Z ω))) ∂P := by
        rw [← hUA, lintegral_iUnion hAm hAd]
    _ = ∑' m, P (A m ∩ E m) := by simp only [hterm]
    _ = P (Z ⁻¹' C ∩ {ω | ω ∈ E (sel (Z ω))}) := by
        rw [hset, measure_iUnion hdisj fun m => (hAm m).inter (hE m)]

end Selected

/-! ### The stages succeed together -/

section Stages

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Conditional success bounds multiply along the stages.** For increasing σ-algebras `𝓕 j` (the information at the
start of stage `j`), stage success events `S j ∈ 𝓕 (j + 1)` with `(1 − ε_j) P(A) ≤ P(A ∩ S j)` for `A ∈ 𝓕 j`, and
`ε_j ≤ 1`: for `A ∈ 𝓕 m`, `∏_{j ∈ [m, m + n)} (1 − ε_j) P(A) ≤ P(A ∩ ⋂_{j ∈ [m, m + n)} S j)`. -/
theorem le_measureReal_inter_iInter_Ico [IsFiniteMeasure P] {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : Monotone 𝓕)
    {S : ℕ → Set Ω} (hS : ∀ j, MeasurableSet[𝓕 (j + 1)] (S j)) {ε : ℕ → ℝ} (hε1 : ∀ j, ε j ≤ 1)
    (hstep : ∀ j A, MeasurableSet[𝓕 j] A → (1 - ε j) * P.real A ≤ P.real (A ∩ S j)) (m : ℕ) {A : Set Ω}
    (hA : MeasurableSet[𝓕 m] A) :
    ∀ n : ℕ, (∏ j ∈ Finset.Ico m (m + n), (1 - ε j)) * P.real A ≤
      P.real (A ∩ ⋂ j ∈ Finset.Ico m (m + n), S j)
  | 0 => by simp
  | n + 1 => by
    have ih := le_measureReal_inter_iInter_Ico h𝓕 hS hε1 hstep m hA n
    have hset : A ∩ ⋂ j ∈ Finset.Ico m (m + (n + 1)), S j =
        (A ∩ ⋂ j ∈ Finset.Ico m (m + n), S j) ∩ S (m + n) := by
      ext ω
      simp only [mem_inter_iff, mem_iInter, Finset.mem_Ico]
      constructor
      · rintro ⟨hA', h⟩
        exact ⟨⟨hA', fun j hj => h j ⟨hj.1, by omega⟩⟩, h (m + n) ⟨by omega, by omega⟩⟩
      · rintro ⟨⟨hA', h⟩, h'⟩
        refine ⟨hA', fun j hj => ?_⟩
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 (show j < m + n + 1 by omega)) with hlt | rfl
        · exact h j ⟨hj.1, hlt⟩
        · exact h'
    have hB : MeasurableSet[𝓕 (m + n)] (A ∩ ⋂ j ∈ Finset.Ico m (m + n), S j) :=
      (h𝓕 (Nat.le_add_right m n) _ hA).inter (Finset.measurableSet_biInter _ fun j hj =>
        h𝓕 (show j + 1 ≤ m + n by have := (Finset.mem_Ico.1 hj).2; omega) _ (hS j))
    have hprod : ∏ j ∈ Finset.Ico m (m + (n + 1)), (1 - ε j) =
        (∏ j ∈ Finset.Ico m (m + n), (1 - ε j)) * (1 - ε (m + n)) := by
      rw [show m + (n + 1) = (m + n) + 1 by ring, Finset.prod_Ico_succ_top (Nat.le_add_right m n)]
    rw [hset, hprod]
    calc (∏ j ∈ Finset.Ico m (m + n), (1 - ε j)) * (1 - ε (m + n)) * P.real A
        = (1 - ε (m + n)) * ((∏ j ∈ Finset.Ico m (m + n), (1 - ε j)) * P.real A) := by ring
      _ ≤ (1 - ε (m + n)) * P.real (A ∩ ⋂ j ∈ Finset.Ico m (m + n), S j) :=
          mul_le_mul_of_nonneg_left ih (by linarith [hε1 (m + n)])
      _ ≤ _ := hstep _ _ hB

/-- `∏ (1 − ε_j) ≥ 1 − Σ ε_j` for `0 ≤ ε_j ≤ 1`. -/
theorem one_sub_sum_le_prod (s : Finset ℕ) {ε : ℕ → ℝ} (hε0 : ∀ j, 0 ≤ ε j) (hε1 : ∀ j, ε j ≤ 1) :
    1 - ∑ j ∈ s, ε j ≤ ∏ j ∈ s, (1 - ε j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hp : 0 ≤ ∏ j ∈ s, (1 - ε j) := Finset.prod_nonneg fun j _ => by linarith [hε1 j]
    have hp1 : ∏ j ∈ s, (1 - ε j) ≤ 1 :=
      Finset.prod_le_one₀ (fun j _ => by linarith [hε1 j]) fun j _ => by linarith [hε0 j]
    nlinarith [hε0 a, hε1 a]

/-- **All stages succeed with conditional probability at least `1 − Σ ε_j`** (GB9, p. 526; shortcut note §1.2). -/
theorem le_measureReal_inter_iInter_Ico_sum [IsFiniteMeasure P] {𝓕 : ℕ → MeasurableSpace Ω} (h𝓕 : Monotone 𝓕)
    {S : ℕ → Set Ω} (hS : ∀ j, MeasurableSet[𝓕 (j + 1)] (S j)) {ε : ℕ → ℝ} (hε0 : ∀ j, 0 ≤ ε j)
    (hε1 : ∀ j, ε j ≤ 1) (hstep : ∀ j A, MeasurableSet[𝓕 j] A → (1 - ε j) * P.real A ≤ P.real (A ∩ S j))
    (m : ℕ) {A : Set Ω} (hA : MeasurableSet[𝓕 m] A) (n : ℕ) :
    (1 - ∑ j ∈ Finset.Ico m (m + n), ε j) * P.real A ≤ P.real (A ∩ ⋂ j ∈ Finset.Ico m (m + n), S j) :=
  (mul_le_mul_of_nonneg_right (one_sub_sum_le_prod _ hε0 hε1) measureReal_nonneg).trans
    (le_measureReal_inter_iInter_Ico h𝓕 hS hε1 hstep m hA n)

end Stages

end GB9Cap

end Supp8

end InteractingSLE
