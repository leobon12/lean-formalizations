/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TipSystemRule
import InteractingSLE.Spec.Supplement.GB9Stop

/-!
# GW2's stage experiment: the stage outcomes from the least qualifying rule

Packet PROVE-T14-TIP12. Follow-up note A.2 and A.4 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt`
L80–L117, L190–L214): "If `K_z` is the retained kernel at state `z`, choose `m(z) = min{m : K_z(E_m) > 1 − ε}`. This
exists for almost every realized state by the strict probability margin. The test events are Borel in the recorded
path, so the existing transition kernel makes this a measurable integer […] It is fixed before the next piece is
revealed"; "enumerate the admissible triples consisting of a buffer, an angle index and a candidate count, and take
the least triple whose finite-candidate success probability exceeds `1 − ε`".

A stage from a node with stage-start state `Z` and retained kernel `K` (`P(Z ∈ C, B) = ∫_{Z ∈ C} K(Z, B) dP`) has
countably many **rules** `i : ℕ` (a buffer, an angle and a candidate count), rule `i` succeeding on the event `E i`
with one of countably many **outcomes** `o` (the switching time), on the events `O i o`. The stage outcome `(i, o)` is
realized when `i` is the selected rule (`GB9Stop.selIndex`, the least index whose success has kernel probability at
least `1 − ε`) and `O i o` occurs (`selOut`). This file proves the two per-node bounds of a stage rule
(`GW2TipSystem.StageRule.IsValid`) for these outcomes:

* `pairwise_disjoint_selOut`: different outcomes are disjoint;
* **`measure_diff_iUnion_selOut_le`**: if almost surely on the stage-start event `Z ∈ C` some rule succeeds with
  kernel probability at least `1 − ε`, the stage fails (no outcome) with probability at most `ε P(Z ∈ C)` — the
  `hstep` field;
* **`measure_inter_iUnion_selOut_diff_le`**: if almost surely the selected rule's "success without a unit" event has
  kernel probability at most `1 − p₀`, so does the stage — the `hunit` field (A.5, the uniform Lemma 5.10);
* `exists_index_of_lt` (A.1's "strict probability margin"): increasing success events whose union has kernel
  probability `> 1 − ε` contain one with probability `≥ 1 − ε`.

The statements are generic (no SLE content).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2TipSystem

open Supp8.GB9Stop

section Select

variable {𝒵 Ω κo : Type*} [m𝒵 : MeasurableSpace 𝒵] [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The stage outcome `(i, o)`**: rule `i` is the selected one and its outcome `o` occurs. -/
def selOut (K : Kernel 𝒵 Ω) (Z : Ω → 𝒵) (E : ℕ → Set Ω) (ε : ℝ≥0∞) (O : ℕ → κo → Set Ω) (c : ℕ × κo) :
    Set Ω :=
  {ω | selIndex K E ε (Z ω) = c.1} ∩ O c.1 c.2

/-- Different stage outcomes are disjoint (one selected rule; disjoint outcomes of one rule). -/
theorem pairwise_disjoint_selOut (K : Kernel 𝒵 Ω) (Z : Ω → 𝒵) (E : ℕ → Set Ω) (ε : ℝ≥0∞) {O : ℕ → κo → Set Ω}
    (hO : ∀ i, Pairwise fun o o' => Disjoint (O i o) (O i o')) :
    Pairwise fun c c' => Disjoint (selOut K Z E ε O c) (selOut K Z E ε O c') := by
  rintro ⟨i, o⟩ ⟨i', o'⟩ hne
  refine Set.disjoint_left.2 fun ω h1 h2 => ?_
  have hi : i = i' := h1.1.symm.trans h2.1
  subst hi
  have ho : o ≠ o' := fun h => hne (by rw [h])
  exact (hO i ho).le_bot ⟨h1.2, h2.2⟩

/-- The selected rule index is measurable in the stage-start state's σ-algebra. -/
theorem measurableSet_selIndex_eq (K : Kernel 𝒵 Ω) (Z : Ω → 𝒵) {E : ℕ → Set Ω} (hE : ∀ i, MeasurableSet (E i))
    (ε : ℝ≥0∞) (i : ℕ) : MeasurableSet[MeasurableSpace.comap Z inferInstance] {ω | selIndex K E ε (Z ω) = i} :=
  ⟨selIndex K E ε ⁻¹' {i}, measurable_selIndex K hE ε (measurableSet_singleton i), rfl⟩

/-- The states at which some rule reaches the level `1 − ε`. -/
def qualSet (K : Kernel 𝒵 Ω) (E : ℕ → Set Ω) (ε : ℝ≥0∞) : Set 𝒵 := {z | ∃ i, 1 - ε ≤ K z (E i)}

theorem measurableSet_qualSet (K : Kernel 𝒵 Ω) {E : ℕ → Set Ω} (hE : ∀ i, MeasurableSet (E i)) (ε : ℝ≥0∞) :
    MeasurableSet (qualSet K E ε) := by
  have e : qualSet K E ε = ⋃ i, {z | 1 - ε ≤ K z (E i)} := by
    ext z; simp only [qualSet, mem_ofPred_eq, mem_iUnion]
  rw [e]
  exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (K.measurable_coe (hE i))

/-- **One stage fails with probability at most `ε`** (`hstep`): if almost surely on `Z ∈ C` some rule succeeds with
kernel probability at least `1 − ε`, then `P(Z ∈ C, no outcome) ≤ ε P(Z ∈ C)`. On the selected rule `i` the failure
event is `Eᵢᶜ`, of kernel probability `1 − K(Eᵢ) ≤ ε`. -/
theorem measure_diff_iUnion_selOut_le {K : Kernel 𝒵 Ω} [IsMarkovKernel K] {Z : Ω → 𝒵} (hZ : Measurable Z)
    {E : ℕ → Set Ω} (hE : ∀ i, MeasurableSet (E i)) {O : ℕ → κo → Set Ω} (hEO : ∀ i, E i ⊆ ⋃ o, O i o)
    (hK : ∀ C B, MeasurableSet C → MeasurableSet B → P (Z ⁻¹' C ∩ B) = ∫⁻ ω in Z ⁻¹' C, K (Z ω) B ∂P)
    {ε : ℝ≥0∞} {C : Set 𝒵} (hC : MeasurableSet C)
    (hex : ∀ᵐ ω ∂P, ω ∈ Z ⁻¹' C → ∃ i, 1 - ε ≤ K (Z ω) (E i)) :
    P (Z ⁻¹' C \ ⋃ c, selOut K Z E ε O c) ≤ ε * P (Z ⁻¹' C) := by
  classical
  set sel : 𝒵 → ℕ := selIndex K E ε with hsel
  have hselm : Measurable sel := measurable_selIndex K hE ε
  have hQ := measurableSet_qualSet K hE ε
  set A : ℕ → Set Ω := fun i => Z ⁻¹' (C ∩ qualSet K E ε ∩ sel ⁻¹' {i}) with hA
  have hAm : ∀ i, MeasurableSet (A i) := fun i => hZ ((hC.inter hQ).inter (hselm (measurableSet_singleton i)))
  have hAd : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.2 fun ω h1 h2 => hij ?_
    have e1 : sel (Z ω) = i := h1.2
    have e2 : sel (Z ω) = j := h2.2
    rw [← e1, ← e2]
  -- the failure event is covered by a null set and the failures of the selected rules
  have hsub : Z ⁻¹' C \ ⋃ c, selOut K Z E ε O c ⊆ Z ⁻¹' (C \ qualSet K E ε) ∪ ⋃ i, (A i \ E i) := by
    rintro ω ⟨hωC, hωn⟩
    by_cases hq : Z ω ∈ qualSet K E ε
    · refine Or.inr (mem_iUnion.2 ⟨sel (Z ω), ⟨⟨⟨hωC, hq⟩, rfl⟩, fun hωE => hωn ?_⟩⟩)
      obtain ⟨o, ho⟩ := mem_iUnion.1 (hEO _ hωE)
      exact mem_iUnion.2 ⟨(sel (Z ω), o), rfl, ho⟩
    · exact Or.inl ⟨hωC, hq⟩
  have hnull : P (Z ⁻¹' (C \ qualSet K E ε)) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hex] with ω hω hmem
    exact hmem.2 (hω hmem.1)
  have hterm : ∀ i, P (A i \ E i) ≤ ε * P (A i) := by
    intro i
    rw [Set.sdiff_eq, show A i = Z ⁻¹' (C ∩ qualSet K E ε ∩ sel ⁻¹' {i}) from rfl,
      hK _ _ ((hC.inter hQ).inter (hselm (measurableSet_singleton i))) (hE i).compl]
    calc ∫⁻ ω in Z ⁻¹' (C ∩ qualSet K E ε ∩ sel ⁻¹' {i}), K (Z ω) (E i)ᶜ ∂P
        ≤ ∫⁻ _ in Z ⁻¹' (C ∩ qualSet K E ε ∩ sel ⁻¹' {i}), ε ∂P := by
          refine setLIntegral_mono measurable_const fun ω hω => ?_
          have hsi : sel (Z ω) = i := hω.2
          have hsp := selIndex_spec K E ε hω.1.2
          rw [← hsel, hsi] at hsp
          rw [prob_compl_eq_one_sub (hE i)]
          exact tsub_le_iff_right.2 (by rw [add_comm]; exact tsub_le_iff_right.1 hsp)
      _ = ε * P (Z ⁻¹' (C ∩ qualSet K E ε ∩ sel ⁻¹' {i})) := by rw [setLIntegral_const]
  have hUA : (⋃ i, A i) ⊆ Z ⁻¹' C := iUnion_subset fun i ω hω => hω.1.1
  calc P (Z ⁻¹' C \ ⋃ c, selOut K Z E ε O c)
      ≤ P (Z ⁻¹' (C \ qualSet K E ε)) + P (⋃ i, (A i \ E i)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + ∑' i, ε * P (A i) := by
        rw [hnull, zero_add, zero_add]
        exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hterm)
    _ = ε * P (⋃ i, A i) := by rw [zero_add, ENNReal.tsum_mul_left, measure_iUnion hAd hAm]
    _ ≤ ε * P (Z ⁻¹' C) := by gcongr

/-- **One stage succeeds without a unit with probability at most `1 − p₀`** (`hunit`): if almost surely on `Z ∈ C`
the selected rule's event `D i`, which contains every outcome `o` of `i` without the unit event `V i o`, has kernel
probability at most `1 − p₀`, then so does the stage. -/
theorem measure_inter_iUnion_selOut_diff_le {K : Kernel 𝒵 Ω} {Z : Ω → 𝒵} (hZ : Measurable Z)
    {E : ℕ → Set Ω} (hE : ∀ i, MeasurableSet (E i)) {O V : ℕ → κo → Set Ω} {D : ℕ → Set Ω}
    (hD : ∀ i, MeasurableSet (D i)) (hOD : ∀ i o, O i o \ V i o ⊆ D i)
    (hK : ∀ C B, MeasurableSet C → MeasurableSet B → P (Z ⁻¹' C ∩ B) = ∫⁻ ω in Z ⁻¹' C, K (Z ω) B ∂P)
    {ε : ℝ≥0∞} {p : ℝ≥0∞} {C : Set 𝒵} (hC : MeasurableSet C)
    (hp : ∀ᵐ ω ∂P, ω ∈ Z ⁻¹' C → K (Z ω) (D (selIndex K E ε (Z ω))) ≤ p) :
    P (Z ⁻¹' C ∩ ⋃ c, (selOut K Z E ε O c \ V c.1 c.2)) ≤ p * P (Z ⁻¹' C) := by
  classical
  set sel : 𝒵 → ℕ := selIndex K E ε with hsel
  have hselm : Measurable sel := measurable_selIndex K hE ε
  set A : ℕ → Set Ω := fun i => Z ⁻¹' (C ∩ sel ⁻¹' {i}) with hA
  have hAm : ∀ i, MeasurableSet (A i) := fun i => hZ (hC.inter (hselm (measurableSet_singleton i)))
  have hAd : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.2 fun ω h1 h2 => hij ?_
    have e1 : sel (Z ω) = i := h1.2
    have e2 : sel (Z ω) = j := h2.2
    rw [← e1, ← e2]
  have hsub : Z ⁻¹' C ∩ ⋃ c, (selOut K Z E ε O c \ V c.1 c.2) ⊆ ⋃ i, (A i ∩ D i) := by
    rintro ω ⟨hωC, hω⟩
    obtain ⟨⟨i, o⟩, ⟨hsi, ho⟩, hv⟩ := mem_iUnion.1 hω
    exact mem_iUnion.2 ⟨i, ⟨hωC, hsi⟩, hOD i o ⟨ho, hv⟩⟩
  have hterm : ∀ i, P (A i ∩ D i) ≤ p * P (A i) := by
    intro i
    rw [show A i = Z ⁻¹' (C ∩ sel ⁻¹' {i}) from rfl, hK _ _ (hC.inter (hselm (measurableSet_singleton i))) (hD i)]
    calc ∫⁻ ω in Z ⁻¹' (C ∩ sel ⁻¹' {i}), K (Z ω) (D i) ∂P
        ≤ ∫⁻ _ in Z ⁻¹' (C ∩ sel ⁻¹' {i}), p ∂P := by
          refine setLIntegral_mono_ae' (hAm i) ?_
          filter_upwards [hp] with ω hω hωA
          have hsi : sel (Z ω) = i := hωA.2
          have h := hω hωA.1
          rwa [hsi] at h
      _ = p * P (Z ⁻¹' (C ∩ sel ⁻¹' {i})) := by rw [setLIntegral_const]
  have hUA : (⋃ i, A i) ⊆ Z ⁻¹' C := iUnion_subset fun i ω hω => hω.1
  calc P (Z ⁻¹' C ∩ ⋃ c, (selOut K Z E ε O c \ V c.1 c.2))
      ≤ ∑' i, P (A i ∩ D i) := (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' i, p * P (A i) := ENNReal.tsum_le_tsum hterm
    _ = p * P (⋃ i, A i) := by rw [ENNReal.tsum_mul_left, measure_iUnion hAd hAm]
    _ ≤ p * P (Z ⁻¹' C) := by gcongr

/-- **A.1's strict probability margin**: increasing events whose union has kernel probability greater than `1 − ε`
contain one of kernel probability at least `1 − ε`. -/
theorem exists_index_of_lt (K : Kernel 𝒵 Ω) {E : ℕ → Set Ω} (hmono : Monotone E) {z : 𝒵} {ε : ℝ≥0∞}
    (hlt : 1 - ε < K z (⋃ m, E m)) : ∃ m, 1 - ε ≤ K z (E m) := by
  have hlim := tendsto_measure_iUnion_atTop (μ := K z) hmono
  obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
  exact ⟨m, hm.le⟩

end Select

end GW2TipSystem

end Theorem14

end InteractingSLE
