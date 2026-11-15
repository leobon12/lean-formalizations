/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField2Code

/-!
# Walls ∪ hull at a walls-dependent stop: the determination-free union law (abstract core)

Packet PROVE-STRIPSYS37. Specification §6.1, Lemma 6.2 and its proof (`source/spec/p145-192.md#lem-6.2`, pp. 155–156),
used with "the walls fully explored and the counterflow stopped at `T(q)`" for Aux. lemmas 35–36 and 124
(`source/spec/p145-192.md` L908–L940, `source/spec/p385-432.md` L171–L196).

Lemma 6.2 needs every explored curve to be determined by the field. For the `κ′ > 4` counterflow of the strip
system that determination is Theorem 1.2 at `κ′`, which ruling R48 forbids here. The proof of Lemma 6.2 uses
determination only to pass the earlier curves' information to `h_{U^c}`; the **last** explored object only needs
its conditional independence. This file proves the corresponding abstract statement for

* walls `Γ` with information `X` that are *determined local* (Lemma 6.2's output for the walls fully explored: for every
  open `U` and every `X`-event `B`, `{Γ ∩ U = ∅} ∩ {X ∈ B}` is almost surely an event of `h_{U^c}`), and
* a monotone hull process `K_t` that is only *marked local* at its own deterministic times and at its own capped
  hitting times of `U` (what the frozen optional hull coupling gives through the capacity coding theorem),

at a stop `T` which may depend on the walls but is a stopping time in the raw sense: the marks before `T` are
`σ(X) ∨ 𝓕_r`-events on `{T < r}` and `σ(X) ∨ 𝓕_σ`-events on `{T = σ}` (the Galmarino property of a raw stopping time of
`(X, path)`; ruling R37 records that the right-continuous version fails already for Lemma 6.2).

## Main results

* `IsCompEvent m P Y E`: `P[E | m]` is almost surely a measurable function of `Y` (for `m = σ(h)` and
  `Y = h − G h` this is the marked avoidance criterion of one event); closure under `∅`, `Ω`, proper differences,
  disjoint unions, countable disjoint unions (`isCompEvent_iUnion`) and intersections with `Y`-events;
* **`isCompEvent_inter_of_isPiSystem`** (the walls union lemma): if `S₀ ∩ {X ∈ B}` is almost surely a `Y`-event for
  every `B`, and every member of a π-system `p` is a good event, then `S₀ ∩ E` is good for every `E ∈ σ(X) ∨ σ(p)`;
* **`isCompEvent_walls_hull_stop`**: `{Γ ∩ U = ∅} ∩ {K_T ∩ U = ∅} ∩ M` is good, by splitting `{K_T ∩ U = ∅}` at the
  capped hitting time `σ` of `U` into `⋃_{r ∈ ℚ} {K_r ∩ U = ∅} ∩ {T < r}` and `{K_σ ∩ U = ∅} ∩ {T = σ}`;
* **`isHistoryAvoidanceLocal_walls_hull`**: the history-marked avoidance criterion (Aux. lemma 18) of
  `E = ℍ ∩ (Γ ∪ K_T)` on `{T < ∞}` (`E = ℍ` elsewhere) for any marks `ℳ` with the raw stopping property.

No field determination of the hull's curve is used. Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopWalls

/-! ### Good events -/

section Def

variable {Ω β : Type*} [MeasurableSpace β]

/-- **A good event**: its conditional probability given `m` is almost surely a measurable function of `Y`. -/
def IsCompEvent (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → β) (E : Set Ω) : Prop :=
  MeasurableSet E ∧ ∃ g : β → ℝ, Measurable g ∧ P⟦E | m⟧ =ᵐ[P] fun ω => g (Y ω)

end Def

section Good

variable {Ω β : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] [MeasurableSpace β] {Y : Ω → β}

omit [IsProbabilityMeasure P] in
/-- Good events are stable under almost sure equality. -/
theorem IsCompEvent.congr_ae {E E' : Set Ω} (hE : IsCompEvent m P Y E) (hE' : MeasurableSet E')
    (he : E =ᵐ[P] E') : IsCompEvent m P Y E' := by
  obtain ⟨-, g, hg, hge⟩ := hE
  exact ⟨hE', g, hg, (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set he.symm)).trans hge⟩

omit [IsProbabilityMeasure P] in
theorem isCompEvent_empty : IsCompEvent m P Y ∅ := by
  refine ⟨MeasurableSet.empty, fun _ => 0, measurable_const, ?_⟩
  have e : (∅ : Set Ω).indicator (fun _ => (1 : ℝ)) = 0 := indicator_empty _
  rw [e, condExp_zero]
  exact Eventually.of_forall fun _ => rfl

theorem isCompEvent_univ (hm : m ≤ mΩ) : IsCompEvent m P Y univ := by
  refine ⟨MeasurableSet.univ, fun _ => 1, measurable_const, ?_⟩
  have e : (univ : Set Ω).indicator (fun _ => (1 : ℝ)) = fun _ => 1 := indicator_univ _
  rw [e, condExp_const hm]

/-- **Proper differences.** -/
theorem IsCompEvent.diff {A B : Set Ω} (hA : IsCompEvent m P Y A) (hB : IsCompEvent m P Y B) (hBA : B ⊆ A) :
    IsCompEvent m P Y (A \ B) := by
  obtain ⟨hAm, gA, hgA, hA'⟩ := hA
  obtain ⟨hBm, gB, hgB, hB'⟩ := hB
  refine ⟨hAm.diff hBm, fun y => gA y - gB y, hgA.sub hgB, ?_⟩
  have hi : (A \ B).indicator (fun _ => (1 : ℝ)) =
      A.indicator (fun _ => (1 : ℝ)) - B.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ B
    · simp [h1, h2]
    · simp [h1, h2]
    · exact absurd (hBA h2) h1
    · simp [h1, h2]
  rw [hi]
  filter_upwards [condExp_sub ((integrable_const (1 : ℝ)).indicator hAm)
    ((integrable_const (1 : ℝ)).indicator hBm) m, hA', hB'] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

/-- **Disjoint unions of two good events.** -/
theorem IsCompEvent.union {A B : Set Ω} (hA : IsCompEvent m P Y A) (hB : IsCompEvent m P Y B)
    (hd : Disjoint A B) : IsCompEvent m P Y (A ∪ B) := by
  obtain ⟨hAm, gA, hgA, hA'⟩ := hA
  obtain ⟨hBm, gB, hgB, hB'⟩ := hB
  refine ⟨hAm.union hBm, fun y => gA y + gB y, hgA.add hgB, ?_⟩
  rw [indicator_union_of_disjoint hd]
  filter_upwards [condExp_add ((integrable_const (1 : ℝ)).indicator hAm)
    ((integrable_const (1 : ℝ)).indicator hBm) m, hA', hB'] with ω h1 h2 h3
  rw [show (fun ω => A.indicator (fun _ => (1 : ℝ)) ω + B.indicator (fun _ => (1 : ℝ)) ω) =
    A.indicator (fun _ => (1 : ℝ)) + B.indicator (fun _ => (1 : ℝ)) from rfl, h1, Pi.add_apply, h2, h3]

/-- **Countable disjoint unions.** -/
theorem isCompEvent_iUnion {E : ℕ → Set Ω} (hE : ∀ i, IsCompEvent m P Y (E i))
    (hd : Pairwise (Disjoint on E)) : IsCompEvent m P Y (⋃ i, E i) := by
  set S : ℕ → Set Ω := fun n => ⋃ i ∈ Finset.range n, E i with hSdef
  have hS : ∀ n, IsCompEvent m P Y (S n) := by
    intro n
    induction n with
    | zero =>
      have e : S 0 = ∅ := by simp [hSdef]
      rw [e]
      exact isCompEvent_empty
    | succ n ih =>
      have e : S (n + 1) = S n ∪ E n := by
        simp only [hSdef, Finset.range_add_one, Finset.mem_insert, iUnion_iUnion_eq_or_left]
        exact union_comm _ _
      rw [e]
      refine ih.union (hE n) (Set.disjoint_left.2 fun ω hω hωn => ?_)
      obtain ⟨i, hi, hωi⟩ := mem_iUnion₂.1 hω
      exact Set.disjoint_left.1 (hd (Finset.mem_range.1 hi).ne) hωi hωn
  have hUm : MeasurableSet (⋃ i, E i) := MeasurableSet.iUnion fun i => (hE i).1
  have hSsub : ∀ n, S n ⊆ ⋃ i, E i := fun n => iUnion₂_subset fun i _ => subset_iUnion E i
  refine ⟨hUm, ?_⟩
  refine WholeField.exists_condExp_eq_comp_of_tendsto hUm (fun n => (hS n).1) ?_ fun n => (hS n).2
  have hanti : Antitone fun n => (⋃ i, E i) \ S n := fun a b hab =>
    sdiff_subset_sdiff_right (biUnion_subset_biUnion_left (Finset.coe_subset.2 (Finset.range_subset_range.2 hab)))
  have hinter : (⋂ n, (⋃ i, E i) \ S n) = ∅ := by
    refine eq_empty_of_forall_notMem fun ω hω => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (mem_iInter.1 hω 0).1
    exact (mem_iInter.1 hω (i + 1)).2 (mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_self i), hi⟩)
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (hUm.diff (hS n).1).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
  rw [hinter, measure_empty] at hlim
  refine hlim.congr fun n => ?_
  simp only [Function.comp_apply]
  congr 1
  rw [symmDiff_comm]
  exact (symmDiff_of_ge (hSsub n)).symm

/-- **Increasing unions.** -/
theorem isCompEvent_iUnion_of_monotone {E : ℕ → Set Ω} (hE : ∀ i, IsCompEvent m P Y (E i)) (hmono : Monotone E) :
    IsCompEvent m P Y (⋃ i, E i) := by
  have hUm : MeasurableSet (⋃ i, E i) := MeasurableSet.iUnion fun i => (hE i).1
  refine ⟨hUm, WholeField.exists_condExp_eq_comp_of_tendsto hUm (fun n => (hE n).1) ?_ fun n => (hE n).2⟩
  have hanti : Antitone fun n => (⋃ i, E i) \ E n := fun a b hab => sdiff_subset_sdiff_right (hmono hab)
  have hinter : (⋂ n, (⋃ i, E i) \ E n) = ∅ := by
    refine eq_empty_of_forall_notMem fun ω hω => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (mem_iInter.1 hω 0).1
    exact (mem_iInter.1 hω i).2 hi
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun n => (hUm.diff (hE n).1).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
  rw [hinter, measure_empty] at hlim
  refine hlim.congr fun n => ?_
  simp only [Function.comp_apply]
  congr 1
  rw [symmDiff_comm]
  exact (symmDiff_of_ge (subset_iUnion E n)).symm

/-- **Intersections with `Y`-events.** -/
theorem IsCompEvent.inter_preimage (hYm : Measurable[m] Y) {B : Set β} (hB : MeasurableSet B)
    (hYm' : Measurable Y) {E : Set Ω} (hE : IsCompEvent m P Y E) : IsCompEvent m P Y (Y ⁻¹' B ∩ E) := by
  obtain ⟨hEm, g, hg, hge⟩ := hE
  refine ⟨(hYm' hB).inter hEm, B.indicator g, hg.indicator hB, ?_⟩
  rw [← indicator_indicator]
  filter_upwards [condExp_indicator ((integrable_const (1 : ℝ)).indicator hEm) (hYm hB), hge] with ω h1 h2
  rw [h1]
  by_cases hω : Y ω ∈ B
  · rw [indicator_of_mem (show ω ∈ Y ⁻¹' B from hω), indicator_of_mem hω, h2]
  · rw [indicator_of_notMem (show ω ∉ Y ⁻¹' B from hω), indicator_of_notMem hω]

end Good

/-! ### The walls union lemma -/

section Walls

variable {Ω β 𝒳 : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] [MeasurableSpace β] {Y : Ω → β} [MeasurableSpace 𝒳]

omit mΩ in
/-- The π-system `{X ∈ B} ∩ F` (`F ∈ p ∪ {Ω}`) generates `σ(X) ∨ σ(p)`. -/
theorem generateFrom_preimage_inter (X : Ω → 𝒳) (p : Set (Set Ω)) :
    MeasurableSpace.generateFrom {s | ∃ B : Set 𝒳, MeasurableSet B ∧ ∃ F ∈ insert univ p, s = X ⁻¹' B ∩ F} =
      MeasurableSpace.comap X inferInstance ⊔ MeasurableSpace.generateFrom p := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (sup_le ?_ ?_)
  · rintro _ ⟨B, hB, F, hF, rfl⟩
    refine MeasurableSet.inter (le_sup_left (a := MeasurableSpace.comap X inferInstance) _
      (MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩)) ?_
    rcases hF with rfl | hF
    · exact MeasurableSet.univ
    · exact le_sup_right (b := MeasurableSpace.generateFrom p) _ (MeasurableSpace.measurableSet_generateFrom hF)
  · rintro _ ⟨B, hB, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨B, hB, univ, mem_insert _ _, (inter_univ _).symm⟩
  · refine MeasurableSpace.generateFrom_le fun F hF => MeasurableSpace.measurableSet_generateFrom
      ⟨univ, MeasurableSet.univ, F, mem_insert_of_mem _ hF, ?_⟩
    rw [preimage_univ, univ_inter]

omit mΩ in
theorem isPiSystem_preimage_inter (X : Ω → 𝒳) {p : Set (Set Ω)} (hp : IsPiSystem p) :
    IsPiSystem {s | ∃ B : Set 𝒳, MeasurableSet B ∧ ∃ F ∈ insert univ p, s = X ⁻¹' B ∩ F} := by
  rintro _ ⟨B, hB, F, hF, rfl⟩ _ ⟨B', hB', F', hF', rfl⟩ hne
  have hFF : (F ∩ F').Nonempty := by
    obtain ⟨ω, hω⟩ := hne
    exact ⟨ω, hω.1.2, hω.2.2⟩
  refine ⟨B ∩ B', hB.inter hB', F ∩ F', hp.insert_univ F hF F' hF' hFF, ?_⟩
  ext ω
  simp only [mem_inter_iff, mem_preimage]
  tauto

/-- **The walls union lemma.** Suppose that for every measurable `B`, `S₀ ∩ {X ∈ B}` is almost surely a `Y`-event (the
walls avoid `U` and carry the information `X`, determined by `h_{U^c}`), and let `p` be a π-system of good events.
Then `S₀ ∩ E` is good for every `E ∈ σ(X) ∨ σ(p)`. -/
theorem isCompEvent_inter_of_isPiSystem (hm : m ≤ mΩ) (hYm : Measurable[m] Y) (hYm' : Measurable Y)
    {X : Ω → 𝒳} (hX : Measurable X) {S₀ : Set Ω} (hS₀ : MeasurableSet S₀)
    (hW : ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set β, MeasurableSet B' ∧ S₀ ∩ X ⁻¹' B =ᵐ[P] Y ⁻¹' B')
    {p : Set (Set Ω)} (hp : IsPiSystem p) (hpg : ∀ F ∈ p, IsCompEvent m P Y F) {E : Set Ω}
    (hE : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ MeasurableSpace.generateFrom p] E) :
    IsCompEvent m P Y (S₀ ∩ E) := by
  set q : Set (Set Ω) := {s | ∃ B : Set 𝒳, MeasurableSet B ∧ ∃ F ∈ insert univ p, s = X ⁻¹' B ∩ F} with hqdef
  have hgood : ∀ F ∈ insert univ p, IsCompEvent m P Y F := by
    rintro F (rfl | hF)
    · exact isCompEvent_univ hm
    · exact hpg F hF
  refine MeasurableSpace.induction_on_inter (C := fun s _ => IsCompEvent m P Y (S₀ ∩ s))
    (generateFrom_preimage_inter X p).symm (isPiSystem_preimage_inter X hp) ?_ ?_ ?_ ?_ E hE
  · rw [inter_empty]
    exact isCompEvent_empty
  · rintro _ ⟨B, hB, F, hF, rfl⟩
    obtain ⟨B', hB', hae⟩ := hW B hB
    have hF' := hgood F hF
    have e : S₀ ∩ (X ⁻¹' B ∩ F) = (S₀ ∩ X ⁻¹' B) ∩ F := (inter_assoc _ _ _).symm
    rw [e]
    exact (hF'.inter_preimage hYm hB' hYm').congr_ae ((hS₀.inter (hX hB)).inter hF'.1)
      (hae.symm.inter EventuallyEq.rfl)
  · intro t htm ht
    have hS : IsCompEvent m P Y S₀ := by
      have h1 : IsCompEvent m P Y (S₀ ∩ (X ⁻¹' univ ∩ univ)) := by
        obtain ⟨B', hB', hae⟩ := hW univ MeasurableSet.univ
        have e : S₀ ∩ (X ⁻¹' univ ∩ univ) = (S₀ ∩ X ⁻¹' univ) ∩ univ := (inter_assoc _ _ _).symm
        rw [e]
        exact ((isCompEvent_univ hm).inter_preimage hYm hB' hYm').congr_ae
          ((hS₀.inter (hX MeasurableSet.univ)).inter MeasurableSet.univ) (hae.symm.inter EventuallyEq.rfl)
      simpa using h1
    have e : S₀ ∩ tᶜ = S₀ \ (S₀ ∩ t) := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [e]
    exact hS.diff ht inter_subset_left
  · intro f hfd _ hf
    rw [inter_iUnion]
    exact isCompEvent_iUnion hf fun i j hij => (hfd hij).mono inter_subset_right inter_subset_right

end Walls

/-! ### The stop -/

section Stop

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **Traces of a join.** If `D` is `𝒮`-measurable and `D ∩ F` is `𝒮`-measurable for every `X`-event and every
`𝒜`-event `F`, then `D ∩ Q` is `𝒮`-measurable for every `Q ∈ σ(X) ∨ 𝒜`. -/
theorem measurableSet_inter_of_sup {𝒮 𝒜 : MeasurableSpace Ω} {D : Set Ω} (hD : MeasurableSet[𝒮] D)
    {X : Ω → 𝒳} (hX : ∀ B : Set 𝒳, MeasurableSet B → MeasurableSet[𝒮] (D ∩ X ⁻¹' B))
    (hA : ∀ F, MeasurableSet[𝒜] F → MeasurableSet[𝒮] (D ∩ F)) {Q : Set Ω}
    (hQ : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ 𝒜] Q) : MeasurableSet[𝒮] (D ∩ Q) := by
  let 𝒯 : MeasurableSpace Ω :=
    { MeasurableSet' := fun Q => MeasurableSet[𝒮] (D ∩ Q)
      measurableSet_empty := by
        simp only [inter_empty]
        exact @MeasurableSet.empty _ 𝒮
      measurableSet_compl := fun Q hQ => by
        have e : D ∩ Qᶜ = D \ (D ∩ Q) := by
          ext ω
          simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
          tauto
        rw [e]
        exact hD.diff hQ
      measurableSet_iUnion := fun f hf => by
        rw [inter_iUnion]
        exact MeasurableSet.iUnion hf }
  have hle : MeasurableSpace.comap X inferInstance ⊔ 𝒜 ≤ 𝒯 := by
    refine sup_le ?_ hA
    rintro _ ⟨B, hB, rfl⟩
    exact hX B hB
  exact hle Q hQ

variable {β : Type*} [MeasurableSpace β] {Y : Ω → β}

/-- **The union law at a raw stop.** Let the walls `S₀ = {Γ ∩ U = ∅}` with information `X` be determined local
(`hW`), let `K_t` be a monotone hull process whose avoidance events are good with the marks `ℱ r` at every deterministic
time and with the marks `ℱσ` at the capped hitting time `σ ≤ N` of `U` (`hσ1`, `hσ2`), and let the stop `T < N` and
the mark `M` satisfy the raw stopping properties `hS1`, `hS2`. Then `{Γ ∩ U = ∅} ∩ {K_T ∩ U = ∅} ∩ M` is good. -/
theorem isCompEvent_walls_hull_stop {m ℱσ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hm : m ≤ mΩ) (hYm : Measurable[m] Y) (hYm' : Measurable Y)
    {X : Ω → 𝒳} (hX : Measurable X) {S₀ : Set Ω} (hS₀ : MeasurableSet S₀)
    (hW : ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set β, MeasurableSet B' ∧ S₀ ∩ X ⁻¹' B =ᵐ[P] Y ⁻¹' B')
    {K : ℝ≥0 → Ω → Set ℂ} {U : Set ℂ} (hKmono : ∀ ω, Monotone fun t => K t ω)
    {ℱ : ℝ≥0 → MeasurableSpace Ω} (hℱmono : Monotone ℱ)
    (hK : ∀ r F, MeasurableSet[ℱ r] F → IsCompEvent m P Y ({ω | Disjoint (K r ω) U} ∩ F))
    {σ : Ω → ℝ≥0}
    (hKσ : ∀ F, MeasurableSet[ℱσ] F → IsCompEvent m P Y ({ω | Disjoint (K (σ ω) ω) U} ∩ F))
    {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N) (hσ1 : ∀ ω (t : ℝ≥0), t < σ ω → Disjoint (K t ω) U)
    (hσ2 : ∀ ω (t : ℝ≥0), σ ω < t → t ≤ N → ¬ Disjoint (K t ω) U)
    {T : Ω → ℝ≥0} {M : Set Ω} (hMT : ∀ ω ∈ M, T ω < N)
    (hS1 : ∀ r : ℝ≥0, MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ℱ r] ({ω | T ω < r} ∩ M))
    (hS2 : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ℱσ] ({ω | T ω = σ ω} ∩ M)) :
    IsCompEvent m P Y (S₀ ∩ ({ω | Disjoint (K (T ω) ω) U} ∩ M)) := by
  -- the π-systems of the deterministic times and of the hitting time
  set p₁ : Set (Set Ω) := {s | ∃ (r : ℝ≥0) (F : Set Ω), MeasurableSet[ℱ r] F ∧
    s = {ω | Disjoint (K r ω) U} ∩ F} with hp₁
  set p₂ : Set (Set Ω) := {s | ∃ F : Set Ω, MeasurableSet[ℱσ] F ∧ s = {ω | Disjoint (K (σ ω) ω) U} ∩ F}
    with hp₂
  have hdisj_max : ∀ ω (r r' : ℝ≥0), (Disjoint (K r ω) U ∧ Disjoint (K r' ω) U) ↔
      Disjoint (K (max r r') ω) U := fun ω r r' => by
    rcases le_total r r' with h | h
    · rw [max_eq_right h]
      exact ⟨fun h' => h'.2, fun h' => ⟨h'.mono_left (hKmono ω h), h'⟩⟩
    · rw [max_eq_left h]
      exact ⟨fun h' => h'.1, fun h' => ⟨h', h'.mono_left (hKmono ω h)⟩⟩
  have hπ₁ : IsPiSystem p₁ := by
    rintro _ ⟨r, F, hF, rfl⟩ _ ⟨r', F', hF', rfl⟩ -
    refine ⟨max r r', F ∩ F', (hℱmono (le_max_left r r') F hF).inter
      (hℱmono (le_max_right r r') F' hF'), ?_⟩
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, ← hdisj_max ω r r']
    tauto
  have hπ₂ : IsPiSystem p₂ := by
    rintro _ ⟨F, hF, rfl⟩ _ ⟨F', hF', rfl⟩ -
    refine ⟨F ∩ F', hF.inter hF', ?_⟩
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  have hg₁ : ∀ F ∈ p₁, IsCompEvent m P Y F := by
    rintro _ ⟨r, F, hF, rfl⟩
    exact hK r F hF
  have hg₂ : ∀ F ∈ p₂, IsCompEvent m P Y F := by
    rintro _ ⟨F, hF, rfl⟩
    exact hKσ F hF
  have hX₁ : ∀ B : Set 𝒳, MeasurableSet B → MeasurableSet[MeasurableSpace.comap X inferInstance ⊔
      MeasurableSpace.generateFrom p₁] (X ⁻¹' B) := fun B hB =>
    le_sup_left (a := MeasurableSpace.comap X inferInstance) _ (MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩)
  have hX₂ : ∀ B : Set 𝒳, MeasurableSet B → MeasurableSet[MeasurableSpace.comap X inferInstance ⊔
      MeasurableSpace.generateFrom p₂] (X ⁻¹' B) := fun B hB =>
    le_sup_left (a := MeasurableSpace.comap X inferInstance) _ (MeasurableSpace.measurableSet_comap.2 ⟨B, hB, rfl⟩)
  -- the event before the hitting time
  set A : Set Ω := ⋃ q : {q : ℚ // ((q : ℝ).toNNReal) ≤ N},
    {ω | Disjoint (K ((q.1 : ℝ).toNNReal) ω) U} ∩ ({ω | T ω < (q.1 : ℝ).toNNReal} ∩ M) with hAdef
  have hAm : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ MeasurableSpace.generateFrom p₁] A := by
    refine MeasurableSet.iUnion fun q => ?_
    have hD : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ MeasurableSpace.generateFrom p₁]
        {ω | Disjoint (K ((q.1 : ℝ).toNNReal) ω) U} := by
      have h := MeasurableSpace.measurableSet_generateFrom (s := p₁)
        ⟨(q.1 : ℝ).toNNReal, univ, MeasurableSet.univ, rfl⟩
      rw [inter_univ] at h
      exact le_sup_right (b := MeasurableSpace.generateFrom p₁) _ h
    refine measurableSet_inter_of_sup hD (fun B hB => hD.inter (hX₁ B hB)) (fun F hF => ?_) (hS1 _)
    exact le_sup_right (b := MeasurableSpace.generateFrom p₁) _
      (MeasurableSpace.measurableSet_generateFrom ⟨(q.1 : ℝ).toNNReal, F, hF, rfl⟩)
  -- the event at the hitting time
  set Bσ : Set Ω := {ω | Disjoint (K (σ ω) ω) U} ∩ ({ω | T ω = σ ω} ∩ M) with hBdef
  have hBm : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ MeasurableSpace.generateFrom p₂] Bσ := by
    have hD : MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ MeasurableSpace.generateFrom p₂]
        {ω | Disjoint (K (σ ω) ω) U} := by
      have h := MeasurableSpace.measurableSet_generateFrom (s := p₂) ⟨univ, MeasurableSet.univ, rfl⟩
      rw [inter_univ] at h
      exact le_sup_right (b := MeasurableSpace.generateFrom p₂) _ h
    refine measurableSet_inter_of_sup hD (fun B hB => hD.inter (hX₂ B hB)) (fun F hF => ?_) hS2
    exact le_sup_right (b := MeasurableSpace.generateFrom p₂) _
      (MeasurableSpace.measurableSet_generateFrom ⟨F, hF, rfl⟩)
  have hA := isCompEvent_inter_of_isPiSystem hm hYm hYm' hX hS₀ hW hπ₁ hg₁ hAm
  have hB := isCompEvent_inter_of_isPiSystem hm hYm hYm' hX hS₀ hW hπ₂ hg₂ hBm
  -- the decomposition
  have hAlt : ∀ ω ∈ A, T ω < σ ω := by
    intro ω hω
    obtain ⟨r, hr⟩ := mem_iUnion.1 hω
    refine lt_of_lt_of_le hr.2.1 (not_lt.1 fun hlt => hσ2 ω _ hlt r.2 hr.1)
  have e : {ω | Disjoint (K (T ω) ω) U} ∩ M = A ∪ Bσ := by
    ext ω
    constructor
    · rintro ⟨hK', hM⟩
      rcases lt_trichotomy (T ω) (σ ω) with hlt | heq | hgt
      · left
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ((T ω : ℝ)) < (σ ω : ℝ) from hlt)
        have hq0 : (0 : ℝ) ≤ q := (T ω).2.trans hq1.le
        have hqT : T ω < (q : ℝ).toNNReal := Real.lt_toNNReal_iff_coe_lt.2 hq1
        have hqσ : (q : ℝ).toNNReal < σ ω := (Real.toNNReal_lt_iff_lt_coe hq0).2 hq2
        exact mem_iUnion.2 ⟨⟨q, hqσ.le.trans (hσN ω)⟩, hσ1 ω _ hqσ, hqT, hM⟩
      · right
        refine ⟨?_, heq, hM⟩
        show Disjoint (K (σ ω) ω) U
        rw [← heq]
        exact hK'
      · exact absurd hK' (hσ2 ω _ hgt (hMT ω hM).le)
    · rintro (hω | ⟨hK', heq, hM⟩)
      · have hlt := hAlt ω hω
        obtain ⟨r, hr⟩ := mem_iUnion.1 hω
        exact ⟨hσ1 ω _ hlt, hr.2.2⟩
      · refine ⟨?_, hM⟩
        show Disjoint (K (T ω) ω) U
        rw [heq]
        exact hK'
  have hdisj : Disjoint (S₀ ∩ A) (S₀ ∩ Bσ) := by
    refine Set.disjoint_left.2 fun ω h1 h2 => ?_
    exact (hAlt ω h1.2).ne h2.2.2.1
  rw [e, inter_union_distrib_left]
  exact hA.union hB hdisj

end Stop

/-! ### The history-marked criterion of `ℍ ∩ (Γ ∪ K_T)` -/

section Assembly

open QuantumZipper (H)
open LQGMetric (DistOn)
open LocalSets

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **The walls with the hull at the stop**: `ℍ ∩ (Γ ∪ K_T)` where `T < ∞`, and `ℍ` elsewhere. -/
def wallsHullAt (Γ : Ω → Set ℂ) (K : ℝ≥0 → Ω → Set ℂ) (T : Ω → ℝ≥0∞) (ω : Ω) : Set ℂ :=
  if T ω < ⊤ then H ∩ (Γ ω ∪ K (T ω).toNNReal ω) else H

theorem disjoint_H_inter_union_iff {Γ K U : Set ℂ} (hUH : U ⊆ H) :
    Disjoint (H ∩ (Γ ∪ K)) U ↔ Disjoint Γ U ∧ Disjoint K U := by
  constructor
  · intro hd
    refine ⟨Set.disjoint_left.2 fun z hz hzU => ?_, Set.disjoint_left.2 fun z hz hzU => ?_⟩
    · exact Set.disjoint_left.1 hd ⟨hUH hzU, Or.inl hz⟩ hzU
    · exact Set.disjoint_left.1 hd ⟨hUH hzU, Or.inr hz⟩ hzU
  · rintro ⟨h1, h2⟩
    refine Set.disjoint_left.2 fun z hz hzU => ?_
    rcases hz.2 with hz | hz
    · exact Set.disjoint_left.1 h1 hz hzU
    · exact Set.disjoint_left.1 h2 hz hzU

/-- **The walls ∪ hull law at a raw stop** (Lemma 6.2 for "the walls fully explored and the hull stopped at `T`",
without field determination of the hull). Hypotheses:
* `hW`: the walls `Γ` with information `X` are determined local (for every `U`, `G` and `X`-event `B`, the event
  `{Γ ∩ U = ∅} ∩ {X ∈ B}` is almost surely an event of `h − G h`);
* `hK`: the monotone hull process `K` is marked local at every deterministic time `r` with the marks `ℱ r`;
* `hσ`: for every `U` and every `N` there is a capped hitting time `σ_N ≤ N` of `U` by `K` at which `K` is marked local
  with marks `ℱσ N`, and on `{T < N}` the marks restricted to `{T = σ_N}` are `σ(X) ∨ ℱσ N`-events;
* `hS1`, `hS0`: the marks restricted to `{T < r}` are `σ(X) ∨ ℱ r`-events, and all marks are `σ(X) ∨ ⋁ᵣ ℱ r`-events.
Then `wallsHullAt Γ K T` satisfies the history-marked avoidance criterion for the marks `ℳ`. -/
theorem isHistoryAvoidanceLocal_walls_hull {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {X : Ω → 𝒳} (hX : Measurable X) {Γ : Ω → Set ℂ} (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G → GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => markovCompl G (h ω)) ⁻¹' B')
    {K : ℝ≥0 → Ω → Set ℂ} (hKmono : ∀ ω, Monotone fun t => K t ω)
    {ℱ : ℝ≥0 → MeasurableSpace Ω} (hℱmono : Monotone ℱ)
    (hK : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G → GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ (r : ℝ≥0) (F : Set Ω), MeasurableSet[ℱ r] F →
        IsCompEvent (MeasurableSpace.comap h inferInstance) P (fun ω => markovCompl G (h ω))
          ({ω | Disjoint (K r ω) U} ∩ F))
    {T : Ω → ℝ≥0∞}
    (hσ : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G → GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∃ (σ : ℕ → Ω → ℝ≥0) (ℱσ : ℕ → MeasurableSpace Ω), ∀ N : ℕ, (∀ ω, σ N ω ≤ N) ∧
        (∀ ω (t : ℝ≥0), t < σ N ω → Disjoint (K t ω) U) ∧
        (∀ ω (t : ℝ≥0), σ N ω < t → t ≤ N → ¬ Disjoint (K t ω) U) ∧
        (∀ F, MeasurableSet[ℱσ N] F → IsCompEvent (MeasurableSpace.comap h inferInstance) P
          (fun ω => markovCompl G (h ω)) ({ω | Disjoint (K (σ N ω) ω) U} ∩ F)) ∧
        ∀ M, MeasurableSet[ℳ] M → MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ℱσ N]
          ({ω | T ω = (σ N ω : ℝ≥0∞)} ∩ ({ω | T ω < N} ∩ M)))
    (hS1 : ∀ M, MeasurableSet[ℳ] M → ∀ r : ℝ≥0,
      MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ℱ r] ({ω | T ω < r} ∩ M))
    (hS0 : ∀ M, MeasurableSet[ℳ] M → MeasurableSet[MeasurableSpace.comap X inferInstance ⊔ ⨆ r, ℱ r] M) :
    WholeField.IsHistoryAvoidanceLocal ℳ (wallsHullAt Γ K T) h P := by
  intro U G hUH hG hMD M hM
  set Y : Ω → DistOn upperHalfPlaneOpens := fun ω => markovCompl G (h ω) with hYdef
  have hm : MeasurableSpace.comap h inferInstance ≤ mΩ := hh.comap_le
  have hYm : Measurable[MeasurableSpace.comap h inferInstance] Y :=
    (measurable_markovCompl hG).comp (comap_measurable h)
  have hYm' : Measurable Y := (measurable_markovCompl hG).comp hh
  have hS₀ : MeasurableSet {ω | Disjoint (Γ ω) U} := hΓ (measurableSet_avoid U.isOpen hUH)
  suffices hgood : IsCompEvent (MeasurableSpace.comap h inferInstance) P Y
      ({ω | Disjoint (wallsHullAt Γ K T ω) U} ∩ M) from hgood.2
  by_cases hU0 : (U : Set ℂ) = ∅
  · -- `U = ∅`: every mark is an event of `σ(X) ∨ ⋁ᵣ ℱ r`, where every event is good
    have e : {ω | Disjoint (wallsHullAt Γ K T ω) U} ∩ M = {ω | Disjoint (Γ ω) U} ∩ M := by
      ext ω
      simp only [hU0, mem_inter_iff, mem_ofPred_eq, disjoint_empty, true_and]
    rw [e]
    set p : Set (Set Ω) := {F | ∃ r, MeasurableSet[ℱ r] F} with hpdef
    have hp : IsPiSystem p := by
      rintro F ⟨r, hF⟩ F' ⟨r', hF'⟩ -
      exact ⟨max r r', (hℱmono (le_max_left r r') F hF).inter (hℱmono (le_max_right r r') F' hF')⟩
    have hpg : ∀ F ∈ p, IsCompEvent (MeasurableSpace.comap h inferInstance) P Y F := by
      rintro F ⟨r, hF⟩
      have h1 := hK U G hUH hG hMD r F hF
      have e1 : {ω | Disjoint (K r ω) U} ∩ F = F := by
        ext ω
        simp only [hU0, mem_inter_iff, mem_ofPred_eq, disjoint_empty, true_and]
      rwa [e1] at h1
    have hle : (⨆ r, ℱ r) ≤ MeasurableSpace.generateFrom p :=
      iSup_le fun r F hF => MeasurableSpace.measurableSet_generateFrom ⟨r, hF⟩
    exact isCompEvent_inter_of_isPiSystem hm hYm hYm' hX hS₀ (hW U G hUH hG hMD) hp hpg
      (sup_le_sup_left hle _ M (hS0 M hM))
  · -- `U ≠ ∅`: the increasing union over the horizons `N`
    have hUne : (U : Set ℂ).Nonempty := nonempty_iff_ne_empty.2 hU0
    obtain ⟨σ, ℱσ, hσN⟩ := hσ U G hUH hG hMD
    set Es : ℕ → Set Ω := fun N => {ω | Disjoint (Γ ω) U} ∩
      ({ω | Disjoint (K (T ω).toNNReal ω) U} ∩ ({ω | T ω < N} ∩ M)) with hEsdef
    have hEs : ∀ N : ℕ, IsCompEvent (MeasurableSpace.comap h inferInstance) P Y (Es N) := by
      intro N
      obtain ⟨hσle, hσ1, hσ2, hKσ, hS2⟩ := hσN N
      refine isCompEvent_walls_hull_stop (ℱσ := ℱσ N) (N := (N : ℝ≥0)) hm hYm hYm' hX hS₀
        (hW U G hUH hG hMD) hKmono hℱmono (hK U G hUH hG hMD) hKσ hσle hσ1 hσ2 ?_ ?_ ?_
      · rintro ω ⟨hTN, -⟩
        have hTN' : T ω < ((N : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hTN
        exact (ENNReal.toNNReal_lt_toNNReal hTN'.ne_top ENNReal.coe_ne_top).2 hTN' |>.trans_le
          (by rw [ENNReal.toNNReal_coe])
      · intro r
        have e : {ω | (T ω).toNNReal < r} ∩ ({ω | T ω < N} ∩ M) = {ω | T ω < r} ∩ ({ω | T ω < N} ∩ M) := by
          ext ω
          simp only [mem_inter_iff, mem_ofPred_eq]
          constructor
          · rintro ⟨h1, h2, h3⟩
            refine ⟨?_, h2, h3⟩
            have hne : T ω ≠ ⊤ := (h2.trans (ENNReal.natCast_lt_top N)).ne
            rw [← ENNReal.coe_toNNReal hne]
            exact_mod_cast h1
          · rintro ⟨h1, h2, h3⟩
            refine ⟨?_, h2, h3⟩
            have hne : T ω ≠ ⊤ := (h2.trans (ENNReal.natCast_lt_top N)).ne
            rw [← ENNReal.coe_toNNReal hne] at h1
            exact_mod_cast h1
        rw [e]
        rcases le_total r (N : ℝ≥0) with hrN | hNr
        · have e' : {ω | T ω < r} ∩ ({ω | T ω < N} ∩ M) = {ω | T ω < r} ∩ M := by
            ext ω
            simp only [mem_inter_iff, mem_ofPred_eq]
            constructor
            · rintro ⟨h1, -, h3⟩
              exact ⟨h1, h3⟩
            · rintro ⟨h1, h3⟩
              refine ⟨h1, h1.trans_le ?_, h3⟩
              exact_mod_cast hrN
          rw [e']
          exact hS1 M hM r
        · have e' : {ω | T ω < r} ∩ ({ω | T ω < N} ∩ M) = {ω | T ω < (N : ℝ≥0)} ∩ M := by
            ext ω
            simp only [mem_inter_iff, mem_ofPred_eq]
            constructor
            · rintro ⟨-, h2, h3⟩
              exact ⟨by exact_mod_cast h2, h3⟩
            · rintro ⟨h2, h3⟩
              refine ⟨h2.trans_le ?_, by exact_mod_cast h2, h3⟩
              exact_mod_cast hNr
          rw [e']
          exact sup_le_sup_left (hℱmono hNr) _ _ (hS1 M hM (N : ℝ≥0))
      · have e : {ω | (T ω).toNNReal = σ N ω} ∩ ({ω | T ω < N} ∩ M) =
            {ω | T ω = (σ N ω : ℝ≥0∞)} ∩ ({ω | T ω < N} ∩ M) := by
          ext ω
          simp only [mem_inter_iff, mem_ofPred_eq]
          constructor
          · rintro ⟨h1, h2, h3⟩
            have hne : T ω ≠ ⊤ := (h2.trans (ENNReal.natCast_lt_top N)).ne
            exact ⟨by rw [← h1, ENNReal.coe_toNNReal hne], h2, h3⟩
          · rintro ⟨h1, h2, h3⟩
            exact ⟨by rw [h1, ENNReal.toNNReal_coe], h2, h3⟩
        rw [e]
        exact hS2 M hM
    have hmono : Monotone Es := by
      intro a b hab ω hω
      have h3 : T ω < (a : ℝ≥0∞) := hω.2.2.1
      refine ⟨hω.1, hω.2.1, show T ω < (b : ℝ≥0∞) from lt_of_lt_of_le h3 ?_, hω.2.2.2⟩
      exact_mod_cast hab
    have hU := isCompEvent_iUnion_of_monotone hEs hmono
    have e : {ω | Disjoint (wallsHullAt Γ K T ω) U} ∩ M = ⋃ N, Es N := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, hEsdef]
      constructor
      · rintro ⟨hd, hM'⟩
        by_cases hT : T ω < ⊤
        · simp only [wallsHullAt, hT, ↓reduceIte] at hd
          obtain ⟨h1, h2⟩ := (disjoint_H_inter_union_iff hUH).1 hd
          obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hT.ne
          exact ⟨N, h1, h2, hN, hM'⟩
        · simp only [wallsHullAt, hT, ↓reduceIte] at hd
          obtain ⟨z, hz⟩ := hUne
          exact absurd hz (Set.disjoint_left.1 hd (hUH hz))
      · rintro ⟨N, h1, h2, hN, hM'⟩
        have hT : T ω < ⊤ := hN.trans (ENNReal.natCast_lt_top N)
        refine ⟨?_, hM'⟩
        simp only [wallsHullAt, hT, ↓reduceIte]
        exact (disjoint_H_inter_union_iff hUH).2 ⟨h1, h2⟩
    rw [e]
    exact hU

end Assembly

end InteractingSLE.Sec7.PocketStopWalls
