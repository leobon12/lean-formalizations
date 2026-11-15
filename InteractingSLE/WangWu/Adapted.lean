/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Locality
import InteractingSLE.GFF.LocalSets.UnionLaw
import InteractingSLE.Spec.Sec6.CondMeanStop

/-!
# Wang–Wu Lemma 4.5: adapted finite unions of field-determined local sets

Packet PROVE-WW-B5. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.1,
Lemma 4.5 (p. 17, text dump L1034–1056):

> **Lemma 4.5** (Adapted finite unions). Let `γ₁, …, γ_k` be continuous, field-determined curves whose initial
> segments at stopping times are local. Expose successively an initial segment of each curve, allowing the stopping
> time of the next curve to depend on the previously exposed segments. The finite union of the exposed segments is
> local and determined by the field.
>
> *Proof.* Use induction on the number of segments. For a deterministic open set `U`, let `σ_j = inf{t : γ_j(t) ∈ U}`.
> … Lemma 4.4 shows that this stopped curve is determined by `h_{U^c}`. Its eventwise version applied to the
> preceding union makes both that union's avoidance event and its cemetery-valued restriction measurable from
> `h_{U^c}`. On this event the stopping-time rule can consequently be evaluated until `σ_j` from `h_{U^c}`. In
> particular, the event that the new stopped segment avoids `U`, and the segment itself on that event, are
> determined by `h_{U^c}`. The avoidance characterization of local sets gives locality of the new union.

## Main results

* **Lemma 4.5** (`isLocalSet_explored_and_aeDetermined`): for curves `η₁, …, η_k` (continuous, deterministic starting
  points, field-determined, history-sensitively local at first entrance times) stopped successively at Galmarino
  stopping times `τ_j` of the filtrations enlarged by the earlier exposed segments, the exposed union
  `explored η τ = ⋃ η_i([0, τ_i]) ∩ ℍ` is local **and determined by the field**. Locality is the specification's
  Lemma 6.2 at stopping times, landed as `Sec6.isLocalSet_explored` (PROVE-SEC6-A3: the same statement, proved by the
  same first-entrance-time argument, ruling R37); field determination is new here (`aeDeterminedSigma_explored`: the
  stopping times are the Galmarino reconstruction `recon` from the complete paths, `eq_recon_top`).
* **The avoidance characterization for field-determined sets** (`isLocalSet_iff_isMarkedDetermined`): a
  field-determined random relatively closed set `S` is local iff for every deterministic open `U ⊆ ℍ` (and Borel
  version `G` of the projection onto `H(U)`) the σ-algebra `markedSigma S U` of the avoidance event `{S ∩ U = ∅}` and of
  the cemetery-valued restriction `S_U` is a.s. determined by `h_{U^c} = h − G h` (`⇒`: Lemma 4.4, landed as
  `IsLocalSet.aeDeterminedSigma_markedSigma`; `⇐`: Lemma 3.6 (ii) ⇒ (iv), since a σ-algebra a.s. determined by `𝒢` is
  conditionally independent of everything given `𝒢`).
* **The union step for arbitrary random sets** (`markedSigma_union_le`, `isLocalSet_union_of_isRelMarkedDetermined`):
  if `A` is a field-determined local set and the trace of `markedSigma B U` on `{A ∩ U = ∅}` is determined by
  `h_{U^c}` for every `U` ("on this event … the event that the new stopped segment avoids `U`, and the segment itself on
  that event, are determined by `h_{U^c}`"), then `A ∪ B` is local and field-determined; `B` need not be local by
  itself. This is the set-level form of the induction step, usable when the new piece is not a curve segment.
* **Without adaptedness** (`isLocalSet_union_of_aeDetermined`, `isLocalSet_biUnion_of_aeDetermined`): finite unions of
  field-determined local sets are local and field-determined (used in the proof of Proposition 4.19: "Expose `β` and
  `α[0, r]`. Their union is local by Lemma 4.5").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open LQGMetric (DistOn CondIndepEv AEDeterminedSigma IsZeroBoundaryGFF)
open QuantumZipper (H)
open InteractingSLE.LocalSets
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

/-! ### The trace of a σ-algebra on an event -/

section Trace

variable {Ω : Type*}

/-- The trace σ-algebra of `m` on a measurable event `E`, pulled back to `Ω`: the sets `s` with `E ∩ s` measurable
for `m`. -/
@[instance_reducible]
def traceSigma (m : MeasurableSpace Ω) (E : Set Ω) (hE : MeasurableSet[m] E) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[m] (E ∩ s)
  measurableSet_empty := by simp
  measurableSet_compl s hs := by
    have e : E ∩ sᶜ = E \ (E ∩ s) := by
      ext ω; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [e]
    exact @MeasurableSet.diff Ω m _ _ hE hs
  measurableSet_iUnion f hf := by
    rw [inter_iUnion]
    exact @MeasurableSet.iUnion Ω ℕ m _ _ hf

theorem measurableSet_traceSigma_iff {m : MeasurableSpace Ω} {E : Set Ω} (hE : MeasurableSet[m] E)
    {s : Set Ω} : MeasurableSet[traceSigma m E hE] s ↔ MeasurableSet[m] (E ∩ s) := Iff.rfl

theorem le_traceSigma {m : MeasurableSpace Ω} {E : Set Ω} (hE : MeasurableSet[m] E) :
    m ≤ traceSigma m E hE := fun _ hs => @MeasurableSet.inter Ω m _ _ hE hs

end Trace

/-! ### The marked σ-algebra of a union -/

section Marked

variable {Ω : Type*}

theorem markedSet_of_disjoint {U S : Set ℂ} (h : Disjoint S U) : markedSet U S = S := by
  ext z; simp [markedSet, h]

theorem markedSet_of_not_disjoint {U S : Set ℂ} (h : ¬ Disjoint S U) : markedSet U S = ∅ := by
  ext z; simp [markedSet, h]

theorem measurableSet_avoid_markedSigma (A : Ω → Set ℂ) (U : Set ℂ) :
    MeasurableSet[markedSigma A U] {ω | Disjoint (A ω) U} :=
  (le_sup_left : MeasurableSpace.generateFrom _ ≤ markedSigma A U) _
    (MeasurableSpace.measurableSet_generateFrom (mem_singleton _))

theorem measurable_markedSet_markedSigma (A : Ω → Set ℂ) (U : Set ℂ) :
    Measurable[markedSigma A U, hittingSigma] fun ω => markedSet U (A ω) :=
  fun _ hM => (le_sup_right : MeasurableSpace.comap _ _ ≤ markedSigma A U) _ ⟨_, hM, rfl⟩

/-- **The union step of Lemma 4.5.** If the marked σ-algebra of `A` is contained in `𝒢`, and the trace of the marked
σ-algebra of `B` on the avoidance event `{A ∩ U = ∅}` is contained in `𝒢`, then the marked σ-algebra of `A ∪ B` is
contained in `𝒢`. -/
theorem markedSigma_union_le {A B : Ω → Set ℂ} {U : Set ℂ} {𝒢 : MeasurableSpace Ω}
    (hA : markedSigma A U ≤ 𝒢)
    (hB : ∀ s, MeasurableSet[markedSigma B U] s → MeasurableSet[𝒢] ({ω | Disjoint (A ω) U} ∩ s)) :
    markedSigma (fun ω => A ω ∪ B ω) U ≤ 𝒢 := by
  set EA : Set Ω := {ω | Disjoint (A ω) U} with hEAdef
  set EB : Set Ω := {ω | Disjoint (B ω) U} with hEBdef
  have hEA : MeasurableSet[𝒢] EA := hA _ (measurableSet_avoid_markedSigma A U)
  set 𝒯 := traceSigma 𝒢 EA hEA
  have hA𝒯 : markedSigma A U ≤ 𝒯 := hA.trans (le_traceSigma hEA)
  have hB𝒯 : markedSigma B U ≤ 𝒯 := hB
  have hEB𝒯 : MeasurableSet[𝒯] EB := hB𝒯 _ (measurableSet_avoid_markedSigma B U)
  have hE : {ω | Disjoint (A ω ∪ B ω) U} = EA ∩ EB := by
    ext ω; simp [hEAdef, hEBdef, disjoint_union_left]
  have hE𝒢 : MeasurableSet[𝒢] (EA ∩ EB) := hEB𝒯
  refine sup_le ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ rfl
    rw [hE]
    exact hE𝒢
  · rintro _ ⟨M, hM, rfl⟩
    -- the union of the two cemetery-valued restrictions
    have hmA := measurable_markedSet_markedSigma A U
    have hmB := measurable_markedSet_markedSigma B U
    have hU : Measurable[markedSigma A U ⊔ markedSigma B U, hittingSigma]
        fun ω => markedSet U (A ω) ∪ markedSet U (B ω) :=
      @measurable_union_hitting Ω (markedSigma A U ⊔ markedSigma B U) _ _
        (hmA.mono le_sup_left le_rfl) (hmB.mono le_sup_right le_rfl)
    have hX : MeasurableSet[𝒯] {ω | markedSet U (A ω) ∪ markedSet U (B ω) ∈ M} :=
      (sup_le hA𝒯 hB𝒯) _ (hU hM)
    have hX' : MeasurableSet[𝒢] (EA ∩ (EB ∩ {ω | markedSet U (A ω) ∪ markedSet U (B ω) ∈ M})) :=
      @MeasurableSet.inter Ω 𝒯 _ _ hEB𝒯 hX
    have hc : MeasurableSet[𝒢] ((EA ∩ EB)ᶜ ∩ {_ω | (∅ : Set ℂ) ∈ M}) := by
      by_cases h0 : (∅ : Set ℂ) ∈ M
      · simpa [h0] using hE𝒢.compl
      · simp [h0]
    have e : (fun ω => markedSet U (A ω ∪ B ω)) ⁻¹' M =
        (EA ∩ (EB ∩ {ω | markedSet U (A ω) ∪ markedSet U (B ω) ∈ M})) ∪
          ((EA ∩ EB)ᶜ ∩ {_ω | (∅ : Set ℂ) ∈ M}) := by
      ext ω
      by_cases hω : ω ∈ EA ∩ EB
      · obtain ⟨ha, hb⟩ := hω
        have hab : Disjoint (A ω ∪ B ω) U := disjoint_union_left.2 ⟨ha, hb⟩
        simp only [mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
        rw [markedSet_of_disjoint hab, markedSet_of_disjoint ha, markedSet_of_disjoint hb]
        exact ⟨fun h => Or.inl ⟨ha, hb, h⟩, fun h => h.elim (fun h => h.2.2)
          (fun h => absurd ⟨ha, hb⟩ h.1)⟩
      · have hab : ¬ Disjoint (A ω ∪ B ω) U := by
          rw [disjoint_union_left]; exact hω
        simp only [mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
        rw [markedSet_of_not_disjoint hab]
        exact ⟨fun h => Or.inr ⟨hω, h⟩, fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hω)
          (fun h => h.2)⟩
    rw [e]
    exact @MeasurableSet.union Ω 𝒢 _ _ hX' hc

end Marked

/-! ### The avoidance characterization for field-determined sets -/

section Local

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Marked determination** (the conclusion of Lemma 4.4): for every deterministic open `U ⊆ ℍ` and every Borel
version `G` of the projection onto `H(U)`, the marked σ-algebra of `S` (avoidance event `{S ∩ U = ∅}` and
cemetery-valued restriction `S_U`) is a.s. determined by the complementary projection `h_{U^c} = h − G h`. -/
def IsMarkedDetermined (S : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω) : Prop :=
  ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
    (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      markedSigma S U ≤
        LocalSets.aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P

/-- **Relative marked determination of `B` given `A`** (the step "on this event the stopping-time rule can be
evaluated until `σ_j` from `h_{U^c}`; in particular, the event that the new stopped segment avoids `U`, and the
segment itself on that event, are determined by `h_{U^c}`"): for every deterministic open `U ⊆ ℍ` and Borel version
`G`, the trace of the marked σ-algebra of `B` on the avoidance event `{A ∩ U = ∅}` is a.s. determined by `h − G h`. -/
def IsRelMarkedDetermined (A B : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω) : Prop :=
  ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
    (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ s, MeasurableSet[markedSigma B U] s →
        MeasurableSet[LocalSets.aeSigma
          (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P]
          ({ω | Disjoint (A ω) U} ∩ s)

/-- **Lemma 4.4 in marked-determination form**: a field-determined local set is marked-determined. -/
theorem IsLocalSet.isMarkedDetermined (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {S : Ω → Set ℂ} (hS : Measurable[mΩ, hittingSigma] S) (hloc : IsLocalSet S h P)
    (hdet : AEDeterminedSigma (MeasurableSpace.comap S hittingSigma)
      (MeasurableSpace.comap h inferInstance) P) :
    IsMarkedDetermined S h P := fun U G hUH hG hd s hs =>
  IsLocalSet.aeDeterminedSigma_markedSigma hh.measurable hS hloc hdet U hUH G hG hd s hs

/-- **The avoidance characterization, converse direction**: a marked-determined random relatively closed set is
local (Lemma 3.6 (ii) ⇒ (iv): a σ-algebra a.s. determined by `σ(h − G h)` is conditionally independent of `σ(G h)`
given `σ(h − G h)`). -/
theorem isLocalSet_of_isMarkedDetermined (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {S : Ω → Set ℂ} (hS : Measurable[mΩ, hittingSigma] S)
    (hSc : ∀ᵐ ω ∂P, S ω ⊆ H ∧ IsOpen (H \ S ω)) (hm : IsMarkedDetermined S h P) :
    IsLocalSet S h P := by
  refine ((isLocalSet_tfae hh hS hSc).out 2 4).1 fun U G hUH hG hd => ?_
  have hYm : Measurable fun ω => markovCompl G (h ω) := (measurable_markovCompl hG).comp hh.measurable
  have hXm : Measurable fun ω => G (h ω) := hG.comp hh.measurable
  exact Sec6.condIndepEv_of_le_aeSigma hYm.comap_le hXm.comap_le (hm U G hUH hG hd)

/-- **The avoidance characterization of field-determined local sets**: a field-determined random relatively closed
set is local iff it is marked-determined. -/
theorem isLocalSet_iff_isMarkedDetermined (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {S : Ω → Set ℂ} (hS : Measurable[mΩ, hittingSigma] S)
    (hSc : ∀ᵐ ω ∂P, S ω ⊆ H ∧ IsOpen (H \ S ω))
    (hdet : AEDeterminedSigma (MeasurableSpace.comap S hittingSigma)
      (MeasurableSpace.comap h inferInstance) P) :
    IsLocalSet S h P ↔ IsMarkedDetermined S h P :=
  ⟨fun hloc => IsLocalSet.isMarkedDetermined hh hS hloc hdet, isLocalSet_of_isMarkedDetermined hh hS hSc⟩

omit [IsProbabilityMeasure P] in
/-- Marked determination of a union from marked determination of the first set and relative marked determination of
the second (`markedSigma_union_le`). -/
theorem IsMarkedDetermined.union {A B : Ω → Set ℂ} (hA : IsMarkedDetermined A h P)
    (hB : IsRelMarkedDetermined A B h P) : IsMarkedDetermined (fun ω => A ω ∪ B ω) h P :=
  fun U G hUH hG hd => markedSigma_union_le (hA U G hUH hG hd) (hB U G hUH hG hd)

omit [IsProbabilityMeasure P] in
/-- Two marked-determined sets: the second is relatively marked-determined given the first. -/
theorem IsMarkedDetermined.isRelMarkedDetermined {A B : Ω → Set ℂ} (hA : IsMarkedDetermined A h P)
    (hB : IsMarkedDetermined B h P) : IsRelMarkedDetermined A B h P :=
  fun U G hUH hG hd s hs => @MeasurableSet.inter Ω _ _ _
    (hA U G hUH hG hd _ (measurableSet_avoid_markedSigma A U)) (hB U G hUH hG hd s hs)

omit [IsProbabilityMeasure P] in
/-- Field determination of a union of two field-determined sets. -/
theorem aeDeterminedSigma_union {𝒢 : MeasurableSpace Ω} {A B : Ω → Set ℂ}
    (hA : AEDeterminedSigma (MeasurableSpace.comap A hittingSigma) 𝒢 P)
    (hB : AEDeterminedSigma (MeasurableSpace.comap B hittingSigma) 𝒢 P) :
    AEDeterminedSigma (MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma) 𝒢 P := by
  have hA' : Measurable[LocalSets.aeSigma 𝒢 P, hittingSigma] A := fun M hM => hA _ ⟨M, hM, rfl⟩
  have hB' : Measurable[LocalSets.aeSigma 𝒢 P, hittingSigma] B := fun M hM => hB _ ⟨M, hM, rfl⟩
  have hU := @measurable_union_hitting Ω (LocalSets.aeSigma 𝒢 P) _ _ hA' hB'
  rintro _ ⟨M, hM, rfl⟩
  exact hU hM

/-- **Wang–Wu Lemma 4.5, one adapted step.** Let `A` be a field-determined local set and `B` a field-determined random
relatively closed set which is relatively marked-determined given `A` (`IsRelMarkedDetermined`: on the avoidance event
of `A`, the avoidance event of `B` and `B` itself are determined by the complementary projection; this is what a
segment stopped by a rule depending on `A` satisfies). Then `A ∪ B` is local and field-determined. `B` need not be
local by itself. -/
theorem isLocalSet_union_of_isRelMarkedDetermined (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A B : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A) (hB : Measurable[mΩ, hittingSigma] B)
    (hlocA : IsLocalSet A h P)
    (hdetA : AEDeterminedSigma (MeasurableSpace.comap A hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hdetB : AEDeterminedSigma (MeasurableSpace.comap B hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω)) (hrel : IsRelMarkedDetermined A B h P) :
    IsLocalSet (fun ω => A ω ∪ B ω) h P ∧
      AEDeterminedSigma (MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma)
        (MeasurableSpace.comap h inferInstance) P := by
  refine ⟨isLocalSet_of_isMarkedDetermined hh (measurable_union_hitting hA hB) ?_
    ((IsLocalSet.isMarkedDetermined hh hA hlocA hdetA).union hrel), aeDeterminedSigma_union hdetA hdetB⟩
  filter_upwards [hlocA.2.1, hBc] with ω ⟨hs₁, ho₁⟩ ⟨hs₂, ho₂⟩
  refine ⟨union_subset hs₁ hs₂, ?_⟩
  have e : H \ (A ω ∪ B ω) = (H \ A ω) ∩ (H \ B ω) := by
    ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
  rw [e]
  exact ho₁.inter ho₂

/-- **Wang–Wu Lemma 4.5 without adaptedness**: the union of two field-determined local sets is local and
field-determined. -/
theorem isLocalSet_union_of_aeDetermined (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A B : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A) (hB : Measurable[mΩ, hittingSigma] B)
    (hlocA : IsLocalSet A h P) (hlocB : IsLocalSet B h P)
    (hdetA : AEDeterminedSigma (MeasurableSpace.comap A hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hdetB : AEDeterminedSigma (MeasurableSpace.comap B hittingSigma)
      (MeasurableSpace.comap h inferInstance) P) :
    IsLocalSet (fun ω => A ω ∪ B ω) h P ∧
      AEDeterminedSigma (MeasurableSpace.comap (fun ω => A ω ∪ B ω) hittingSigma)
        (MeasurableSpace.comap h inferInstance) P :=
  isLocalSet_union_of_isRelMarkedDetermined hh hA hB hlocA hdetA hdetB hlocB.2.1
    ((IsLocalSet.isMarkedDetermined hh hA hlocA hdetA).isRelMarkedDetermined
      (IsLocalSet.isMarkedDetermined hh hB hlocB hdetB))

/-- The empty set is a field-determined local set. -/
theorem isLocalSet_empty (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) :
    IsLocalSet (fun _ : Ω => (∅ : Set ℂ)) h P := by
  refine isLocalSet_of_isMarkedDetermined hh measurable_const
    (Eventually.of_forall fun _ => ⟨empty_subset _, by simpa using QuantumZipper.isOpen_H⟩) ?_
  intro U G hUH hG hd
  refine sup_le ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ rfl
    simp
  · rintro _ ⟨M, -, rfl⟩
    by_cases h0 : markedSet (U : Set ℂ) ∅ ∈ M
    · simp [h0]
    · simp [h0]

/-- **Wang–Wu Lemma 4.5 without adaptedness, finite families**: a finite union of field-determined local sets is
local and field-determined. -/
theorem isLocalSet_biUnion_of_aeDetermined (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {ι : Type*} (s : Finset ι) {A : ι → Ω → Set ℂ}
    (hA : ∀ i ∈ s, Measurable[mΩ, hittingSigma] (A i)) (hloc : ∀ i ∈ s, IsLocalSet (A i) h P)
    (hdet : ∀ i ∈ s, AEDeterminedSigma (MeasurableSpace.comap (A i) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P) :
    IsLocalSet (fun ω => ⋃ i ∈ s, A i ω) h P ∧
      AEDeterminedSigma (MeasurableSpace.comap (fun ω => ⋃ i ∈ s, A i ω) hittingSigma)
        (MeasurableSpace.comap h inferInstance) P ∧
      Measurable[mΩ, hittingSigma] (fun ω => ⋃ i ∈ s, A i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
    refine ⟨isLocalSet_empty hh, ?_, measurable_const⟩
    rintro _ ⟨M, -, rfl⟩
    by_cases h0 : (∅ : Set ℂ) ∈ M
    · exact ⟨univ, @MeasurableSet.univ Ω (MeasurableSpace.comap h inferInstance), by simp [h0]⟩
    · exact ⟨∅, @MeasurableSet.empty Ω (MeasurableSpace.comap h inferInstance), by simp [h0]⟩
  | insert j s hj ih =>
    obtain ⟨hl, hd, hm⟩ := ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
      (fun i hi => hloc i (Finset.mem_insert_of_mem hi))
      (fun i hi => hdet i (Finset.mem_insert_of_mem hi))
    have e : (fun ω => ⋃ i ∈ insert j s, A i ω) = fun ω => A j ω ∪ ⋃ i ∈ s, A i ω := by
      funext ω; simp
    rw [e]
    obtain ⟨h1, h2⟩ := isLocalSet_union_of_aeDetermined hh (hA j (Finset.mem_insert_self j s)) hm
      (hloc j (Finset.mem_insert_self j s)) hl (hdet j (Finset.mem_insert_self j s)) hd
    exact ⟨h1, h2, measurable_union_hitting (hA j (Finset.mem_insert_self j s)) hm⟩

end Local

/-! ### Lemma 4.5 for successively stopped curves -/

section Curves

open Sec6

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {k : ℕ} {η : Fin k → Ω → ℝ≥0 → ℂ} {x : Fin k → ℂ}
  {τ : Fin k → Ω → ℝ≥0∞} {S : Fin k → (Fin k → Hist) → (ℚ≥0 → ℂ) → ℝ≥0∞}

omit mΩ [IsProbabilityMeasure P] in
/-- The successive stopping times are the reconstruction from the complete paths (`forall_le_iff_recon` with all
reconstruction horizons `∞`). -/
theorem eq_recon_top (hSg : ∀ j, IsGalmarino (S j))
    (hτ : ∀ j ω, τ j ω = S j (prevHist (fun i => pathCoord (η i ω)) (fun i => τ i ω) j)
      (pathCoord (η j ω))) (ω : Ω) :
    (fun j => τ j ω) = recon S (fun i => histOf (pathCoord (η i ω)) ⊤) :=
  ((forall_le_iff_recon hSg (fun j => hτ j ω)).2 fun _ => le_top).symm

omit [IsProbabilityMeasure P] in
/-- **The exposed union is determined by the field**: if every coordinate `η_i(t)` is almost surely a Borel function
of `h` and the stopping times are successive Galmarino functionals of the paths, the explored set
`⋃ η_i([0, τ_i])` is a.s. determined by `h`. -/
theorem aeDeterminedSigma_explored (hc : ∀ i ω, Continuous (η i ω))
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hSm : ∀ j, Measurable (Function.uncurry (S j))) (hSg : ∀ j, IsGalmarino (S j))
    (hτ : ∀ j ω, τ j ω = S j (prevHist (fun i => pathCoord (η i ω)) (fun i => τ i ω) j)
      (pathCoord (η j ω))) :
    AEDeterminedSigma (MeasurableSpace.comap (explored η τ) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P := by
  set 𝒜 := LocalSets.aeSigma (MeasurableSpace.comap h inferInstance) P with h𝒜
  -- the path coordinates are `𝒜`-measurable
  have hηm : ∀ i t, Measurable[𝒜] fun ω => η i ω t := by
    intro i t B hB
    obtain ⟨f, hf, hfe⟩ := hdet i t
    refine ⟨(fun ω => f (h ω)) ⁻¹' B, ⟨f ⁻¹' B, hf hB, rfl⟩, ?_⟩
    filter_upwards [hfe] with ω hω
    simp only [eq_iff_iff, mem_preimage]
    rw [hω]
  have hpath : Measurable[𝒜] fun ω => fun i => histOf (pathCoord (η i ω)) ⊤ := by
    refine Measurable.of_eval fun i => ?_
    have hc' : Measurable[𝒜] fun ω => pathCoord (η i ω) := Measurable.of_eval fun q => hηm i q
    have hp : Measurable[𝒜] fun ω => ((⊤ : ℝ≥0∞), pathCoord (η i ω)) :=
      (measurable_const : Measurable[𝒜] fun _ : Ω => (⊤ : ℝ≥0∞)).prodMk hc'
    exact measurable_histOf.comp hp
  have hτm : ∀ i, Measurable[𝒜] (τ i) := by
    intro i
    have e : τ i = fun ω => recon S (fun i => histOf (pathCoord (η i ω)) ⊤) i := by
      funext ω
      exact congrFun (eq_recon_top hSg hτ ω) i
    rw [e]
    exact (measurable_pi_apply i).comp ((measurable_recon hSm).comp hpath)
  have hE := measurable_explored (mΩ := 𝒜) hc hηm hτm
  rintro _ ⟨M, hM, rfl⟩
  exact hE hM

/-- **Wang–Wu Lemma 4.5 (adapted finite unions).** Let `η₁, …, η_k` be continuous curves with deterministic starting
points, field-determined (every coordinate a.s. a Borel function of `h`), whose initial segments at stopping times are
local in the history-sensitive sense (`IsEntranceHistoryLocal`: Lemma 4.4 for the stopped curve through the first
entrance time of every open set). Expose successively an initial segment of each curve, `τ_j` a stopping time of the
filtration generated by the earlier exposed segments and the `j`-th curve (Galmarino form). If the exposed union is
a.s. relatively closed in `ℍ`, it is a local set and it is determined by the field.

Locality is the specification's Lemma 6.2 at stopping times (`Sec6.isLocalSet_explored`, packet PROVE-SEC6-A3), whose
statement and proof are those of Lemma 4.5; field determination is `aeDeterminedSigma_explored`. -/
theorem isLocalSet_explored_and_aeDetermined (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (η i ω))
    (h0 : ∀ i ω, η i ω 0 = x i) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P)
    (hSm : ∀ j, Measurable (Function.uncurry (S j))) (hSg : ∀ j, IsGalmarino (S j))
    (hτ : ∀ j ω, τ j ω = S j (prevHist (fun i => pathCoord (η i ω)) (fun i => τ i ω) j)
      (pathCoord (η j ω)))
    (hτm : ∀ i, Measurable (τ i)) (hcl : ∀ᵐ ω ∂P, IsOpen (H \ explored η τ ω)) :
    IsLocalSet (explored η τ) h P ∧
      AEDeterminedSigma (MeasurableSpace.comap (explored η τ) hittingSigma)
        (MeasurableSpace.comap h inferInstance) P :=
  ⟨isLocalSet_explored hh hc h0 hηm hdet hloc hSm hSg hτ hτm hcl,
    aeDeterminedSigma_explored hc hdet hSm hSg hτ⟩

end Curves

end InteractingSLE.WangWu
