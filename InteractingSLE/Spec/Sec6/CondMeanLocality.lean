/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.UnionLaw

/-!
# Locality of unions of field-determined explorations (toward Lemma 6.2)

Packet PROVE-SEC6-A2 (specification §6.1, `source/spec/p145-192.md`, `#lem-6.2`, p. 155, and the
paragraph before Proposition 6.1, p. 153).

* `exists_measurableSet_ae_eq_of_condIndepEv`: **the elementary fact** of the proof of Lemma 6.2
  ("a random variable which is measurable with respect to `(X, Y)` and conditionally independent of
  `X` given `Y` is `Y`-measurable, up to completion"), for events.
* `condIndepEv_of_ae_measurableSet`: σ-algebras that are almost surely contained in `G` are
  conditionally independent given `G`.
* `IsMarkedAvoidanceLocal.exists_avoid_ae_eq_compl`: for a local set determined by the field, the
  marked avoidance information of Lemma 3.6 (ii) for an open `U` is almost surely determined by the
  projection `h_{U^c}` alone (the step "Consequently it is determined by `h_{U^c}` alone").
* `IsLocalSet.isLocalSet_union_of_determined`, `isLocalSet_biUnion_of_determined`: **the union of
  finitely many local sets determined by the field is local** ("the conditionally independent union
  of `η_{θ₁}` and `η_{θ₂}` given `h` is almost surely the same as the usual union since `η_{θ₁}` and
  `η_{θ₂}` are both almost surely determined by `h`", p. 153; this is the case `τ_i = ∞` of
  Lemma 6.2, used for `A(∞) = η_{θ₁} ∪ η_{θ₂}` in the proof of Proposition 6.1).

"Determined by the field" is `A =ᵐ F ∘ h` for a hitting-measurable `F` on the distribution space.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper LQGMetric TopologicalSpace

section General

/-- **The elementary fact of Lemma 6.2.** If an event `b` of `B` is almost surely in `A ⊔ G` and
`B` is conditionally independent of `A` given `G`, then `b` is almost surely equal to an event of
`G`. -/
theorem exists_measurableSet_ae_eq_of_condIndepEv {Ω : Type*} {G A B : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hci : CondIndepEv G A B P) {b : Set Ω} (hb : MeasurableSet[B] b)
    (hbAG : ∃ b₀, MeasurableSet[A ⊔ G] b₀ ∧ b =ᵐ[P] b₀) :
    ∃ b', MeasurableSet[G] b' ∧ b =ᵐ[P] b' := by
  obtain ⟨b₀, hb₀, hbb₀⟩ := hbAG
  have hsup : A ⊔ G ≤ mΩ := sup_le hA hG
  have h1 := condExp_sup_eq_of_condIndepEv hG hA hB hci hb
  have hind : b.indicator (fun _ => (1 : ℝ)) =ᵐ[P] b₀.indicator (fun _ => (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set hbb₀
  have h2 : P⟦b | A ⊔ G⟧ =ᵐ[P] b₀.indicator (fun _ => (1 : ℝ)) := by
    refine (condExp_congr_ae hind).trans ?_
    rw [condExp_of_stronglyMeasurable hsup
      (@StronglyMeasurable.indicator Ω ℝ (fun _ => (1 : ℝ)) (A ⊔ G) _ _ stronglyMeasurable_const _
        hb₀)
      ((integrable_const (1 : ℝ)).indicator (hsup _ hb₀))]
  have h3 : b.indicator (fun _ => (1 : ℝ)) =ᵐ[P] P⟦b | G⟧ := hind.trans (h2.symm.trans h1)
  refine ⟨{ω | (P⟦b | G⟧) ω = 1}, ?_, ?_⟩
  · exact stronglyMeasurable_condExp.measurable (measurableSet_singleton (1 : ℝ))
  · filter_upwards [h3] with ω hω
    simp only [eq_iff_iff]
    change ω ∈ b ↔ (P⟦b | G⟧) ω = 1
    rw [← hω]
    by_cases hωb : ω ∈ b
    · simp [hωb]
    · simp [hωb]

/-- σ-algebras whose events are almost surely events of `G` are conditionally independent given
`G`. -/
theorem condIndepEv_of_ae_measurableSet {Ω : Type*} {G A B : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] (hG : G ≤ mΩ)
    (hA : ∀ a, MeasurableSet[A] a → ∃ a', MeasurableSet[G] a' ∧ a =ᵐ[P] a')
    (hB : ∀ b, MeasurableSet[B] b → ∃ b', MeasurableSet[G] b' ∧ b =ᵐ[P] b') :
    CondIndepEv G A B P := by
  intro a b ha hb
  obtain ⟨a', ha', haa'⟩ := hA a ha
  obtain ⟨b', hb', hbb'⟩ := hB b hb
  have hcond : ∀ {s s' : Set Ω}, MeasurableSet[G] s' → s =ᵐ[P] s' →
      P⟦s | G⟧ =ᵐ[P] s'.indicator (fun _ => (1 : ℝ)) := by
    intro s s' hs' hss'
    refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hss')).trans ?_
    rw [condExp_of_stronglyMeasurable hG
      (@StronglyMeasurable.indicator Ω ℝ (fun _ => (1 : ℝ)) G _ _ stronglyMeasurable_const _ hs')
      ((integrable_const (1 : ℝ)).indicator (hG _ hs'))]
  have hab : a ∩ b =ᵐ[P] a' ∩ b' := haa'.inter hbb'
  filter_upwards [hcond (ha'.inter hb') hab, hcond ha' haa', hcond hb' hbb'] with ω h1 h2 h3
  rw [h1, Pi.mul_apply, h2, h3, indOne_inter_eq, Pi.mul_apply]

end General

section GFF

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ in
/-- The field is measurable with respect to its two Markov projections:
`σ(h) ≤ σ(h_U) ⊔ σ(h_{U^c})`. -/
theorem comap_le_sup_markov {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} :
    MeasurableSpace.comap h inferInstance ≤
      MeasurableSpace.comap (fun ω => G (h ω)) inferInstance ⊔
        MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance := by
  set S := MeasurableSpace.comap (fun ω => G (h ω)) inferInstance ⊔
    MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance
  have h1 : Measurable[S] (fun ω => G (h ω)) := (comap_measurable _).mono le_sup_left le_rfl
  have h2 : Measurable[S] (fun ω => markovCompl G (h ω)) :=
    (comap_measurable _).mono le_sup_right le_rfl
  have hsum : Measurable[S] h := by
    let _ : MeasurableSpace Ω := S
    refine measurable_distOn_iff.2 fun φ => ?_
    have := ((measurable_distOn_apply φ).comp h1).add ((measurable_distOn_apply φ).comp h2)
    convert this using 1
    funext ω
    simp [markovCompl]
  exact hsum.comap_le

/-- **"Consequently it is determined by `h_{U^c}` alone"** (proof of Lemma 6.2). For a local set `A`
and a deterministic open `U ⊆ ℍ` with a Borel version `G` of the projection onto `H(U)`, every event
of the marked avoidance information `(S, Ã)` of Lemma 3.6 (ii) that is almost surely determined by
the field is almost surely an event of `σ(h_{U^c})`. -/
theorem IsLocalSet.exists_marked_ae_eq_compl {A : Ω → Set ℂ} (hhm : Measurable h)
    (hAm : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P) {U : Opens ℂ}
    (hUH : (U : Set ℂ) ⊆ H) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hG : Measurable G) (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    {b : Set Ω} (hb : MeasurableSet[markedSigma A U] b)
    (hbh : ∃ b₀, MeasurableSet[MeasurableSpace.comap h inferInstance] b₀ ∧ b =ᵐ[P] b₀) :
    ∃ b', MeasurableSet[MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance] b' ∧
      b =ᵐ[P] b' := by
  have hci := IsLocalSet.isMarkedAvoidanceLocal hhm hAm hloc U G hUH hG hd
  obtain ⟨b₀, hb₀, hbb₀⟩ := hbh
  refine exists_measurableSet_ae_eq_of_condIndepEv
    (((measurable_markovCompl hG).comp hhm).comap_le) ((hG.comp hhm).comap_le)
    ((markedSigma_le_comap A U.isOpen hUH).trans hAm.comap_le) hci.symm hb
    ⟨b₀, comap_le_sup_markov (G := G) _ hb₀, hbb₀⟩

omit [IsProbabilityMeasure P] in
/-- Events of a random set that is almost surely determined by the field are almost surely events
of `σ(h)`. -/
theorem ae_measurableSet_comap_of_determined {A : Ω → Set ℂ}
    {F : DistOn upperHalfPlaneOpens → Set ℂ} (hF : Measurable[inferInstance, hittingSigma] F)
    (hAF : A =ᵐ[P] fun ω => F (h ω)) {a : Set Ω}
    (ha : MeasurableSet[MeasurableSpace.comap A hittingSigma] a) :
    ∃ a', MeasurableSet[MeasurableSpace.comap h inferInstance] a' ∧ a =ᵐ[P] a' := by
  obtain ⟨S, hS, rfl⟩ := ha
  refine ⟨h ⁻¹' (F ⁻¹' S), ⟨F ⁻¹' S, hF hS, rfl⟩, ?_⟩
  filter_upwards [hAF] with ω hω
  simp only [mem_preimage, hω]

/-- **Two field-determined local sets have a local union** (specification p. 153: "the
conditionally independent union of `η_{θ₁}` and `η_{θ₂}` given `h` is almost surely the same as the
usual union since `η_{θ₁}` and `η_{θ₂}` are both almost surely determined by `h`"). -/
theorem IsLocalSet.isLocalSet_union_of_determined
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A₁ A₂ : Ω → Set ℂ}
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hd₁ : ∃ F : DistOn upperHalfPlaneOpens → Set ℂ, Measurable[inferInstance, hittingSigma] F ∧
      A₁ =ᵐ[P] fun ω => F (h ω))
    (hd₂ : ∃ F : DistOn upperHalfPlaneOpens → Set ℂ, Measurable[inferInstance, hittingSigma] F ∧
      A₂ =ᵐ[P] fun ω => F (h ω))
    (h₁ : IsLocalSet A₁ h P) (h₂ : IsLocalSet A₂ h P) :
    IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) h P := by
  obtain ⟨F₁, hF₁, hAF₁⟩ := hd₁
  obtain ⟨F₂, hF₂, hAF₂⟩ := hd₂
  refine IsLocalSet.isLocalSet_union hh hA₁ hA₂ ?_ h₁ h₂
  exact condIndepEv_of_ae_measurableSet hh.measurable.comap_le
    (fun a ha => ae_measurableSet_comap_of_determined hF₁ hAF₁ ha)
    (fun b hb => ae_measurableSet_comap_of_determined hF₂ hAF₂ hb)

/-- **Finitely many field-determined local sets have a local union**, which is again determined by
the field (the case `τ_i = ∞` of Lemma 6.2). -/
theorem isLocalSet_biUnion_of_determined (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {ι : Type*} (s : Finset ι) {A : ι → Ω → Set ℂ}
    (hA : ∀ i ∈ s, Measurable[mΩ, hittingSigma] (A i))
    (hd : ∀ i ∈ s, ∃ F : DistOn upperHalfPlaneOpens → Set ℂ,
      Measurable[inferInstance, hittingSigma] F ∧ A i =ᵐ[P] fun ω => F (h ω))
    (hloc : ∀ i ∈ s, IsLocalSet (A i) h P) :
    IsLocalSet (fun ω => ⋃ i ∈ s, A i ω) h P ∧
      Measurable[mΩ, hittingSigma] (fun ω => ⋃ i ∈ s, A i ω) ∧
      ∃ F : DistOn upperHalfPlaneOpens → Set ℂ, Measurable[inferInstance, hittingSigma] F ∧
        (fun ω => ⋃ i ∈ s, A i ω) =ᵐ[P] fun ω => F (h ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
    refine ⟨isLocalSet_const hh (empty_subset _) (by rw [sdiff_empty]; exact isOpen_H), ?_,
      fun _ => ∅, ?_, Eventually.of_forall fun _ => rfl⟩
    · exact @measurable_const (Set ℂ) Ω hittingSigma mΩ ∅
    · exact @measurable_const (Set ℂ) (DistOn upperHalfPlaneOpens) hittingSigma _ ∅
  | insert a s has ih =>
    obtain ⟨hl, hm, F, hF, hAF⟩ := ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
      (fun i hi => hd i (Finset.mem_insert_of_mem hi))
      (fun i hi => hloc i (Finset.mem_insert_of_mem hi))
    obtain ⟨Fa, hFa, hAFa⟩ := hd a (Finset.mem_insert_self a s)
    have he : (fun ω => ⋃ i ∈ insert a s, A i ω) = fun ω => A a ω ∪ ⋃ i ∈ s, A i ω := by
      funext ω; rw [Finset.set_biUnion_insert]
    rw [he]
    refine ⟨IsLocalSet.isLocalSet_union_of_determined hh (hA a (Finset.mem_insert_self a s)) hm
        ⟨Fa, hFa, hAFa⟩ ⟨F, hF, hAF⟩ (hloc a (Finset.mem_insert_self a s)) hl,
      measurable_union_hitting (hA a (Finset.mem_insert_self a s)) hm,
      fun T => Fa T ∪ F T, measurable_union_hitting hFa hF, ?_⟩
    filter_upwards [hAFa, hAF] with ω h1 h2
    simp only [h1, h2]

end GFF

end LocalSets
end InteractingSLE
