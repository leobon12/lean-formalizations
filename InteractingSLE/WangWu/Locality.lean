/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import LQGMetric.Prob.CondIndepAEDet
import InteractingSLE.GFF.LocalSets.MarkedAvoidance

/-!
# Wang–Wu §4.1: measure-theoretic reductions (Lemmas 4.1–4.4)

Packet PROVE-WW-B. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31),
§4.1, pp. 16–17 (text dump lines 977–1057).

Conditional independence is the event form `LQGMetric.CondIndepEv G A B μ`
(`P[a ∩ b | G] = P[a | G] P[b | G]`), used by all local-set lemmas of the project; "determined by"
is `LQGMetric.AEDeterminedSigma A G μ` (every event of `A` agrees a.s. with an event of `G`) or,
for standard Borel targets, `LQGMetric.AEDeterminedBy Y X μ` (`Y = F ∘ X` a.s., `F` Borel).

## Main results

* `exists_measurable_ae_eq_comp_of_condIndepEv_of_ae_eq` — **Lemma 4.1** (diagonal conditional
  kernels): `X ⟂ Y | H`, `X = Y` a.s. ⇒ `X = Y = F(H)` a.s. (LQGMetric's two-copies criterion);
* `aeDeterminedSigma_of_condIndepEv_of_sup` — **Lemma 4.2** (eliminating unused randomness),
  σ-algebra form: `𝒳 ⊆ 𝒴 ∨ 𝒵` (mod null sets), `𝒳 ⟂ 𝒵 | 𝒴` ⇒ `𝒳 ⊆ 𝒴` (mod null sets); the
  conditional version "given another variable `B`" is the case `𝒴 = ℬ ∨ 𝒴'`;
  `aeDeterminedBy_of_condIndepEv_of_aeDeterminedBy_prod` is the random-variable form;
* `condIndepEv_sup_sup_of_condIndepEv` — **Lemma 4.3** (combining conditional independence);
* `IsLocalSet.aeDeterminedSigma_markedSigma` — **Lemma 4.4** (a local set determined by the field
  uses no unseen field): the avoidance event `{A ∩ U = ∅}` and the cemetery-valued restriction
  `A_U` are a.s. determined by the projection `h_{U^c} = h − G h` of `h` onto `H^⊥(U)`;
  `IsLocalSet.aeDeterminedSigma_of_ae_disjoint` is its "in particular" clause.

The weak-union property of conditional independence (`CondIndepEv.weakUnion`) is the one step
added to the source's proofs; it is a two-line consequence of the Markov form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter
open LQGMetric

namespace InteractingSLE.WangWu

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Lemma 4.1 -/

/-- **Wang–Wu, Lemma 4.1** (diagonal conditional kernels). Let `H, X, Y` be random variables, `X, Y`
valued in the same standard Borel space. If `X` and `Y` are conditionally independent given `H`
and `X = Y` almost surely, then there is a Borel map `F` with `X = Y = F(H)` almost surely. The
conditional laws of `X` and `Y` are not required to be equal in advance. -/
theorem exists_measurable_ae_eq_comp_of_condIndepEv_of_ae_eq [IsProbabilityMeasure μ]
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β] [StandardBorelSpace β]
    {H : Ω → α} (hH : Measurable H) {X Y : Ω → β} (hX : Measurable X)
    (hXY : CondIndepEv (mα.comap H) (mβ.comap X) (mβ.comap Y) μ) (heq : X =ᵐ[μ] Y) :
    ∃ F : α → β, Measurable F ∧ X =ᵐ[μ] F ∘ H ∧ Y =ᵐ[μ] F ∘ H := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have : Nonempty β := ⟨X (Classical.arbitrary Ω)⟩
  obtain ⟨F, hF, hXF⟩ := aeDeterminedBy_of_condIndepEv_of_ae_eq hH hX hXY heq
  exact ⟨F, hF, hXF, heq.symm.trans hXF⟩

/-! ### Lemma 4.2 -/

/-- If `P[a | 𝒴] = 1_a` almost surely, then `a` agrees almost surely with an event of `𝒴`. -/
lemma exists_ae_eq_set_of_condExp_ae_eq_indicator [IsFiniteMeasure μ] {Y : MeasurableSpace Ω}
    {a : Set Ω} (h : μ⟦a | Y⟧ =ᵐ[μ] a.indicator fun _ => (1 : ℝ)) :
    ∃ t, MeasurableSet[Y] t ∧ a =ᵐ[μ] t := by
  refine ⟨μ⟦a | Y⟧ ⁻¹' {1}, stronglyMeasurable_condExp.measurable (measurableSet_singleton 1), ?_⟩
  rw [eventuallyEqSet_iff]
  filter_upwards [h] with x hx
  simp only [mem_preimage, mem_singleton_iff, hx]
  by_cases hxa : x ∈ a
  · simp [hxa]
  · simp [hxa]

/-- **Wang–Wu, Lemma 4.2** (eliminating unused randomness), σ-algebra form. If `𝒳` is a.s.
determined by `𝒴 ∨ 𝒵` and `𝒳` is conditionally independent of `𝒵` given `𝒴`, then `𝒳` is a.s.
determined by `𝒴`. The same assertion conditionally on another variable `B` is the case of
`ℬ ∨ 𝒴` in place of `𝒴`. -/
theorem aeDeterminedSigma_of_condIndepEv_of_sup [IsProbabilityMeasure μ]
    {X Y Z : MeasurableSpace Ω} (hX : X ≤ mΩ) (hY : Y ≤ mΩ) (hZ : Z ≤ mΩ)
    (hdet : AEDeterminedSigma X (Y ⊔ Z) μ) (hind : CondIndepEv Y X Z μ) :
    AEDeterminedSigma X Y μ := by
  intro a ha
  obtain ⟨t, ht, hat⟩ := hdet a ha
  have ha0 := hX a ha
  have hYZ : Y ⊔ Z ≤ mΩ := sup_le hY hZ
  -- `1_a = 1_t = P[t | 𝒴 ∨ 𝒵] = P[a | 𝒵 ∨ 𝒴] = P[a | 𝒴]`
  have h1 : μ⟦a | Z ⊔ Y⟧ =ᵐ[μ] μ⟦a | Y⟧ :=
    condExp_sup_eq_of_condIndepEv hY hZ hX hind.symm ha
  have h2 : μ⟦a | Z ⊔ Y⟧ =ᵐ[μ] a.indicator fun _ => (1 : ℝ) := by
    rw [sup_comm]
    have e1 : μ⟦a | Y ⊔ Z⟧ =ᵐ[μ] μ⟦t | Y ⊔ Z⟧ :=
      condExp_congr_ae (indOne_ae_eq_of_ae_eq hat)
    have e2 : μ⟦t | Y ⊔ Z⟧ = t.indicator fun _ => (1 : ℝ) :=
      condExp_of_stronglyMeasurable hYZ (stronglyMeasurable_const.indicator ht)
        (integrable_indOne (hYZ t ht))
    rw [e2] at e1
    exact e1.trans (indOne_ae_eq_of_ae_eq hat.symm)
  exact exists_ae_eq_set_of_condExp_ae_eq_indicator (h1.symm.trans h2)

/-- **Wang–Wu, Lemma 4.2**, random-variable form. If `X = F(Y, Z)` almost surely for a Borel `F`
(`X` is measurable with respect to `σ(Y, Z)` up to null sets) and `X` is conditionally independent
of `Z` given `Y`, then `X` has a `σ(Y)`-measurable version: `X = F'(Y)` almost surely. -/
theorem aeDeterminedBy_of_condIndepEv_of_aeDeterminedBy_prod [IsProbabilityMeasure μ]
    {β γ δ : Type*} [mβ : MeasurableSpace β] [StandardBorelSpace β]
    [mγ : MeasurableSpace γ] [mδ : MeasurableSpace δ] {X : Ω → β} {Y : Ω → γ} {Z : Ω → δ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hdet : AEDeterminedBy X (fun ω => (Y ω, Z ω)) μ)
    (hind : CondIndepEv (mγ.comap Y) (mβ.comap X) (mδ.comap Z) μ) :
    AEDeterminedBy X Y μ := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have : Nonempty β := ⟨X (Classical.arbitrary Ω)⟩
  refine aeDeterminedBy_of_aeDeterminedSigma ?_
  refine aeDeterminedSigma_of_condIndepEv_of_sup hX.comap_le hY.comap_le hZ.comap_le ?_ hind
  obtain ⟨F, hF, hXF⟩ := hdet
  rintro _ ⟨B, hB, rfl⟩
  refine ⟨(fun ω => (Y ω, Z ω)) ⁻¹' (F ⁻¹' B), ?_, ?_⟩
  · rw [← MeasurableSpace.comap_prodMk]
    exact ⟨F ⁻¹' B, hF hB, rfl⟩
  · rw [eventuallyEqSet_iff]
    filter_upwards [hXF] with ω hω
    simp [hω]

/-! ### Lemma 4.3 -/

/-- **Weak union.** If `𝒜 ∨ 𝒞 ⟂ ℬ | 𝒢`, then `𝒜 ⟂ ℬ | 𝒞 ∨ 𝒢`. -/
theorem CondIndepEv.weakUnion [IsProbabilityMeasure μ] {G A B C : MeasurableSpace Ω}
    (hG : G ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) (hC : C ≤ mΩ) (h : CondIndepEv G (A ⊔ C) B μ) :
    CondIndepEv (C ⊔ G) A B μ := by
  refine (condIndepEv_of_condExp_sup_eq (sup_le hC hG) hB hA fun b hb => ?_).symm
  -- both sides are `P[b | 𝒢]`
  have e1 : μ⟦b | (A ⊔ C) ⊔ G⟧ =ᵐ[μ] μ⟦b | G⟧ :=
    condExp_sup_eq_of_condIndepEv hG (sup_le hA hC) hB h hb
  have e2 : μ⟦b | C ⊔ G⟧ =ᵐ[μ] μ⟦b | G⟧ :=
    condExp_sup_eq_of_condIndepEv hG hC hB (h.mono le_sup_right le_rfl) hb
  have e3 : A ⊔ (C ⊔ G) = (A ⊔ C) ⊔ G := (sup_assoc A C G).symm
  rw [e3]
  exact e1.trans e2.symm

/-- **Wang–Wu, Lemma 4.3** (combining conditional independence). Conditionally on `ℬ`, if
`(X, Y, P, Q) ⟂ E`, `(X, Y, P) ⟂ Q` and `(X, Y, Q) ⟂ P`, then `(X, Y) ⟂ (E, P, Q)`. Here `𝒳` is the
σ-algebra of `(X, Y)` and `ℰ, 𝒫, 𝒬` those of `E, P, Q` (`σ(X, Y, P) = 𝒳 ∨ 𝒫`,
`MeasurableSpace.comap_prodMk`). -/
theorem condIndepEv_sup_sup_of_condIndepEv [IsProbabilityMeasure μ]
    {B X E P Q : MeasurableSpace Ω} (hB : B ≤ mΩ) (hX : X ≤ mΩ) (hE : E ≤ mΩ) (hP : P ≤ mΩ)
    (hQ : Q ≤ mΩ) (h₁ : CondIndepEv B (X ⊔ P ⊔ Q) E μ) (h₂ : CondIndepEv B (X ⊔ P) Q μ)
    (h₃ : CondIndepEv B (X ⊔ Q) P μ) : CondIndepEv B X (E ⊔ P ⊔ Q) μ := by
  have hPQ : P ⊔ Q ≤ mΩ := sup_le hP hQ
  -- the three Markov forms
  have k₁ : CondIndepEv ((P ⊔ Q) ⊔ B) X E μ := by
    refine CondIndepEv.weakUnion hB hX hE hPQ ?_
    rwa [← sup_assoc]
  have k₂ : CondIndepEv (P ⊔ B) X Q μ := CondIndepEv.weakUnion hB hX hQ hP h₂
  have k₃ : CondIndepEv B X P μ := h₃.mono le_sup_left le_rfl
  refine condIndepEv_of_condExp_sup_eq hB hX (sup_le (sup_le hE hP) hQ) fun a ha => ?_
  have m₁ : μ⟦a | E ⊔ ((P ⊔ Q) ⊔ B)⟧ =ᵐ[μ] μ⟦a | (P ⊔ Q) ⊔ B⟧ :=
    condExp_sup_eq_of_condIndepEv (sup_le hPQ hB) hE hX k₁.symm ha
  have m₂ : μ⟦a | Q ⊔ (P ⊔ B)⟧ =ᵐ[μ] μ⟦a | P ⊔ B⟧ :=
    condExp_sup_eq_of_condIndepEv (sup_le hP hB) hQ hX k₂.symm ha
  have m₃ : μ⟦a | P ⊔ B⟧ =ᵐ[μ] μ⟦a | B⟧ :=
    condExp_sup_eq_of_condIndepEv hB hP hX k₃.symm ha
  have s₁ : (E ⊔ P ⊔ Q) ⊔ B = E ⊔ ((P ⊔ Q) ⊔ B) := by
    simp only [sup_assoc]
  have s₂ : (P ⊔ Q) ⊔ B = Q ⊔ (P ⊔ B) := by
    rw [sup_comm P Q, sup_assoc]
  rw [s₁]
  refine m₁.trans ?_
  rw [s₂]
  exact m₂.trans m₃

/-! ### Lemma 4.4 -/

section LocalSet

open QuantumZipper InteractingSLE.LocalSets TopologicalSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ [IsProbabilityMeasure P] in
/-- The σ-algebra of `({A ∩ U = ∅}, A_U)` is contained in that of `A`. -/
theorem markedSigma_le_comap {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    markedSigma A U ≤ MeasurableSpace.comap A hittingSigma := by
  refine sup_le ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ rfl
    exact ⟨_, measurableSet_avoid hU hUH, rfl⟩
  · exact (@Measurable.comp Ω (Set ℂ) (Set ℂ) (MeasurableSpace.comap A hittingSigma)
      hittingSigma hittingSigma (markedSet U) A (measurable_markedSet hU hUH)
      (comap_measurable A)).comap_le

/-- **Wang–Wu, Lemma 4.4** (a local set determined by the field uses no unseen field). Let `A` be
a local set of the zero-boundary GFF `h` on `ℍ`, a.s. determined by `h`, and let `U ⊆ ℍ` be a
deterministic open set, with `h = h_U + h_{U^c}` the Dirichlet orthogonal decomposition
(`h_U = G h`, `h_{U^c} = h − G h`, Proposition 3.1). Then the avoidance event `E_U = {A ∩ U = ∅}`
and the cemetery-valued restriction `A_U` (`A` on `E_U`, `∅` off it: `markedSet U A`) are a.s.
determined by `h_{U^c}`: every event of their σ-algebra `markedSigma A U` agrees a.s. with an event
of `σ(h − G h)`. -/
theorem IsLocalSet.aeDeterminedSigma_markedSigma (hhm : Measurable h)
    (hAm : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    (hdet : AEDeterminedSigma (MeasurableSpace.comap A hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (U : Opens ℂ) (hUH : (U : Set ℂ) ⊆ H)
    (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) :
    AEDeterminedSigma (markedSigma A U)
      (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P := by
  have hind := LocalSets.IsLocalSet.isMarkedAvoidanceLocal hhm hAm hloc U G hUH hG hd
  have hXm : Measurable fun ω => G (h ω) := hG.comp hhm
  have hYm : Measurable fun ω => markovCompl G (h ω) := (measurable_markovCompl hG).comp hhm
  refine aeDeterminedSigma_of_condIndepEv_of_sup (markedSigma_le hAm U.isOpen hUH)
    hYm.comap_le hXm.comap_le ?_ hind
  intro s hs
  obtain ⟨t, ht, hst⟩ := hdet s (markedSigma_le_comap U.isOpen hUH s hs)
  refine ⟨t, ?_, hst⟩
  rw [comap_eq_sup_markov h hG, sup_comm] at ht
  exact ht

/-- **Wang–Wu, Lemma 4.4**, "in particular": if the local set `A`, a.s. determined by `h`, avoids
the deterministic open set `U` almost surely, then `A` itself is a.s. determined by the projection
`h_{U^c} = h − G h` of `h` onto `H^⊥(U)`. -/
theorem IsLocalSet.aeDeterminedSigma_of_ae_disjoint (hhm : Measurable h)
    (hAm : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    (hdet : AEDeterminedSigma (MeasurableSpace.comap A hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (U : Opens ℂ) (hUH : (U : Set ℂ) ⊆ H)
    (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (havoid : ∀ᵐ ω ∂P, Disjoint (A ω) U) :
    AEDeterminedSigma (MeasurableSpace.comap A hittingSigma)
      (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P := by
  have hmain := IsLocalSet.aeDeterminedSigma_markedSigma hhm hAm hloc hdet U hUH G hG hd
  rintro _ ⟨B, hB, rfl⟩
  -- on the avoidance event, `A_U = A`
  have hmk : MeasurableSet[markedSigma A U] ((fun ω => markedSet U (A ω)) ⁻¹' B) :=
    (le_sup_right : _ ≤ markedSigma A U) _ ⟨B, hB, rfl⟩
  obtain ⟨t, ht, hst⟩ := hmain _ hmk
  refine ⟨t, ht, EventuallyEq.trans ?_ hst⟩
  filter_upwards [havoid] with ω hω
  have e : markedSet U (A ω) = A ω := by
    ext z
    simp [markedSet, hω]
  simp only [mem_preimage, e]

end LocalSet

/-! ### Transfer of field determination along absolute continuity (Lemma 4.10) -/

/-- **Wang–Wu, Lemma 4.10**, "in particular: field determination of this stopped hull transfers
from one problem to the other". If the joint law of (restricted field, stopped history) in the
second problem is absolutely continuous with respect to that in the first, and in the first the
history is a Borel function `Φ` of the restricted field, then the same `Φ` determines it in the
second problem. -/
theorem ae_eq_comp_of_map_absolutelyContinuous {α β Ω₁ Ω₂ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableEq β] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {F₁ : Ω₁ → α} {X₁ : Ω₁ → β} {F₂ : Ω₂ → α} {X₂ : Ω₂ → β}
    (h₁ : AEMeasurable (fun ω => (F₁ ω, X₁ ω)) P₁) (h₂ : AEMeasurable (fun ω => (F₂ ω, X₂ ω)) P₂)
    (hac : P₂.map (fun ω => (F₂ ω, X₂ ω)) ≪ P₁.map (fun ω => (F₁ ω, X₁ ω)))
    {Φ : α → β} (hΦ : Measurable Φ) (hdet : X₁ =ᵐ[P₁] Φ ∘ F₁) : X₂ =ᵐ[P₂] Φ ∘ F₂ := by
  set S : Set (α × β) := {p | p.2 = Φ p.1}ᶜ
  have hS : MeasurableSet S := (measurableSet_eq_fun measurable_snd (hΦ.comp measurable_fst)).compl
  have hS₁ : P₁.map (fun ω => (F₁ ω, X₁ ω)) S = 0 := by
    rw [Measure.map_apply_of_aemeasurable h₁ hS]
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hdet)
    simpa [S] using hω
  have hS₂ := hac hS₁
  rw [Measure.map_apply_of_aemeasurable h₂ hS] at hS₂
  refine ae_iff.2 (measure_mono_null (fun ω hω => ?_) hS₂)
  simpa [S] using hω

/-! ### Independence of a joint variable (Proposition 4.24, last step) -/

/-- If `𝒳 ∨ 𝒴 ⟂ 𝒵`, then `𝒳 ⟂ 𝒵 | 𝒴`. -/
theorem condIndepEv_of_indep_sup [IsProbabilityMeasure μ] {X Y Z : MeasurableSpace Ω}
    (hX : X ≤ mΩ) (hY : Y ≤ mΩ) (hZ : Z ≤ mΩ) (hind : Indep (X ⊔ Y) Z μ) :
    CondIndepEv Y X Z μ := by
  refine (condIndepEv_of_condExp_sup_eq hY hZ hX fun z hz => ?_).symm
  have hf : StronglyMeasurable[Z] (z.indicator fun _ => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hz
  have e1 : μ⟦z | X ⊔ Y⟧ =ᵐ[μ] fun _ => ∫ ω, z.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
    condExp_indep_eq hZ (sup_le hX hY) hf hind.symm
  have e2 : μ⟦z | Y⟧ =ᵐ[μ] fun _ => ∫ ω, z.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
    condExp_indep_eq hZ hY hf (indep_of_indep_of_le_left hind le_sup_right).symm
  exact e1.trans e2.symm

/-- **Wang–Wu, Proposition 4.24**, last step ("the joint conditional law of `(X, H)` given `B` is
independent of `B` … `L(X | H, B) = L(X | H)`; the former is a point mass; the latter is therefore a
point mass too"): if `σ(X) ∨ σ(H)` is independent of `σ(B)` and `σ(X)` is a.s. determined by
`σ(H) ∨ σ(B)`, then `σ(X)` is a.s. determined by `σ(H)`. -/
theorem aeDeterminedSigma_of_indep_sup [IsProbabilityMeasure μ] {X Y Z : MeasurableSpace Ω}
    (hX : X ≤ mΩ) (hY : Y ≤ mΩ) (hZ : Z ≤ mΩ) (hind : Indep (X ⊔ Y) Z μ)
    (hdet : AEDeterminedSigma X (Y ⊔ Z) μ) : AEDeterminedSigma X Y μ :=
  aeDeterminedSigma_of_condIndepEv_of_sup hX hY hZ hdet (condIndepEv_of_indep_sup hX hY hZ hind)

end InteractingSLE.WangWu
