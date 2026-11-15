/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkPastLaw
import InteractingSLE.WangWu.PrefixLocalMean

/-!
# Theorem 1.4: the marked union of the two boundary walks

Packet PROVE-T14-WALKLAW. Lemma GW3, proof (`source/spec/p625-671.md` L210–L226, p. 636): "The two finite-stage marked
local sets have their complete kernels by GW1. Their union […] retain[s] the marked Gaussian union law."

The source's union step is Proposition 3.7 (a conditionally independent union of local sets, with both set labels
retained). The two walks are determined by the field (PROVE-T14-SB7's (a1)), so for them the marked avoidance
criterion takes a simple form: a marked avoidance event is almost surely an event of the complementary Markov
projection `h − G h` (`mem_aeSigma_of_isHistoryAvoidanceLocal`, `isHistoryAvoidanceLocal_of_mem_aeSigma`). The events
`F` for which `{A ∩ U = ∅} ∩ F` has that property form a σ-algebra as soon as `{A ∩ U = ∅}` itself does, so the
criterion passes to unions with joined marks without the π–λ machinery of Proposition 3.7
(**`isHistoryAvoidanceLocal_union_of_det`**).

## Main results

* `mem_aeSigma_of_isHistoryAvoidanceLocal`, `isHistoryAvoidanceLocal_of_mem_aeSigma`: the criterion for marks and sets
  determined by the field;
* **`isHistoryAvoidanceLocal_union_of_det`**: the union of two determined marked local sets, with the joined marks;
* **`walkUnion_marked`**: for the two boundary walks (from the per-walk input `WalkMarkedLocalRegStatement` and the
  determination `PastDetRegStatement`), the union of their ranges is a local set of the centred field marked by both
  retained pasts, with avoidance events in the joined past;
* **`walkUnion_condLaw`**: hence, for every test function, the conditional characteristic functional of the centred
  field given the germs of the union and both retained pasts is Gaussian with the zero-boundary variance of
  `ℍ \ (R ∪ L)` (Aux. lemma 18 with marks, `WholeField.exists_condExp_germSigma_history`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace WalkLaw

open LocalSets

/-! ### The marked criterion for sets and marks determined by the field -/

section Det

variable {Ω : Type*} {ℋ ℋ₁ ℋ₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **For a marked event determined by the field, the marked criterion makes it almost surely an event of the
complementary projection.** -/
theorem mem_aeSigma_of_isHistoryAvoidanceLocal (hhm : Measurable h) {A : Ω → Set ℂ}
    (hloc : WholeField.IsHistoryAvoidanceLocal ℋ A h P) {U : Opens ℂ}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) {F : Set Ω}
    (hF : MeasurableSet[ℋ] F)
    (hEF : MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P] ({ω | Disjoint (A ω) U} ∩ F)) :
    MeasurableSet[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P]
      ({ω | Disjoint (A ω) U} ∩ F) := by
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd F hF
  obtain ⟨K, hK, hEK⟩ := hEF
  have hle : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  have hKm : MeasurableSet K := hle K hK
  -- the conditional probability of `K` given `h` is its indicator
  have h1 : P⟦{ω | Disjoint (A ω) U} ∩ F | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P]
      K.indicator fun _ => (1 : ℝ) := by
    refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hEK)).trans ?_
    rw [condExp_of_stronglyMeasurable hle ((measurable_const.indicator hK).stronglyMeasurable)
      ((integrable_const (1 : ℝ)).indicator hKm)]
  have h2 : (K.indicator fun _ => (1 : ℝ)) =ᵐ[P] fun ω => g (markovCompl G (h ω)) := h1.symm.trans hge
  set K' : Set Ω := (fun ω => markovCompl G (h ω)) ⁻¹' (g ⁻¹' {1}) with hK'
  refine ⟨K', ⟨g ⁻¹' {1}, hg (measurableSet_singleton 1), rfl⟩, hEK.trans ?_⟩
  filter_upwards [h2] with ω hω
  simp only [hK', mem_preimage, mem_singleton_iff, ← hω]
  by_cases hωK : ω ∈ K
  · simp [hωK]
  · simp [hωK]

/-- **The marked criterion from the almost-sure measurability of the marked avoidance events with respect to the
complementary projection.** -/
theorem isHistoryAvoidanceLocal_of_mem_aeSigma (hhm : Measurable h) {A : Ω → Set ℂ}
    (hmem : ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ F : Set Ω, MeasurableSet[ℋ] F →
        MeasurableSet[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P]
          ({ω | Disjoint (A ω) U} ∩ F)) :
    WholeField.IsHistoryAvoidanceLocal ℋ A h P := by
  intro U G hUH hG hd F hF
  obtain ⟨K, ⟨B, hB, rfl⟩, hEK⟩ := hmem U G hUH hG hd F hF
  have hle : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  have hYm : Measurable[MeasurableSpace.comap h inferInstance] fun ω => markovCompl G (h ω) :=
    (measurable_markovCompl hG).comp (comap_measurable h)
  refine ⟨B.indicator fun _ => (1 : ℝ), measurable_const.indicator hB, ?_⟩
  refine (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hEK)).trans ?_
  have hKm : MeasurableSet[MeasurableSpace.comap h inferInstance] ((fun ω => markovCompl G (h ω)) ⁻¹' B) :=
    hYm hB
  rw [condExp_of_stronglyMeasurable hle ((measurable_const.indicator hKm).stronglyMeasurable)
    ((integrable_const (1 : ℝ)).indicator (hle _ hKm))]
  exact Eventually.of_forall fun ω => by
    by_cases hω : markovCompl G (h ω) ∈ B
    · simp [hω]
    · simp [hω]

omit mΩ [IsFiniteMeasure P] in
/-- The marks `F` for which `E ∩ F` lies in a σ-algebra `𝒦`, once `E` itself does, form a σ-algebra. -/
@[instance_reducible]
def traceSigma (𝒦 : MeasurableSpace Ω) (E : Set Ω) (hE : MeasurableSet[𝒦] E) : MeasurableSpace Ω where
  MeasurableSet' F := MeasurableSet[𝒦] (E ∩ F)
  measurableSet_empty := by simp only [inter_empty]; exact @MeasurableSet.empty _ 𝒦
  measurableSet_compl F hF := by
    have e : E ∩ Fᶜ = E ∩ (E ∩ F)ᶜ := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff]
      tauto
    rw [e]
    exact hE.inter hF.compl
  measurableSet_iUnion f hf := by
    rw [inter_iUnion]
    exact MeasurableSet.iUnion hf

omit [IsFiniteMeasure P] in
/-- The events that are almost surely events of the complementary Markov projection `h − G h`. -/
@[instance_reducible]
def complSigma (P : Measure Ω) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (h : Ω → DistOn upperHalfPlaneOpens) : MeasurableSpace Ω :=
  aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P

/-- **The union of two determined marked local sets is a marked local set for the joined marks.** If `A₁`, `A₂` are
marked by `ℋ₁`, `ℋ₂`, their avoidance events are marks, and all marks are almost surely events of `σ(h)`, then
`A₁ ∪ A₂` satisfies the history-marked avoidance criterion for `ℋ₁ ⊔ ℋ₂`. -/
theorem isHistoryAvoidanceLocal_union_of_det (hhm : Measurable h) {A₁ A₂ : Ω → Set ℂ}
    (hA₁ : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ₁] {ω | Disjoint (A₁ ω) U})
    (hA₂ : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ₂] {ω | Disjoint (A₂ ω) U})
    (hdet₁ : ℋ₁ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hdet₂ : ℋ₂ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hloc₁ : WholeField.IsHistoryAvoidanceLocal ℋ₁ A₁ h P)
    (hloc₂ : WholeField.IsHistoryAvoidanceLocal ℋ₂ A₂ h P) :
    WholeField.IsHistoryAvoidanceLocal (ℋ₁ ⊔ ℋ₂) (fun ω => A₁ ω ∪ A₂ ω) h P := by
  refine isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF => ?_
  set E₁ : Set Ω := {ω | Disjoint (A₁ ω) U} with hE₁
  set E₂ : Set Ω := {ω | Disjoint (A₂ ω) U} with hE₂
  -- the marked avoidance events of each set
  have hm₁ : ∀ F₁, MeasurableSet[ℋ₁] F₁ → MeasurableSet[complSigma P G h] (E₁ ∩ F₁) := fun F₁ hF₁ =>
    mem_aeSigma_of_isHistoryAvoidanceLocal hhm hloc₁ hUH hG hd hF₁ (hdet₁ _ ((hA₁ U hUH).inter hF₁))
  have hm₂ : ∀ F₂, MeasurableSet[ℋ₂] F₂ → MeasurableSet[complSigma P G h] (E₂ ∩ F₂) := fun F₂ hF₂ =>
    mem_aeSigma_of_isHistoryAvoidanceLocal hhm hloc₂ hUH hG hd hF₂ (hdet₂ _ ((hA₂ U hUH).inter hF₂))
  have hE₁𝒦 : MeasurableSet[complSigma P G h] E₁ := by
    simpa using hm₁ univ (@MeasurableSet.univ _ ℋ₁)
  have hE₂𝒦 : MeasurableSet[complSigma P G h] E₂ := by
    simpa using hm₂ univ (@MeasurableSet.univ _ ℋ₂)
  have hE : {ω | Disjoint (A₁ ω ∪ A₂ ω) U} = E₁ ∩ E₂ := by
    ext ω
    simp only [mem_ofPred_eq, disjoint_union_left, hE₁, hE₂, mem_inter_iff]
  have hE𝒦 : MeasurableSet[complSigma P G h] (E₁ ∩ E₂) := hE₁𝒦.inter hE₂𝒦
  rw [hE]
  -- the marks `F` with `(E₁ ∩ E₂) ∩ F ∈ 𝒦` form a σ-algebra containing `ℋ₁` and `ℋ₂`
  have hle₁ : ℋ₁ ≤ traceSigma (complSigma P G h) (E₁ ∩ E₂) hE𝒦 := fun F₁ hF₁ => by
    change MeasurableSet[complSigma P G h] ((E₁ ∩ E₂) ∩ F₁)
    have e : (E₁ ∩ E₂) ∩ F₁ = (E₁ ∩ F₁) ∩ E₂ := by
      ext ω; simp only [mem_inter_iff]; tauto
    rw [e]
    exact (hm₁ F₁ hF₁).inter hE₂𝒦
  have hle₂ : ℋ₂ ≤ traceSigma (complSigma P G h) (E₁ ∩ E₂) hE𝒦 := fun F₂ hF₂ => by
    change MeasurableSet[complSigma P G h] ((E₁ ∩ E₂) ∩ F₂)
    have e : (E₁ ∩ E₂) ∩ F₂ = E₁ ∩ (E₂ ∩ F₂) := by
      ext ω; simp only [mem_inter_iff]; tauto
    rw [e]
    exact hE₁𝒦.inter (hm₂ F₂ hF₂)
  exact sup_le hle₁ hle₂ F hF

end Det

end WalkLaw

end Theorem14

end InteractingSLE
