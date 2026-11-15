/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmMarks

/-!
# GW2's open lines: conditional expectations given countably generated marks under the kernel of a coarser σ-algebra

Packet PROVE-GW2-STAGEMEAN, R117(b) round. The stage identity is read under `μ_{ω₀} = condExpKernel P 𝒢 ω₀`, `𝒢` the
σ-algebra of the earlier pieces. The marks `𝓚` of the stage union are countably generated and contain `𝒢` ((T2)). Then
a conditional expectation given `𝓚` under `P` is one under `μ_{ω₀}` for `P`-a.e. `ω₀`:

* `piOf b`: the finite intersections of a family `b` of sets (a π-system, countable when `b` is, generating the same
  σ-algebra);
* **`ae_condExp_condExpKernel_eq`**: `μ_{ω₀}[f | 𝓚] = P[f | 𝓚]` `μ_{ω₀}`-a.e., for `P`-a.e. `ω₀` (on the countable
  π-system by the tower property, then for all of `𝓚` by Dynkin's π-λ theorem, then uniqueness of conditional
  expectations).

General measure theory; no hypothesis about GW2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InteractingSLE.Theorem14.GW2Olm

/-! ### A countable π-system of finite intersections -/

/-- The finite intersections of members of `b` (the empty intersection is `univ`). -/
def piOf {α : Type*} (b : Set (Set α)) : Set (Set α) :=
  {A | ∃ F : Finset (Set α), (↑F : Set (Set α)) ⊆ b ∧ A = ⋂₀ (↑F : Set (Set α))}

theorem isPiSystem_piOf {α : Type*} (b : Set (Set α)) : IsPiSystem (piOf b) := by
  classical
  rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG, rfl⟩ -
  refine ⟨F ∪ G, ?_, ?_⟩
  · rw [Finset.coe_union]
    exact union_subset hF hG
  · rw [Finset.coe_union, sInter_union]

theorem countable_piOf {α : Type*} {b : Set (Set α)} (hb : b.Countable) : (piOf b).Countable := by
  classical
  have hF : {F : Finset (Set α) | (↑F : Set (Set α)) ⊆ b}.Countable := by
    have := hb.to_subtype
    have e : {F : Finset (Set α) | (↑F : Set (Set α)) ⊆ b} ⊆
        range (fun G : Finset b => G.map (Function.Embedding.subtype _)) := by
      intro F hF
      refine ⟨F.subtype (· ∈ b), ?_⟩
      ext A
      simp only [Finset.mem_map, Finset.mem_subtype, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨⟨B, hB⟩, hBF, rfl⟩
        exact hBF
      · intro hA
        exact ⟨⟨A, hF hA⟩, hA, rfl⟩
    exact (countable_range _).mono e
  have e : piOf b = (fun F : Finset (Set α) => ⋂₀ (↑F : Set (Set α))) ''
      {F : Finset (Set α) | (↑F : Set (Set α)) ⊆ b} := by
    ext A
    simp only [piOf, mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact ⟨F, hF, rfl⟩
    · rintro ⟨F, hF, rfl⟩
      exact ⟨F, hF, rfl⟩
  rw [e]
  exact hF.image _

theorem subset_piOf {α : Type*} (b : Set (Set α)) : b ⊆ piOf b := by
  classical
  intro A hA
  refine ⟨{A}, ?_, ?_⟩
  · simp only [Finset.coe_singleton, singleton_subset_iff]
    exact hA
  · simp only [Finset.coe_singleton, sInter_singleton]

theorem univ_mem_piOf {α : Type*} (b : Set (Set α)) : univ ∈ piOf b :=
  ⟨∅, by simp, by simp⟩

theorem generateFrom_piOf {α : Type*} (b : Set (Set α)) :
    MeasurableSpace.generateFrom (piOf b) = MeasurableSpace.generateFrom b := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_mono (subset_piOf b))
  rintro _ ⟨F, hF, rfl⟩
  exact MeasurableSet.sInter F.countable_toSet fun A hA => MeasurableSpace.measurableSet_generateFrom (hF hA)

/-! ### The tower under the conditional kernel -/

/-- **A conditional expectation given countably generated marks `𝓚 ⊇ 𝒢` under `P` is one under the conditional
kernel `condExpKernel P 𝒢 ω₀`, for `P`-a.e. `ω₀`.** -/
theorem ae_condExp_condExpKernel_eq {Ω : Type*} {𝒢 𝓚 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ 𝓚) (h𝓚 : 𝓚 ≤ mΩ)
    (hcg : @MeasurableSpace.CountablyGenerated Ω 𝓚) {f : Ω → ℂ} (hf : Integrable f P) :
    ∀ᵐ ω₀ ∂P, (condExpKernel P 𝒢 ω₀)[f | 𝓚] =ᵐ[condExpKernel P 𝒢 ω₀] P[f | 𝓚] := by
  obtain ⟨b, hbc, hb⟩ := hcg.isCountablyGenerated
  set Z : Ω → ℂ := P[f | 𝓚] with hZ
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans h𝓚
  have hZi : Integrable Z P := integrable_condExp
  have hgen : 𝓚 = MeasurableSpace.generateFrom (piOf b) := hb.trans (generateFrom_piOf b).symm
  have hbasic : ∀ A ∈ piOf b, ∀ᵐ ω₀ ∂P,
      ∫ x in A, Z x ∂(condExpKernel P 𝒢 ω₀) = ∫ x in A, f x ∂(condExpKernel P 𝒢 ω₀) := by
    intro A hA
    have hAK : MeasurableSet[𝓚] A := by
      rw [hgen]
      exact MeasurableSpace.measurableSet_generateFrom hA
    have hAm : MeasurableSet A := h𝓚 _ hAK
    have h1 := condExp_ae_eq_integral_condExpKernel h𝒢m (hZi.indicator hAm)
    have h2 := condExp_ae_eq_integral_condExpKernel h𝒢m (hf.indicator hAm)
    have h3 : P[A.indicator Z | 𝒢] =ᵐ[P] P[A.indicator f | 𝒢] := by
      have e1 : A.indicator Z =ᵐ[P] P[A.indicator f | 𝓚] := (condExp_indicator hf hAK).symm
      calc P[A.indicator Z | 𝒢] =ᵐ[P] P[P[A.indicator f | 𝓚] | 𝒢] := condExp_congr_ae e1
        _ =ᵐ[P] P[A.indicator f | 𝒢] := condExp_condExp_of_le h𝒢 h𝓚
    filter_upwards [h1, h2, h3] with ω₀ e1 e2 e3
    rw [← integral_indicator hAm, ← integral_indicator hAm, ← e1, ← e2, e3]
  have hcount : (piOf b).Countable := countable_piOf hbc
  have := hcount.to_subtype
  have hall : ∀ᵐ ω₀ ∂P, ∀ A : piOf b,
      ∫ x in (A : Set Ω), Z x ∂(condExpKernel P 𝒢 ω₀) = ∫ x in (A : Set Ω), f x ∂(condExpKernel P 𝒢 ω₀) :=
    ae_all_iff.2 fun A => hbasic A A.2
  filter_upwards [hall, hf.condExpKernel_ae, hZi.condExpKernel_ae] with ω₀ hω hfi hZi'
  set μ := condExpKernel P 𝒢 ω₀ with hμ
  have hall' : ∀ A, MeasurableSet[𝓚] A → ∫ x in A, Z x ∂μ = ∫ x in A, f x ∂μ := by
    intro A hA
    refine MeasurableSpace.induction_on_inter (m := 𝓚)
      (C := fun A _ => ∫ x in A, Z x ∂μ = ∫ x in A, f x ∂μ) hgen (isPiSystem_piOf b) ?_ ?_ ?_ ?_ A hA
    · simp only [Measure.restrict_empty, integral_zero_measure]
    · intro t ht
      exact hω ⟨t, ht⟩
    · intro t htm ht
      have htm' : MeasurableSet t := h𝓚 _ htm
      have hu := hω ⟨univ, univ_mem_piOf b⟩
      simp only [Measure.restrict_univ] at hu
      rw [setIntegral_compl htm' hZi', setIntegral_compl htm' hfi, ht, hu]
    · intro F hd hFm hF
      rw [integral_iUnion (fun i => h𝓚 _ (hFm i)) hd hZi'.integrableOn,
        integral_iUnion (fun i => h𝓚 _ (hFm i)) hd hfi.integrableOn]
      simp only [hF]
  exact (ae_eq_condExp_of_forall_setIntegral_eq h𝓚 hfi (fun s _ _ => hZi'.integrableOn)
    (fun s hs _ => hall' s hs) stronglyMeasurable_condExp.aestronglyMeasurable).symm

end InteractingSLE.Theorem14.GW2Olm
