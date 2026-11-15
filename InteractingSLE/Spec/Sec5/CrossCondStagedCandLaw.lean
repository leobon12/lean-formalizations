/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedCandComp
import InteractingSLE.WangWu.Prop418RangeMain

/-!
# Proposition 5.9: transferring a comparison-form stage law between probability spaces

Packet PROVE-STAGED7. The staged cross-conditioning results (S2, S3) live on the θ-glued space `Ω × HistorySpace`
(the flow side on `Ω`, the counterflow history glued conditionally on the field), while PROVE-PROP59-PIECES' candidates
live on `Ω × Ωa` with the counterflow of the same sample. The comparison clause of a stage law (`IsCompLaw`, in
particular the killed law `IsStageLawFar`) only sees the **law** of the variables generating the past, the reached
event and the observable. This file proves the two generic steps of the transfer:

* **`compClause_of_map_eq`**: if `Z` and `Z'` have the same law, the comparison clause for the past `σ(Z)`-events,
  the reached event `{Z ∈ R}` and the observable `o ∘ Z` passes from `Z'` to `Z`;
* **`isCompLaw_of_map_eq`**: the comparison-form law itself passes, given the pathwise clause on the target space
  (pathwise predicates are not measurable events in general, so that clause is not a law statement — ruling R51);
* **`map_pair_eq_glue`**: for a field `X`, a second variable `Y` whose conditional law given `X` is the kernel `k`,
  and data `D` almost surely a measurable function of `X`, the pair `(D, Y)` has the same law on the one space as
  `(D ∘ fst, snd)` on the glued space `glueMeasure P k X`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedCand

/-! ### The comparison clause depends only on the law -/

section Transfer

variable {Ω Ω' Γ X : Type*} {𝓜 : MeasurableSpace Γ} {𝓠 : MeasurableSpace Ω} {𝓠' : MeasurableSpace Ω'}
  [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [mΓ : MeasurableSpace Γ] [mX : MeasurableSpace X]

/-- **The comparison clause depends only on the law of its generating variable.** If `Z` and `Z'` have the same law,
`𝓜 ≤ mΓ`, `RΓ ∈ 𝓜` and `o` is measurable, then the comparison inequalities for the past events `σ_𝓜(Z')`, the reached
event `{Z' ∈ RΓ}` and the observable `o ∘ Z'` give those for `Z`. -/
theorem compClause_of_map_eq {P : Measure Ω} {P' : Measure Ω'} {Z : Ω → Γ} {Z' : Ω' → Γ} (hZ : Measurable Z)
    (hZ' : Measurable Z') (hlaw : P.map Z = P'.map Z') (h𝓜 : 𝓜 ≤ mΓ) {RΓ : Set Γ} (hR : MeasurableSet[𝓜] RΓ)
    {o : Γ → X} (ho : Measurable o) {Prem : Set X → ℝ≥0∞ → Prop}
    (h' : ∀ S : Set X, MeasurableSet S → ∀ p : ℝ≥0∞, Prem S p → ∀ A : Set Ω', MeasurableSet[𝓜.comap Z'] A →
      A ⊆ Z' ⁻¹' RΓ → p * P' A ≤ P' (A ∩ {ω | o (Z' ω) ∈ S})) :
    ∀ S : Set X, MeasurableSet S → ∀ p : ℝ≥0∞, Prem S p → ∀ A : Set Ω, MeasurableSet[𝓜.comap Z] A →
      A ⊆ Z ⁻¹' RΓ → p * P A ≤ P (A ∩ {ω | o (Z ω) ∈ S}) := by
  intro S hS p hp A hA hAR
  obtain ⟨M, hM, rfl⟩ := hA
  have hMR : Z ⁻¹' M = Z ⁻¹' (M ∩ RΓ) := by
    ext ω
    simp only [mem_preimage, mem_inter_iff]
    exact ⟨fun h => ⟨h, hAR h⟩, fun h => h.1⟩
  have hM' : MeasurableSet[𝓜] (M ∩ RΓ) := hM.inter hR
  have hM'm : MeasurableSet (M ∩ RΓ) := h𝓜 _ hM'
  have hT : MeasurableSet (M ∩ RΓ ∩ o ⁻¹' S) := hM'm.inter (ho hS)
  have e1 : P (Z ⁻¹' (M ∩ RΓ)) = P' (Z' ⁻¹' (M ∩ RΓ)) := by
    rw [← Measure.map_apply hZ hM'm, hlaw, Measure.map_apply hZ' hM'm]
  have e2 : P (Z ⁻¹' (M ∩ RΓ) ∩ {ω | o (Z ω) ∈ S}) = P' (Z' ⁻¹' (M ∩ RΓ) ∩ {ω | o (Z' ω) ∈ S}) := by
    have a : Z ⁻¹' (M ∩ RΓ) ∩ {ω | o (Z ω) ∈ S} = Z ⁻¹' (M ∩ RΓ ∩ o ⁻¹' S) := rfl
    have b : Z' ⁻¹' (M ∩ RΓ) ∩ {ω | o (Z' ω) ∈ S} = Z' ⁻¹' (M ∩ RΓ ∩ o ⁻¹' S) := rfl
    rw [a, b, ← Measure.map_apply hZ hT, hlaw, Measure.map_apply hZ' hT]
  rw [hMR, e1, e2]
  exact h' S hS p hp _ ⟨M ∩ RΓ, hM', rfl⟩ fun ω h => h.2

variable {nL nR : ℕ} {Φ : StageRec nL nR → Prop} {g : StageRec nL nR → X} {Prem : Set X → ℝ≥0∞ → Prop}

/-- **A comparison-form law passes between spaces with the same law of the generating variable.** On `Ω'` the law
holds for a past containing `σ_𝓜(Z')`, the reached event `{Z' ∈ RΓ}` and a record whose observable is a.s. `o ∘ Z'`
there; on `Ω` the past is contained in `σ_𝓜(Z)`, the reached event is `{Z ∈ RΓ}`, the observable is a.s. `o ∘ Z` there,
and the pathwise clause is given. Then the law holds on `Ω`. -/
theorem isCompLaw_of_map_eq {P : Measure Ω} {P' : Measure Ω'} {Z : Ω → Γ} {Z' : Ω' → Γ} (hZ : Measurable Z)
    (hZ' : Measurable Z') (hlaw : P.map Z = P'.map Z') (h𝓜 : 𝓜 ≤ mΓ) {RΓ : Set Γ} (hR : MeasurableSet[𝓜] RΓ)
    {o : Γ → X} (ho : Measurable o) {rec' : Ω' → StageRec nL nR}
    (hL' : IsCompLaw P' 𝓠' (Z' ⁻¹' RΓ) Φ g Prem rec') (h𝓠' : 𝓜.comap Z' ≤ 𝓠')
    (hobs' : ∀ᵐ ω ∂P', ω ∈ Z' ⁻¹' RΓ → g (rec' ω) = o (Z' ω))
    {rec : Ω → StageRec nL nR} (h𝓠 : 𝓠 ≤ 𝓜.comap Z)
    (hobs : ∀ᵐ ω ∂P, ω ∈ Z ⁻¹' RΓ → g (rec ω) = o (Z ω)) (hpath : ∀ᵐ ω ∂P, ω ∈ Z ⁻¹' RΓ → Φ (rec ω)) :
    IsCompLaw P 𝓠 (Z ⁻¹' RΓ) Φ g Prem rec := by
  refine ⟨hpath, fun S hS p hp A hA hAR => ?_⟩
  have key := compClause_of_map_eq hZ hZ' hlaw h𝓜 hR ho (Prem := Prem) (fun S hS p hp A hA hAR => by
    refine ((hL'.2 S hS p hp A (h𝓠' _ hA) hAR).trans (le_of_eq (measure_congr ?_)))
    filter_upwards [hobs'] with ω hω
    refine propext ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
    · show o (Z' ω) ∈ S
      rw [← hω (hAR h.1)]; exact h.2
    · show g (rec' ω) ∈ S
      rw [hω (hAR h.1)]; exact h.2) S hS p hp A (h𝓠 _ hA) hAR
  refine key.trans (le_of_eq (measure_congr ?_))
  filter_upwards [hobs] with ω hω
  refine propext ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · show g (rec ω) ∈ S
    rw [hω (hAR h.1)]; exact h.2
  · show o (Z ω) ∈ S
    rw [← hω (hAR h.1)]; exact h.2

end Transfer

/-! ### The one-space pair and the glued pair have the same law -/

section Glue

variable {Ω α β E : Type*} [mΩ : MeasurableSpace Ω] [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  [mE : MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → α}

/-- The glued pair `(X ∘ fst, snd)` has the law `law(X) ⊗ k` (generic form of `WangWu.glueMeasure_map_pair`). -/
theorem glueMeasure_map_pair_gen (hX : Measurable X) (k : Kernel α β) [IsMarkovKernel k] :
    (WangWu.glueMeasure P k X hX).map (fun p => (X p.1, p.2)) = P.map X ⊗ₘ k := by
  have hm : Measurable fun p : Ω × β => (X p.1, p.2) := (hX.comp measurable_fst).prodMk measurable_snd
  refine Measure.ext_prod fun {A C} hA hC => ?_
  rw [Measure.map_apply hm (hA.prod hC), Measure.compProd_apply_prod hA hC]
  have e : (fun p : Ω × β => (X p.1, p.2)) ⁻¹' (A ×ˢ C) = (X ⁻¹' A) ×ˢ C := by ext; simp
  rw [e, WangWu.glueMeasure_apply_prod k hX (hX hA) hC, setLIntegral_map hA (k.measurable_coe hC) hX]

/-- **The one-space pair and the glued pair have the same law.** If the conditional law of `Y` given the field `X` is
the kernel `k` (`law(X, Y) = law(X) ⊗ k`) and `D` is almost surely a measurable function `L` of `X` (e.g. the staged
records of fixed schedules, PROVE-STAGED5's `ae_pastMap_eq_codePast`), then `(D, Y)` on `(Ω, P)` has the law of
`(D ∘ fst, snd)` on the glued space. -/
theorem map_pair_eq_glue (hX : Measurable X) {Y : Ω → β} (hY : Measurable Y) (k : Kernel α β) [IsMarkovKernel k]
    (hk : P.map (fun ω => (X ω, Y ω)) = P.map X ⊗ₘ k) {D : Ω → E} {L : α → E}
    (hL : Measurable L) (hDL : ∀ᵐ ω ∂P, D ω = L (X ω)) :
    P.map (fun ω => (D ω, Y ω)) = (WangWu.glueMeasure P k X hX).map (fun p => (D p.1, p.2)) := by
  have hLm : Measurable (Prod.map L (id : β → β)) := hL.prodMap measurable_id
  have h1 : P.map (fun ω => (D ω, Y ω)) = (P.map X ⊗ₘ k).map (Prod.map L id) := by
    rw [← hk, Measure.map_map hLm (hX.prodMk hY)]
    refine Measure.map_congr ?_
    filter_upwards [hDL] with ω hω
    simp only [Function.comp_apply, Prod.map_apply, id_eq, hω]
  have h2 : (WangWu.glueMeasure P k X hX).map (fun p => (D p.1, p.2)) = (P.map X ⊗ₘ k).map (Prod.map L id) := by
    have hm : Measurable fun p : Ω × β => (X p.1, p.2) := (hX.comp measurable_fst).prodMk measurable_snd
    rw [← glueMeasure_map_pair_gen hX k, Measure.map_map hLm hm]
    refine Measure.map_congr ?_
    filter_upwards [WangWu.ae_glue_fst k hX hDL] with p hp
    simp only [Function.comp_apply, Prod.map_apply, id_eq, hp]
  rw [h1, h2]

end Glue

end InteractingSLE.Sec5.CrossCond.StagedCand
