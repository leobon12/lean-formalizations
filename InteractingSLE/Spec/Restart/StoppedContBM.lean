/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.RestartMarkov
import InteractingSLE.Spec.Coupling.WholeField5Ext

/-!
# (CONT), the Brownian part: product factors and a switch at time `0`

Packet PROVE-WFS0, input (CONT) of `planning/handoffs/PROVE-DOMAINMARKOV10.md` §4.1. The continuation of a local
evolution stopped at `V` is built on `Ω × Ω₀`, where `Ω₀` carries an independent full evolution of the same word: on
`{V = 0}` the local evolution says nothing and the full evolution of `Ω₀` is used, with its own Brownian motion. This
file proves the two Brownian facts this needs:

* `isFilteredBrownianReal_prod_fst`, `isFilteredBrownianReal_prod_snd`: a Brownian motion of a factor, read through
  the projection, is a Brownian motion of the product filtration (`WholeField.prodFiltration`) under the product
  measure;
* **`IsFilteredBrownianReal.switch`**: two Brownian motions of one filtration, switched on an event of `𝓖₀`, give a
  Brownian motion of that filtration (the event is independent of both paths, by `Sec2.Restart.indep_future` at `0`,
  and of every increment after time `s`, since it belongs to `𝓖_s`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace StoppedCont

open WholeField QuantumZipper.StrongMarkov

/-! ### The factors of a product -/

section Product

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀]
  {P₀ : Measure Ω₀} [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]

/-- Under a product measure the two coordinate σ-algebras are independent. -/
theorem indep_comap_fst_snd :
    Indep (mΩ.comap Prod.fst) (m₀.comap Prod.snd) (P.prod P₀) := by
  rw [Indep_iff]
  rintro _ _ ⟨A, hA, rfl⟩ ⟨C, hC, rfl⟩
  have e : Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' C = A ×ˢ C := rfl
  rw [e, Measure.prod_prod, ← prod_univ, Measure.prod_prod, ← univ_prod, Measure.prod_prod, measure_univ,
    measure_univ, mul_one, one_mul]

omit [IsProbabilityMeasure P] in
/-- Independence on the first factor lifts to the product. -/
theorem indep_comap_fst {m₁ m₂ : MeasurableSpace Ω} (h : Indep m₁ m₂ P) :
    Indep (m₁.comap Prod.fst) (m₂.comap Prod.fst) (@Measure.prod Ω Ω₀ mΩ m₀ P P₀) := by
  rw [Indep_iff] at h ⊢
  rintro _ _ ⟨A, hA, rfl⟩ ⟨C, hC, rfl⟩
  have e : ∀ D : Set Ω, Prod.fst ⁻¹' D = D ×ˢ (univ : Set Ω₀) := fun D => prod_univ.symm
  have hpp : ∀ (S : Set Ω) (T : Set Ω₀), (@Measure.prod Ω Ω₀ mΩ m₀ P P₀) (S ×ˢ T) = P S * P₀ T :=
    fun S T => @Measure.prod_prod Ω Ω₀ mΩ m₀ P P₀ _ S T
  rw [← preimage_inter, e, e, e, hpp, hpp, hpp, @measure_univ Ω₀ m₀ P₀ _, mul_one, mul_one, mul_one]
  exact h _ _ hA hC

/-- Independence on the second factor lifts to the product. -/
theorem indep_comap_snd {m₁ m₂ : MeasurableSpace Ω₀} (h : Indep m₁ m₂ P₀) :
    Indep (m₁.comap Prod.snd) (m₂.comap Prod.snd) (@Measure.prod Ω Ω₀ mΩ m₀ P P₀) := by
  rw [Indep_iff] at h ⊢
  rintro _ _ ⟨A, hA, rfl⟩ ⟨C, hC, rfl⟩
  have e : ∀ D : Set Ω₀, Prod.snd ⁻¹' D = (univ : Set Ω) ×ˢ D := fun D => univ_prod.symm
  have hpp : ∀ (S : Set Ω) (T : Set Ω₀), (@Measure.prod Ω Ω₀ mΩ m₀ P P₀) (S ×ˢ T) = P S * P₀ T :=
    fun S T => @Measure.prod_prod Ω Ω₀ mΩ m₀ P P₀ _ S T
  rw [← preimage_inter, e, e, e, hpp, hpp, hpp, @measure_univ Ω mΩ P _, one_mul, one_mul, one_mul]
  exact h _ _ hA hC

/-- **A Brownian motion of the first factor is a Brownian motion of the product filtration.** -/
theorem isFilteredBrownianReal_prod_fst {𝓕 : Filtration ℝ≥0 mΩ} (𝓦 : Filtration ℝ≥0 m₀) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓕 B P) :
    IsFilteredBrownianReal (prodFiltration 𝓕 𝓦) (fun t p => B t p.1) (P.prod P₀) := by
  obtain ⟨hb, ha, hi⟩ := hB
  have hmap : (P.prod P₀).map Prod.fst = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hqmp : Measure.QuasiMeasurePreserving Prod.fst (P.prod P₀) P :=
    ⟨measurable_fst, hmap.le.absolutelyContinuous⟩
  refine ⟨⟨⟨fun I => ?_⟩, hqmp.ae hb.cont⟩, fun t => ?_, fun s t hst => ?_⟩
  · have hL := hb.hasLaw I
    refine ⟨hL.aemeasurable.comp_quasiMeasurePreserving hqmp, ?_⟩
    have hL' : AEMeasurable (fun ω => I.restrict (B · ω)) ((P.prod P₀).map Prod.fst) := by
      rw [hmap]; exact hL.aemeasurable
    rw [← hL.map_eq]
    conv_rhs => rw [← hmap]
    rw [AEMeasurable.map_map_of_aemeasurable hL' measurable_fst.aemeasurable]
    rfl
  · exact ((ha t).comp (comap_measurable Prod.fst)).mono (comap_fst_le_prodFiltration 𝓕 𝓦 t) le_rfl
  · have hBm : ∀ r, Measurable (B r) := fun r => (ha r).mono (𝓕.le r) le_rfl
    have h12 : Indep ((MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance).comap Prod.fst)
        ((𝓕 s).comap Prod.fst) (P.prod P₀) := indep_comap_fst (hi s t hst)
    have h123 : Indep ((MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance).comap Prod.fst ⊔
        (𝓕 s).comap Prod.fst) ((𝓦 s).comap Prod.snd) (P.prod P₀) := by
      refine indep_of_indep_of_le_right (indep_of_indep_of_le_left indep_comap_fst_snd ?_) ?_
      · exact sup_le (MeasurableSpace.comap_mono (((hBm t).sub (hBm s)).comap_le))
          (MeasurableSpace.comap_mono (𝓕.le s))
      · exact MeasurableSpace.comap_mono (𝓦.le s)
    have h := Sec2.Restart.indep_sup_right_of_indep
      (MeasurableSpace.comap_mono ((hBm t).sub (hBm s)).comap_le |>.trans
        (measurable_fst.comap_le))
      ((MeasurableSpace.comap_mono (𝓕.le s)).trans measurable_fst.comap_le)
      ((MeasurableSpace.comap_mono (𝓦.le s)).trans measurable_snd.comap_le) h12 h123
    rw [MeasurableSpace.comap_comp] at h
    rw [prodFiltration_apply]
    exact h

/-- **A Brownian motion of the second factor is a Brownian motion of the product filtration.** -/
theorem isFilteredBrownianReal_prod_snd (𝓕 : Filtration ℝ≥0 mΩ) {𝓦 : Filtration ℝ≥0 m₀} {B : ℝ≥0 → Ω₀ → ℝ}
    (hB : IsFilteredBrownianReal 𝓦 B P₀) :
    IsFilteredBrownianReal (prodFiltration 𝓕 𝓦) (fun t p => B t p.2) (P.prod P₀) := by
  obtain ⟨hb, ha, hi⟩ := hB
  have hmap : (P.prod P₀).map Prod.snd = P₀ := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hqmp : Measure.QuasiMeasurePreserving Prod.snd (P.prod P₀) P₀ :=
    ⟨measurable_snd, hmap.le.absolutelyContinuous⟩
  refine ⟨⟨⟨fun I => ?_⟩, hqmp.ae hb.cont⟩, fun t => ?_, fun s t hst => ?_⟩
  · have hL := hb.hasLaw I
    refine ⟨hL.aemeasurable.comp_quasiMeasurePreserving hqmp, ?_⟩
    have hL' : AEMeasurable (fun ω => I.restrict (B · ω)) ((P.prod P₀).map Prod.snd) := by
      rw [hmap]; exact hL.aemeasurable
    rw [← hL.map_eq]
    conv_rhs => rw [← hmap]
    rw [AEMeasurable.map_map_of_aemeasurable hL' measurable_snd.aemeasurable]
    rfl
  · exact ((ha t).comp (comap_measurable Prod.snd)).mono
      (le_sup_right : (𝓦 t).comap Prod.snd ≤ prodFiltration 𝓕 𝓦 t) le_rfl
  · have hBm : ∀ r, Measurable (B r) := fun r => (ha r).mono (𝓦.le r) le_rfl
    have h12 : Indep ((MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance).comap Prod.snd)
        ((𝓦 s).comap Prod.snd) (P.prod P₀) := indep_comap_snd (hi s t hst)
    have h123 : Indep ((MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance).comap Prod.snd ⊔
        (𝓦 s).comap Prod.snd) ((𝓕 s).comap Prod.fst) (P.prod P₀) := by
      refine indep_of_indep_of_le_right (indep_of_indep_of_le_left indep_comap_fst_snd.symm ?_) ?_
      · exact sup_le (MeasurableSpace.comap_mono (((hBm t).sub (hBm s)).comap_le))
          (MeasurableSpace.comap_mono (𝓦.le s))
      · exact MeasurableSpace.comap_mono (𝓕.le s)
    have h := Sec2.Restart.indep_sup_right_of_indep
      (MeasurableSpace.comap_mono ((hBm t).sub (hBm s)).comap_le |>.trans
        (measurable_snd.comap_le))
      ((MeasurableSpace.comap_mono (𝓦.le s)).trans measurable_snd.comap_le)
      ((MeasurableSpace.comap_mono (𝓕.le s)).trans measurable_fst.comap_le) h12 h123
    rw [MeasurableSpace.comap_comp] at h
    rw [prodFiltration_apply, sup_comm]
    exact h

end Product


/-! ### Switching two Brownian motions on an event of `𝓖₀` -/

section Switch

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- **An event of `𝓖₀` is independent of the path of a `𝓖`-Brownian motion**: for every finite set of times, the
event and the values at these times are independent. -/
theorem measure_inter_restrict_preimage {X : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓖 X P) {Z : Set Ω}
    (hZ : MeasurableSet[𝓖 0] Z) (I : Finset ℝ≥0) {S : Set (I → ℝ)} (hS : MeasurableSet S) :
    P (Z ∩ (fun ω => I.restrict (X · ω)) ⁻¹' S) = P Z * BrownianReal.projectiveFamily I S := by
  have := hB.isProbabilityMeasure'
  have hXm : ∀ t, Measurable (X t) := hB.measurable'
  have hind := Sec2.Restart.indep_future hB 0
  have h0 := hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero
  set Y : Ω → ℝ≥0 → ℝ := smPath X (fun _ => (0 : ℝ≥0)) with hY
  have hae : (fun ω => I.restrict (X · ω)) =ᵐ[P] fun ω => I.restrict (Y ω) := by
    filter_upwards [h0] with ω hω
    funext i
    simp only [Finset.restrict, hY, smPath, smShift, zero_add, hω, sub_zero]
  have hf : Measurable fun ω => I.restrict (X · ω) :=
    (Finset.measurable_restrict I).comp (measurable_pi_iff.2 hXm)
  have hL := (hB.1.toIsPreBrownianReal.hasLaw I).map_eq
  have hT : MeasurableSet[MeasurableSpace.comap Y MeasurableSpace.pi]
      ((fun ω => I.restrict (Y ω)) ⁻¹' S) :=
    ⟨(fun f : ℝ≥0 → ℝ => I.restrict f) ⁻¹' S, (Finset.measurable_restrict I) hS, rfl⟩
  have e1 : P (Z ∩ (fun ω => I.restrict (X · ω)) ⁻¹' S) = P (Z ∩ (fun ω => I.restrict (Y ω)) ⁻¹' S) :=
    measure_congr (EventuallyEqSet.inter (by rfl) (hae.preimage S))
  have e2 : P ((fun ω => I.restrict (Y ω)) ⁻¹' S) = BrownianReal.projectiveFamily I S := by
    rw [← measure_congr (hae.preimage S), ← hL, Measure.map_apply hf hS]
  rw [e1, (Indep_iff _ _ _).1 hind _ _ hZ hT, e2]

/-- **Two Brownian motions of one filtration, switched on an event of `𝓖₀`, form a Brownian motion of it**: the
event is independent of both paths (so the finite-dimensional laws are Brownian), and it belongs to every `𝓖_s` (so
an increment after `s`, whose law is the same `N(0, t − s)` for both, stays independent of `𝓖_s`). -/
theorem IsFilteredBrownianReal.switch {X₁ X₂ : ℝ≥0 → Ω → ℝ} (h₁ : IsFilteredBrownianReal 𝓖 X₁ P)
    (h₂ : IsFilteredBrownianReal 𝓖 X₂ P) {Z : Set Ω} [DecidablePred (· ∈ Z)] (hZ : MeasurableSet[𝓖 0] Z) :
    IsFilteredBrownianReal 𝓖 (fun t ω => if ω ∈ Z then X₂ t ω else X₁ t ω) P := by
  have := h₁.isProbabilityMeasure'
  have hZm : MeasurableSet Z := 𝓖.le 0 Z hZ
  have hZs : ∀ s, MeasurableSet[𝓖 s] Z := fun s => 𝓖.mono (zero_le : (0 : ℝ≥0) ≤ s) Z hZ
  have hm₁ : ∀ t, Measurable (X₁ t) := h₁.measurable'
  have hm₂ : ∀ t, Measurable (X₂ t) := h₂.measurable'
  refine ⟨⟨⟨fun I => ?_⟩, ?_⟩, fun t => ?_, fun s t hst => ?_⟩
  · have e : (fun ω => I.restrict (fun t => if ω ∈ Z then X₂ t ω else X₁ t ω)) =
        fun ω => if ω ∈ Z then I.restrict (X₂ · ω) else I.restrict (X₁ · ω) := by
      funext ω
      by_cases hω : ω ∈ Z <;> simp only [hω, ↓reduceIte]
    have hf₁ : Measurable fun ω => I.restrict (X₁ · ω) :=
      (Finset.measurable_restrict I).comp (measurable_pi_iff.2 hm₁)
    have hf₂ : Measurable fun ω => I.restrict (X₂ · ω) :=
      (Finset.measurable_restrict I).comp (measurable_pi_iff.2 hm₂)
    have hf : Measurable fun ω => if ω ∈ Z then I.restrict (X₂ · ω) else I.restrict (X₁ · ω) :=
      Measurable.ite hZm hf₂ hf₁
    rw [e]
    refine ⟨hf.aemeasurable, ?_⟩
    ext S hS
    rw [Measure.map_apply hf hS]
    have e2 : (fun ω => if ω ∈ Z then I.restrict (X₂ · ω) else I.restrict (X₁ · ω)) ⁻¹' S =
        (Z ∩ (fun ω => I.restrict (X₂ · ω)) ⁻¹' S) ∪ (Zᶜ ∩ (fun ω => I.restrict (X₁ · ω)) ⁻¹' S) := by
      ext ω
      by_cases hω : ω ∈ Z <;> simp [hω]
    rw [e2, measure_union (disjoint_compl_right.mono inter_subset_left inter_subset_left)
      (hZm.compl.inter (hf₁ hS)), measure_inter_restrict_preimage h₂ hZ I hS,
      measure_inter_restrict_preimage h₁ (MeasurableSet.compl hZ) I hS, ← add_mul, measure_add_measure_compl hZm,
      measure_univ, one_mul]
  · filter_upwards [h₁.1.cont, h₂.1.cont] with ω c₁ c₂
    by_cases hω : ω ∈ Z
    · simpa only [hω, ↓reduceIte] using c₂
    · simpa only [hω, ↓reduceIte] using c₁
  · exact Measurable.ite (hZs t) (h₂.2.1 t) (h₁.2.1 t)
  · rw [Indep_iff]
    rintro _ T ⟨S, hS, rfl⟩ hT
    have hL₁ := h₁.1.hasLaw_sub t s
    have hL₂ := h₂.1.hasLaw_sub t s
    have e₁ : P ((fun ω => X₁ t ω - X₁ s ω) ⁻¹' S) = gaussianReal 0 (nndist t.1 s.1) S := by
      rw [← hL₁.map_eq, Measure.map_apply_of_aemeasurable hL₁.aemeasurable hS]; rfl
    have e₂ : P ((fun ω => X₂ t ω - X₂ s ω) ⁻¹' S) = gaussianReal 0 (nndist t.1 s.1) S := by
      rw [← hL₂.map_eq, Measure.map_apply_of_aemeasurable hL₂.aemeasurable hS]; rfl
    have hΔ₁ : Measurable fun ω => X₁ t ω - X₁ s ω := (hm₁ t).sub (hm₁ s)
    have hΔ₂ : Measurable fun ω => X₂ t ω - X₂ s ω := (hm₂ t).sub (hm₂ s)
    have key : ∀ T : Set Ω, MeasurableSet[𝓖 s] T →
        P ((fun ω => (if ω ∈ Z then X₂ t ω else X₁ t ω) - (if ω ∈ Z then X₂ s ω else X₁ s ω)) ⁻¹' S ∩ T) =
          gaussianReal 0 (nndist t.1 s.1) S * P T := by
      intro T hT
      have hTm : MeasurableSet T := 𝓖.le s T hT
      have e : (fun ω => (if ω ∈ Z then X₂ t ω else X₁ t ω) - (if ω ∈ Z then X₂ s ω else X₁ s ω)) ⁻¹' S ∩ T =
          ((fun ω => X₂ t ω - X₂ s ω) ⁻¹' S ∩ (T ∩ Z)) ∪ ((fun ω => X₁ t ω - X₁ s ω) ⁻¹' S ∩ (T ∩ Zᶜ)) := by
        ext ω
        by_cases hω : ω ∈ Z <;> simp [hω, and_comm]
      have i₁ := (Indep_iff _ _ _).1 (h₁.2.2 s t hst) _ _ ⟨S, hS, rfl⟩ (hT.inter (hZs s).compl)
      have i₂ := (Indep_iff _ _ _).1 (h₂.2.2 s t hst) _ _ ⟨S, hS, rfl⟩ (hT.inter (hZs s))
      have hdis : Disjoint ((fun ω => X₂ t ω - X₂ s ω) ⁻¹' S ∩ (T ∩ Z))
          ((fun ω => X₁ t ω - X₁ s ω) ⁻¹' S ∩ (T ∩ Zᶜ)) :=
        disjoint_compl_right.mono (inter_subset_right.trans inter_subset_right)
          (inter_subset_right.trans inter_subset_right)
      rw [e, measure_union hdis ((hΔ₁ hS).inter (hTm.inter hZm.compl)), i₁, i₂, e₁, e₂, ← mul_add, ← sdiff_eq,
        measure_inter_add_sdiff T hZm]
    have h1 := key T hT
    have h2 := key univ MeasurableSet.univ
    rw [inter_univ, measure_univ, mul_one] at h2
    rw [h1, h2]

end Switch

end StoppedCont

end Restart

end InteractingSLE
