/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibKCode

/-!
# Disintegration with history-dependent integrands, and conditional kernels in a fibre

Packet PROVE-AUX61-FIB2. PROVE-AUX61-FIB's `ae_forall_setIntegral_condDistrib_eq_zero` passes vanishing rectangle
integrals of `h(Y)` to almost every fibre. The fibre's data (`FibData`: the correction `q`, the cutoff, the reference
word) are functions of the retained history `Z`, so the integrands are `h(Z, Y)`:

* `setIntegral_rect_eq₂`, `ae_setIntegral_condDistrib_eq_zero₂`, **`ae_forall_setIntegral_condDistrib_eq_zero₂`**: the
  same statements for a bounded jointly measurable `h : β × S → ℂ` and a π-system indexed by any countable type;
* **`ae_condExp_eq_of_forall_setIntegral`**: in one fibre, if `∫_{A ∩ G} f = ∫_{A ∩ G} g` for every event `A` of a
  σ-algebra `𝒞` containing `G`, with `g` bounded and `𝒞`-measurable, then `E[f | 𝒞] = g` almost surely on `G`.

Measure theory only. R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any
`*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61FibK

/-! ### Rectangle integrals with history-dependent integrands -/

section Disint

variable {X β S : Type*} [MeasurableSpace X] [MeasurableSpace β] [mS : MeasurableSpace S] [StandardBorelSpace S]
  [Nonempty S] {μ : Measure X} [IsFiniteMeasure μ] {Z : X → β} {Y : X → S}

/-- **Rectangle set integrals disintegrate**: `∫_{Z ∈ B, Y ∈ A} h(Z, Y) dμ = ∫_B (∫_A h(z, ·) dP_z) d(Z_* μ)(z)`. -/
theorem setIntegral_rect_eq₂ (hZ : Measurable Z) (hY : Measurable Y) {h : β × S → ℂ} (hh : Measurable h)
    {C : ℝ} (hC : ∀ p, ‖h p‖ ≤ C) {B : Set β} (hB : MeasurableSet B) {A : Set S} (hA : MeasurableSet A) :
    ∫ x in Z ⁻¹' B ∩ Y ⁻¹' A, h (Z x, Y x) ∂μ =
      ∫ z in B, (∫ s in A, h (z, s) ∂(condDistrib Y Z μ z)) ∂(μ.map Z) := by
  have hZY : Measurable fun x => (Z x, Y x) := hZ.prodMk hY
  have e1 : ∫ x in Z ⁻¹' B ∩ Y ⁻¹' A, h (Z x, Y x) ∂μ = ∫ p in B ×ˢ A, h p ∂(μ.map fun x => (Z x, Y x)) := by
    rw [setIntegral_map (f := h) (hB.prod hA) hh.aestronglyMeasurable hZY.aemeasurable]
    rfl
  rw [e1, ← compProd_map_condDistrib hZ.aemeasurable hY.aemeasurable, Measure.setIntegral_compProd hB hA]
  exact (Integrable.of_bound hh.aestronglyMeasurable C (ae_of_all _ hC)).integrableOn

/-- **Vanishing rectangle integrals vanish in almost every fibre** (history-dependent integrand). -/
theorem ae_setIntegral_condDistrib_eq_zero₂ (hZ : Measurable Z) (hY : Measurable Y) {h : β × S → ℂ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ p, ‖h p‖ ≤ C) {A : Set S} (hA : MeasurableSet A)
    (H : ∀ B : Set β, MeasurableSet B → ∫ x in Z ⁻¹' B ∩ Y ⁻¹' A, h (Z x, Y x) ∂μ = 0) :
    ∀ᵐ x ∂μ, ∫ s in A, h (Z x, s) ∂(condDistrib Y Z μ (Z x)) = 0 := by
  set Φ : β → ℂ := fun z => ∫ s in A, h (z, s) ∂(condDistrib Y Z μ z) with hΦ
  have hΦm : StronglyMeasurable Φ := by
    have hf : StronglyMeasurable fun p : β × S => A.indicator (fun s => h (p.1, s)) p.2 := by
      have e : (fun p : β × S => A.indicator (fun s => h (p.1, s)) p.2) = (Prod.snd ⁻¹' A).indicator h := by
        funext p
        by_cases hp : p.2 ∈ A
        · simp [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' A from hp)]
        · simp [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' A from hp)]
      rw [e]
      exact (hh.indicator (measurable_snd hA)).stronglyMeasurable
    have := hf.integral_condDistrib (X := Z) (Y := Y) (μ := μ)
    convert this using 2 with z
    exact (integral_indicator hA).symm
  have hΦb : ∀ z, ‖Φ z‖ ≤ C := by
    intro z
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (z, Classical.arbitrary S))
    refine (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun s _ => hC (z, s)).trans ?_
    calc C * (condDistrib Y Z μ z A).toReal ≤ C * 1 :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal zero_le_one
            (by rw [ENNReal.ofReal_one]; exact prob_le_one)) hC0
      _ = C := mul_one C
  have hint : Integrable Φ (μ.map Z) := Integrable.of_bound hΦm.aestronglyMeasurable C (ae_of_all _ hΦb)
  have h0 : Φ =ᵐ[μ.map Z] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun _ _ _ => hint.integrableOn) fun B hB _ => ?_
    rw [← setIntegral_rect_eq₂ hZ hY hh hC hB hA, H B hB]
  exact ae_of_ae_map hZ.aemeasurable h0

/-- **Vanishing on a countable π-system passes to the generated σ-algebra in almost every fibre** (history-dependent
integrand, any countable index type). -/
theorem ae_forall_setIntegral_condDistrib_eq_zero₂ (hZ : Measurable Z) (hY : Measurable Y) {h : β × S → ℂ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ p, ‖h p‖ ≤ C) {ι : Type*} [Countable ι] {𝒜 : ι → Set S}
    (h𝒜 : ∀ n, MeasurableSet (𝒜 n)) (hpi : IsPiSystem (range 𝒜))
    (H : ∀ n, ∀ B : Set β, MeasurableSet B → ∫ x in Z ⁻¹' B ∩ Y ⁻¹' 𝒜 n, h (Z x, Y x) ∂μ = 0)
    (Huniv : ∀ B : Set β, MeasurableSet B → ∫ x in Z ⁻¹' B, h (Z x, Y x) ∂μ = 0) :
    ∀ᵐ x ∂μ, ∀ A : Set S, MeasurableSet[MeasurableSpace.generateFrom (range 𝒜)] A →
      ∫ s in A, h (Z x, s) ∂(condDistrib Y Z μ (Z x)) = 0 := by
  have h1 : ∀ᵐ x ∂μ, ∀ n, ∫ s in 𝒜 n, h (Z x, s) ∂(condDistrib Y Z μ (Z x)) = 0 :=
    ae_all_iff.2 fun n => ae_setIntegral_condDistrib_eq_zero₂ hZ hY hh hC (h𝒜 n) (H n)
  have h2 : ∀ᵐ x ∂μ, ∫ s in univ, h (Z x, s) ∂(condDistrib Y Z μ (Z x)) = 0 :=
    ae_setIntegral_condDistrib_eq_zero₂ hZ hY hh hC MeasurableSet.univ fun B hB => by
      simpa only [preimage_univ, inter_univ] using Huniv B hB
  have hle : MeasurableSpace.generateFrom (range 𝒜) ≤ mS :=
    MeasurableSpace.generateFrom_le (by rintro _ ⟨n, rfl⟩; exact h𝒜 n)
  filter_upwards [h1, h2] with x hx hxu
  set ν := condDistrib Y Z μ (Z x) with hν
  have hint : Integrable (fun s => h (Z x, s)) ν :=
    Integrable.of_bound (hh.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
      (ae_of_all _ fun s => hC _)
  intro A hA
  induction A, hA using MeasurableSpace.induction_on_inter (h_eq := rfl) (h_inter := hpi) with
  | empty => simp
  | basic t ht =>
    obtain ⟨n, rfl⟩ := ht
    exact hx n
  | compl t htm ht =>
    have e := integral_add_compl (hle t htm) hint
    have hall : ∫ s, h (Z x, s) ∂ν = 0 := by rw [← setIntegral_univ]; exact hxu
    rw [ht, zero_add, hall] at e
    exact e
  | iUnion f hd hfm hf =>
    rw [integral_iUnion (fun i => hle _ (hfm i)) hd hint.integrableOn]
    simp [hf]

end Disint

/-! ### Conditional kernels in one fibre -/

section Fibre

variable {S : Type*} {𝒞 : MeasurableSpace S} [mS : MeasurableSpace S] {ν : Measure S} [IsFiniteMeasure ν]

/-- **Set integrals on the events of `𝒞` identify the conditional expectation on an event of `𝒞`**: if
`∫_{A ∩ G} f = ∫_{A ∩ G} g` for every `A ∈ 𝒞`, with `G ∈ 𝒞` and `g` bounded and `𝒞`-measurable, then
`E[f | 𝒞] = g` almost surely on `G`. -/
theorem ae_condExp_eq_of_forall_setIntegral (h𝒞 : 𝒞 ≤ mS) {f g : S → ℂ} (hf : Integrable f ν)
    (hg : StronglyMeasurable[𝒞] g) {C : ℝ} (hgb : ∀ s, ‖g s‖ ≤ C) {G : Set S} (hG : MeasurableSet[𝒞] G)
    (H : ∀ A : Set S, MeasurableSet[𝒞] A → ∫ s in A ∩ G, f s ∂ν = ∫ s in A ∩ G, g s ∂ν) :
    ∀ᵐ s ∂ν, s ∈ G → ν[f | 𝒞] s = g s := by
  have hGm : MeasurableSet G := h𝒞 _ hG
  have hgint : Integrable g ν := Integrable.of_bound (hg.mono h𝒞).aestronglyMeasurable C (ae_of_all _ hgb)
  have h1 : G.indicator g =ᵐ[ν] ν[G.indicator f | 𝒞] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq h𝒞 (hf.indicator hGm)
      (fun s _ _ => (hgint.indicator hGm).integrableOn) (fun A hA _ => ?_)
      (hg.indicator hG).aestronglyMeasurable
    rw [setIntegral_indicator hGm, setIntegral_indicator hGm, H A hA]
  have h2 := condExp_indicator (m := 𝒞) hf hG
  filter_upwards [h1, h2] with s hs1 hs2 hsG
  have e1 : G.indicator g s = g s := indicator_of_mem hsG g
  have e2 : G.indicator (ν[f | 𝒞]) s = ν[f | 𝒞] s := indicator_of_mem hsG _
  rw [← e1, hs1, hs2, e2]

end Fibre

end InteractingSLE.Sec5.Aux61FibK
