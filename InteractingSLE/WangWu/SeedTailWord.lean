/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Shift.Statement

/-!
# The shifted two-slit word up to its killing time

Packet PROVE-WW-B27. The shifted mean-martingale law is the input of PROVE-WW-B26.
The geometric good set uses only the two marginal laws, so the two weights on the
reverse coupling may differ from those on the forward coupling. Lemma 2.11 then
gives the integrated equations before the killing time, without continuing the trace.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedTail

open LQGMetric (DistOn)
open LawUnique ImgWord ImgDrv MartChar

section Good

variable {rL rR bL bR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h X : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ}
  {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- Good glued samples depend on the marginal words separately. -/
theorem ae_isGlueGood_of_marginals (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hbL : 0 ≤ bL) (hbR : 0 ≤ bR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR)
      P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => bL) (fun _ => bR)
      P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (hXm : Measurable X) (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) {s : ℚ} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k X hXm), IsGlueGood s ζ W p := by
  have hα := ae_glue_fst (μ := P) k hXm (ae_good_twoSeed hL hR hC.1)
  have hRh₂ := measurable_reflectField.comp hC₂.2.1
  have hD₂ := measurable_killedHistory hC₂.2.2.2.1
  have hβ := ae_glue_snd hXm hRh₂ hD₂ hlaw k hk (measurableSet_betaSet s)
    (ae_killedHistory_mem_betaSet hbL hbR hC₂.1 hs)
  have hg := ae_glue_snd hXm hRh₂ hD₂ hlaw k hk (measurableSet_goodHist s)
    (ae_mem_goodHist_twoSeed hbL hbR hC₂.1 s)
  filter_upwards [hα, hβ, hg] with p hp hβp hgp
  exact ⟨hp.1, hβp, hgp⟩

end Good

/-- Lemma 2.11 for the shifted two-slit word. The Brownian motion is constructed on
an independent extension; the word and its killing time keep their original values. -/
theorem exists_isWordEntrance_shift (hI : ImageWordFiltShiftStatement.{u})
    (rL rR δ : ℝ) (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hbR : 0 ≤ rL + δ) (hbL : 0 ≤ rR - δ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR)
      P 𝓕 W VL VR B ζ h)
    (X : Ω → DistOn upperHalfPlaneOpens) (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (𝓕₂ : Filtration ℝ≥0 mΩ₂) (W₂ : ℝ≥0 → Ω₂ → ℝ)
    (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞)
    (h₂ : Ω₂ → DistOn upperHalfPlaneOpens)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ)
      P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) (s : ℚ) (hs : 0 < s) :
    let μ := glueMeasure P k X hXm
    let E := glueGood μ s ζ W
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (β : ℝ≥0 → (Ω × HistorySpace 1 1) × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration (imgFilt μ s ζ W E) 𝓦) β (μ.prod P₀) ∧
      (∀ p, Continuous fun t => β t p) ∧
      ∀ᵐ p ∂(μ.prod P₀), Sec7.Aux117.IsWordEntrance 4
        (fun i => imgVL s ζ W E i 0 p.1) (fun j => imgVR s ζ W E j 0 p.1)
        ![rL, -rL - δ] ![rR, -rR + δ] (fun t => imgW s ζ W E t p.1)
        (fun i t => imgVL s ζ W E i t p.1) (fun j t => imgVR s ζ W E j t p.1)
        (fun t => β t p) (imgT s ζ W E p.1 : ℝ≥0∞) := by
  let μ := glueMeasure P k X hXm
  let E := glueGood μ s ζ W
  have hEg : ∀ p ∈ E, IsGlueGood s ζ W p := isGlueGood_of_mem_glueGood
  have hEm : MeasurableSet E := measurableSet_glueGood
  have hWa : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hgood := ae_isGlueGood_of_marginals hL hR hbL hbR hC hC₂ hXm hlaw k hk hs
  have hσ : ∀ n, IsStoppingTime (imgFilt μ s ζ W E)
      (fun p => (imgAnn s ζ W E n p : WithTop ℝ≥0)) := by
    intro n r
    have he : {p : Ω × HistorySpace 1 1 | (imgAnn s ζ W E n p : WithTop ℝ≥0) ≤ r} =
        {p | imgAnn s ζ W E n p ≤ r} := by
      ext p
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    rw [he]
    exact measurableSet_imgFilt_of_gen ⟨r, le_rfl, Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))⟩
      (measurableSet_le (measurable_imgAnn hs hWa hEm hEg n) measurable_const)
  exact (isKilledWord_img hs hEg).exists_isWordEntrance (by norm_num : (0 : ℝ) < 4)
    (fun A hA h0 => Ito.measurableSet_usualAugmentation_of_null hA h0 0)
    (stronglyAdapted_imgFilt_of (measurable_imgW hs hWa hEm hEg) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inl rfl⟩⟩)
    (fun i => stronglyAdapted_imgFilt_of (measurable_imgVL hs hWa hEm hEg i) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩)
    (fun j => stronglyAdapted_imgFilt_of (measurable_imgVR hs hWa hEm hEg j) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inr (Or.inr ⟨j, rfl⟩)⟩⟩)
    hσ (monotone_imgAnn hs hEg) (fun n p => imgAnn_lt_imgT hs hEg n p)
    (by
      filter_upwards [ae_mem_glueGood hgood] with p hp
      exact fun t ht => exists_le_imgAnn hs hEg hp ht)
    (hI rL rR δ hL hR hbR hbL P 𝓕 W VL VR B ζ h hC X hXm hX
      P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs)

end InteractingSLE.WangWu.SeedTail
