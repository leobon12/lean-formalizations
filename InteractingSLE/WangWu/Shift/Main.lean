/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Shift.Img

/-!
# The height-shifted two-slit law, part 7: `ImageWordFiltShiftStatement` (Wang–Wu Proposition 4.19, κ = 4)

Packet PROVE-WW-B26 (PROVE-WW-B19's `ImgChartConst`/`ImgChartConstMarks` and PROVE-WW-B18's step B4 with the height
shift). In the setting of `ImageWordFiltShiftStatement` (forward coupling of `(r_L; r_R)` with the field `h`, glued
field `X = h − δλ`, reverse coupling of `(r_R − δ; r_L + δ)`, glued space `P ⊗ k(X)`):

* `ae_condExp_imgRaw_eq_imgFW_shift`: at a fixed image time `r`, almost surely on the validity event,
  `E[e^{i(h,φ)} | imgRaw r] = imgFW ![r_L, −r_L − δ] ![r_R, −r_R + δ] (r)` (Astra's E.4: B19's optional passage along
  strict upper dyadic forward times from the shifted two-slit law at rational forward times);
* **`isChartCouplingCharFunConst_img_shift`**: the chart coupling clause of the explicit image word with the weights
  `(![r_L, −r_L − δ], ![r_R, −r_R + δ])` at fixed image times of the raw filtration (B18's `ImgChartConstStatement`,
  shifted; B19's `ImgMarksStatement` is weight-free and reused through `exists_marks_ae_eq_inter`/`_avoid`);
* **`imageWordFiltShiftStatement`**: `ImageWordFiltShiftStatement` (B18's step B4: usual augmentation, chart transport,
  integrability with a random initial word, local martingales of the coupling means).

Nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or B16's
`ae_exists_continuation` (rulings R43, R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open ImgWord LawUnique WholeField LocalSets Coupling ChartConst
open ImgDrv MartChar Sec7.PhaseSelFull

section Main

variable {rL rR δ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- **The clause at a fixed image time from the stopped-history measurability** (Astra's E.4 with the passage of the
characteristic functions along strict upper dyadic forward times): almost surely on the validity event at the image
time `r`, `E[e^{i(h,φ)} | imgRaw r] = imgF(r)`. -/
theorem ae_condExp_imgRaw_eq_imgFW_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ) (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) {s : ℚ} (hs : 0 < s)
    (hM1 : ∀ (r : ℝ≥0) (t' t : ℚ), 0 ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 1 1),
      MeasurableSet[imgRaw s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) r] A →
      ∃ B', MeasurableSet[twoSlitMarks W VL VR ζ t s] B' ∧ B' =ᵐ[glueMeasure P k X hXm]
        A ∩ {p | (t' : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p ∧
          (r : ℝ) < capClock (gCurve s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p) t'})
    (hM3 : ∀ (t : ℚ), 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
      ∃ B', MeasurableSet[twoSlitMarks W VL VR ζ t s] B' ∧ B' =ᵐ[glueMeasure P k X hXm]
        {p | (t : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p ∧
          Sec7.Lemma71D.IsChartAvoid (fun r => imgW s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) r p)
            (imgT s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p : ℝ≥0∞) (imgChart s p.2) φ
            (capClock (gCurve s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p) t).toNNReal})
    (r : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k X hXm),
      p ∈ {p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) t p)
        (imgT s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p : ℝ≥0∞) (imgChart s p.2) φ r} →
      (glueMeasure P k X hXm)[fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
          imgRaw s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) r] p =
        imgFW ![rL, -rL - δ] ![rR, -rR + δ] s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) φ r p := by
  set μ := glueMeasure P k X hXm with hμ
  set E := glueGood μ s ζ W with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood
  have hEg : ∀ p ∈ E, IsGlueGood s ζ W p := fun p hp => isGlueGood_of_mem_glueGood p hp
  have hW : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  obtain ⟨hXk, -⟩ := hC.2.2.2
  have hEae : ∀ᵐ p ∂μ, p ∈ E := ae_mem_glueGood (ae_isGlueGood_shift hL hR hL₁ hR₁ hC hXm hC₂ hlaw k hk hs)
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData 4 (fun _ : Fin 1 => rL)
    (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR
  have hEm : Measurable fun p : Ω × HistorySpace 1 1 => Complex.exp (Complex.I * (h p.1 φ : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (((LQGMetric.measurable_distOn_apply φ).comp hC.2.1).comp measurable_fst)))
  have hXb : ∀ p : Ω × HistorySpace 1 1, ‖Complex.exp (Complex.I * (h p.1 φ : ℂ))‖ ≤ 1 := fun p => by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hXi : Integrable (fun p : Ω × HistorySpace 1 1 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) μ :=
    Integrable.of_bound hEm.aestronglyMeasurable 1 (Eventually.of_forall hXb)
  obtain ⟨hErm, hmeanm, hvarm⟩ := measurable_imgChartAvoid_rawW ![rL, -rL - δ] ![rR, -rR + δ] hs hW hE hEg r φ
  set Er := {p : Ω × HistorySpace 1 1 | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
    (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ r} with hErdef
  -- the candidate is `imgRaw r`-measurable on `Er`
  have hGm : Measurable[imgRaw s ζ W E r] (Er.indicator (imgFW ![rL, -rL - δ] ![rR, -rR + δ] s ζ W E φ r)) := by
    have e : Er.indicator (imgFW ![rL, -rL - δ] ![rR, -rR + δ] s ζ W E φ r) =
        Er.indicator (fun p => Complex.exp (Complex.I *
        ((Er.indicator (fun p => Sec7.Lemma71D.chartMean 4 ![rL, -rL - δ] ![rR, -rR + δ] (fun t => imgW s ζ W E t p)
          (fun i t => imgVL s ζ W E i t p) (fun j t => imgVR s ζ W E j t p) (imgChart s p.2) 0 0 φ r) p : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * Er.indicator (fun p => Sec7.Lemma71D.chartVar (fun t => imgW s ζ W E t p)
          (imgChart s p.2) φ r) p : ℝ) : ℂ))) := by
      refine Set.indicator_congr fun p hp => ?_
      simp only [imgFW, indicator_of_mem hp]
    rw [e]
    refine Measurable.indicator ?_ hErm
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hmeanm).const_mul _ |>.sub
      (Complex.measurable_ofReal.comp (hvarm.const_mul _)))
  have hGi : Integrable (Er.indicator (imgFW ![rL, -rL - δ] ![rR, -rR + δ] s ζ W E φ r)) μ := by
    refine Integrable.of_bound ((hGm.mono ((imgRaw s ζ W E).le r) le_rfl).aestronglyMeasurable) 1
      (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ Er
    · rw [indicator_of_mem hp]
      exact norm_imgFW_le_one ![rL, -rL - δ] ![rR, -rR + δ] hs hEg φ hp.1
    · rw [indicator_of_notMem hp, norm_zero]
      exact zero_le_one
  refine ae_condExp_eq_of_forall_setIntegral ((imgRaw s ζ W E).le r) hErm hXi hGm.stronglyMeasurable hGi ?_
  intro A hA
  have hUm : ∀ t : ℚ, Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2 := fun t =>
    measurable_union_hitting (((measurable_histHull t).comp (measurable_killedHistory hXk)).comp measurable_fst)
      ((measurable_image_negInv.comp (measurable_histHull s)).comp measurable_snd)
  refine setIntegral_eq_of_dyadic hXi (Eventually.of_forall hXb)
    (fun n k => germSigma (fun p : Ω × HistorySpace 1 1 =>
      histHull (dyqQ n k) (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
        (fun p => centredField h u₀ p.1) ⊔ twoSlitMarks W VL VR ζ (dyqQ n k) s)
    (fun n k => sup_le (germSigma_le (hUm _) ((measurable_centredField hC.2.1 u₀).comp measurable_fst))
      (twoSlitMarks_le _ _ hXk))
    (Av := imgAv s ζ W E φ)
    (F := fun q p => imgFW ![rL, -rL - δ] ![rR, -rR + δ] s ζ W E φ (capClock (gCurve s ζ W E p) q).toNNReal p)
    (fun q p hp => norm_imgFW_le_one ![rL, -rL - δ] ![rR, -rR + δ] hs hEg φ hp.2.2.1) ?_
    (measurable_imgTheta hs hW hE hEg r)
    (((imgRaw s ζ W E).le r _ hA).inter ((imgRaw s ζ W E).le r _ hErm)) ?_ ?_
  · -- the clause at the rational forward times
    intro n j
    have h1 := ae_condExp_twoSlit_glue_eq_imgFW_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hu₀ (dyqQ_pos n j) hs φ
    filter_upwards [h1] with p hp hAv
    obtain ⟨hpE, hpP, hpA⟩ := hAv
    have hc := dyqQ_coe n j
    rw [← hc] at hpP hpA
    show _ = imgFW ![rL, -rL - δ] ![rR, -rR + δ] s ζ W E φ
      (capClock (gCurve s ζ W E p) ((dyq n j : ℝ≥0) : ℝ)).toNNReal p
    rw [← hc]
    exact hp hpE hpP hpA
  · -- the pieces are in the marks
    intro n j
    have ht0 := dyqQ_pos n j
    have hk0 : (0 : ℚ) ≤ (j : ℚ) / 2 ^ n := by positivity
    have hkt : (j : ℚ) / 2 ^ n ≤ dyqQ n j := by
      rw [dyqQ]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    obtain ⟨B1, hB1m, hB1e⟩ := hM1 r (dyqQ n j) (dyqQ n j) ht0.le le_rfl ht0 (A ∩ Er) (hA.inter hErm)
    obtain ⟨B2, hB2m, hB2e⟩ := hM1 r ((j : ℚ) / 2 ^ n) (dyqQ n j) hk0 hkt ht0 univ MeasurableSet.univ
    obtain ⟨B3, hB3m, hB3e⟩ := hM3 (dyqQ n j) ht0 φ
    refine ⟨B1 ∩ B2ᶜ ∩ B3, le_sup_right (a := germSigma (fun p : Ω × HistorySpace 1 1 =>
      histHull (dyqQ n j) (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
        (fun p => centredField h u₀ p.1)) _ ((hB1m.inter hB2m.compl).inter hB3m), ?_⟩
    refine ((hB1e.inter hB2e.compl).inter hB3e).trans ?_
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hEae] with p hpE
    simp only [mem_inter_iff, mem_compl_iff, mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨⟨hAp, hEr⟩, h1⟩, h2⟩, h3⟩
      have hh := (dyIdx_imgTheta_and_mem_imgAv_iff hs hEg hpE hEr.1 n j φ).2 ⟨h1, h2, h3⟩
      exact ⟨⟨⟨hAp, hEr⟩, hh.1⟩, hh.2⟩
    · rintro ⟨⟨⟨hAp, hEr⟩, hd⟩, hav⟩
      obtain ⟨h1, h2, h3⟩ := (dyIdx_imgTheta_and_mem_imgAv_iff hs hEg hpE hEr.1 n j φ).1 ⟨hd, hav⟩
      exact ⟨⟨⟨⟨hAp, hEr⟩, h1⟩, h2⟩, h3⟩
  · -- the right limit
    filter_upwards [hEae] with p hpE hpD
    exact tendsto_imgFW_dyF ![rL, -rL - δ] ![rR, -rR + δ] hs hEg hpE hpD.2

/-- **The chart coupling clause of the shifted image word at fixed image times** (B18's `ImgChartConstStatement`
with the height shift): on `P ⊗ k(X)`, for each rational `s > 0`, the explicit image word with the weights
`(![r_L, −r_L − δ], ![r_R, −r_R + δ])` satisfies `Lemma71D.IsChartCouplingCharFunConst` for the field `h ∘ fst`, the
raw image filtration `imgRaw` and the chart `imgChart`. -/
theorem isChartCouplingCharFunConst_img_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ) (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) {s : ℚ} (hs : 0 < s) :
    Sec7.Lemma71D.IsChartCouplingCharFunConst 4 ![rL, -rL - δ] ![rR, -rR + δ] (glueMeasure P k X hXm)
      (imgRaw s ζ W (glueGood (glueMeasure P k X hXm) s ζ W))
      (imgW s ζ W (glueGood (glueMeasure P k X hXm) s ζ W))
      (imgVL s ζ W (glueGood (glueMeasure P k X hXm) s ζ W))
      (imgVR s ζ W (glueGood (glueMeasure P k X hXm) s ζ W))
      (fun p => (imgT s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p : ℝ≥0∞))
      (fun p => imgChart s p.2) 0 0 (fun p => h p.1) := by
  have hEg : ∀ p ∈ glueGood (glueMeasure P k X hXm) s ζ W, IsGlueGood s ζ W p := fun p hp =>
    isGlueGood_of_mem_glueGood p hp
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    (IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1).mono
      fun ω hω => hω.1
  have hgood : ∀ᵐ p ∂(glueMeasure P k X hXm), p ∈ glueGood (glueMeasure P k X hXm) s ζ W ∧
      Aux50Hit.IsGoodPath W VL VR ζ p.1 := by
    filter_upwards [ae_mem_glueGood (ae_isGlueGood_shift hL hR hL₁ hR₁ hC hXm hC₂ hlaw k hk hs),
      ae_glue_fst (μ := P) k hXm (Aux50Hit.ae_isGoodPath hC.1 hζ)] with p h1 h2
    exact ⟨h1, h2⟩
  have hM1 : ∀ (r : ℝ≥0) (t' t : ℚ), 0 ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 1 1),
      MeasurableSet[imgRaw s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) r] A →
      ∃ B', MeasurableSet[twoSlitMarks W VL VR ζ t s] B' ∧ B' =ᵐ[glueMeasure P k X hXm]
        A ∩ {p | (t' : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p ∧
          (r : ℝ) < capClock (gCurve s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p) t'} :=
    fun r t' t ht'0 ht't ht A hA => exists_marks_ae_eq_inter hs ht hEg hgood r (by exact_mod_cast ht'0) ht't hA
  have hM3 : ∀ (t : ℚ), 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
      ∃ B', MeasurableSet[twoSlitMarks W VL VR ζ t s] B' ∧ B' =ᵐ[glueMeasure P k X hXm]
        {p | (t : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p ∧
          Sec7.Lemma71D.IsChartAvoid (fun r => imgW s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) r p)
            (imgT s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p : ℝ≥0∞) (imgChart s p.2) φ
            (capClock (gCurve s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p) t).toNNReal} :=
    fun t ht φ => exists_marks_ae_eq_avoid hs ht hEg hgood φ
  have hkw := isKilledWord_img (ζ := ζ) (W := W) hs hEg
  intro r u hu φ
  filter_upwards [ae_condExp_imgRaw_eq_imgFW_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hs hM1 hM3 r φ]
    with p hp hr hsupp
  have hav : Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) t p)
      (imgT s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p : ℝ≥0∞) (imgChart s p.2) φ r := ⟨hr, hsupp⟩
  rw [hp hav, imgFW]
  have hint := Sec7.Lemma71D.integral_couplingMean_eq_chartMean (κ := 4) (ρL := ![rL, -rL - δ])
    (ρR := ![rR, -rR + δ]) (a := 0) (k := 0) (isConformal_imgChart hs p.2) (hkw.contW p) hav
    (fun i => hkw.ordL p r i hr) (fun j => hkw.ordR p r j hr) (hu p)
  congr 3
  exact congrArg Complex.ofReal hint.symm

end Main

/-- **The height-shifted two-slit law holds** (Wang–Wu, proof of Proposition 4.19, κ = 4; "Lemma 4.15 in this
form"): the explicit coupling means of the killed image word with the weights `(![r_L, −r_L − δ], ![r_R, −r_R + δ])`
are local martingales before `min (swallowTime z) imgT` in the filtration of the image word, under the glued measure
`P ⊗ k(X)`. -/
theorem imageWordFiltShiftStatement : ImageWordFiltShiftStatement.{u} := by
  intro rL rR δ hL hR hL₁ hR₁ Ω mΩ P _ 𝓕 W VL VR B ζ h hC X hXm hX Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk
    s hs z hz
  set μ := glueMeasure P k X hXm with hμ
  set E := glueGood μ s ζ W with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood
  have hEg : ∀ p ∈ E, IsGlueGood s ζ W p := isGlueGood_of_mem_glueGood
  have hWad : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hK := isKilledWord_img hs hEg (ζ := ζ) (W := W)
  set 𝓖 := imgFilt μ s ζ W E with h𝓖
  have : 𝓖.IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  set ζ' : Ω × HistorySpace 1 1 → ℝ≥0∞ := fun p => (imgT s ζ W E p : ℝ≥0∞) with hζ'
  set hF : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens := fun p => h p.1 with hFdef
  have hFm : Measurable hF := hC.2.1.comp measurable_fst
  have hcc : ∀ p : Ω × HistorySpace 1 1, (imgChart s p.2).IsConformal := fun p => isConformal_imgChart hs p.2
  -- the chart clause at every stopping time of `imgFilt`
  have hcf0 := isChartCouplingCharFunConst_img_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hs
  have hcfU : Coupling.MartMeans2.IsChartCouplingCharFun 4 ![rL, -rL - δ] ![rR, -rR + δ] μ 𝓖 (imgW s ζ W E)
      (imgVL s ζ W E) (imgVR s ζ W E) ζ' (fun p => imgChart s p.2) 0 0 hF :=
    Sec7.Lemma71D.isChartCouplingCharFun_usualAugmentation hFm hcc
      (fun p => continuousOn_lift_imgChart p.2) (fun p => hK.contW p) (fun i p => (hK.pathL p i).1)
      (fun j p => (hK.pathR p j).1) (fun p t ht => ⟨fun i => hK.ordL p t i ht, fun j => hK.ordR p t j ht⟩) hcf0
  -- the transported field
  set h' : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens :=
    fun p => Sec7.Lemma71K.chartField (imgChart s p.2) 0 0 (hF p) with hh'
  have ht : ∀ p, IsChartTransport (imgChart s p.2) 1 0 0 (hF p) (h' p) := fun p =>
    Sec7.Lemma71K.isChartTransport_chartField (hcc p) (continuousOn_lift_imgChart p.2) 0 0 (hF p)
  have hdom : ∀ z, MeasurableSet[𝓖 0] {p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom} := fun z =>
    measurableSet_mem_dom_imgChart hs z
  have hfwd : ∀ z, Measurable[𝓖 0]
      ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).1 z) := fun z =>
    measurable_indicator_fwd_imgChart hs z
  have hliftm : ∀ z, Measurable[𝓖 0]
      ({p : Ω × HistorySpace 1 1 | z ∈ (imgChart s p.2).dom}.indicator fun p => (imgChart s p.2).2.2 z) := fun z =>
    measurable_indicator_lift_imgChart z
  have hcf' : Coupling.MartMeans.IsCouplingCharFun 4 ![rL, -rL - δ] ![rR, -rR + δ] μ 𝓖 (imgW s ζ W E) (imgVL s ζ W E)
      (imgVR s ζ W E) ζ' h' :=
    Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hcc hdom hfwd hliftm
      (fun p => continuousOn_lift_imgChart p.2) hFm (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p⟩)
      hcfU ht
  -- measurability of the transported field
  have hh'm : Measurable h' := by
    have hm := Chart.measurable_chartTransport_random' hcc (fun z => 𝓖.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl)
      (fun p => continuousOn_lift_imgChart p.2) hFm 1 0 0
    have e : h' = fun p => Chart.chartTransport (hcc p) 1 0 0 (hF p) := by
      funext p
      simp only [hh', Sec7.Lemma71K.chartField, hcc p, ↓reduceDIte]
    rw [e]
    exact hm
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun p => h' p φ) μ := fun φ =>
    integrable_apply_of_isCouplingCharFun_of_bounded hcf'
      (Eventually.of_forall fun p => ⟨(isKilledArc_gCurve hs hEg (ζ := ζ) (W := W) p).zero_lt_kLife, hK.contW p,
        hK.w_zero p⟩)
      φ ((LQGMetric.measurable_distOn_apply φ).comp hh'm)
  -- the filtration clauses
  have hnull : ∀ A, MeasurableSet A → μ A = 0 → MeasurableSet[𝓖 0] A := fun A hA h0 =>
    Ito.measurableSet_usualAugmentation_of_null hA h0 0
  have hζm : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {p | ζ' p ≤ t} := by
    intro t
    have h1 := (measurableSet_imgFilt_of_gen (μ := μ) ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩
      (measurableSet_lt_imgT hs hWad hE hEg t)).compl
    convert h1 using 1
    ext p
    simp only [hζ', mem_ofPred_eq, mem_compl_iff, not_lt]
    rfl
  have hWa : StronglyAdapted 𝓖 (imgW s ζ W E) :=
    stronglyAdapted_imgFilt_of (measurable_imgW hs hWad hE hEg) fun r B hB => ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inl rfl⟩⟩
  have hVLa : ∀ i, StronglyAdapted 𝓖 (imgVL s ζ W E i) := fun i =>
    stronglyAdapted_imgFilt_of (measurable_imgVL hs hWad hE hEg i) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩
  have hVRa : ∀ j, StronglyAdapted 𝓖 (imgVR s ζ W E j) := fun j =>
    stronglyAdapted_imgFilt_of (measurable_imgVR hs hWad hE hEg j) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inr (Or.inr ⟨j, rfl⟩)⟩⟩
  have hσ : ∀ n, IsStoppingTime 𝓖 fun p => (imgAnn s ζ W E n p : WithTop ℝ≥0) := by
    intro n r
    have e : {p : Ω × HistorySpace 1 1 | ((imgAnn s ζ W E n p : ℝ≥0) : WithTop ℝ≥0) ≤ r} =
        {p | imgAnn s ζ W E n p ≤ r} := by
      ext p
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    rw [e]
    exact measurableSet_imgFilt_of_gen ⟨r, le_rfl, Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))⟩
      (measurableSet_le (measurable_imgAnn hs hWad hE hEg n) measurable_const)
  have hT : Coupling.IsAnnouncingSeq 𝓖 μ ζ' (imgAnn s ζ W E) := by
    refine ⟨hσ, monotone_imgAnn hs hEg, fun n => Eventually.of_forall fun p => imgAnn_lt_imgT hs hEg n p, ?_⟩
    filter_upwards [ae_mem_glueGood (ae_isGlueGood_shift hL hR hL₁ hR₁ hC hXm hC₂ hlaw k hk hs)] with p hp
    exact fun u hu => exists_le_imgAnn hs hEg hp hu
  obtain ⟨G, hG, hGae, hloc⟩ := Coupling.MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull
    (MartChar.adaptedBefore_of_stronglyAdapted hζm hWa)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVLa i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVRa j))
    (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p, ⟨fun i => (hK.pathL p i).1, fun j => (hK.pathR p j).1⟩,
      fun t ht => ⟨fun i => hK.ordL p t i ht, fun j => hK.ordR p t j ht⟩⟩)
    hT hint hcf' (fun p t => meanExt 4 ![rL, -rL - δ] ![rR, -rR + δ] (imgW s ζ W E t p) (fun i => imgVL s ζ W E i t p)
      (fun j => imgVR s ζ W E j t p))
    (fun p t => isBoundedHarmonicExtension_meanExt 4 ![rL, -rL - δ] ![rR, -rR + δ] _ _ _) hz
  exact Restart.ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG hGae
    (Restart.ConverseBefore.measurable_coupProc_zero hK.w_zero (fun i => measurable_imgVL hs hWad hE hEg i 0)
      (fun j => measurable_imgVR hs hWad hE hEg j 0) hz) hloc

/-- **Consistency check: at `δ = 0` the shifted statement is B17's `ImageWordFiltStatement`** (glued field `X = h`,
weights `(![r_L, −r_L], ![r_R, −r_R])`). -/
theorem imageWordFiltStatement_of_shift (hS : ImageWordFiltShiftStatement.{u}) : ImageWordFiltStatement.{u} := by
  intro rL rR hL hR Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk s hs z hz
  have e₂ : (fun _ : Fin 1 => rR - 0) = (fun _ : Fin 1 => rR) ∧ (fun _ : Fin 1 => rL + 0) = (fun _ : Fin 1 => rL) :=
    ⟨funext fun _ => sub_zero rR, funext fun _ => add_zero rL⟩
  have hC₂' : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - 0) (fun _ => rL + 0) P₂ 𝓕₂ W₂ VL₂
      VR₂ B₂ ζ₂ h₂ := by
    rw [e₂.1, e₂.2]; exact hC₂
  have hX : ∀ ω, h ω = Exist.flowField 0 (0 * wwLambda) (h ω) := fun ω => by
    rw [zero_mul, Sec5.GlueCond.flowField_zero_zero]
  have H0 := hS rL rR 0 hL hR (by rwa [add_zero]) (by rwa [sub_zero]) P 𝓕 W VL VR B ζ h hC h hC.2.1 hX P₂ 𝓕₂ W₂
    VL₂ VR₂ B₂ ζ₂ h₂ hC₂' hlaw k hk s hs z hz
  have e₁ : (![rL, -rL - 0] : Fin 2 → ℝ) = imgρ rL ∧ (![rR, -rR + 0] : Fin 2 → ℝ) = imgρ rR := by
    rw [sub_zero, add_zero]
    exact ⟨rfl, rfl⟩
  rw [e₁.1, e₁.2] at H0
  exact H0

end InteractingSLE.WangWu
