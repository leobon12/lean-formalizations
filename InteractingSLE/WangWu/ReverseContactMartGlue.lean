/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartWord

/-!
# The image word of the contact step, part 2: the killed image word on the glued space

Packet PROVE-WW-B17. On the glued space `Ω × HistorySpace 1 1` of the contact step (PROVE-WW-B11–B16), at a rational
reverse time `s > 0`, the image of the forward line `α = seedLine ζ W p.1` in the chart `Ψ = revChart W_β s` of
`ℍ \ G`, `G = R(β((0, s]))`, is a killed arc on the pre-contact times (PROVE-WW-B15's `isKilledArc_imgCurve`) on the
good glued samples. This file defines, for every glued sample, the killed `SLE₄(r_L, −r_L; r_R, −r_R)` word of
`ImageMartStatement` (on a set `E` of good samples; a vertical ray with fixed marks elsewhere, so that every clause
holds at every sample):

* `gCurve`, `gPre`, `gXL`, `gXR`: the image curve, its pre-contact times, and the marks `(0, −1/v_R)`, `(0, −1/v_L)`
  (the images of `0∓` and of `Ψ(∞∓)`);
* `imgW`, `imgVL`, `imgVR`, `imgT`, `imgTr`: the killed glued driver, the images of the marks, the terminal capacity
  and the image trace in capacity time;
* **`isKilledWord_img`**: the word satisfies `ImgDrv.IsKilledWord` (every sample);
* **`isGeneratingTraceIcc_imgTr`**, `imgTr_inj`, `imgTr_mem_H`: the image trace is a simple trace in `ℍ` generating
  the killed chain before the terminal capacity (every sample);
* **`imgW_eq_chainDrv`**: on good samples, every pre-contact prefix has capacity below the terminal capacity and the
  killed driver is PROVE-WW-B15's glued driver `chainDrv` on its capacity range;
* `glueGood`, `measurableSet_glueGood`, `ae_mem_glueGood`: a measurable full-measure set of good glued samples.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open ImgWord LawUnique

/-! ### The vertical ray -/

namespace ImgWord

/-- The vertical ray `u ↦ u i`. -/
def vRay (u : ℝ) : ℂ := (u : ℂ) * I

end ImgWord

theorem isKilledArc_vRay : IsKilledArc vRay (Ici 0) where
  zero_mem := self_mem_Ici
  nonneg _ hu := hu
  icc _ _ := Icc_subset_Ici_self
  exists_gt S hS := ⟨S + 1, by simp only [mem_Ici] at hS ⊢; linarith, by linarith⟩
  zero := by simp [vRay]
  cont := by unfold vRay; fun_prop
  inj u _ v _ e := by simpa [vRay] using e
  mem_H u _ hu := by show (0 : ℝ) < ((u : ℂ) * I).im; simpa using hu

/-! ### The image word on the glued space -/

namespace ImgWord

variable {Ω : Type*}

/-- **A good glued sample**: the forward line is a simple proper arc, and the reverse history is good (B14's
`BetaSet`, B13's `GoodHist`). -/
def IsGlueGood (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (p : Ω × HistorySpace 1 1) : Prop :=
  IsProperArc (seedLine ζ W p.1) ∧ p.2 ∈ BetaSet s ∧ p.2 ∈ GoodHist s

open scoped Classical in
/-- **The image curve** `Ψ ∘ α` on `E`, the vertical ray elsewhere. -/
def gCurve (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1))
    (p : Ω × HistorySpace 1 1) : ℝ → ℂ :=
  if p ∈ E then imgCurve (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1) else vRay

open scoped Classical in
/-- **The pre-contact times** of the forward line on `E`, `[0, ∞)` elsewhere. -/
def gPre (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1))
    (p : Ω × HistorySpace 1 1) : Set ℝ :=
  if p ∈ E then preContact (seedLine ζ W p.1) (negInv '' histHull s p.2) else Ici 0

open scoped Classical in
/-- The left marks: `0⁻` and `Ψ(∞⁻) = −1/v_R` (`−1` off `E`). -/
def gXL (s : ℚ) (E : Set (Ω × HistorySpace 1 1)) (p : Ω × HistorySpace 1 1) : Fin 2 → ℝ :=
  ![0, if p ∈ E then -1 / frzVR s p.2 else -1]

open scoped Classical in
/-- The right marks: `0⁺` and `Ψ(∞⁺) = −1/v_L` (`1` off `E`). -/
def gXR (s : ℚ) (E : Set (Ω × HistorySpace 1 1)) (p : Ω × HistorySpace 1 1) : Fin 2 → ℝ :=
  ![0, if p ∈ E then -1 / frzVL s p.2 else 1]

/-- **The killed image driver.** -/
def imgW (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) :
    ℝ≥0 → Ω × HistorySpace 1 1 → ℝ :=
  fun t p => kW (gCurve s ζ W E p) (gPre s ζ W E p) t

/-- **The images of the left marks.** -/
def imgVL (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) :
    Fin 2 → ℝ≥0 → Ω × HistorySpace 1 1 → ℝ :=
  fun i t p => kVL (gCurve s ζ W E p) (gPre s ζ W E p) (gXL s E p) i t

/-- **The images of the right marks.** -/
def imgVR (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) :
    Fin 2 → ℝ≥0 → Ω × HistorySpace 1 1 → ℝ :=
  fun j t p => kVR (gCurve s ζ W E p) (gPre s ζ W E p) (gXR s E p) j t

/-- **The terminal capacity of the image.** -/
def imgT (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) :
    Ω × HistorySpace 1 1 → WithTop ℝ≥0 :=
  fun p => kLife (gCurve s ζ W E p) (gPre s ζ W E p)

/-- **The image trace in capacity time.** -/
def imgTr (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1))
    (p : Ω × HistorySpace 1 1) : ℝ≥0 → ℂ :=
  kTrace (gCurve s ζ W E p) (gPre s ζ W E p)

end ImgWord

section Glue

variable {Ω : Type*} {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

theorem gCurve_of_mem {p : Ω × HistorySpace 1 1} (hp : p ∈ E) :
    gCurve s ζ W E p = imgCurve (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1) := by
  simp only [gCurve, hp, ↓reduceIte]

theorem gPre_of_mem {p : Ω × HistorySpace 1 1} (hp : p ∈ E) :
    gPre s ζ W E p = preContact (seedLine ζ W p.1) (negInv '' histHull s p.2) := by
  simp only [gPre, hp, ↓reduceIte]

/-- **On good samples the image is a killed arc** (PROVE-WW-B15's `isKilledArc_imgCurve`); elsewhere the vertical ray. -/
theorem isKilledArc_gCurve (hs : 0 < s) (hE : ∀ p ∈ E, IsGlueGood s ζ W p) (p : Ω × HistorySpace 1 1) :
    IsKilledArc (gCurve s ζ W E p) (gPre s ζ W E p) := by
  by_cases hp : p ∈ E
  · rw [gCurve_of_mem hp, gPre_of_mem hp]
    obtain ⟨hα, hβ, hg⟩ := hE p hp
    obtain ⟨hcont, h0, -, -, hhull, -, -⟩ := trace_of_mem_betaSet hs hβ
    have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
    have hG : IsClosed (negInv '' fwdHull (Ito.rpath (frzDrive s p.2)) s) := by
      rw [← hhull]; exact isClosed_image_negInv_histHull hs hg
    have hK := isKilledArc_imgCurve hcont h0 hs' hG hα
    rwa [← hhull] at hK
  · simp only [gCurve, gPre, hp, ↓reduceIte]
    exact isKilledArc_vRay

theorem gXL_nonpos (hs : 0 < s) (hE : ∀ p ∈ E, IsGlueGood s ζ W p) (p : Ω × HistorySpace 1 1) (i : Fin 2) :
    gXL s E p i ≤ 0 := by
  classical
  fin_cases i
  · simp [gXL]
  · by_cases hp : p ∈ E
    · have hv := (trace_of_mem_betaSet hs (hE p hp).2.1).2.2.2.2.2.2
      simp only [gXL, hp, ↓reduceIte, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [neg_div]
      exact neg_nonpos.2 (div_pos one_pos hv).le
    · simp [gXL, hp]

theorem gXR_nonneg (hs : 0 < s) (hE : ∀ p ∈ E, IsGlueGood s ζ W p) (p : Ω × HistorySpace 1 1) (j : Fin 2) :
    0 ≤ gXR s E p j := by
  classical
  fin_cases j
  · simp [gXR]
  · by_cases hp : p ∈ E
    · have hv := (trace_of_mem_betaSet hs (hE p hp).2.1).2.2.2.2.2.1
      simp only [gXR, hp, ↓reduceIte, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [neg_div, ← div_neg]
      exact (div_pos one_pos (neg_pos.2 hv)).le
    · simp [gXR, hp]

theorem antitone_gXL (hs : 0 < s) (hE : ∀ p ∈ E, IsGlueGood s ζ W p) (p : Ω × HistorySpace 1 1) :
    Antitone (gXL s E p) := by
  intro a b hab
  have h1 := gXL_nonpos hs hE p 1
  fin_cases a <;> fin_cases b
  · exact le_rfl
  · simpa [gXL] using h1
  · exact absurd hab (by decide)
  · exact le_rfl

theorem monotone_gXR (hs : 0 < s) (hE : ∀ p ∈ E, IsGlueGood s ζ W p) (p : Ω × HistorySpace 1 1) :
    Monotone (gXR s E p) := by
  intro a b hab
  have h1 := gXR_nonneg hs hE p 1
  fin_cases a <;> fin_cases b
  · exact le_rfl
  · simpa [gXR] using h1
  · exact absurd hab (by decide)
  · exact le_rfl

/-- **The image word is a killed word** at every glued sample. -/
theorem isKilledWord_img (hs : 0 < s) (hE : ∀ p ∈ E, IsGlueGood s ζ W p) :
    ImgDrv.IsKilledWord (imgW s ζ W E) (imgVL s ζ W E) (imgVR s ζ W E) (imgT s ζ W E) :=
  isKilledWord_kW (isKilledArc_gCurve hs hE) (gXL_nonpos hs hE) (gXR_nonneg hs hE) (antitone_gXL hs hE)
    (monotone_gXR hs hE)

/-- **The image trace** is a simple trace in `ℍ` generating the killed image chain before the terminal capacity. -/
theorem isGeneratingTraceIcc_imgTr (hs : 0 < s) (hE : ∀ p ∈ E, IsGlueGood s ζ W p) (p : Ω × HistorySpace 1 1)
    {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < imgT s ζ W E p) :
    Sec7.IsGeneratingTraceIcc (imgW s ζ W E · p) t (imgTr s ζ W E p) :=
  (isKilledArc_gCurve hs hE p).isGeneratingTraceIcc_kTrace ht

theorem imgTr_inj (hs : 0 < s) (hE : ∀ p ∈ E, IsGlueGood s ζ W p) (p : Ω × HistorySpace 1 1) {a b : ℝ≥0}
    (ha : (a : WithTop ℝ≥0) < imgT s ζ W E p) (hb : (b : WithTop ℝ≥0) < imgT s ζ W E p)
    (hab : imgTr s ζ W E p a = imgTr s ζ W E p b) : a = b :=
  (isKilledArc_gCurve hs hE p).kTrace_injOn ha hb hab

theorem imgTr_mem_H (hs : 0 < s) (hE : ∀ p ∈ E, IsGlueGood s ζ W p) (p : Ω × HistorySpace 1 1) {t : ℝ≥0}
    (ht0 : 0 < t) (ht : (t : WithTop ℝ≥0) < imgT s ζ W E p) : imgTr s ζ W E p t ∈ H :=
  (isKilledArc_gCurve hs hE p).kTrace_mem_H ht0 ht

/-- **Identification with the glued driver of PROVE-WW-B15** on good samples. -/
theorem imgW_eq_chainDrv (hs : 0 < s) (hE : ∀ p ∈ E, IsGlueGood s ζ W p) {p : Ω × HistorySpace 1 1} (hp : p ∈ E)
    {S : ℝ} (hS : S ∈ preContact (seedLine ζ W p.1) (negInv '' histHull s p.2)) :
    (((capClock (imgCurve (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1)) S).toNNReal : ℝ≥0) :
        WithTop ℝ≥0) < imgT s ζ W E p ∧
      ∀ r ∈ Icc 0 (capClock (imgCurve (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1)) S),
        imgW s ζ W E r.toNNReal p = chainDrv (imgCurve (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1))
          (preContact (seedLine ζ W p.1) (negInv '' histHull s p.2)) r := by
  have hK := isKilledArc_gCurve hs hE p
  rw [gCurve_of_mem hp, gPre_of_mem hp] at hK
  have := hK.kW_eq_chainDrv hS
  simp only [imgT, imgW, gCurve_of_mem hp, gPre_of_mem hp]
  exact this

end Glue

/-! ### A measurable full-measure set of good samples -/

namespace ImgWord

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A measurable set of good glued samples** of full `μ`-measure (when good samples have full measure). -/
def glueGood (μ : Measure (Ω × HistorySpace 1 1)) (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) :
    Set (Ω × HistorySpace 1 1) :=
  (toMeasurable μ {p | ¬ IsGlueGood s ζ W p})ᶜ

variable {μ : Measure (Ω × HistorySpace 1 1)} {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}

theorem measurableSet_glueGood : MeasurableSet (glueGood μ s ζ W) := (measurableSet_toMeasurable _ _).compl

theorem isGlueGood_of_mem_glueGood : ∀ p ∈ glueGood μ s ζ W, IsGlueGood s ζ W p := fun p hp => by
  by_contra h
  exact hp (subset_toMeasurable _ _ h)

theorem measure_compl_glueGood (hae : ∀ᵐ p ∂μ, IsGlueGood s ζ W p) : μ (glueGood μ s ζ W)ᶜ = 0 := by
  rw [glueGood, compl_compl, measure_toMeasurable]
  exact ae_iff.1 hae

theorem ae_mem_glueGood (hae : ∀ᵐ p ∂μ, IsGlueGood s ζ W p) : ∀ᵐ p ∂μ, p ∈ glueGood μ s ζ W := by
  rw [ae_iff]
  exact measure_compl_glueGood hae

end ImgWord

section Setting

open LQGMetric (DistOn)

universe u

variable {rL rR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- **Almost every glued sample is good** (PROVE-WW-B10/B13/B14: the forward line is a simple proper arc, the reverse
history lies in `BetaSet s` and in `GoodHist s`). -/
theorem ae_isGlueGood (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) {s : ℚ} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1), IsGlueGood s ζ W p := by
  have hh : Measurable h := hC.2.1
  have hRh₂ : Measurable fun ω => reflectField (h₂ ω) := measurable_reflectField.comp hC₂.2.1
  have hD₂ := measurable_killedHistory hC₂.2.2.2.1
  have hgood := ae_glue_fst (μ := P) k hh (ae_good_twoSeed hL hR hC.1)
  have hbeta : ∀ᵐ p ∂(glueMeasure P k h hh), p.2 ∈ BetaSet s :=
    ae_glue_snd hh hRh₂ hD₂ hlaw k hk (measurableSet_betaSet s) (ae_killedHistory_mem_betaSet hR hL hC₂.1 hs)
  have hgh := ae_goodHist_snd_glue hL hR hC hC₂ hlaw k hk s
  filter_upwards [hgood, hbeta, hgh] with p hpα hpβ hpg
  exact ⟨hpα.1, hpβ, hpg⟩

end Setting

end InteractingSLE.WangWu
