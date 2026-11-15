/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartAnn
import InteractingSLE.WangWu.ReverseContactMartReduce
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# The image word of the contact step, part 8: the filtration of the image word; the contact step from Lemma 2.11's
martingale hypothesis alone

Packet PROVE-WW-B17, steps B1–B2 of PROVE-WW-B15's plan completed. The **filtration of the image word** `imgFilt` is
the usual augmentation (null sets at time `0`, right-continuous) of the raw filtration generated, up to each time `r`,
by the killed image driver, the images of the four marks, the killing events `{r' < imgT}`, the announcing events
`{σₙ ≤ r'}` (`imgAnn`, the capacity of the first approach within `1/(n+1)` of `G`) and, at time `0`, the reverse
history stopped at `s` (which carries the chart `Ψ`). The word is adapted to it
(`measurable_imgW`, `measurable_imgVL`, `measurable_imgVR`), the `σₙ` are stopping times announcing `imgT`, and
`{q < imgT} ∈ 𝓖_q`. What remains of steps B1–B4 is exactly Lemma 2.11's martingale hypothesis for the explicit word in
this filtration, the named input `ImageWordFiltStatement` (the field side: steps B3–B4):

* **`imageWordMartStatement_of_imageWordFilt`**: `ImageWordFiltStatement → ImageWordMartStatement`;
* **`reverseTipContactStatement_of_imageWordFilt`**: with PROVE-WW-B15/B16's reductions,
  `ImageWordFiltStatement → ReverseTipContactStatement`.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open LQGMetric (DistOn TestOn)
open LawUnique ImgWord
open ImgDrv MartChar Sec7.PhaseSelFull

namespace ImgWord

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The generating events of the raw filtration of the image word at time `r`: the word, the killing and announcing
events up to `r`, and (at time `0`) the reverse history stopped at `s`, which carries the chart `Ψ` of `ℍ \ G`. -/
def imgGen (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) (r : ℝ≥0) :
    Set (Set (Ω × HistorySpace 1 1)) :=
  {A | ∃ r' : ℝ≥0, r' ≤ r ∧ ((∃ B : Set ℝ, MeasurableSet B ∧ (A = imgW s ζ W E r' ⁻¹' B ∨
    (∃ i, A = imgVL s ζ W E i r' ⁻¹' B) ∨ ∃ j, A = imgVR s ζ W E j r' ⁻¹' B)) ∨
    A = {p | (r' : WithTop ℝ≥0) < imgT s ζ W E p} ∨ (∃ n, A = {p | imgAnn s ζ W E n p ≤ r'}) ∨
    ∃ B : Set (HistorySpace 1 1), MeasurableSet B ∧ A = (fun p => revStop s p.2) ⁻¹' B)}

/-- **The raw filtration of the image word** (intersected with the ambient σ-algebra, so that no measurability
hypothesis enters the definition). -/
def imgRaw (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 1 1)) where
  seq r := MeasurableSpace.generateFrom (imgGen s ζ W E r) ⊓ inferInstance
  mono' r r' hrr' := by
    refine inf_le_inf_right _ (MeasurableSpace.generateFrom_mono ?_)
    rintro A ⟨r'', hr'', h⟩
    exact ⟨r'', hr''.trans hrr', h⟩
  le' _ := inf_le_right

/-- **The filtration of the image word**: the usual augmentation of `imgRaw` under `μ`. -/
def imgFilt (μ : Measure (Ω × HistorySpace 1 1)) (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (E : Set (Ω × HistorySpace 1 1)) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 1 1)) :=
  usualAugmentation (imgRaw s ζ W E) μ

end ImgWord

section Filt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℚ} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)} {μ : Measure (Ω × HistorySpace 1 1)}

theorem measurableSet_imgRaw_of_gen {r : ℝ≥0} {A : Set (Ω × HistorySpace 1 1)} (hA : A ∈ imgGen s ζ W E r)
    (hAm : MeasurableSet A) : MeasurableSet[imgRaw s ζ W E r] A :=
  ⟨MeasurableSpace.measurableSet_generateFrom hA, hAm⟩

theorem measurableSet_imgFilt_of_gen {r : ℝ≥0} {A : Set (Ω × HistorySpace 1 1)} (hA : A ∈ imgGen s ζ W E r)
    (hAm : MeasurableSet A) : MeasurableSet[imgFilt μ s ζ W E r] A :=
  Ito.le_usualAugmentation (imgRaw s ζ W E) μ r _ (measurableSet_imgRaw_of_gen hA hAm)

/-- A process whose preimages at time `r` are generators is adapted to the filtration of the image word. -/
theorem stronglyAdapted_imgFilt_of {X : ℝ≥0 → Ω × HistorySpace 1 1 → ℝ} (hX : ∀ r, Measurable (X r))
    (hgen : ∀ r (B : Set ℝ), MeasurableSet B → X r ⁻¹' B ∈ imgGen s ζ W E r) :
    StronglyAdapted (imgFilt μ s ζ W E) X := fun r => by
  have hm : Measurable[imgFilt μ s ζ W E r] (X r) := fun B hB =>
    measurableSet_imgFilt_of_gen (hgen r B hB) (hX r hB)
  exact hm.stronglyMeasurable

/-- The reverse history stopped at `s` is known at time `0`. -/
theorem measurable_revStop_imgFilt (r : ℝ≥0) :
    Measurable[imgFilt μ s ζ W E r] fun p : Ω × HistorySpace 1 1 => revStop s p.2 := fun B hB =>
  measurableSet_imgFilt_of_gen ⟨0, zero_le, Or.inr (Or.inr (Or.inr ⟨B, hB, rfl⟩))⟩
    ((measurable_revStop s).comp measurable_snd hB)

/-- The good set is known at time `0` (its complement is a null set). -/
theorem measurableSet_imgFilt_glueGood (hae : ∀ᵐ p ∂μ, IsGlueGood s ζ W p) (r : ℝ≥0) :
    MeasurableSet[imgFilt μ s ζ W (glueGood μ s ζ W) r] (glueGood μ s ζ W) := by
  have hN := Ito.measurableSet_usualAugmentation_of_null (𝓕 := imgRaw s ζ W (glueGood μ s ζ W)) (P := μ)
    (measurableSet_toMeasurable μ {p | ¬ IsGlueGood s ζ W p})
    (by rw [measure_toMeasurable]; exact ae_iff.1 hae) r
  exact hN.compl

end Filt

/-- **Named input: Lemma 2.11's martingale hypothesis for the explicit image word in its filtration** (steps B3–B4 of
PROVE-WW-B15's plan, the field side). In the setting of `ReverseTipContactStatement`, for each rational `s > 0` and
every `z ∈ ℍ`, the explicit coupling mean of the killed image word `(imgW, imgVL, imgVR)` (weights `(r_L, −r_L; r_R,
−r_R)`) is a local martingale before `min (swallowTime z) imgT` in the filtration of the image word `imgFilt`, under
the glued measure (Wang–Wu, proof of Proposition 4.18: "Its conditional harmonic means and conformal-radius brackets,
just identified, satisfy Lemma 2.11"). -/
def ImageWordFiltStatement : Prop :=
  ∀ (rL rR : ℝ), 0 ≤ rL → 0 ≤ rR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (𝓕₂ : Filtration ℝ≥0 mΩ₂) (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ)
      (ζ₂ : Ω₂ → ℝ≥0∞) (h₂ : Ω₂ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ →
      P.map h = P₂.map (fun ω => reflectField (h₂ ω)) →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k],
        P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
          P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k →
        ∀ s : ℚ, 0 < s → ∀ z ∈ H,
          IsLocalMartingaleBefore
            (imgFilt (glueMeasure P k h hC.2.1) s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W))
            (glueMeasure P k h hC.2.1)
            (fun p => min (QuantumZipper.swallowTime
                (wpath (imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W)) p) z : WithTop ℝ≥0)
              (imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p))
            (coupProc 4 (imgρ rL) (imgρ rR) (imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W))
              (imgVL s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W))
              (imgVR s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W)) z)

/-- **The filtration clauses of the explicit image word from Lemma 2.11's martingale hypothesis**: the filtration of
the image word contains the null sets at time `0`, the word is adapted, the `σₙ` are stopping times announcing the
killing time, and `{q < imgT} ∈ 𝓖_q`. -/
theorem imageWordMartStatement_of_imageWordFilt (hI : ImageWordFiltStatement.{u}) : ImageWordMartStatement.{u} := by
  intro rL rR hL hR Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk s hs
  set μ := glueMeasure P k h hC.2.1 with hμ
  set E := glueGood μ s ζ W with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood
  have hEg : ∀ p ∈ E, IsGlueGood s ζ W p := isGlueGood_of_mem_glueGood
  have hW : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  refine ⟨imgFilt μ s ζ W E, imgAnn s ζ W E, fun A hA h0 => ?_, ?_, fun i => ?_, fun j => ?_, fun n => ?_,
    monotone_imgAnn hs hEg, fun n p => imgAnn_lt_imgT hs hEg n p, ?_, fun q => ?_,
    hI rL rR hL hR P 𝓕 W VL VR B ζ h hC P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs⟩
  · exact Ito.measurableSet_usualAugmentation_of_null hA h0 0
  · exact stronglyAdapted_imgFilt_of (measurable_imgW hs hW hE hEg) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inl rfl⟩⟩
  · exact stronglyAdapted_imgFilt_of (measurable_imgVL hs hW hE hEg i) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩
  · exact stronglyAdapted_imgFilt_of (measurable_imgVR hs hW hE hEg j) fun r B hB =>
      ⟨r, le_rfl, Or.inl ⟨B, hB, Or.inr (Or.inr ⟨j, rfl⟩)⟩⟩
  · intro r
    have e : {p : Ω × HistorySpace 1 1 | ((imgAnn s ζ W E n p : ℝ≥0) : WithTop ℝ≥0) ≤ r} =
        {p | imgAnn s ζ W E n p ≤ r} := by
      ext p
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    rw [e]
    exact measurableSet_imgFilt_of_gen ⟨r, le_rfl, Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))⟩
      (measurableSet_le (measurable_imgAnn hs hW hE hEg n) measurable_const)
  · filter_upwards [ae_mem_glueGood (ae_isGlueGood hL hR hC hC₂ hlaw k hk hs)] with p hp
    exact fun u hu => exists_le_imgAnn hs hEg hp hu
  · exact measurableSet_imgFilt_of_gen ⟨q, le_rfl, Or.inr (Or.inl rfl)⟩
      (measurableSet_lt_imgT hs hW hE hEg q)

/-- **The contact step from Lemma 2.11's martingale hypothesis for the explicit image word** (with PROVE-WW-B15/B16's
reductions). -/
theorem reverseTipContactStatement_of_imageWordFilt (hI : ImageWordFiltStatement.{u}) :
    ReverseTipContactStatement.{u} :=
  reverseTipContactStatement_of_imageWordMart (imageWordMartStatement_of_imageWordFilt hI)

end InteractingSLE.WangWu
