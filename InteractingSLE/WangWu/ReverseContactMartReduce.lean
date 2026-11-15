/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartGlue

/-!
# The image word of the contact step, part 3: `ImageMartStatement` from the filtration clauses of the explicit word

Packet PROVE-WW-B17. PROVE-WW-B16 reduced the contact step to `ImageMartStatement` (the field side of Lemma 2.11 for
the image driver, steps B1–B4 of PROVE-WW-B15's plan): the existence of a killed word with six groups of clauses. The
deterministic clauses — the killed word itself (`ImgDrv.IsKilledWord`), the simple image trace generating it, and its
identification with the glued driver `chainDrv` on every pre-contact prefix — hold for the explicit image word of
`ReverseContactMartGlue` (`imgW`, `imgVL`, `imgVR`, `imgT` on the measurable good set `glueGood`). This file isolates
what remains as the named input `ImageWordMartStatement`: for that explicit word, a filtration of the glued space with
the null sets at time `0`, adaptedness, announcing stopping times, `{q < T} ∈ 𝓖_q`, and the martingale clause (Lemma
2.11's hypothesis), and proves

* **`imageMartStatement_of_imageWordMart`**: `ImageWordMartStatement → ImageMartStatement`;
* `reverseTipContactStatement_of_imageWordMart`: with PROVE-WW-B15/B16's reductions, `ImageWordMartStatement →
  ReverseTipContactStatement`.

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

/-- **Named input: the filtration clauses of the explicit image word** (the probabilistic part of steps B1–B4 of
PROVE-WW-B15's plan). In the setting of `ReverseTipContactStatement`, for each rational `s > 0`, the explicit killed
image word `(imgW, imgVL, imgVR)` killed at `imgT` (on the good glued samples `glueGood`) is adapted to a filtration
`𝓖` of the glued space whose time-zero σ-algebra contains the null sets; its killing time is announced by stopping
times `σₙ < imgT` with `{q < imgT} ∈ 𝓖_q`; and its explicit coupling means are local martingales before
`min (swallowTime z) imgT` (Lemma 2.11's martingale hypothesis: "Its conditional harmonic means and conformal-radius
brackets, just identified, satisfy Lemma 2.11", Wang–Wu, proof of Proposition 4.18). -/
def ImageWordMartStatement : Prop :=
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
        ∀ s : ℚ, 0 < s →
          ∃ (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 1 1)))
            (σ : ℕ → Ω × HistorySpace 1 1 → ℝ≥0),
            (∀ A, MeasurableSet A → glueMeasure P k h hC.2.1 A = 0 → MeasurableSet[𝓖 0] A) ∧
            StronglyAdapted 𝓖 (imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W)) ∧
            (∀ i, StronglyAdapted 𝓖 (imgVL s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) i)) ∧
            (∀ j, StronglyAdapted 𝓖 (imgVR s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) j)) ∧
            (∀ n, IsStoppingTime 𝓖 fun p => (σ n p : WithTop ℝ≥0)) ∧ (∀ p, Monotone (σ · p)) ∧
            (∀ n p, (σ n p : WithTop ℝ≥0) < imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p) ∧
            (∀ᵐ p ∂(glueMeasure P k h hC.2.1), ∀ u : ℝ≥0,
              (u : WithTop ℝ≥0) < imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p → ∃ n, u ≤ σ n p) ∧
            (∀ q : ℝ≥0, MeasurableSet[𝓖 q]
              {p | (q : WithTop ℝ≥0) < imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p}) ∧
            ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 (glueMeasure P k h hC.2.1)
              (fun p => min (QuantumZipper.swallowTime
                  (wpath (imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W)) p) z : WithTop ℝ≥0)
                (imgT s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W) p))
              (coupProc 4 (imgρ rL) (imgρ rR) (imgW s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W))
                (imgVL s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W))
                (imgVR s ζ W (glueGood (glueMeasure P k h hC.2.1) s ζ W)) z)

/-- **`ImageMartStatement` from the filtration clauses of the explicit image word**: the deterministic clauses (killed
word, image trace, identification with `chainDrv`) are proved for the explicit word (`isKilledWord_img`,
`isGeneratingTraceIcc_imgTr`, `imgW_eq_chainDrv`). -/
theorem imageMartStatement_of_imageWordMart (hI : ImageWordMartStatement.{u}) : ImageMartStatement.{u} := by
  intro rL rR hL hR Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk s hs
  obtain ⟨𝓖, σ, hnull, hWa, hVLa, hVRa, hσ, hσm, hσT, hσlim, hTq, hmart⟩ :=
    hI rL rR hL hR P 𝓕 W VL VR B ζ h hC P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs
  set E := glueGood (glueMeasure P k h hC.2.1) s ζ W with hEdef
  have hE : ∀ p ∈ E, IsGlueGood s ζ W p := isGlueGood_of_mem_glueGood
  refine ⟨𝓖, imgW s ζ W E, imgVL s ζ W E, imgVR s ζ W E, imgT s ζ W E, σ, hnull, isKilledWord_img hs hE, hWa,
    hVLa, hVRa, hσ, hσm, hσT, hσlim, hTq, hmart, Eventually.of_forall fun p => ⟨imgTr s ζ W E p,
      fun t ht => isGeneratingTraceIcc_imgTr hs hE p ht, fun a b ha hb hab => imgTr_inj hs hE p ha hb hab,
      fun t ht0 ht => imgTr_mem_H hs hE p ht0 ht⟩, ?_⟩
  filter_upwards [ae_mem_glueGood (ae_isGlueGood hL hR hC hC₂ hlaw k hk hs)] with p hp
  exact fun S hS => imgW_eq_chainDrv hs hE hp hS

/-- **The contact step from the filtration clauses of the explicit image word** (with PROVE-WW-B15/B16's reductions). -/
theorem reverseTipContactStatement_of_imageWordMart (hI : ImageWordMartStatement.{u}) :
    ReverseTipContactStatement.{u} :=
  reverseTipContactStatement_of_imageMart (imageMartStatement_of_imageWordMart hI)

end InteractingSLE.WangWu
