/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactImgKilled
import InteractingSLE.WangWu.ReverseContactS4Chain

/-!
# The image driver of the contact step, part 7: `ImageDriverStatement` from its field-side input

Packet PROVE-WW-B16. PROVE-WW-B15 reduced the contact step of Wang–Wu's Proposition 4.18 (`ReverseTipContactStatement`)
to `ImageDriverStatement`: almost surely on the glued space, the glued driver `chainDrv` of the image chain `Ψ ∘ α` has a
continuation whose Loewner trace is a simple proper arc. Steps B5–B7 of its plan (Lemma 2.11 for the killed image driver,
the continuation, the trace) are now proved generically (`ImgDrv.IsKilledWord.ae_exists_continuation_four`). This file
isolates what remains, steps B1–B4 (the field side: "Its conditional harmonic means and conformal-radius brackets, just
identified, satisfy Lemma 2.11", text dump L1627–L1628), as the named input `ImageMartStatement`, and proves

* **`imageDriverStatement_of_imageMart`**: `ImageMartStatement → ImageDriverStatement`;
* `reverseTipContactStatement_of_imageMart`: with PROVE-WW-B15's reduction, `ImageMartStatement →
  ReverseTipContactStatement`.

`ImageMartStatement` asks, in the setting of `ReverseTipContactStatement` and for each rational `s > 0`, for a filtration
`𝓖` on the glued space (time-zero σ-algebra containing the null sets) and a killed `SLE₄(r_L, −r_L; r_R, −r_R)` word
`(Wi, VLi, VRi)` before a time `Ti` (`ImgDrv.IsKilledWord`; the force points are the images of `0⁻`, `Ψ(∞⁻)` and `0⁺`,
`Ψ(∞⁺)`) such that: the coordinates are adapted; `Ti` is announced by stopping times `σₙ < Ti`; `{q < Ti} ∈ 𝓖_q`; the
explicit coupling means are local martingales before `min (swallowTime z) Ti` (Lemma 2.11's martingale hypothesis — B3/B4:
B14's union-mean identity read in the image chart, extended to stopping times); the driver has a simple trace in `ℍ`
before `Ti` (the image curve); and the killed driver is the glued image driver on the capacity range of every pre-contact
prefix, which lies before `Ti` (B1/B2). Conditional helper; it replaces no source theorem.
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
open LawUnique
open ImgDrv MartChar Sec7.PhaseSelFull

/-- The weights of the image word on one side: `r` at the image of the seed `0∓`, `−r` at the image of `Ψ(∞∓)`. -/
def imgρ (r : ℝ) : Fin 2 → ℝ := ![r, -r]

theorem hasNonnegCumWeights_imgρ {rL rR : ℝ} (hL : 0 ≤ rL) (hR : 0 ≤ rR) : HasNonnegCumWeights (imgρ rL) (imgρ rR) := by
  have key : ∀ {r : ℝ}, 0 ≤ r → ∀ j : Fin 2, 0 ≤ ∑ i ∈ Finset.Iic j, imgρ r i := by
    intro r hr j
    fin_cases j
    · have e : (Finset.Iic (0 : Fin 2)) = {0} := by decide
      simp [e, imgρ, hr]
    · have e : (Finset.Iic (1 : Fin 2)) = {0, 1} := by decide
      simp [e, imgρ]
  exact ⟨key hL, key hR⟩

/-- **Named input: the field side of the contact step (steps B1–B4 of PROVE-WW-B15's plan)**. In the setting of
`ReverseTipContactStatement`, for each rational `s > 0`, the glued image driver, killed at its terminal capacity and
read with the images of the four boundary marks, is a killed `SLE₄(r_L, −r_L; r_R, −r_R)` word whose explicit coupling
means are local martingales before swallowing and before the killing time, in a filtration of the glued space whose
time-zero σ-algebra contains the null sets; its killing time is announced by stopping times and its driver has a simple
trace in `ℍ` before the killing time; and it is the glued driver `chainDrv` of the image chain on the capacity range of
every pre-contact prefix. -/
def ImageMartStatement : Prop :=
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
            (Wi : ℝ≥0 → Ω × HistorySpace 1 1 → ℝ) (VLi VRi : Fin 2 → ℝ≥0 → Ω × HistorySpace 1 1 → ℝ)
            (Ti : Ω × HistorySpace 1 1 → WithTop ℝ≥0) (σ : ℕ → Ω × HistorySpace 1 1 → ℝ≥0),
            (∀ A, MeasurableSet A → glueMeasure P k h hC.2.1 A = 0 → MeasurableSet[𝓖 0] A) ∧
            IsKilledWord Wi VLi VRi Ti ∧ StronglyAdapted 𝓖 Wi ∧ (∀ i, StronglyAdapted 𝓖 (VLi i)) ∧
            (∀ j, StronglyAdapted 𝓖 (VRi j)) ∧ (∀ n, IsStoppingTime 𝓖 fun p => (σ n p : WithTop ℝ≥0)) ∧
            (∀ p, Monotone (σ · p)) ∧ (∀ n p, (σ n p : WithTop ℝ≥0) < Ti p) ∧
            (∀ᵐ p ∂(glueMeasure P k h hC.2.1), ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < Ti p → ∃ n, u ≤ σ n p) ∧
            (∀ q : ℝ≥0, MeasurableSet[𝓖 q] {p | (q : WithTop ℝ≥0) < Ti p}) ∧
            (∀ z ∈ H, IsLocalMartingaleBefore 𝓖 (glueMeasure P k h hC.2.1)
              (fun p => min (QuantumZipper.swallowTime (wpath Wi p) z : WithTop ℝ≥0) (Ti p))
              (coupProc 4 (imgρ rL) (imgρ rR) Wi VLi VRi z)) ∧
            (∀ᵐ p ∂(glueMeasure P k h hC.2.1), ∃ γ : ℝ≥0 → ℂ,
              (∀ t : ℝ≥0, (t : WithTop ℝ≥0) < Ti p → Sec7.IsGeneratingTraceIcc (Wi · p) t γ) ∧
              (∀ a b : ℝ≥0, (a : WithTop ℝ≥0) < Ti p → (b : WithTop ℝ≥0) < Ti p → γ a = γ b → a = b) ∧
              ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) < Ti p → γ t ∈ H) ∧
            ∀ᵐ p ∂(glueMeasure P k h hC.2.1),
              ∀ S ∈ preContact (seedLine ζ W p.1) (negInv '' histHull s p.2),
                (((capClock (imgCurve (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1)) S).toNNReal : ℝ≥0) :
                  WithTop ℝ≥0) < Ti p ∧
                ∀ r ∈ Icc 0 (capClock (imgCurve (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1)) S),
                  Wi r.toNNReal p = chainDrv (imgCurve (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1))
                    (preContact (seedLine ζ W p.1) (negInv '' histHull s p.2)) r

/-- **`ImageDriverStatement` from the field side of the contact step**: the generic continuation of a killed
`SLE₄(ρ)` word (`ImgDrv.IsKilledWord.ae_exists_continuation_four`) applied to the image word. -/
theorem imageDriverStatement_of_imageMart (hI : ImageMartStatement.{u}) : ImageDriverStatement.{u} := by
  intro rL rR hL hR Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk s hs
  obtain ⟨𝓖, Wi, VLi, VRi, Ti, σ, hnull, hK, hWa, hVLa, hVRa, hσ, hσm, hσT, hσlim, hTq, hmart, hγ, hid⟩ :=
    hI rL rR hL hR P 𝓕 W VL VR B ζ h hC P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs
  filter_upwards [hK.ae_exists_continuation_four hnull hWa hVLa hVRa hσ hσm hσT hσlim hTq
    (hasNonnegCumWeights_imgρ hL hR) hmart hγ, hid] with p hX hidp
  obtain ⟨X, hXc, hX0, hXW, hXg⟩ := hX
  obtain ⟨η, -, -, -, hLT, hP⟩ := hXg.trace hXc hX0
  refine ⟨Ito.rpath X, continuous_rpath hXc, by simp [Ito.rpath, hX0], ⟨_, hLT, hP⟩, fun S hS r hr => ?_⟩
  obtain ⟨hlt, heq⟩ := hidp S hS
  rw [← heq r hr]
  show X r.toNNReal = Wi r.toNNReal p
  exact hXW _ (lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr.2)) hlt)

/-- **The contact step from the field side of the contact step** (with PROVE-WW-B15's reduction). -/
theorem reverseTipContactStatement_of_imageMart (hI : ImageMartStatement.{u}) : ReverseTipContactStatement.{u} :=
  reverseTipContactStatement_of_imageDriver (imageDriverStatement_of_imageMart hI)

end InteractingSLE.WangWu
