/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartFilt
import InteractingSLE.Spec.Exist.FlowField

/-!
# The height-shifted two-slit law: the statement (Wang–Wu Proposition 4.19, κ = 4)

Packet PROVE-WW-B26 (route R2 of PROVE-WW-B21/B25, step 2: "Lemma 4.15 in this form"). Wang–Wu
(`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of Proposition 4.19 (L1655–L1708): the
forward line `α` is the level line of a field `h` of the two-seed word `(r_L; r_R)`, the reverse line `β` is the level
line of `X = h − δλ` (the word `(r_L + δ; r_R − δ)`), read backwards through the reflection `R(z) = −1/z` on the
glued space `P ⊗ k(X)` of PROVE-WW-B12–B19. In the chart `Ψ` of `ℍ \ R(β(0, s])` the forward line before contact is
the killed image word `(imgW, imgVL, imgVR)` of PROVE-WW-B17, whose weights are now `(r_L, −r_L − δ; r_R, −r_R + δ)`
(on the sides of the reverse slit `h = X + δλ = ±λ + δλ`). With `δ = 0` this is `ImageWordFiltStatement`.

* **`ImageWordFiltShiftStatement`**: the explicit coupling means of the killed image word with these weights are local
  martingales before `min (swallowTime z) imgT` in the filtration of the image word `imgFilt`, under the glued measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open LQGMetric (DistOn TestOn)
open LawUnique ImgWord ImgDrv MartChar

/-- **The height-shifted two-slit law of the contact step** (Wang–Wu, proof of Proposition 4.19, κ = 4; route R2 of
PROVE-WW-B25, "Lemma 4.15 in this form"). Let `h` carry an optional hull coupling of the two-seed word `(r_L; r_R)`
(forward line `α`), let `h = X + δλ` (`Exist.flowField 0 (δλ) X`, `λ = π/2`), and let `(P₂, h₂)` carry an optional
hull coupling of the reflected word `(r_R − δ; r_L + δ)` of `X` (reverse line `β`) whose reflected field `−h₂ ∘ R`
has the law of `X`, with `k` a regular conditional law of its killed history given the reflected field. All four
weights are nonnegative. Then on the glued space `P ⊗ k(X)`, for each rational `s > 0` and every `z ∈ ℍ`, the
explicit coupling mean of the killed image word `(imgW, imgVL, imgVR)` with the weights
`(![r_L, −r_L − δ], ![r_R, −r_R + δ])` is a local martingale before `min (swallowTime z) imgT` in the filtration of the
image word `imgFilt`. -/
def ImageWordFiltShiftStatement : Prop :=
  ∀ (rL rR δ : ℝ), 0 ≤ rL → 0 ≤ rR → 0 ≤ rL + δ → 0 ≤ rR - δ →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h →
      ∀ (X : Ω → DistOn upperHalfPlaneOpens) (hXm : Measurable X),
      (∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω)) →
      ∀ {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (𝓕₂ : Filtration ℝ≥0 mΩ₂) (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ)
        (ζ₂ : Ω₂ → ℝ≥0∞) (h₂ : Ω₂ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
        ζ₂ h₂ →
      P.map X = P₂.map (fun ω => reflectField (h₂ ω)) →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k],
        P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
          P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k →
        ∀ s : ℚ, 0 < s → ∀ z ∈ H,
          IsLocalMartingaleBefore
            (imgFilt (glueMeasure P k X hXm) s ζ W (glueGood (glueMeasure P k X hXm) s ζ W))
            (glueMeasure P k X hXm)
            (fun p => min (QuantumZipper.swallowTime
                (wpath (imgW s ζ W (glueGood (glueMeasure P k X hXm) s ζ W)) p) z : WithTop ℝ≥0)
              (imgT s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p))
            (coupProc 4 ![rL, -rL - δ] ![rR, -rR + δ] (imgW s ζ W (glueGood (glueMeasure P k X hXm) s ζ W))
              (imgVL s ζ W (glueGood (glueMeasure P k X hXm) s ζ W))
              (imgVR s ζ W (glueGood (glueMeasure P k X hXm) s ζ W)) z)

end InteractingSLE.WangWu
