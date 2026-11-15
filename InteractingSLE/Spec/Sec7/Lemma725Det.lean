/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50HitMain
import InteractingSLE.Spec.Sec7.Prop73Ref

/-!
# Lemma 7.25, determination (`κ > 4`, both seed weights below `κ/2 − 4`), and the wiring of Aux. lemma 50

Packet PROVE-AUX50B. Specification Lemma 7.25 (`source/spec/p385-432.md` L490–L515, pp. 413–414): "Every coupling of
the integrated `SLE_{κ'}(ρ^L; ρ^R)` law with its canonical GFF satisfying Theorem 1.1 is concentrated on one measurable
field–curve graph. […] its full joint law with the field is unique." Its proof ends: "This proves finite-time
continuity for the prescribed two-seed driving law, then universal field determination and uniqueness of its full
joint field–curve law." The determination step is the one of Proposition 7.3 (`Prop73Det`) and Theorem R.7
(`R7.hasFieldDeterminedHistories_twoSeed_of_reference`): one reference coupling whose killed driving history is a
Borel function of its field, the finite-time continuity of every two-seed evolution, and Aux. lemma 50's common field
kernel (Aux. lemma 51), which is proved here for `κ < 8` (`Aux50Hit.hasTraceStopKernel_of_lt_eight`).

* `lemma725DeterminationStatement_of_reference`: `LP.Lemma725DeterminationStatement` from the reference
  (`Lemma725DetReferenceStatement`, named input: the pocket-word construction of Aux. lemmas 119–130 with Aux. lemma
  126's transfer, at the level of the field), the trace part (`LP.Lemma725TraceStatement`, named input of LP7) and Aux.
  lemma 50 for `κ ≥ 8` only (`Lemma725KernelGeEightStatement`);
* the Proposition 7.3 wiring of PROVE-PROP73R with its kernel input discharged
  (`prop73DeterminationStatement_of_embeddedPair`, `lemma75Statement_of_embeddedPair`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Aux50Hit

/-! ### Lemma 7.25, determination -/

/-- **Named input: the reference of Lemma 7.25** (pp. 413–414; Aux. lemmas 119–130): for `k > 4` and seed weights
`r_L, r_R ∈ (−2, k/2 − 4)` there is one coupling of the two-seed word `SLE_k(r_L; r_R)` (marks at `0⁻`, `0⁺`) with the
original optional hull specification whose killed driving history is a Borel function of its field. The form is that
of Proposition 7.3's reference (`Prop73Det.Prop73ReferenceStatement`) and of Theorem R.7's
(`R7.R7ReferenceStatement`, without its trace clause, carried here by `LP.Lemma725TraceStatement`). -/
def Lemma725DetReferenceStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.IsFieldDeterminedHistory P h W VL VR ζ

/-- **Named input: Aux. lemma 50 for the both-low two-seed words at `κ ≥ 8`** (for `κ < 8` it is
`hasTraceStopKernel_of_lt_eight`). -/
def Lemma725KernelGeEightStatement : Prop :=
  ∀ κ : ℝ, 8 ≤ κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
    Aux50.HasTraceStopKernel.{u, u} κ rL rR

/-- **Lemma 7.25, determination** (`LP.Lemma725DeterminationStatement`, unowned per PROVE-WIRE2), by Proposition 7.3's
route: the reference, the finite-time continuity of the both-low two-seed evolutions, and Aux. lemma 50's common
kernel (proved for `4 < κ < 8`; the `κ ≥ 8` part is the named input `Lemma725KernelGeEightStatement`). -/
theorem lemma725DeterminationStatement_of_reference (h725t : LP.Lemma725TraceStatement.{u})
    (href : Lemma725DetReferenceStatement.{u}) (h8 : Lemma725KernelGeEightStatement.{u}) :
    LP.Lemma725DeterminationStatement.{u} := by
  intro κ hκ rL rR hL hL' hR hR'
  have hK : Aux50.HasTraceStopKernel.{u, u} κ rL rR := by
    rcases lt_or_ge κ 8 with hκ8 | hκ8
    · exact hasTraceStopKernel_of_lt_eight (by linarith) hκ8 hL hR
    · exact h8 κ hκ8 rL rR hL hL' hR hR'
  obtain ⟨Ψ, hΨ, hKu, -⟩ := Aux50.exists_twoSeedTraceFieldKernel (by linarith) hL hR hK
  have htr : R7.TwoSeedHasTraces.{u} κ rL rR := fun P _ 𝓕 W VL VR B ζ hE =>
    h725t κ hκ rL rR hL hL' hR hR' P 𝓕 W VL VR B ζ hE
  have hκ0 : 0 < κ := by linarith
  exact @R7.hasFieldDeterminedHistories_twoSeed_of_reference.{u, u} κ rL rR Ψ hκ0 hΨ htr htr hKu hKu
    (href κ hκ rL rR hL hL' hR hR')

/-- **Lemma 7.25, determination for `4 < κ < 8`**, from the reference and the trace part alone. -/
theorem hasFieldDeterminedHistories_lemma725_of_lt_eight (h725t : LP.Lemma725TraceStatement.{u})
    (href : Lemma725DetReferenceStatement.{u}) {κ : ℝ} (hκ : 4 < κ) (hκ8 : κ < 8) {rL rR : ℝ} (hL : -2 < rL)
    (hL' : rL < κ / 2 - 4) (hR : -2 < rR) (hR' : rR < κ / 2 - 4) :
    LP.HasFieldDeterminedHistories.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) := by
  obtain ⟨Ψ, hΨ, hKu, -⟩ := Aux50.exists_twoSeedTraceFieldKernel (by linarith) hL hR
    (hasTraceStopKernel_of_lt_eight.{u, u} (by linarith) hκ8 hL hR)
  have htr : R7.TwoSeedHasTraces.{u} κ rL rR := fun P _ 𝓕 W VL VR B ζ hE =>
    h725t κ hκ rL rR hL hL' hR hR' P 𝓕 W VL VR B ζ hE
  have hκ0 : 0 < κ := by linarith
  exact @R7.hasFieldDeterminedHistories_twoSeed_of_reference.{u, u} κ rL rR Ψ hκ0 hΨ htr htr hKu hKu
    (href κ hκ rL rR hL hL' hR hR')

/-! ### Proposition 7.3 and Lemma 7.5 with the kernel input discharged -/

/-- **Proposition 7.3's determination from Lemma 7.1's embedded pair and the trace part** (PROVE-PROP73R's
`Prop73Ref.prop73DeterminationStatement_of_embeddedPair` with its Aux. lemma 50 input proved). -/
theorem prop73DeterminationStatement_of_embeddedPair (h73t : Sec7.Prop73TraceStatement.{u})
    (h71 : Prop73Ref.EmbeddedPairStatement.{u}) : Determination.Prop73DeterminationStatement.{u} :=
  Prop73Ref.prop73DeterminationStatement_of_embeddedPair h73t h71 fun _ hκ hκ4 _ _ hL hR _ =>
    hasTraceStopKernel_of_lt_eight hκ (by linarith) hL hR

/-- **Lemma 7.5, universal form**, from Lemma 7.1's embedded pair, the trace part of Proposition 7.3 and LOCEXT's
inputs (PROVE-PROP73R's `Prop73Ref.lemma75Statement_of_embeddedPair` with its Aux. lemma 50 input proved). -/
theorem lemma75Statement_of_embeddedPair (h73t : Sec7.Prop73TraceStatement.{u})
    (h71 : Prop73Ref.EmbeddedPairStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.StoppedSeedExtensionStatement.{u} κ)
    (hrs : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.RestartSeedCouplingStatement.{u} κ) :
    Theorem15.Lemma75Statement.{u} :=
  Prop73Ref.lemma75Statement_of_embeddedPair h73t h71
    (fun _ hκ hκ4 _ _ hL hR _ => hasTraceStopKernel_of_lt_eight hκ (by linarith) hL hR) hext hrs

end Aux50Hit

end InteractingSLE
