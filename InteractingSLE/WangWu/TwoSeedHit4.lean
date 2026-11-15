/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50HitMain
import InteractingSLE.Spec.Sec7.Aux50Kernel
import InteractingSLE.Spec.Supplement.R7Reference
import InteractingSLE.WangWu.Prop418RangeMain
import InteractingSLE.WangWu.ImgChartConstMarks

/-!
# Wang–Wu at `κ = 4`: the boundary-hitting two-seed words from one reference coupling each

Packet PROVE-WW-B20. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Proposition 4.24
(text dump L1816–L1867): "For every `ρL, ρR > −2`, the level-line coupling with adjacent force points `0−, 0+` has a
simple continuous transient trace, determined by the field. […] The same fixed joint law identifies every coupling with
the stated local Gaussian kernel."

Proposition 4.24 is proved by realising the word `SLE₄(ρL; ρR)` as the image of the middle seed line in a chamber
between two ordered seed lines (Propositions 4.18–4.20, Lemmas 4.21–4.22, Corollary 4.23). Its output is **one**
coupling of the word with a transient trace and a field-determined history. This file shows that this output is all
that the two remaining `κ = 4` inputs of Theorem 1.2's wiring (`Spec/Wire/Thm12Inputs3.lean`) need:

* **`hhit`** (`Theorem18.TwoSeedHittingStatement 4`): one evolution of the word with a transient generating trace gives
  the trace for every evolution (`R7.hasTransientGeneratingTrace_of_reference`: the trace event is a measurable function
  of the driver and the driving law is unique by Theorem 2.2) — `twoSeedHittingStatement_four_of_reference`;
* **`hneg`** (determination for the words with a weight in `(−2, 0)`): with the traces of all evolutions, Aux. lemma 50
  at `κ = 4` (`Aux50Hit.hasTraceStopKernel_of_lt_eight`, proved for every `0 < κ < 8`) and Theorem 2.2's two-seed
  uniqueness give one joint law of field and killed history for all couplings of the word
  (`R7.isOptionalHullLawUnique_twoSeed`), so the reference's determining graph transfers to every coupling
  (`R7.hasFieldDeterminedHistories_twoSeed_of_reference`) — `hasFieldDeterminedHistories_four_of_reference`;
* with the contact step (`reverseTipContactStatement`, PROVE-WW-B19) for the nonnegative words:
  **`LP.TwoSeedGraphInput 4`
  from the two references** — `twoSeedGraphInput_four_of_reference`.

This is the last sentence of Proposition 4.24's proof ("The same fixed joint law identifies every coupling with the
stated local Gaussian kernel"), carried out with the project's Aux. lemma 50 instead of Lemma 2.8. The two references
are named inputs (`Hit4TraceReferenceStatement`, `Hit4DetReferenceStatement`): the chamber construction of
Proposition 4.24.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE.WangWu

/-! ### The two references (Proposition 4.24's chamber construction) -/

/-- **The trace half of Proposition 4.24 for one realisation**: for every pair of seed weights `ρL, ρR > −2` with a
weight in `(−2, 0)` there is an integrated `SLE₄(ρL; ρR)` evolution (force points `0−, 0+`) on a probability space in
the universe `v` whose driver almost surely has a continuous generating trace on `[0, ∞)` tending to infinity ("the
level-line coupling with adjacent force points `0−, 0+` has a simple continuous transient trace"). -/
def Hit4TraceReferenceStatement : Prop :=
  ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ ∧
        LP.HasTransientGeneratingTrace P W ζ

/-- **The determination half of Proposition 4.24 for one realisation**: for every pair of seed weights `ρL, ρR > −2`
with a weight in `(−2, 0)` there is a coupling of the word `SLE₄(ρL; ρR)` with the original optional hull
specification (on a probability space in the universe `v`) whose killed driving history is a Borel function of its
field ("determined by the field"). -/
def Hit4DetReferenceStatement : Prop :=
  ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.IsFieldDeterminedHistory P h W VL VR ζ

/-! ### `hhit` -/

/-- **`hhit` from the trace reference**: every integrated `SLE₄(ρL; ρR)` evolution with `ρL, ρR > −2` and a weight
in `(−2, 0)` almost surely has a continuous generating trace on `[0, ∞)` tending to infinity. -/
theorem twoSeedHittingStatement_four_of_reference (href : Hit4TraceReferenceStatement.{v}) :
    Theorem18.TwoSeedHittingStatement.{u} 4 := by
  intro rL rR hL hR hhit Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hneg : rL < 0 ∨ rR < 0 := by norm_num at hhit; exact hhit
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀, htr₀⟩ := href rL rR hL hR hneg
  exact R7.hasTransientGeneratingTrace_of_reference (by norm_num) hL hR hE₀ htr₀ hE

/-- The finite-time traces (`R7.TwoSeedHasTraces`) of the hitting words, from the trace reference. -/
theorem twoSeedHasTraces_four_of_reference (href : Hit4TraceReferenceStatement.{v}) {rL rR : ℝ} (hL : -2 < rL)
    (hR : -2 < rR) (hneg : rL < 0 ∨ rR < 0) : R7.TwoSeedHasTraces.{u} 4 rL rR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hhit := twoSeedHittingStatement_four_of_reference.{u, v} href rL rR hL hR (by norm_num; exact hneg)
    P 𝓕 W VL VR B ζ hE
  filter_upwards [hhit] with ω hω
  obtain ⟨η, hη, -⟩ := hω
  exact ⟨η, hη⟩

/-! ### `hneg` -/

/-- **`hneg` from the two references**: every coupling of a two-seed word `SLE₄(ρL; ρR)` with `ρL, ρR > −2` and a
weight in `(−2, 0)` satisfying the original optional hull specification has a field-determined killed driving
history. -/
theorem hasFieldDeterminedHistories_four_of_reference (htr : Hit4TraceReferenceStatement.{v})
    (hdet : Hit4DetReferenceStatement.{v}) {rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR) (hneg : rL < 0 ∨ rR < 0) :
    LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) := by
  obtain ⟨Ψ, hΨ, hKv, hKu⟩ := Aux50.exists_twoSeedTraceFieldKernel.{v, u} (κ := 4) (by norm_num) hL hR
    (Aux50Hit.hasTraceStopKernel_of_lt_eight (κ := 4) (by norm_num) (by norm_num) hL hR)
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀, hdet₀⟩ := hdet rL rR hL hR hneg
  exact R7.hasFieldDeterminedHistories_twoSeed_of_reference (by norm_num) hΨ
    (twoSeedHasTraces_four_of_reference.{v, v} htr hL hR hneg)
    (twoSeedHasTraces_four_of_reference.{u, v} htr hL hR hneg) hKv hKu
    ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀, hdet₀⟩

/-! ### The two-seed input of Theorem 1.2 at `κ = 4` -/

/-- **`LP.TwoSeedGraphInput 4` from the two references of Proposition 4.24** (the nonnegative words by the contact step
of Proposition 4.18, `reverseTipContactStatement`, PROVE-WW-B19). -/
theorem twoSeedGraphInput_four_of_reference (htr : Hit4TraceReferenceStatement.{v})
    (hdet : Hit4DetReferenceStatement.{v}) : LP.TwoSeedGraphInput.{u} 4 :=
  twoSeedGraphInput_four_of_contact reverseTipContactStatement.{0}
    (fun _ _ hL hR hneg => hasFieldDeterminedHistories_four_of_reference.{u, v} htr hdet hL hR hneg)
    (twoSeedHittingStatement_four_of_reference.{u, v} htr)

end InteractingSLE.WangWu
