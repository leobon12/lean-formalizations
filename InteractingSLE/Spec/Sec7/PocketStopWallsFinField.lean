/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsFinLeft
import InteractingSLE.Spec.Sec7.PocketStopFieldStrip

/-!
# The field-level pocket inputs with the walls' union law at the left end `T⁰(q)` (ruling R67)

Packet PROVE-STRIPSYS41. PROVE-STRIPSYS35's remaining field-level inputs `PocketStopWallsInput`/`…Inf` ask for Aux.
lemma 35's walls union law with the hull at the RIGHT end `T(q)` of the erasure fibre (`stopHull`), which is only an
optional time of the walls and the counterflow (PROVE-STRIPSYS37 §5.3). By ruling R67 the field-level statement is
made at the LEFT end `T⁰(q)` (`stopHull0`) and transferred to `T(q)` by `C ∩ D_{T⁰(q)} = C ∩ D_{T(q)}`
(`PocketStopWallsFinLeft.lean`). Here:

* `PocketStopWallsInput0`, `PocketStopWallsInputInf0`: the inputs with `stopHull0`, `stopHull0Inf`;
* **`pocketStopFieldInput_of_walls0`**, **`pocketStopFieldInputInf_of_walls0`**: STRIPSYS33's `PocketStopFieldInput`
  (at `T(q)`, unchanged) from them;
* **`pocketWordEvolution_of_wallsInput0'`**, **`StripPocketConfig.pocketWordEvolution_of_stripPocket_walls0`**: hPW
  with these inputs.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopField

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopWallsFin LocalSets WholeField

section Defs

variable {Ω : Type*}

/-- **The remaining field-level pocket inputs on every word-shape event** (bounded change pocket): STRIPSYS33's
`PocketStopFieldInput` with the chart constructed and the union law of `B ∪ R_{T(q)}` replaced by Aux. lemma 35's
walls union law. -/
def PocketStopWallsInput0 (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopWallsField (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0 R L r W η ψ) h₀ u) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopWallsField (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0 R L r W η ψ) h₀ u)

/-- **The remaining field-level pocket inputs on every word-shape event** (change pocket opening at the flow seed). -/
def PocketStopWallsInputInf0 (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopWallsField (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0Inf R L r W η ψ) h₀ u) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopWallsField (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0Inf R L r W η ψ) h₀ u)

end Defs

section Field

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketStopField` for the bounded change pocket** from the remaining data `PocketStopWallsField` at `T⁰(q)`
(ruling R67) (the canonical
pocket chart and Aux. lemma 124's union law from Aux. lemma 35's walls union law). -/
theorem pocketStopField_cfPocket0 {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h𝓦 : 𝓦 ≤ mΩ)
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hin : PocketStopWallsField κ ρL ρR 𝓦 P A (travAll R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0 R L r W η ψ) h₀ u) :
    PocketStopField κ ρL ρR 𝓦 P A (travAll R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      (stopHull R L r W η ψ) h₀ u := by
  obtain ⟨n, a, hn, hq⟩ := hin
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA hγ
      (PocketTraversalMeasRand.traversalMeasStatement_of_measurable h𝓦 hRm hLm hGm hcfg hηm A (h𝓦 _ hA) hAG ψ hψ
        hψm)
  exact pocketStopField_of_chart (isPocketChartOn_cfPocket hRm hLm hGm hG hA hAG hψ hψm)
    (measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG) hn
    (fun q => pocketStopUnionLaw_stopHull_of_stopHull0 hcfg hAG
      (pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1)) fun q => (hq q).2

/-- **`PocketStopField` for the change pocket opening at the flow seed** from the remaining data. -/
theorem pocketStopField_cfPocketInf0 {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h𝓦 : 𝓦 ≤ mΩ)
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hin : PocketStopWallsField κ ρL ρR 𝓦 P A (travAllInf R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0Inf R L r W η ψ) h₀ u) :
    PocketStopField κ ρL ρR 𝓦 P A (travAllInf R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      (stopHullInf R L r W η ψ) h₀ u := by
  obtain ⟨n, a, hn, hq⟩ := hin
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q ≤ mΩ :=
    locPrefixSigma_le h𝓦 hA hγ fun u hu => measurable_travSubInf h𝓦 hRm hLm hGm hcfg hηm hAG hψ hψm hu
  exact pocketStopField_of_chart (isPocketChartOn_cfPocketInf hRm hLm hGm hG hA hAG hψ hψm)
    (measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG) hn
    (fun q => pocketStopUnionLaw_stopHullInf_of_stopHull0Inf hcfg hAG
      (pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1)) fun q => (hq q).2

end Field

section Input

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **STRIPSYS33's `PocketStopFieldInput` from the remaining data** (bounded change pocket). -/
theorem pocketStopFieldInput_of_walls0 {κ rL rR : ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω}
    (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hin : PocketStopWallsInput0 κ rL rR 𝓦 P R L r W η G h₀ u) :
    PocketStopFieldInput κ rL rR 𝓦 P R L r W η G h₀ u := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨h1, h2⟩ := hin A hA hAG hPA ψ hψ hψm
  exact ⟨fun hs => pocketStopField_cfPocket0 h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm (h1 hs),
    fun hs => pocketStopField_cfPocket0 h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm (h2 hs)⟩

/-- **STRIPSYS33's `PocketStopFieldInputInf` from the remaining data** (change pocket opening at the flow seed). -/
theorem pocketStopFieldInputInf_of_walls0 {κ rL rR : ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω}
    (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hin : PocketStopWallsInputInf0 κ rL rR 𝓦 P R L r W η G h₀ u) :
    PocketStopFieldInputInf κ rL rR 𝓦 P R L r W η G h₀ u := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨h1, h2⟩ := hin A hA hAG hPA ψ hψ hψm
  exact ⟨fun hs => pocketStopField_cfPocketInf0 h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm (h1 hs),
    fun hs => pocketStopField_cfPocketInf0 h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm (h2 hs)⟩

end Input

section Word

/-- **`pocketWordEvolution_of_fieldInput'` with the remaining inputs**: on a walls-measurable configuration event `G` of
positive probability, hPW follows from `PocketStopWallsInput0`/`…Inf0` (ruling R67) on its two parts and the bounded
harmonic
representation of `𝔥` (the configurations give STRIPSYS33's field inputs through `pocketStopFieldInput_of_walls`,
`pocketStopFieldInputInf_of_walls`). -/
theorem pocketWordEvolution_of_wallsInput0'.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hR : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r → IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 → IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) (𝔥 : DistOn upperHalfPlaneOpens) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    (hin : PocketStopWallsInput0 (16 / κ') rL rR 𝓦 P R L r W η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} h₀ u)
    (hinI : PocketStopWallsInputInf0 (16 / κ') rL rR 𝓦 P R L r W η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} h₀
      u) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR := by
  have hGp : MeasurableSet[𝓦] {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} :=
    (measurableSet_rightLo_pos_and (mΩ := 𝓦) hRm hLm hGm hconf).1
  have hG0 : MeasurableSet[𝓦] {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} := by
    have e : {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} = G \ {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} := by
      ext ω
      exact ⟨fun h => ⟨h.1, fun h' => h.2 h'.2⟩, fun h => ⟨h.1, fun h' => h.2 ⟨h.1, h'⟩⟩⟩
    rw [e]
    exact hGm.diff hGp
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r},
      IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω) := fun ω hω =>
    hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) (hconf ω hω.1).changeCorner_props.1.1)
  exact pocketWordEvolution_of_fieldInput' hκ' hL hLd hR hRd h𝓦 hRm hLm hGm hPG hconf hcfg hcfgI hηm hh₀ 𝔥 hu
    hub h𝔥 (pocketStopFieldInput_of_walls0 h𝓦 hRm hLm hGp (fun ω hω => hcfg ω hω.1 hω.2) hηm hin)
    (pocketStopFieldInputInf_of_walls0 h𝓦 hRm hLm hG0 hcfgI' hηm hinI)

end Word

end InteractingSLE.Sec7.PocketStopField

namespace InteractingSLE.Sec7.StripPocketConfig

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling

/-- **hPW from the strip pocket with the remaining field-level pocket inputs** (Aux. lemmas 35–36, 119, 124–125 and 130,
Lemma 7.25's proof): STRIPSYS33's `pocketWordEvolution_of_stripPocket_field` with the pocket chart constructed
(`PocketStopField.pChart`) and the union law of `B ∪ R_{T(q)}` obtained from Aux. lemma 35's walls union law: `hin` is
`PocketStopField.PocketStopWallsInput0`, `PocketStopWallsInputInf0` (the walls union law at the left end `T⁰(q)`,
ruling R67). The other hypotheses are those of
`pocketWordEvolution_of_stripPocket_field`. -/
theorem pocketWordEvolution_of_stripPocket_walls0.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hRr : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ)
    {R β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ q t, Measurable[𝓦] fun ω => Lr q ω t)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar)
    (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hLw : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hnohit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hlate : ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ range (R ω))
    (htrace : ∀ᵐ ω ∂P, IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0)
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω)))
    (hattach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (R ω) (Lr q ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (Lr q ω) (StripSys.rt q))
        (cfArcR (R ω) (Lr q ω) (StripSys.rt q)) (cfArcL (R ω) (Lr q ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (Lr q ω) (StripSys.rt q) 0)))
    (hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) →
      rightLo (R ω) (Lr q ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (Lr q ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (Lr q ω) (StripSys.rt q))
          (cfArcRInf (R ω) (Lr q ω) (StripSys.rt q)) (cfArcLInf (R ω) (Lr q ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (Lr q ω) (StripSys.rt q) 0)))
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (𝔥 : DistOn upperHalfPlaneOpens)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q)) →
      PocketStopField.PocketStopWallsInput0 (16 / κ') rL rR (𝓦 ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u ∧
        PocketStopField.PocketStopWallsInputInf0 (16 / κ') rL rR (𝓦 ⊔ Ito.nullSets P) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR := by
  obtain ⟨q, hq, G, hGm, hPG, hG⟩ := exists_stripPocketEvent_ae (P := P) h𝓦 hRm hLm hβm hηm hηc hηH hη0 hR hβ
    hLw hnohit hlate (Q := fun q ω => (IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0) ∧
      (∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) ∧
      (IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) → 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q) →
        Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (Lr q ω) (StripSys.rt q))
          (cfArcR (R ω) (Lr q ω) (StripSys.rt q)) (cfArcL (R ω) (Lr q ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcR (R ω) (Lr q ω) (StripSys.rt q) 1))
          (firstHit (η ω) (cfArcR (R ω) (Lr q ω) (StripSys.rt q) 0))) ∧
      (IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) → rightLo (R ω) (Lr q ω) (StripSys.rt q) = 0 →
        Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (Lr q ω) (η ω) ∧
          Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (Lr q ω) (StripSys.rt q))
            (cfArcRInf (R ω) (Lr q ω) (StripSys.rt q)) (cfArcLInf (R ω) (Lr q ω) (StripSys.rt q))
            (firstHit (η ω) (cfArcRInf (R ω) (Lr q ω) (StripSys.rt q) 0))) ∧
      IsSimpleProper (β ω) ∧ Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (fun q hq => by
      filter_upwards [htrace, hav, hattach q hq, hattachI q hq, hβ, hLw q hq] with ω h1 h2 h3 h4 h5 h6
      exact ⟨h1, h2, h3, h4, h5.1, h6.2.2⟩)
  obtain ⟨hin1, hin2⟩ := hin q hq G hGm hPG fun ω hω => ⟨(hG ω hω).1, (hG ω hω).2.1⟩
  refine PocketStopField.pocketWordEvolution_of_wallsInput0' (W := W) hκ' hL hLd hRr hRd (sup_le h𝓦 (Ito.nullSets_le P))
    (fun t => (hRm t).mono le_sup_left le_rfl) (fun t => (hLm q t).mono le_sup_left le_rfl) hGm hPG
    (fun ω hω => (hG ω hω).1) (fun ω hω hpos => ?_) (fun ω hω h0 => ?_) hηm hh₀ 𝔥 hu hub h𝔥 hin1 hin2
  · obtain ⟨hconf, -, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, havω, hatt, -, hβsp, hLβ⟩ := hG ω hω
    exact isCfPocketConfig_of_cfAvoid hconf hpos htr hWc hW0 hrevR hrevL hvisR (hatt hconf hpos) hβsp hLβ havω
  · obtain ⟨hconf, -, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, havω, -, hattI, hβsp, hLβ⟩ := hG ω hω
    obtain ⟨htrans, hvisL, hatt⟩ := hattI hconf h0
    exact isCfPocketConfigInf_of_cfAvoid hconf h0 htr hWc hW0 htrans hrevR hrevL hvisR hvisL hatt hβsp hLβ havω

end InteractingSLE.Sec7.StripPocketConfig
