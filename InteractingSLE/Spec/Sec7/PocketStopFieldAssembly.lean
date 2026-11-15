/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopFieldUnion

/-!
# The field-level pocket inputs with the pocket chart constructed and Aux. lemma 35's walls union

Packet PROVE-STRIPSYS35. Specification §7.4, Aux. lemmas 119 (the measurable lift), 124 (`B ∪ R_T` from `A ∪ R_t`)
and 35–36 (`source/spec/p385-432.md` L1–L54, L171–L196; `source/spec/p145-192.md` L908–L940).

PROVE-STRIPSYS33's `PocketStopChart.PocketStopFieldInput` (the input `hin` of Theorem 1.3's pocket word,
`StripPocketConfig.pocketWordEvolution_of_stripPocket_field`) asks, on every word-shape event, for a pocket chart with
a derivative logarithm and, at every relative capacity time, the marked union law of `B ∪ R_{T(q)}` and the boundary
values of the mean in the relative chart. Here the chart is the canonical pocket chart `pChart` of
`PocketStopFieldChart.lean` (its branch shifted by a walls-measurable integer `n`, `shiftChart`), and the union law of
`B ∪ R_{T(q)}` comes from the union law of the walls with the hull, `m(walls) ∪ R_{T(q)}`
(`PocketStopFieldUnion.lean`). What remains is `PocketStopWallsField`: a walls-measurable branch integer `n`, a
constant `a`, and at every `q` Aux. lemma 35's walls union law and the boundary values of the mean for the shifted
canonical chart.

## Main results

* `PocketStopWallsField`, `PocketStopWallsInput`, `PocketStopWallsInputInf` (the remaining field-level data);
* **`pocketStopField_cfPocket`**, **`pocketStopField_cfPocketInf`**: one word shape;
* **`pocketStopFieldInput_of_walls`**, **`pocketStopFieldInputInf_of_walls`**: STRIPSYS33's `PocketStopFieldInput`,
  `PocketStopFieldInputInf` from them.

Ruling R48: nothing here uses Theorem 1.2/1.3 or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PocketStopField

open QuantumZipper (H)
open LQGMetric (DistOn)
open WangWu (negInv)
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C LocalSets WholeField
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop

/-! ### The remaining field-level data -/

section Defs

variable {Ω : Type*}

/-- **The remaining field-level data for one word** (canonical pocket chart): a walls-measurable branch integer `n`
and a constant `a` such that at every relative capacity time `q` the walls' marked union law with the hull at `T(q)`
holds (Aux. lemma 35, `PocketStopWallsLaw` with the walls `Γ`) and the mean has the word's boundary values in the
relative chart of the canonical pocket chart with lift shifted by `−2πn` (`PocketStopSideLimit`). -/
def PocketStopWallsField (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (𝓦 : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (Γ : Ω → Set ℂ) (F : ℝ≥0 → Ω → Set ℂ)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0, PocketStopWallsLaw 𝓦 P A γ Γ (F q) h₀ q ∧
    PocketStopSideLimit κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q

/-- **The remaining field-level pocket inputs on every word-shape event** (bounded change pocket): STRIPSYS33's
`PocketStopFieldInput` with the chart constructed and the union law of `B ∪ R_{T(q)}` replaced by Aux. lemma 35's
walls union law. -/
def PocketStopWallsInput (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopWallsField (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull R L r W η ψ) h₀ u) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopWallsField (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull R L r W η ψ) h₀ u)

/-- **The remaining field-level pocket inputs on every word-shape event** (change pocket opening at the flow seed). -/
def PocketStopWallsInputInf (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopWallsField (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHullInf R L r W η ψ) h₀ u) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketStopWallsField (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ
        (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHullInf R L r W η ψ) h₀ u)

end Defs

/-! ### One word shape -/

section Field

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketStopField` from the remaining data** (generic pocket): given the canonical pocket chart's properties
(`IsPocketChartOn` with the derivative logarithm `pLog`), measurable pocket events, and the union law of `B ∪ R_{T(q)}`
at every `q` obtained from the walls' law, the shifted canonical chart is the chart of `PocketStopField`. -/
theorem pocketStopField_of_chart {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {A : Set Ω}
    {γ : Ω → ℝ → ℂ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}
    {F : ℝ≥0 → Ω → Set ℂ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hc : IsPocketChartOn 𝓦 A C ψ (pChart A C ψ) ∧
      ∀ ω ∈ A, IsDerivLog (pChart A C ψ ω).1 (pLog A C ψ ω) (pChart A C ψ ω).dom ∧
        ∀ z ∈ (pChart A C ψ ω).dom, (pChart A C ψ ω).2.2 z = (pLog A C ψ ω z).im)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω}) {n : Ω → ℤ} (hn : Measurable[𝓦] n) {a : ℝ}
    (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀
      u (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q) :
    PocketStopField κ ρL ρR 𝓦 P A γ xL xR C ψ F h₀ u := by
  refine ⟨fun ω => shiftChart (pChart A C ψ ω) (n ω), fun ω z => pLog A C ψ ω z - n ω * (2 * π * I), a,
    isPocketChartOn_shift hc.1 hCm hn, fun ω hω => ⟨isDerivLog_sub_int (hc.2 ω hω).1 (n ω), fun z hz => ?_⟩,
    fun q => ⟨hU q, hside q⟩⟩
  change (pChart A C ψ ω).2.2 z - 2 * π * (n ω : ℝ) = (pLog A C ψ ω z - n ω * (2 * π * I)).im
  rw [im_sub_int_mul, (hc.2 ω hω).2 z hz]

/-- **`PocketStopField` for the bounded change pocket** from the remaining data `PocketStopWallsField` (the canonical
pocket chart and Aux. lemma 124's union law from Aux. lemma 35's walls union law). -/
theorem pocketStopField_cfPocket {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h𝓦 : 𝓦 ≤ mΩ)
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hin : PocketStopWallsField κ ρL ρR 𝓦 P A (travAll R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull R L r W η ψ) h₀ u) :
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
    (fun q => pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1) fun q => (hq q).2

/-- **`PocketStopField` for the change pocket opening at the flow seed** from the remaining data. -/
theorem pocketStopField_cfPocketInf {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h𝓦 : 𝓦 ≤ mΩ)
    {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hin : PocketStopWallsField κ ρL ρR 𝓦 P A (travAllInf R L r η ψ) xL xR (fun ω => cfPocket (R ω) (L ω) r) ψ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHullInf R L r W η ψ) h₀ u) :
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
    (fun q => pocketStopUnionLaw_cfPocket h𝓦 hRm hLm hGm hG hA hAG (hpre q) (hq q).1) fun q => (hq q).2

end Field

/-! ### The field-level inputs of Theorem 1.3's pocket word -/

section Input

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **STRIPSYS33's `PocketStopFieldInput` from the remaining data** (bounded change pocket). -/
theorem pocketStopFieldInput_of_walls {κ rL rR : ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω}
    (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hin : PocketStopWallsInput κ rL rR 𝓦 P R L r W η G h₀ u) :
    PocketStopFieldInput κ rL rR 𝓦 P R L r W η G h₀ u := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨h1, h2⟩ := hin A hA hAG hPA ψ hψ hψm
  exact ⟨fun hs => pocketStopField_cfPocket h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm (h1 hs),
    fun hs => pocketStopField_cfPocket h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm (h2 hs)⟩

/-- **STRIPSYS33's `PocketStopFieldInputInf` from the remaining data** (change pocket opening at the flow seed). -/
theorem pocketStopFieldInputInf_of_walls {κ rL rR : ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω}
    (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hin : PocketStopWallsInputInf κ rL rR 𝓦 P R L r W η G h₀ u) :
    PocketStopFieldInputInf κ rL rR 𝓦 P R L r W η G h₀ u := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨h1, h2⟩ := hin A hA hAG hPA ψ hψ hψm
  exact ⟨fun hs => pocketStopField_cfPocketInf h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm (h1 hs),
    fun hs => pocketStopField_cfPocketInf h𝓦 hRm hLm hGm hcfg hηm hA hAG hψ hψm (h2 hs)⟩

end Input

end InteractingSLE.Sec7.PocketStopField
