/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMarkedInf

/-!
# Consumer wiring: `PocketStopWallsInput0` from the side limit alone

Packet PROVE-STRIPSYS43 (PROVE-STRIPSYS41 §5.2). PROVE-STRIPSYS41's field-level inputs `PocketStopWallsInput0` /
`PocketStopWallsInputInf0` (consumed by `PocketStopField.pocketWordEvolution_of_wallsInput0'`) bundle, on every
walls-measurable sub-event `A` of the configuration event `G` and for every point-measurable Jordan coordinate,
the walls law `PocketStopWallsLaw` at `T⁰(q)` and the side limit `PocketStopSideLimit`. Here the walls law is discharged
by `pocketStopWallsLaw_stopHull0_marked` (and `…Inf_marked`), for the counterflow a frozen coupling with almost surely
infinite lifetime, `ζ′ = ∞` on `G`, and the marks' σ-algebra `𝓦 ≤ σ(fullHist ![R, L]) ∨ 𝓕_0`:

* **`pocketStopWallsInput0_of_sideLimit`**, **`pocketStopWallsInputInf0_of_sideLimit`**: the inputs from the side limit
  (with its chart branch `n` and constant `a`) alone.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopMarked

open QuantumZipper (H)
open LQGMetric (DistOn)
open WangWu (negInv)
open WangWu WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I PocketCoord PocketJordan
  PocketMarks PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopWallsFin

variable {Ω : Type*}

/-- **`PocketStopWallsInput0` from the side limit** (bounded change pocket): the walls law at `T⁰(q)` is
`pocketStopWallsLaw_stopHull0_marked`. -/
theorem pocketStopWallsInput0_of_sideLimit {κ rL rR : ℝ}
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    (h𝓦 : 𝓦 ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0)
    (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) (u : ℂ → ℝ)
    (hside : ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
      ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) P A
            (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a (centredField h'' u₀') u
            (activeCompl A (travAll R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q) ∧
      ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) P A
            (travAll R L r η ψ) marksL1All (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a (centredField h'' u₀') u
            (activeCompl A (travAll R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q)) :
    PocketStopWallsInput0 κ rL rR 𝓦 P R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η G (centredField h'' u₀') u := by
  intro A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hW : ∀ q : ℝ≥0, PocketStopWallsLaw 𝓦 P A (travAll R L r η ψ)
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (stopHull0 R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q)
      (centredField h'' u₀') q := fun q =>
    pocketStopWallsLaw_stopHull0_marked hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
      hlocL h𝓦 hRm' hLm' hGm hG hA hAG (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm q
  obtain ⟨h1, h2⟩ := hside A hA hAG hPA ψ hψ hψm
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨n, a', hn, hS⟩ := h1 hs
    exact ⟨n, a', hn, fun q => ⟨hW q, hS q⟩⟩
  · obtain ⟨n, a', hn, hS⟩ := h2 hs
    exact ⟨n, a', hn, fun q => ⟨hW q, hS q⟩⟩

/-- **`PocketStopWallsInputInf0` from the side limit** (change pocket opening at the flow seed). -/
theorem pocketStopWallsInputInf0_of_sideLimit {κ rL rR : ℝ}
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {G : Set Ω}
    (h𝓦 : 𝓦 ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0)
    (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤) (u : ℂ → ℝ)
    (hside : ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
      ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) P A
            (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a (centredField h'' u₀') u
            (activeCompl A (travAllInf R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q) ∧
      ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) P A
            (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a (centredField h'' u₀') u
            (activeCompl A (travAllInf R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q)) :
    PocketStopWallsInputInf0 κ rL rR 𝓦 P R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η G (centredField h'' u₀') u := by
  intro A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hW : ∀ q : ℝ≥0, PocketStopWallsLaw 𝓦 P A (travAllInf R L r η ψ)
      (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0Inf R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q) (centredField h'' u₀') q := fun q =>
    pocketStopWallsLaw_stopHull0Inf_marked hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
      hlocR hlocL h𝓦 hRm' hLm' hGm hG hA hAG (fun ω hω => hcfg ω (hAG hω)) (fun ω hω => hζG ω (hAG hω)) hψ hψm q
  obtain ⟨h1, h2⟩ := hside A hA hAG hPA ψ hψ hψm
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨n, a', hn, hS⟩ := h1 hs
    exact ⟨n, a', hn, fun q => ⟨hW q, hS q⟩⟩
  · obtain ⟨n, a', hn, hS⟩ := h2 hs
    exact ⟨n, a', hn, fun q => ⟨hW q, hS q⟩⟩

end InteractingSLE.Sec7.PocketStopMarked
