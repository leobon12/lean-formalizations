/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.J5ChartClausePocket
import InteractingSLE.Spec.Sec7.Lemma71MMain

/-!
# Wang–Wu at `κ = 4`, (J5): the chamber chart coupling clause from Proposition 4.20's prime-end premise

Packet PROVE-WW-B22. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.24
(text dump L1816–1867): "The conditional field `H = (h|_C) ∘ ψ⁻¹` is a GFF in `ℍ` with boundary values
`λ − u₂ = −λ(1 + ρL)` on `ℝ₋`, `−λ − u₁ = λ(1 + ρR)` on `ℝ₊`. Proposition 4.20 applies at every stopping time in the
filtration enlarged by the walls. Therefore the transformed middle line `X` satisfies the local Markov coupling with
these values." The coupling clause in the chamber chart is `Coupling.MartMeans2.IsChartCouplingCharFun 4 (ρL) (ρR) …`
(the clause of `WangWu.Chamber4.Chamber4JointStatement`).

The specification's Lemma 7.1 derives the same clause for its pocket from Remark 6.7's three-curve law
(PROVE-LEMMA71L/M: `Sec7.Lemma71M.isChartCouplingCharFunConst_of_premise_ind`, `…_of_primeEnd_ind`,
`measurable_chartAvoid_pocket`, `Sec7.Lemma71K.isPocketChartData_of_isPocketConstruction`,
`Sec7.Lemma71M.isPocketChartData_of_pocketPrimeEnd`). Those proofs use the three-curve space only through its
three-line part (`SeedThree.IsThreeLineSpace`) and are generic in `κ` and in the seed weights; the weights enter only
through the clause's mean. This file restates them on every three-line space with arbitrary weights (same proofs; each
declaration notes its source):

* `IsChamberChartData` (def): the chamber chart data with the clause of the word `(ρL; ρR)`;
* `isChartCouplingCharFunConst_of_premise_three`, `isChartCouplingCharFunConst_of_primeEnd_three`: the fixed-time
  clause in the filtration of the walls and the mapped middle prefix, from the stopped three-line law
  (`IsThreeLineSpace.ae_condExp_exp_eq_three`'s ingredient, Remark 6.7 = Proposition 4.20 stopped/three lines) and its
  prime-end premise (`Sec7.Lemma71L.PocketPrimeEnd`: Corollary 4.8's boundary comparison at the prime ends of the
  remaining chamber);
* `measurable_chartAvoid_pocket_three`: the measurability (B4) of the avoidance event, the chart mean and the variance;
* `isChamberChartData_of_isPocketConstruction`: the clause at every stopping time of the usual augmentation and the
  chart data;
* **`isChamberChartData_of_pocketPrimeEnd`**: on every three-line space with the chamber construction
  (`exists_isPocketConstruction_three`, `exists_capData_three`), the prime-end premise alone gives the chamber chart
  data, in particular **the chart coupling clause (J5)** — at `κ = 4` with `k = χ(4) = 0`;
* `isChartCouplingCharFunConst_of_pocketPrimeEnd_three`, `isChartCouplingCharFunConst_of_sideLimit_three`: the
  **fixed-time** clauses inside the next two results (the form of WW-B23's `ChamberCond.ChamberClauseStatement`);
* **`isChamberChartData_of_sideLimit`** (`Sec7.Lemma71MMain`'s reduction): the same from the side limits
  `Sec7.Lemma71M.PocketSideLimit` of the active chamber component at every capacity time (the local-set means of the
  stopped union, of the three complete lines and of the two walls are constructed; the explicit chart of the active
  component and the disc transfer are `Sec7.Lemma71M.pocketPrimeEnd_of_sideLimit`).

Conditional helpers (on the prime-end premise); they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.WangWu.SeedThree

open QuantumZipper (H Hbar fwdHull)
open Sec7 MartChar Coupling Sec7.Lemma71C Sec7.Lemma71D Sec7.Lemma71E Sec7.Lemma71K Sec6 LocalSets Sec7.Lemma71G
  Sec7.Lemma71L Sec7.Lemma71M

section Data

/-- **The chamber chart data** (the `κ = 4` counterpart, with arbitrary seed weights `ρL`, `ρR`, of the specification's
`Sec7.Lemma72B.IsPocketChartData`; Wang–Wu Proposition 4.24's "wall-measurable Riemann map `ψ`", the transformed
middle line `X` and "the local Markov coupling with these values"): a right-continuous filtration `𝓖` containing the
null sets at time `0`; the mapped middle segment `γ'` (almost surely a continuous simple path in `ℍ̄` from `0` to `∞`
whose real-boundary times have empty interior); its driver `W` (`W₀ = 0`, continuous and adapted before `T`,
generating every filled prefix of `γ'`); the measurable field `h`; the `𝓖₀`-measurable conformal chamber chart `c`
with lifts continuous on the chamber; **the chart coupling clause of the two-seed word `(ρL; ρR)` killed at `T`**;
(S1) the chart is a function of the two walls `(β, α)`; (S2) `∂C ∩ ℍ ⊆ β ∪ α` almost surely; (S3) the filtration lies
in the completed σ-algebra of the three curves. -/
def IsChamberChartData (κ : ℝ) (ρL ρR : Fin 1 → ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (β α γ : Ω → ℝ≥0 → ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (𝓖 : Filtration ℝ≥0 mΩ) (γ' : Ω → ℝ → ℂ)
    (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (c : Ω → Chart) (a k : ℝ) : Prop :=
  𝓖.IsRightContinuous ∧
    (∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) ∧
    (∀ᵐ ω ∂P, ContinuousOn (γ' ω) (Ici 0) ∧ InjOn (γ' ω) (Ici 0) ∧ MapsTo (γ' ω) (Ici 0) Hbar ∧
      γ' ω 0 = 0 ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ' ω u).im = 0} = ∅) ∧
    (∀ ω, W 0 ω = 0) ∧ (∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω}) ∧
    AdaptedBefore 𝓖 T W ∧
    (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
      fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ' ω '' Icc 0 t)) ∧
    Measurable h ∧ (∀ ω, (c ω).IsConformal) ∧
    (∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom}) ∧
    (∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
    (∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
    (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
    Coupling.MartMeans2.IsChartCouplingCharFun κ ρL ρR P 𝓖 W (MartChar.geomL W LP.twoSeedXL)
      (MartChar.geomR W LP.twoSeedXR) T c a k h ∧
    (∀ (z : ℂ) (r : ℝ), MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | Metric.closedBall z r ⊆ (c ω).dom}) ∧
    (∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
    (∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
    (∀ᵐ ω ∂P, frontier ((c ω).dom : Set ℂ) ∩ H ⊆ range (β ω) ∪ range (α ω)) ∧
    ∀ t, 𝓖 t ≤ MeasurableSpace.comap β MeasurableSpace.pi ⊔ MeasurableSpace.comap α MeasurableSpace.pi ⊔
      MeasurableSpace.comap γ MeasurableSpace.pi ⊔ Ito.nullSets P

end Data

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {ρL ρR : Fin 1 → ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}
  {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

-- mirrored from `Sec7.Lemma71MData.isChartCouplingCharFunConst_of_premise_ind`
/-- **The fixed-time chart coupling clause from the three-curve law, with the chart mean and variance measurable on
the avoidance event** (`Lemma71L.isChartCouplingCharFunConst_of_premise` with the indicator forms of B4). -/
theorem isChartCouplingCharFunConst_of_premise_three [IsProbabilityMeasure P]
    (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {c' : Ω → Chart} (hc' : ∀ ω, (c' ω).IsConformal)
    {ρL ρR : Fin 1 → ℝ} {a' : ℝ}
    (hmeas : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens),
      MeasurableSet[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t} ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          fun ω => Lemma71D.chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
          (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
          (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
          (QuantumZipper.chiC κ) φ t) ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          fun ω => chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t))
    (hprem : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∃ gS gL gT : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)))
        (WholeField.centredField h u₀) P gS ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
        (WholeField.centredField h u₀) P gT ∧
      ∀ᵐ ω ∂P, IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t →
        IsThreeChartPremise (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
          (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) u₀
          (QuantumZipper.chiC κ) φ
          (Lemma71D.chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
            (QuantumZipper.chiC κ) φ t)
          (chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t)) :
    IsChartCouplingCharFunConst κ ρL ρR P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω)) c' a'
      (QuantumZipper.chiC κ) h := by
  intro t u hu φ
  have hS' := hS
  obtain ⟨-, hu₀, hh0, hβ62, hα62, hγ62, -⟩ := hS'
  have hpc' := hpc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hseg, -, -⟩ := hpc'
  obtain ⟨gS, gL, gT, hgS, hgL, hgT, hpr⟩ := hprem t φ
  obtain ⟨hEm, hMm, hVm⟩ := hmeas t φ
  have hpr' : ∀ᵐ ω ∂P, ω ∈ {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t} →
      IsThreeChartPremise (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
        (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
        (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) u₀
        (QuantumZipper.chiC κ) φ
        ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          (fun ω => Lemma71D.chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
            (QuantumZipper.chiC κ) φ t) ω)
        ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          (fun ω => chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t) ω) := by
    filter_upwards [hpr] with ω hω hE
    have hE' : ω ∈ {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t} := hE
    rw [indicator_of_mem hE', indicator_of_mem hE']
    exact hω hE
  have hlaw := ae_condExp_exp_eq_three_of_le_aeSigma
    (𝒢 := prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t)
    hh0 hβ62 hα62 hγ62 (measurable_capStop hG hM hY t) (capStop_galmarino t) (fun _ => rfl) hgS hgL hgT hu₀.1
    hu₀.2 (QuantumZipper.chiC κ) φ
    ((prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ').le t)
    ((prefixFiltrationOf_le_aeSigma_three hS hpc hG hM hY hMiff hGeq hYeq t).trans (aeSigma_mono P le_sup_right))
    hEm hMm hVm hpr'
  filter_upwards [hlaw] with ω hω hlt hsupp
  have hE : IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t := ⟨hlt, hsupp⟩
  have h1 := hω hE
  have hE' : ω ∈ {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t} := hE
  rw [indicator_of_mem hE', indicator_of_mem hE'] at h1
  have hfield : (fun ω' => cexp (I * ((WholeField.centredField h u₀ ω' φ + ∫ x, u₀ x * φ x : ℝ) : ℂ))) =
      fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) := by
    funext ω'
    rw [WholeField.centredField_apply h hu₀.1 ω' φ, sub_add_cancel]
  rw [hfield] at h1
  rw [h1]
  have hWc : ∀ ω'', ContinuousOn (fun s => segDriver (γ' ω'') s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ' ω'')} :=
    fun ω'' => (hseg ω'').segDriver_spec.2.1
  obtain ⟨hvL, hvR⟩ := geomL_le_le_geomR (W := fun s ω => segDriver (γ' ω) s) (T := fun ω => capLife (γ' ω))
    hWc LP.twoSeedXL LP.twoSeedXR hlt
  have hkey := integral_couplingMean_eq_chartMean (κ := κ) (ρL := ρL) (ρR := ρR) (a := a')
    (k := QuantumZipper.chiC κ) (vL := fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
    (vR := fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (hc' ω) (hWc ω) hE hvL hvR (hu ω)
  have hkey' : (∫ z, (couplingMean κ (fun s : ℝ => segDriver (γ' ω) s.toNNReal) (t : ℝ) (u ω) ((c' ω).1 z) - a' -
      QuantumZipper.chiC κ * (c' ω).2.2 z) * φ z) =
      Lemma71D.chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
        (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
        (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
        (QuantumZipper.chiC κ) φ t := hkey
  rw [hkey', Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have hr : Ito.rpath (fun s => segDriver (γ' ω) s) = fun s : ℝ => segDriver (γ' ω) s.toNNReal := rfl
  simp only [chartVar, hr]
  push_cast
  ring

-- mirrored from `Sec7.Lemma71MData.isChartCouplingCharFunConst_of_primeEnd_ind`
/-- **The fixed-time chart coupling clause from the prime-end premise**, B4 in indicator form
(`Lemma71L.isChartCouplingCharFunConst_of_primeEnd` with the indicator forms). -/
theorem isChartCouplingCharFunConst_of_primeEnd_three [IsProbabilityMeasure P]
    (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {c' : Ω → Chart} (hc'1 : ∀ ω, (c' ω).1 = (c ω).1)
    (hc'2 : ∀ ω, (c' ω).2.1 = (c ω).2.1) {ρL ρR : Fin 1 → ℝ} {a' : ℝ}
    (hmeas : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens),
      MeasurableSet[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t} ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          fun ω => Lemma71D.chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
          (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
          (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
          (QuantumZipper.chiC κ) φ t) ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t}.indicator
          fun ω => chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t))
    (hP : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∃ gS gL gT : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)))
        (WholeField.centredField h u₀) P gS ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
        (WholeField.centredField h u₀) P gT ∧
      ∀ᵐ ω ∂P, IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (c' ω) φ t →
        PocketPrimeEnd (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
          (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) u₀
          (QuantumZipper.chiC κ) φ
          ((c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t))
          (Lemma71D.chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (c' ω) a'
            (QuantumZipper.chiC κ) φ t)) :
    IsChartCouplingCharFunConst κ ρL ρR P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω)) c' a'
      (QuantumZipper.chiC κ) h := by
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, -, -, hseg, -, -⟩ := hpc'
  have hS' := hS
  obtain ⟨-, -, -, -, -, hγ62, -⟩ := hS'
  have hc' : ∀ ω, (c' ω).IsConformal := fun ω => by
    have := hconf ω
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · rw [hc'2]; exact this.1
    · rw [hc'2]; exact this.2.1
    · rw [hc'1, hc'2]; exact this.2.2 w hw
  refine isChartCouplingCharFunConst_of_premise_three hS hpc hG hM hY hMiff hGeq hYeq hc' hmeas fun t φ => ?_
  obtain ⟨gS, gL, gT, hgS, hgL, hgT, hpr⟩ := hP t φ
  refine ⟨gS, gL, gT, hgS, hgL, hgT, ?_⟩
  filter_upwards [hpr, ae_pocketGood_three hS hpc] with ω hω hg hE
  have hΓ := hseg ω
  have hD := IsSegCurve.fwdHull_segDriver_eq hΓ (NNReal.coe_nonneg t)
    (by rw [ENNReal.ofReal_coe_nnreal]; exact hE.1)
  -- a point of the chart domain
  obtain ⟨R, hR, hKR⟩ := hD.2.exists_subset_ball
  set w₀ : ℂ := ((R + 1 : ℝ) : ℂ) * I with hw₀
  have hw₀H : w₀ ∈ H := by
    show (0 : ℝ) < (((R + 1 : ℝ) : ℂ) * I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_zero,
      add_zero, mul_one]
    linarith
  have hw₀K : w₀ ∉ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t := by
    rw [hD.1]
    intro hw
    have := mem_ball_zero_iff.1 (hKR hw)
    rw [hw₀, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      at this
    linarith
  have hz₀ : (c ω).2.1 w₀ ∈ (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t) :=
    ⟨w₀, ⟨hw₀H, hw₀K⟩, rfl⟩
  obtain ⟨hz₀A, hcomp⟩ := connectedComponentIn_eq_image hg (hC ω).1 (hC ω).2.2.2 (hconf ω) (hdom ω)
    (fun s => hγ62.2.2.1 ω s) (hγ62.1 ω) (hγ62.2.1 ω) hΓ (hMiff ω) (hGeq ω) (hYeq ω) hE.1 hz₀
  have hφ : tsupport φ ⊆ (c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t) := by
    have := hE.2
    rw [hc'2] at this
    exact this
  have hV : chartVar (fun s => segDriver (γ' ω) s) (c' ω) φ t = QuantumZipper.zeroGFFTestCov
      ((c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t)) φ φ := by
    simp only [chartVar, hc'2]
    rfl
  rw [hV]
  exact isThreeChartPremise_of_pocketPrimeEnd hz₀A hcomp hφ (hω hE)

-- mirrored from `Sec7.Lemma71MData.measurable_chartAvoid_pocket`
/-- **B4 for the pocket construction**: the avoidance event at `t` is in the prefix filtration at `t`, and the chart
mean and the chart variance on it are measurable for it (charts `shiftLift (c ω) (n ω)`, `n` `σ(β, α)`-measurable). -/
theorem measurable_chartAvoid_pocket_three (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) (ρL ρR : Fin 1 → ℝ)
    (a' : ℝ) (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] {ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (shiftLift (c ω) (n ω)) φ t} ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (shiftLift (c ω) (n ω)) φ t}.indicator
          fun ω => Lemma71D.chartMean κ ρL ρR (fun s => segDriver (γ' ω) s)
          (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
          (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (shiftLift (c ω) (n ω)) a'
          (QuantumZipper.chiC κ) φ t) ∧
      Measurable[prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
        γ' t] ({ω | IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (shiftLift (c ω) (n ω)) φ t}.indicator
          fun ω => chartVar (fun s => segDriver (γ' ω) s) (shiftLift (c ω) (n ω)) φ t) := by
  obtain ⟨hC, hCm, hconf, hdom, hfm, hlm, hlc, -, -, -, hseg, hγ'm, -⟩ := hpc
  obtain ⟨-, -, -, hβ62, hα62, hγ62, -⟩ := hS
  have hβm : Measurable β := measurable_pi_iff.2 hβ62.2.2.2.1
  have hαm : Measurable α := measurable_pi_iff.2 hα62.2.2.2.1
  have hγm : Measurable γ := measurable_pi_iff.2 hγ62.2.2.2.1
  have h₀ : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ mΩ := (hβm.prodMk hαm).comap_le
  have h𝓑 : MeasurableSpace.comap β MeasurableSpace.pi ⊔ MeasurableSpace.comap α MeasurableSpace.pi ⊔
      MeasurableSpace.comap γ MeasurableSpace.pi ⊔ Ito.nullSets P ≤ mΩ :=
    sup_le (sup_le (sup_le hβm.comap_le hαm.comap_le) hγm.comap_le) (Ito.nullSets_le P)
  have hγ'mΩ : ∀ u, Measurable fun ω => γ' ω u := fun u => (hγ'm u).mono h𝓑 le_rfl
  have hpm : ∀ r n k, MeasurableSet (prefixEvent γ' r n k) := fun r n k =>
    measurableSet_prefixEvent hseg (fun u _ => hγ'mΩ u) r n k
  have hpre : IsPrefixAdapted (prefixFiltrationOf (mΩ := mΩ)
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') γ' :=
    isPrefixAdapted_prefixFiltrationOf _ γ' hpm
  have hWa := adaptedBefore_segDriver hseg hpre
  have hc : ∀ ω, ContinuousOn (fun s => segDriver (γ' ω) s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ' ω)} :=
    fun ω => (hseg ω).segDriver_spec.2.1
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (hC ω).1
  have hdomm : ∀ z, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | z ∈ (c ω).dom} := fun z => by
    have e : {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := by
      ext ω
      show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
      rw [hdom ω]
    rw [e]
    exact @Lemma71E.measurableSet_mem_of_closedBall Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) C hCo hCm z
  exact measurable_chartAvoid (c := fun ω => shiftLift (c ω) (n ω)) κ ρL ρR a' (QuantumZipper.chiC κ) hWa hc
    (fun i => adaptedBefore_geomL hc hWa LP.twoSeedXL i) (fun i => adaptedBefore_geomR hc hWa LP.twoSeedXR i) t
    (le_prefixFiltrationOf h₀ γ' t) hCo hCm (fun ω => isConformal_shiftLift (hconf ω) (n ω)) hdom hfm
    (fun z => @measurable_indicator_shiftLift Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) c n hn
      z (hdomm z) (hlm z))
    (fun ω => continuousOn_shiftLift (hlc ω) (n ω)) φ

-- mirrored from `Sec7.Lemma71KData.isPocketChartData_of_isPocketConstruction`
/-- **`IsPocketChartData` from the pocket construction and the fixed-time chart coupling clause.** On a three-curve
space, for a pocket construction `(C, c, γ')` (`IsPocketConstruction`) and a `σ(β, α)`-measurable branch shift `n`, if
the chart coupling clause holds at fixed times for the prefix filtration of `σ(β, α)` and `γ'`, with the chart lift
shifted by `2πn`, then `IsPocketChartData` holds for the usual augmentation of that filtration, the capacity driver of
`γ'` and its capacity lifetime, including (S1)–(S3). Conditional helper. -/
theorem isChamberChartData_of_isPocketConstruction [IsProbabilityMeasure P]
    (hS : IsThreeLineSpace P h u₀ β α γ) {C : Ω → Set ℂ} {c : Ω → Chart}
    {γ' : Ω → ℝ → ℂ} (hpc : IsPocketConstruction P β α γ C c γ') {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' k : ℝ}
    (hcf : IsChartCouplingCharFunConst κ ρL ρR P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => shiftLift (c ω) (n ω)) a' k h) :
    IsChamberChartData κ ρL ρR P β α γ h
      (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
      γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) (fun ω => shiftLift (c ω) (n ω)) a' k := by
  obtain ⟨hC, hCm, hconf, hdom, hfm, hlm, hlc, -, -, hfr, hseg, hγ'm, -⟩ := hpc
  have hh : Measurable h := hS.1
  obtain ⟨-, -, -, hβ62, hα62, hγ62, -⟩ := hS
  have hβm : Measurable β := measurable_pi_iff.2 hβ62.2.2.2.1
  have hαm : Measurable α := measurable_pi_iff.2 hα62.2.2.2.1
  have hγm : Measurable γ := measurable_pi_iff.2 hγ62.2.2.2.1
  have h₀ : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ mΩ := (hβm.prodMk hαm).comap_le
  have h𝓑 : MeasurableSpace.comap β MeasurableSpace.pi ⊔ MeasurableSpace.comap α MeasurableSpace.pi ⊔
      MeasurableSpace.comap γ MeasurableSpace.pi ⊔ Ito.nullSets P ≤ mΩ :=
    sup_le (sup_le (sup_le hβm.comap_le hαm.comap_le) hγm.comap_le) (Ito.nullSets_le P)
  have hγ'mΩ : ∀ u, Measurable fun ω => γ' ω u := fun u => (hγ'm u).mono h𝓑 le_rfl
  have hpm : ∀ r n k, MeasurableSet (prefixEvent γ' r n k) := fun r n k =>
    measurableSet_prefixEvent hseg (fun u _ => hγ'mΩ u) r n k
  set 𝓐 := prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' with h𝓐def
  have hpre : IsPrefixAdapted 𝓐 γ' := isPrefixAdapted_prefixFiltrationOf _ γ' hpm
  have hle := Ito.le_usualAugmentation 𝓐 P
  have h𝓐₀ : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ usualAugmentation 𝓐 P 0 :=
    (le_prefixFiltrationOf h₀ γ' 0).trans (hle 0)
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (hC ω).1
  have hdomm : ∀ z, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | z ∈ (c ω).dom} := fun z => by
    have e : {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := by
      ext ω
      show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
      rw [hdom ω]
    rw [e]
    exact @Lemma71E.measurableSet_mem_of_closedBall Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) C hCo hCm z
  have hlm' : ∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (shiftLift (c ω) (n ω)).dom}.indicator fun ω => (shiftLift (c ω) (n ω)).2.2 z) := fun z =>
    @measurable_indicator_shiftLift Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) c n hn z
      (hdomm z) (hlm z)
  have hcc : ∀ ω, (shiftLift (c ω) (n ω)).IsConformal := fun ω => isConformal_shiftLift (hconf ω) (n ω)
  have hlc' : ∀ ω, ContinuousOn (shiftLift (c ω) (n ω)).2.2 (shiftLift (c ω) (n ω)).dom := fun ω =>
    continuousOn_shiftLift (hlc ω) (n ω)
  have hc : ∀ ω, ContinuousOn (fun s => segDriver (γ' ω) s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ' ω)} :=
    fun ω => (hseg ω).segDriver_spec.2.1
  refine ⟨Ito.isRightContinuous_usualAugmentation 𝓐 P,
    fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0, Eventually.of_forall fun ω => hseg ω,
    fun ω => (hseg ω).segDriver_spec.1, hc, adaptedBefore_segDriver hseg fun r n j => hle r _ (hpre r n j),
    Eventually.of_forall fun ω => (hseg ω).segDriver_spec.2.2, hh, hcc, fun z => h𝓐₀ _ (hdomm z),
    fun z => (hfm z).mono h𝓐₀ le_rfl, fun z => (hlm' z).mono h𝓐₀ le_rfl, hlc', ?_, fun z r => ?_, hfm, hlm', ?_,
    ?_⟩
  · exact isChartCouplingCharFun_usualAugmentation hh hcc hlc' hc
      (fun i ω => continuousOn_geomL hc LP.twoSeedXL i ω) (fun i ω => continuousOn_geomR hc LP.twoSeedXR i ω)
      (fun ω t ht => geomL_le_le_geomR hc LP.twoSeedXL LP.twoSeedXR ht) hcf
  · have e : {ω | closedBall z r ⊆ ((shiftLift (c ω) (n ω)).dom : Set ℂ)} = {ω | closedBall z r ⊆ C ω} := by
      ext ω
      show closedBall z r ⊆ ((c ω).dom : Set ℂ) ↔ _
      rw [hdom ω]
      exact Iff.rfl
    rw [e]
    exact hCm z r
  · filter_upwards [hfr] with ω hω
    show frontier ((c ω).dom : Set ℂ) ∩ H ⊆ _
    rw [hdom ω]
    exact hω
  · intro t
    exact (usualAugmentation_prefixFiltrationOf_le (P := P) ((comap_pair_le β α γ).trans le_sup_left) hseg hγ'm
      t).trans (sup_le le_rfl le_sup_right)

/-- **The fixed-time chamber clause from the prime-end premise** (the clause inside
`isChamberChartData_of_pocketPrimeEnd`,
in the filtration of the walls and the mapped middle prefix, at every deterministic capacity time `t` on the event
`{t < capLife}`). -/
theorem isChartCouplingCharFunConst_of_pocketPrimeEnd_three [IsProbabilityMeasure P]
    (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' : ℝ}
    (hP : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∃ gS gL gT : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)))
        (WholeField.centredField h u₀) P gS ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
        (WholeField.centredField h u₀) P gT ∧
      ∀ᵐ ω ∂P, IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (shiftLift (c ω) (n ω)) φ t →
        PocketPrimeEnd (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
          (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) u₀
          (QuantumZipper.chiC κ) φ
          ((c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t))
          (Lemma71D.chartMean κ ρL ρR
            (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (shiftLift (c ω) (n ω)) a'
            (QuantumZipper.chiC κ) φ t)) :
    IsChartCouplingCharFunConst κ ρL ρR P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => shiftLift (c ω) (n ω)) a' (QuantumZipper.chiC κ) h :=
  isChartCouplingCharFunConst_of_primeEnd_three hS hpc hG hM hY hMiff hGeq hYeq
    (c' := fun ω => shiftLift (c ω) (n ω)) (fun _ => rfl) (fun _ => rfl)
    (measurable_chartAvoid_pocket_three hS hpc hn _ _ a') hP

-- mirrored from `Sec7.Lemma71MData.isPocketChartData_of_pocketPrimeEnd`
/-- **`IsPocketChartData` from the prime-end premise P alone.** On every three-curve space with the pocket
construction of PROVE-LEMMA71K (`G`, `M`, `Y` from `Lemma71L.exists_capData`) and a `σ(β, α)`-measurable branch
shift `n`, the prime-end premise P for the charts `shiftLift (c ω) (n ω)` gives `IsChamberChartData` (chart
`shiftLift (c ω) (n ω)`, `k = χ`): B4 is `measurable_chartAvoid_pocket`. Conditional helper (on P). -/
theorem isChamberChartData_of_pocketPrimeEnd [IsProbabilityMeasure P]
    (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' : ℝ}
    (hP : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∃ gS gL gT : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)))
        (WholeField.centredField h u₀) P gS ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL ∧
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
        (WholeField.centredField h u₀) P gT ∧
      ∀ᵐ ω ∂P, IsChartAvoid (fun s => segDriver (γ' ω) s) (capLife (γ' ω)) (shiftLift (c ω) (n ω)) φ t →
        PocketPrimeEnd (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
          (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) u₀
          (QuantumZipper.chiC κ) φ
          ((c ω).2.1 '' (H \ QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ' ω) r.toNNReal) t))
          (Lemma71D.chartMean κ ρL ρR
            (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) (shiftLift (c ω) (n ω)) a'
            (QuantumZipper.chiC κ) φ t)) :
    IsChamberChartData κ ρL ρR P β α γ h
      (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
      γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) (fun ω => shiftLift (c ω) (n ω)) a'
      (QuantumZipper.chiC κ) :=
  isChamberChartData_of_isPocketConstruction hS hpc hn
    (isChartCouplingCharFunConst_of_pocketPrimeEnd_three hS hpc hG hM hY hMiff hGeq hYeq hn hP)

-- mirrored from `Sec7.Lemma71MMain.isPocketChartData_of_sideLimit` (the fixed-time clause inside it)
/-- **The fixed-time chamber clause from the side limits of the active component** (the clause inside
`isChamberChartData_of_sideLimit`; at every deterministic capacity time on the event `{t < capLife}`). -/
theorem isChartCouplingCharFunConst_of_sideLimit_three [IsProbabilityMeasure P]
    (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' : ℝ}
    (hside : ∀ (t : ℝ≥0) (gL gT : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
        (WholeField.centredField h u₀) P gT →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL vT : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
        InnerProductSpace.HarmonicOnNhd vT
          (H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω →
            gT ω ψ = ∫ x, vT x * ψ x) →
        ∃ Ex : Set ℝ, Ex.Finite ∧
          PocketSideLimit (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
            (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
            (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) vL vT u₀
            (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t)
            (pocketGl κ ρL ρR
              (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s)
              (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
              (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t a') Ex) :
    IsChartCouplingCharFunConst κ ρL ρR P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => shiftLift (c ω) (n ω)) a' (QuantumZipper.chiC κ) h := by
  refine isChartCouplingCharFunConst_of_pocketPrimeEnd_three hS hpc hG hM hY hMiff hGeq hYeq hn fun t φ => ?_
  have hS' := hS
  obtain ⟨-, -, hh0, hβ62, hα62, hγ62, -⟩ := hS'
  have hpc' := hpc
  obtain ⟨-, -, hconf, hdom, -, -, -, hlift, -, -, hseg, -, -⟩ := hpc'
  obtain ⟨hc, h0, -, hηm, hdet, hloc, htr⟩ := IsLemma62Curve.three hβ62 hα62 hγ62
  -- the stopped union
  have hSm := measurable_capStop hG hM hY t
  have hSg := capStop_galmarino (G := G) (M := M) (Y := Y) t
  have hτ : ∀ ω, capTime G M Y β α γ t ω = capStop G M Y t (histOf (pathCoord (β ω)) ⊤)
      (histOf (pathCoord (α ω)) ⊤) (pathCoord (γ ω)) := fun _ => rfl
  have hstopsS : ∀ i, Measurable (Three.threeStops (capTime G M Y β α γ t) i) :=
    measurable_of_galmarino hηm (Three.measurable_threeRule hSm) (Three.isGalmarino_threeRule hSg)
      (Three.threeStops_eq_threeRule hτ)
  have hlocS := isLocalSet_explored_of_tendsto hh0 hc h0 hηm hdet hloc htr (Three.measurable_threeRule hSm)
    (Three.isGalmarino_threeRule hSg) (Three.threeStops_eq_threeRule hτ)
  obtain ⟨gS, hgS⟩ := IsLocalSet.exists_isLocalSetMean hh0 (measurable_explored hc hηm hstopsS) hlocS
  -- the complete three curves
  have hlocL := isLocalSet_explored_of_tendsto (τ := fun _ _ => ⊤) (S := fun _ _ _ => ⊤) hh0 hc h0 hηm hdet hloc
    htr (fun _ => measurable_const) (fun _ => isGalmarino_const ⊤) (fun _ _ => rfl)
  obtain ⟨gL, hgL⟩ := IsLocalSet.exists_isLocalSetMean hh0
    (measurable_explored hc hηm fun _ => measurable_const) hlocL
  -- the complete outer curves
  have hlocT := isLocalSet_explored_of_tendsto (τ := fun i _ => Three.outerStops i)
    (S := fun j _ _ => Three.outerStops j) hh0 hc h0 hηm hdet hloc htr (fun _ => measurable_const)
    (fun j => isGalmarino_const (Three.outerStops j)) (fun _ _ => rfl)
  obtain ⟨gT, hgT⟩ := IsLocalSet.exists_isLocalSetMean hh0
    (measurable_explored hc hηm fun _ => measurable_const) hlocT
  refine ⟨gS, gL, gT, hgS, hgL, hgT, ?_⟩
  filter_upwards [hgS.2.1, hgL.2.1, hgT.2.1, hside t gL gT hgL hgT] with ω ⟨v, hv, hgv⟩ ⟨vL, hvL, hgvL⟩
    ⟨vT, hvT, hgvT⟩ hsd hE
  obtain ⟨Ex, hEx, hsl⟩ := hsd hE.1 vL vT hvL hgvL hvT hgvT
  have hWc : ∀ ω', ContinuousOn (fun s => segDriver (γ' ω') s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ' ω')} :=
    fun ω' => (hseg ω').segDriver_spec.2.1
  obtain ⟨hvLt, hvRt⟩ := geomL_le_le_geomR (W := fun s ω => segDriver (γ' ω) s) (T := fun ω => capLife (γ' ω))
    hWc LP.twoSeedXL LP.twoSeedXR hE.1
  obtain ⟨Lg, hLg, hLe⟩ := exists_isDerivLog_shiftLift (hdom ω) (hlift ω) (n ω)
  exact pocketPrimeEnd_of_sideLimit φ (isConformal_shiftLift (hconf ω) (n ω)) hLg hLe (hWc ω)
    (hseg ω).segDriver_spec.1 hE.1 κ _ _ hvLt hvRt a' hv hgv hvL hgvL hvT hgvT hEx hsl

-- mirrored from `Sec7.Lemma71MMain.isPocketChartData_of_sideLimit`
/-- **`IsPocketChartData` from the side limits of the active component.** On every three-curve space with the
pocket construction of PROVE-LEMMA71K (`G`, `M`, `Y` from `Lemma71L.exists_capData`) and a `σ(β, α)`-measurable
branch shift `n`: if, at every fixed capacity time `t`, for every version `gL`, `gT` of the local-set means of the
complete three curves and of the complete outer curves, almost surely on `{t < capLife}` and for all their harmonic
representatives `vL`, `vT`, the active component has side limits (`PocketSideLimit`) outside a finite set with the
chart-side function `pocketGl` of the shifted chart, then `IsChamberChartData` holds (chart
`shiftLift (c ω) (n ω)`, `k = χ`). Conditional helper (on the side limits). -/
theorem isChamberChartData_of_sideLimit [IsProbabilityMeasure P]
    (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' : ℝ}
    (hside : ∀ (t : ℝ≥0) (gL gT : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
        (WholeField.centredField h u₀) P gT →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL vT : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
        InnerProductSpace.HarmonicOnNhd vT
          (H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω →
            gT ω ψ = ∫ x, vT x * ψ x) →
        ∃ Ex : Set ℝ, Ex.Finite ∧
          PocketSideLimit (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
            (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
            (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) vL vT u₀
            (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t)
            (pocketGl κ ρL ρR
              (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s)
              (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
              (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t a') Ex) :
    IsChamberChartData κ ρL ρR P β α γ h
      (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
      γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) (fun ω => shiftLift (c ω) (n ω)) a'
      (QuantumZipper.chiC κ) :=
  isChamberChartData_of_isPocketConstruction hS hpc hn
    (isChartCouplingCharFunConst_of_sideLimit_three hS hpc hG hM hY hMiff hGeq hYeq hn hside)

end Main

end InteractingSLE.WangWu.SeedThree
