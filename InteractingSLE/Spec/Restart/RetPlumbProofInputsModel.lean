/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofInputsFiltration

/-!
# Constructing the conditional stopped model on a standard Borel source

Packet PROVE-RETPLUMB. This construction uses the identity reader: it requires
neither a new realization nor a new law-transport assumption. Stochastic inputs
are required only on the conditioning event. The all-sample regularity inputs
remain explicit; in particular this does not assert regularity of an arbitrary
choice of a post-lifetime driver extension.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open LQGMetric (DistOn TestOn)
open Sec2.Assembly Sec7.PocketTraversal Supp7 DomainMarkov DomainMarkov.K2 DomainMarkov.Aux79 FCDet

/-- The stopped geometric driving process is measurable from the already needed
driver adaptedness, initial force coordinates, and lifetime stopping property.
Thus it is not an independent model-construction input. -/
theorem isMeasurableKilledDriving_geom {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓗 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    {V : Ω → ℝ≥0∞} (hWa : StronglyAdapted 𝓗 W)
    (hWc : ∀ ω, Continuous fun t => W t ω)
    (hxL : Measurable[𝓗 0] xL) (hxR : Measurable[𝓗 0] xR)
    (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t}) :
    IsMeasurableKilledDriving W (geomLW W xL) (geomRW W xR) V :=
  Coupling.isMeasurableKilledDriving_of_adaptedBefore
    (MartChar.adaptedBefore_of_stronglyAdapted hVs hWa)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hVs
      (stronglyAdapted_geomLW hWa hWc hxL i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hVs
      (stronglyAdapted_geomRW hWa hWc hxR j))

variable {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- On a nonnull initial event of a standard Borel source, all model-construction
and law-transport obligations are consequences of the displayed stochastic
inputs. Integrability is required only on the unnormalized restriction. -/
def stoppedModelTransfer_cond {κ θ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓗 : Filtration ℝ≥0 mΩ}
    {M : Set Ω} (hM : MeasurableSet[𝓗 0] M) (hPM : P M ≠ 0)
    {c : Ω → BoundaryWord} (hc : Measurable[𝓗 0] c)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : Measurable[𝓗 0] xL) (hxR : Measurable[𝓗 0] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j)
    (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω))
    (htype : ∀ᵐ ω ∂P, ω ∈ M → IsFlowType κ θ (c ω) (xL ω) (xR ω) ρL ρR)
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓗 W)
    {Hc X : Ω → DistOn upperHalfPlaneOpens}
    (hHc : Measurable Hc) (hX : Measurable X)
    (hshift : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) (P.restrict M))
    {V : Ω → ℝ≥0∞}
    (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t})
    (hV0 : ∀ᵐ ω ∂P, ω ∈ M → 0 < V ω)
    (hVthr : ∀ᵐ ω ∂P, ω ∈ M → V ω ≤ thr ρL ρR W xL xR ω)
    {T : ℕ → Ω → ℝ≥0}
    (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓗 P) P V T)
    {σ : ℕ → Ω → WithTop ℝ≥0}
    (hσ : ∀ n, IsStoppingTime
      (drivingFiltration P (isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs)) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω)
    (hσlt : ∀ᵐ ω ∂P, ω ∈ M → ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂P, ω ∈ M →
      Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    (hS : HasSafeLaw κ ρL ρR P 𝓗 M V W (geomLW W xL) (geomRW W xR) X)
    (hL : HasSafeMembers P 𝓗 M V W X)
    {γ : Ω → ℝ≥0 → ℂ} (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ V ω})
    (hγg : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (fun t => W t ω) (V ω) (γ ω)) :
    StoppedModelTransfer κ θ P M c Hc V γ := by
  have hMm : MeasurableSet M := 𝓗.le 0 _ hM
  let hXP := isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs
  let _ : IsProbabilityMeasure (P[|M]) := cond_isProbabilityMeasure hPM
  let D : StoppedTypeData Ω P[|M] κ θ := {
    nL := nL
    nR := nR
    rhoL := ρL
    rhoR := ρR
    filt := 𝓗
    word := c
    wordMeas := hc
    xL := xL
    xR := xR
    xLMeas := hxL
    xRMeas := hxR
    xLNonpos := hxL0
    xRNonneg := hxR0
    xLAnti := hxLa
    xRMono := hxRm
    typed := FCDet.ae_cond_of_ae_imp hMm htype
    driver := W
    driverZero := hW0
    driverCont := hWc
    driverAdapted := hWa
    field := Hc
    shiftedField := X
    fieldMeas := hHc
    shiftedMeas := hX
    shifted := hshift
    integrable := fun φ => by
      rw [ProbabilityTheory.cond]
      exact (hint φ).smul_measure (ENNReal.inv_ne_top.2 hPM)
    life := V
    lifeStop := hVs
    lifePos := FCDet.ae_cond_of_ae_imp hMm hV0
    lifeThreshold := FCDet.ae_cond_of_ae_imp hMm hVthr
    announce := T
    announcing := isAnnouncingSeq_usualAugmentation_cond M hT
    killedMeas := hXP
    driveStops := σ
    driveStopping := fun n t =>
      drivingFiltration_le_of_absolutelyContinuous hXP cond_absolutelyContinuous t _ (hσ n t)
    driveMono := hσm
    driveLt := FCDet.ae_cond_of_ae_imp hMm hσlt
    driveLimit := FCDet.ae_cond_of_ae_imp hMm hσlim
    safeLaw := hasSafeLaw_cond hM hS
    safeMembers := hasSafeMembers_cond hM hL
    trace := γ
    traceMeas := hγm
    traceCont := hγc
    generates := FCDet.ae_cond_of_ae_imp hMm hγg }
  exact {
    model := {
      space := Ω
      sigma := mΩ
      borel := inferInstance
      law := P[|M]
      probability := inferInstance
      data := D }
    read := id
    readMeas := measurable_id
    mapLaw := Measure.map_id
    agrees := Eventually.of_forall fun _ _ => ⟨rfl, rfl, rfl, fun _ _ => rfl⟩ }

end InteractingSLE.Restart.RetAux79
