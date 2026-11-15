/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalAnnounce
import InteractingSLE.Spec.Restart.RetPlumbProofFinalTrace

/-!
# Conditional models using the retained R1 Gaussian law

Packet PROVE-RETPLUMB. The Gaussian conditioning sigma algebra can be the
larger germ sigma algebra supplied by R1. It need not be the capacity sigma
algebra at zero. Noncollision is supplied for the actual retained word by
`retPrelifeNonThreshold_of_retWordAt`.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open LQGMetric (DistOn TestOn)
open Sec2.Assembly Sec7.PocketTraversal Supp7 DomainMarkov DomainMarkov.K2 FCDet
variable {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The R1 pairing law on any conditioning sigma algebra supplies the conditional
model, once the boundary lifetime is announced in its killed driving filtration. -/
def stoppedModelTransfer_cond_of_gaussianLaw {κ θ : ℝ} {nL nR : ℕ}
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
    (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (hg : RetInitialPairingGaussian P 𝒢.1 M X)
    {V : Ω → ℝ≥0∞}
    (hVs : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t})
    (hV0 : ∀ᵐ ω ∂P, ω ∈ M → 0 < V ω)
    (hn : RetPrelifeNonThreshold (P := P) ρL ρR W xL xR V M)
    (hp : RetDrivingLifetimePredictable (P[|M])
      (isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs))
    (hS : HasSafeLaw κ ρL ρR P 𝓗 M V W (geomLW W xL) (geomRW W xR) X)
    (hL : HasSafeMembers P 𝓗 M V W X)
    {γ : Ω → ℝ≥0 → ℂ} (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ V ω})
    (hγg : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (fun t => W t ω) (V ω) (γ ω)) :
    StoppedModelTransfer κ θ P M c Hc V γ := by
  have hMm : MeasurableSet M := 𝓗.le 0 _ hM
  let hXP := isMeasurableKilledDriving_geom hWa hWc hxL hxR hVs
  let _ : IsProbabilityMeasure (P[|M]) := cond_isProbabilityMeasure hPM
  have hint := integrable_restrict_of_retInitialPairingGaussian hMm hg
  have hVthr := life_le_thr_of_retPrelifeNonThreshold hWc hn
  let hs := exists_stoppedK2_sequences (P := P[|M]) hWa hWc hxL hxR hVs hp
  let T := Classical.choose hs
  obtain ⟨hT, hσ, hσm, hσlt, hσlim⟩ := Classical.choose_spec hs
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
    announcing := hT
    killedMeas := hXP
    driveStops := fun n ω => (T n ω : WithTop ℝ≥0)
    driveStopping := hσ
    driveMono := hσm
    driveLt := hσlt
    driveLimit := hσlim
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
