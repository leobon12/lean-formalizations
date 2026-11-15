/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.RefWireAux131

/-!
# Aux. 131 after discharging the marked walls laws and the walls record

PROVE-REF-WIRE. The conull lifetime is retained by the selector. The marked
stop construction supplies both walls laws. The only field inputs left beyond
the frozen counterflow coupling and determined-local walls are the two-seed
side limits and Proposition 5.13. The path geometry is stated separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.RefWire

open WangWu WholeField Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly
  PocketSeedOpen PocketStopField PocketStopWallsFin PocketStopWalls PocketCoupling StripPocketConfig
  PocketWordPerQ PocketStop R7Aux131 R7Pocket

/-- The exact remaining two-seed side limits, with a single branch and phase for every relative time. -/
def TwoSeedSideInput {Ω : Type*} (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAll R L r η ψ)
            (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
            (activeCompl A (travAll R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q

/-- The exact remaining two-seed side limits, with a single branch and phase for every relative time. -/
def TwoSeedSideInputInf {Ω : Type*} (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A (travAllInf R L r η ψ)
            (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
            (activeCompl A (travAllInf R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q

/-- Aux. 131's reference with the record and marked walls laws constructed internally.
The two-seed side limits are required only on configuration events satisfying the retained lifetime. -/
theorem r7PocketStopStatement_of_sideLimit.{u} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {η : Ω → ℝ → ℂ} (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hL : ∀ᵐ ω ∂P, IsSimpleProper (L ω) ∧ IsWallReverseVisit (L ω) (η ω))
    (hne : ∀ᵐ ω ∂P, range (L ω) ≠ range (R ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))))
    (htrace : ∀ᵐ ω ∂P, IsLoewnerTrace (fun s : ℝ => W' s.toNNReal ω) (η ω) ∧
      Continuous (fun s : ℝ => W' s.toNNReal ω) ∧ W' 0 ω = 0)
    (hattach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcR (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0)))
    (hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (L ω) (η ω) ∧
        Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0)))

    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hside : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ' ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      TwoSeedSideInput κ rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u ∧
        TwoSeedSideInputInf κ rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => centredField h'' u₀' ω + smoothDist upperHalfPlaneOpens u) inferInstance]
        fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    R7PocketStopStatement.{u} κ rL rR GoodR7 := by
  have : StandardBorelSpace (ULift.{u} (Fin 2 → Sec6.Hist)) :=
    LQGMetric.standardBorelSpace_of_measurableEquiv MeasurableEquiv.ulift
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have hWeq : wallsSigma P R L ⊔ Ito.nullSets P = wallsSigma P R L :=
    sup_eq_left.2 le_sup_right
  refine r7PocketStopStatement_of_walls (𝓦 := wallsSigma P R L)
    (W := fun ω s => W' s.toNNReal ω) (Q := fun _ ω => ζ' ω = ⊤)
    (wallsSigma_le hRm hLm) hRm' hLm' hηm hηc hη0 hR hL hne hord
    (by simpa only [Real.toNNReal_zero] using htrace) hattach hattachI
    (isZeroBoundaryGFF_centredField hC hu₀') hu hub (fun _ _ => hζ) ?_ h513
    (measurable_wallRecord R L) (wallsSigma_le_wallRecord R L)
  intro q hq G hGm hPG hconf hζG hcfg hcfgI
  rw [hWeq] at hGm ⊢
  obtain ⟨hs, hsI⟩ := hside q hq G hGm hPG hconf hζG hcfg hcfgI
  have hGp : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)},
      IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  constructor
  · exact twoSeedWallsInput_of_sideLimit hT' hTr hu₀ hh hC hκ hu₀' hX hζ
      hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
      (wallsSigma_le_drivingFiltration hX R L) hRm' hLm' hGp
      (fun ω hω => hcfg ω hω.1 hω.2) (fun ω hω => hζG ω hω.1) u hs
  · exact twoSeedWallsInputInf_of_sideLimit hT' hTr hu₀ hh hC hκ hu₀' hX hζ
      hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR hlocL
      (wallsSigma_le_drivingFiltration hX R L) hRm' hLm' hG0 hcfgI'
      (fun ω hω => hζG ω hω.1) u hsI

end InteractingSLE.Sec7.RefWire
