/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.RefWirePerQ
import InteractingSLE.Spec.Sec7.PocketWordPerQSide

/-!
# Lemma 7.25's reference after discharging the marked walls laws

PROVE-REF-WIRE. The frozen optional coupling, determined-local incoming walls,
and the constructed marked stops supply both walls laws. The record is the
existing rational full history, lifted only to match the sample-space universe.
The exact side-limit inputs and counterflow determination remain hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.RefWire

open WangWu WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I
  PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop
  PocketStopWallsFin PocketStopMarked PocketLeftFrontier StripPocketConfig PocketWordPerQ

/-- Lemma 7.25's field reference with both marked walls laws discharged.
Only the selected pair is recorded; the side limits and Proposition 5.13 remain explicit. -/
theorem pocketChartFieldStatement_of_sideLimit_perQ.{u} {κ' rL rR : ℝ} (hκ' : 4 < κ')
    (hL : -2 < rL) (hLd : rL < κ' / 2 - 4) (hRr : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ q ω, Continuous (Lr q ω))
    (hR0 : ∀ ω, R ω 0 = 0) (hL0 : ∀ q ω, Lr q ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t) (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar)
    (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hLw : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧ IsWallReverseVisit (Lr q ω) (η ω) ∧
      Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hnohit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → η ω t ≠ 0)
    (hlate : ∀ᵐ ω ∂P, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ β ω t ∉ range (R ω))
    (htrace : ∀ᵐ ω ∂P, IsLoewnerTrace (fun s : ℝ => W' s.toNNReal ω) (η ω) ∧
      Continuous (fun s : ℝ => W' s.toNNReal ω) ∧ W' 0 ω = 0)
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
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ q t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Lr q ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : ∀ q, Sec6.IsEntranceHistoryLocal (Lr q) (centredField h u₀) P)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hside : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R (Lr q)] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ' ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q) →
        IsCfPocketConfig (R ω) (Lr q ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (Lr q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (R ω) (Lr q ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
      PocketSideLimitInput0 (16 / κ') rL rR (wallsSigma P R (Lr q)) P R (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} (centredField h'' u₀') u ∧
        PocketSideLimitInputInf0 (16 / κ') rL rR (wallsSigma P R (Lr q)) P R (Lr q) (StripSys.rt q) η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} (centredField h'' u₀') u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => centredField h'' u₀' ω + smoothDist upperHalfPlaneOpens u) inferInstance]
        fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    Lemma725RefSafe.PocketChartFieldStatement.{u} κ' rL rR := by
  have : StandardBorelSpace (ULift.{u} (Fin 2 → Sec6.Hist)) :=
    LQGMetric.standardBorelSpace_of_measurableEquiv MeasurableEquiv.ulift
  have hRm' := fun q t => measurable_right_wallsSigma (P := P) hRc (hLc q) t
  have hLm' := fun q t => measurable_left_wallsSigma (P := P) hRc (hLc q) t
  refine pocketChartFieldStatement_of_walls_perQ (𝓦 := fun q => wallsSigma P R (Lr q))
    (W := fun ω s => W' s.toNNReal ω) (Q := fun _ ω => ζ' ω = ⊤) hκ' hL hLd hRr hRd
    (fun q => wallsSigma_le hRm (hLm q)) (fun _ => le_sup_right) hRm' hLm' hβm hηm hηc hηH hη0 hR hβ hLw
    hnohit hlate (by simpa only [Real.toNNReal_zero] using htrace) hav hattach hattachI
    (isZeroBoundaryGFF_centredField hC hu₀') hu hub
    (fun _ _ => hζ) ?_ h513 (fun q => measurable_wallRecord R (Lr q))
    (fun q => wallsSigma_le_wallRecord R (Lr q))
  intro q hq G hGm hPG hconf hζG hcfg hcfgI
  obtain ⟨hs, hsI⟩ := hside q hq G hGm hPG hconf hζG hcfg hcfgI
  have hGp : MeasurableSet[wallsSigma P R (Lr q)]
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R (Lr q)) (hRm' q) (hLm' q) hGm
      (fun ω hω => (hconf ω hω).1)).1
  have hG0 : MeasurableSet[wallsSigma P R (Lr q)]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)},
      IsCfPocketConfigInf (R ω) (Lr q ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω) := by
    intro ω hω
    exact hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).1.changeCorner_props.1.1))
  constructor
  · exact pocketStopWallsInput0_of_sideLimit hT' hTr hu₀ hh hC (by linarith only [hκ']) hu₀' hX hζ
      hRc (hLc q) hR0 (hL0 q) hRm (hLm q) hdetR (hdetL q) hlocR (hlocL q)
      (wallsSigma_le_drivingFiltration hX R (Lr q)) (hRm' q) (hLm' q) hGp
      (fun ω hω => hcfg ω hω.1 hω.2) (fun ω hω => hζG ω hω.1) u hs
  · exact pocketStopWallsInputInf0_of_sideLimit hT' hTr hu₀ hh hC (by linarith only [hκ']) hu₀' hX hζ
      hRc (hLc q) hR0 (hL0 q) hRm (hLm q) hdetR (hdetL q) hlocR (hlocL q)
      (wallsSigma_le_drivingFiltration hX R (Lr q)) (hRm' q) (hLm' q) hG0 hcfgI'
      (fun ω hω => hζG ω hω.1) u hsI


end InteractingSLE.Sec7.RefWire
