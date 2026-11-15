/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketWordPerQAssembly

/-!
# The strip pocket word from per-seed side limits and the proved marked walls laws

Packet PROVE-STRIPSYS-PERQ. The marks at rational seed `q` are exactly
`wallsSigma P R (Lr q) = σ(fullHist ![R, Lr q]) ∨ nullSets P`. The strip selector keeps the infinite-lifetime
property on its selected event. The bounded and seed-opening configurations are derived from the strip paths;
STRIPSYS43 then supplies both walls laws at `T⁰`. The sole remaining field input is the side limit in each shape.
These are conditional assembly lemmas, not unconditional proofs of the side-limit statements or Theorem 1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketWordPerQ

open WangWu WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I PocketCoord PocketJordan
  PocketMarks PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopWallsFin PocketStopMarked
  PocketLeftFrontier StripPocketConfig

/-- The explicit side-limit input for the bounded pocket, with both possible word shapes. -/
def PocketSideLimitInput0 {Ω : Type*} (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) → @IsPointMeasurable Ω 𝓦 R L r G ψ →
      ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) P A
            (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
            (activeCompl A (travAll R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q) ∧
      ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) P A
            (travAll R L r η ψ) marksL1All (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
            (activeCompl A (travAll R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q)

/-- The explicit side-limit input for the seed-opening pocket, with both possible word shapes. -/
def PocketSideLimitInputInf0 {Ω : Type*} (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
      ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) P A
            (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
            (activeCompl A (travAllInf R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q) ∧
      ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        ∃ (n : Ω → ℤ) (a : ℝ), Measurable[𝓦] n ∧ ∀ q : ℝ≥0,
          PocketStopSideLimit (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) P A
            (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ)
            (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) a h₀ u
            (activeCompl A (travAllInf R L r η ψ)
              (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) q)

/-- The pocket word assembled from the strip paths, their locality and determination, the counterflow coupling,
and the side limits at the selected pair's σ-algebra. Both walls laws are discharged by STRIPSYS43. -/
theorem pocketWordEvolution_of_stripPocket_sideLimit_perQ.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ')
    (hL : -2 < rL) (hLd : rL < κ' / 2 - 4) (hRr : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
    (𝔥 : DistOn upperHalfPlaneOpens) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
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
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} (centredField h'' u₀') u) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR := by
  have hRm' := fun q t => measurable_right_wallsSigma (P := P) hRc (hLc q) t
  have hLm' := fun q t => measurable_left_wallsSigma (P := P) hRc (hLc q) t
  refine pocketWordEvolution_of_stripPocket_walls0_perQ (𝓦 := fun q => wallsSigma P R (Lr q))
    (W := fun ω s => W' s.toNNReal ω) (Q := fun _ ω => ζ' ω = ⊤) hκ' hL hLd hRr hRd
    (fun q => wallsSigma_le hRm (hLm q)) (fun _ => le_sup_right) hRm' hLm' hβm hηm hηc hηH hη0 hR hβ hLw
    hnohit hlate (by simpa only [Real.toNNReal_zero] using htrace) hav hattach hattachI
    (isZeroBoundaryGFF_centredField hC hu₀') 𝔥 hu hub h𝔥
    (fun _ _ => hζ) ?_
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

end InteractingSLE.Sec7.PocketWordPerQ
