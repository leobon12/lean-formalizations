/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketWordPerQEvent
import InteractingSLE.Spec.Sec7.PocketWordPerQSigma
import InteractingSLE.Spec.Sec7.PocketStopWallsFinField

/-!
# The strip pocket word assembled with information fixed after selecting its rational seed

Packet PROVE-STRIPSYS-PERQ. The existing fixed-pocket assembly is used with `𝓦 q` after selecting `q`.
The extra almost sure property `Q q` can in particular keep the counterflow lifetime infinite on the event.
The field input receives the configurations already proved by the pathwise strip geometry.
No source theorem is replaced, and no Theorem 1.2/1.3 or parameterized determination is used (R48).
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

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling StripPocketConfig

/-- The strip-level walls-law consumer with a separate null-completed walls σ-algebra at each rational seed. -/
theorem pocketWordEvolution_of_stripPocket_walls0_perQ.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hRr : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : ℚ → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : ∀ q, 𝓦 q ≤ mΩ) (hnull : ∀ q, Ito.nullSets P ≤ 𝓦 q)
    {R β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ q t, Measurable[𝓦 q] fun ω => R ω t) (hLm : ∀ q t, Measurable[𝓦 q] fun ω => Lr q ω t)
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
    {Q : ℚ → Ω → Prop} (hQ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Q q ω)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 q] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (R ω) (Lr q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, Q q ω) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q) →
        IsCfPocketConfig (R ω) (Lr q ω) (StripSys.rt q) (W ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (Lr q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (R ω) (Lr q ω) (StripSys.rt q) (W ω) (η ω)) →
      PocketStopField.PocketStopWallsInput0 (16 / κ') rL rR (𝓦 q) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u ∧
        PocketStopField.PocketStopWallsInputInf0 (16 / κ') rL rR (𝓦 q) P R (Lr q) (StripSys.rt q) W η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q)} h₀ u) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR := by
  obtain ⟨q, hq, G, hGm, hPG, hG⟩ := exists_stripPocketEvent_perQ_ae (P := P) h𝓦 hnull hRm hLm hβm hηm hηc hηH hη0 hR hβ
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
      IsSimpleProper (β ω) ∧ Lr q ω (StripSys.rt q) = β ω (StripSys.rt q) ∧ Q q ω)
    (fun q hq => by
      filter_upwards [htrace, hav, hattach q hq, hattachI q hq, hβ, hLw q hq, hQ q hq] with ω h1 h2 h3 h4 h5 h6 h7
      exact ⟨h1, h2, h3, h4, h5.1, h6.2.2, h7⟩)
  have hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (Lr q ω) (StripSys.rt q) →
      IsCfPocketConfig (R ω) (Lr q ω) (StripSys.rt q) (W ω) (η ω) := fun ω hω hpos => by
    obtain ⟨hconf, -, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, havω, hatt, -, hβsp, hLβ, -⟩ := hG ω hω
    exact isCfPocketConfig_of_cfAvoid hconf hpos htr hWc hW0 hrevR hrevL hvisR (hatt hconf hpos) hβsp hLβ havω
  have hcfgI : ∀ ω ∈ G, rightLo (R ω) (Lr q ω) (StripSys.rt q) = 0 →
      IsCfPocketConfigInf (R ω) (Lr q ω) (StripSys.rt q) (W ω) (η ω) := fun ω hω h0 => by
    obtain ⟨hconf, -, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, havω, -, hattI, hβsp, hLβ, -⟩ := hG ω hω
    obtain ⟨htrans, hvisL, hatt⟩ := hattI hconf h0
    exact isCfPocketConfigInf_of_cfAvoid hconf h0 htr hWc hW0 htrans hrevR hrevL hvisR hvisL hatt hβsp hLβ havω
  obtain ⟨hin1, hin2⟩ := hin q hq G hGm hPG (fun ω hω => ⟨(hG ω hω).1, (hG ω hω).2.1⟩)
    (fun ω hω => (hG ω hω).2.2.2.2.2.2.2.2.2.2.2) hcfg hcfgI
  exact PocketStopField.pocketWordEvolution_of_wallsInput0' (W := W) hκ' hL hLd hRr hRd (h𝓦 q)
    (hRm q) (hLm q) hGm hPG (fun ω hω => (hG ω hω).1) hcfg hcfgI hηm hh₀ 𝔥 hu hub h𝔥 hin1 hin2

end InteractingSLE.Sec7.PocketWordPerQ
