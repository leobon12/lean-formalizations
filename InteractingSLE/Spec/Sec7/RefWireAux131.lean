/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.RefWirePerQ
import InteractingSLE.Spec.Sec7.R7Aux131Strip

/-!
# Aux. 131's reference with the marked-stop lifetime retained

PROVE-REF-WIRE. The selector keeps an arbitrary conull property on the selected
walls event, so the almost surely infinite counterflow lifetime may be used
pointwise by the marked-stop producers. The geometry is the landed Aux. 131
construction; no theorem of full-general determination or continuity is used.
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

open WangWu WholeField Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen
  PocketLeftFrontier PocketCoupling StripPocketConfig PocketWordPerQ R7Aux131 R7Pocket

/-- Aux. 131's selector retaining an additional conull property on the chosen walls event.
This permits the constructed marked-stop laws to use the infinite-lifetime property pointwise. -/
theorem r7PocketStopStatement_of_walls.{u} {Ω : Type u} {𝓦 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0)) (hη0 : ∀ ω, η ω 0 = 0)
    (hR : ∀ᵐ ω ∂P, IsSimpleProper (R ω) ∧ IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω))
    (hL : ∀ᵐ ω ∂P, IsSimpleProper (L ω) ∧ IsWallReverseVisit (L ω) (η ω))
    (hne : ∀ᵐ ω ∂P, range (L ω) ≠ range (R ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))))
    (htrace : ∀ᵐ ω ∂P, IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0)
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
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {Q : ℚ → Ω → Prop} (hQ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Q q ω)
    (hin : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[𝓦 ⊔ Ito.nullSets P] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
      (∀ ω ∈ G, Q q ω) →
      (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (W ω) (η ω)) →
      (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (W ω) (η ω)) →
      TwoSeedWallsInput κ rL rR (𝓦 ⊔ Ito.nullSets P) P R L (StripSys.rt q) W η
          {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u ∧
        TwoSeedWallsInputInf κ rL rR (𝓦 ⊔ Ito.nullSets P) P R L (StripSys.rt q) W η
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} h₀ u)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) :
    R7PocketStopStatement.{u} κ rL rR GoodR7 := by
  have hnc : ∀ᵐ ω ∂P, ∃ t, L ω t ∉ range (R ω) := by
    filter_upwards [hR, hL, hne] with ω hRω hLω hneω using exists_notMem_range_of_range_ne hRω.1 hLω.1 hneω
  obtain ⟨q, hq, G, hGm, hPG, hG⟩ := exists_aux131Event (𝓦 := 𝓦) (P := P) hRm hLm hηc hη0 hR hL hnc
    (Q := fun q ω => (IsLoewnerTrace (W ω) (η ω) ∧ Continuous (W ω) ∧ W ω 0 = 0) ∧
      Disjoint (range (R ω)) (leftSideOf (range (L ω))) ∧
      (IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
        Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
          (cfArcR (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
          (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
          (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0))) ∧
      (IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) → rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
        Tendsto (fun t => ‖η ω t‖) atTop atTop ∧ IsWallVisited (L ω) (η ω) ∧
          Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
            (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
            (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0))) ∧ Q q ω)
    (fun q hq => by
      filter_upwards [htrace, hord, hattach q hq, hattachI q hq, hQ q hq] with ω h1 h2 h3 h4 h5
      exact ⟨h1, h2, h3, h4, h5⟩)
  have hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (W ω) (η ω) := fun ω hω hpos => by
    obtain ⟨hconf, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, hordω, hatt, -, -⟩ := hG ω hω
    exact ⟨hconf, hpos, hconf.isFlowChartOriented_of_leftFrontier hconf.left rfl hordω, htr, hWc, hW0, hrevR,
      hrevL, hvisR, hatt hconf hpos⟩
  have hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (W ω) (η ω) := fun ω hω h0 => by
    obtain ⟨hconf, hrevR, hrevL, hvisR, ⟨htr, hWc, hW0⟩, hordω, -, hattI, -⟩ := hG ω hω
    obtain ⟨htrans, hvisL, hatt⟩ := hattI hconf h0
    exact ⟨hconf, h0, hconf.isFlowChartOriented_of_leftFrontier hconf.left rfl hordω, htr, hWc, hW0, htrans,
      hrevR, hrevL, hvisR, hvisL, hatt⟩
  obtain ⟨hin1, hin2⟩ := hin q hq G hGm hPG (fun ω hω => (hG ω hω).1)
    (fun ω hω => (hG ω hω).2.2.2.2.2.2.2.2) hcfg hcfgI
  exact r7PocketStop_of_changeConfig (𝓦 := 𝓦 ⊔ Ito.nullSets P) (sup_le h𝓦 (Ito.nullSets_le P))
    (fun t => (hRm t).mono le_sup_left le_rfl) (fun t => (hLm t).mono le_sup_left le_rfl) hGm hPG
    (fun ω hω => (hG ω hω).1) hcfg hcfgI hηc hηm hh₀ hu hub hin1 hin2 (hE₀.mono le_sup_left le_rfl)
    (sup_le hgen le_sup_right) h513


end InteractingSLE.Sec7.RefWire
