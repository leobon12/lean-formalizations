/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofDriverPhysical
import InteractingSLE.Spec.Restart.RetPlumbProofDriverModel

/-!
# The actual adapted retained driver with both stopped-K2 safe inputs

Packet PROVE-RETPLUMB. All physical observations, line kernels, filled locality,
clock measurability and killed-driver reconstruction are supplied by the landed
results. Both safe identities are transported to the continuous adapted driver.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open LQGMetric (DistOn TestOn)
open Supp7 Sec7 Sec7.Lemma76F DomainMarkov DomainMarkov.Aux79 K2
universe v
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {G : ℝ≥0 → Set Ω}
    {u r : ℝ≥0} {F : Set Ω} {c₀ : BoundaryWord}

/-- The complete supported-clock adapted-driver and (S)/(L) construction on an
initial type event of good disjoint pairs. No reconstruction input remains. -/
theorem retAdaptedSafeInputs_of_flowLines
    (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω →
      (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    (hGsub : G r ⊆ {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω})
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps)
    (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u
      (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (htype : ∀ ω ∈ F, FCDet.IsFlowType κ θ₂
      (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω) (xL ω) (xR ω) ρL ρR)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hFm : MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0] F)
 :
    ∃ hQa : ∀ t, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
        (F.indicator (retClock G η₁' η₂' ζ₂ u r t)),
      let 𝓗 := timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r)
        (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa
      let V := F.indicator (retLife G η₁' η₂' ζ₂ u r)
      let X := fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1
        (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ) (h ω)
      ∃ W : ℝ≥0 → Ω → ℝ, (∀ ω, W 0 ω = 0) ∧
        (∀ ω, Continuous fun q => W q ω) ∧ StronglyAdapted 𝓗 W ∧
        (∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < V ω →
          W q ω = retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ q ω) ∧
        (∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t}) ∧
        HasSafeLaw κ ρL ρR P 𝓗 F V W
          (PocketTraversal.geomLW W xL) (PocketTraversal.geomRW W xR) X ∧
        HasSafeMembers P 𝓗 F V W X ∧
        ∀ ω ∈ F, IsGeneratingTrace (fun q => W q ω)
          (retLife G η₁' η₂' ζ₂ u r ω) (retPath G η₁' η₂' ζ₂ u r ω) := by
  obtain ⟨hQa, hS, hL⟩ := retSafeInputs_of_flowLines hL75 hκ hκ4 hb hx hh hη₁ hη₂
    ha₁ ha₂ hd hG hGsub hu₀ hc₀ hc₀J hc₀b hF htype hp₁ hp₂ hFm
  have hpair : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r :=
    fun ω hω => (hF ω hω).1
  have hGF : F ⊆ G r := fun ω hω => (hF ω hω).2
  have hFm' : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] F := by
    simpa +instances only [retPhysFiltration_apply, add_zero] using hFm
  have ho := retPrefixObservations_of_flowLines hL75 hκ hκ4 hb hh hη₁ hη₂ ha₁ ha₂
    (hd r) hGsub (hG r) hFm' hGF hp₁ hp₂ hpair
  have ha : AdaptedBefore
      (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r)
        (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa)
      (F.indicator (retLife G η₁' η₂' ζ₂ u r))
      (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) :=
    ho.retKilledDriverObservable hd hGF hp₁ hp₂ hx hpair hc₀ hκ
  obtain ⟨W, hW0, hWc, hWa, he, hSW, hLW⟩ := exists_adapted_safe_version
    (continuous_retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
    (retDrv_zero G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) ha hS hL
  refine ⟨hQa, W, hW0, hWc, hWa, he, Ito.isStoppingTime_lifetime ha, hSW, hLW, ?_⟩
  intro ω hω
  have hg := (isRetDriver_retDriver (exists_isRetDriver hd (hGF hω) (hp₁ ω hω) (hp₂ ω hω)
    hx (hpair ω hω) hc₀ hκ θ₂ (-sleLambda κ - θ₁ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₁ * QuantumZipper.chiC κ))).2.2.1
  apply StoppedK2.isGeneratingTrace_congr (fun q hq => (he ω q ?_).symm) hg
  simpa only [indicator_of_mem hω] using hq

end InteractingSLE.Restart.RetAux79
