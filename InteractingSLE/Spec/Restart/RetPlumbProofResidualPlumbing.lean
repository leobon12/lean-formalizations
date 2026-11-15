/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualLines

/-!
# Supported-clock retained plumbing

Packet PROVE-RETPLUMB. Specialize the on-event line transports to the actual
retained paths, charts, words and filled sets. These adapters preserve every
landed line-kernel and history-locality premise.
-/
set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv logDerivFwd fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
universe v
namespace InteractingSLE.Restart.RetAux79
open Supp7 Sec7 Sec7.Lemma76G MartChar.RealFlow DomainMarkov DomainMarkov.Aux79 K2
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ η₁' η₂' : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {G : ℝ≥0 → Set Ω} {u r : ℝ≥0}
  {c₀ : BoundaryWord} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {F : Set Ω}

/-- The landed retained (S) plumbing with the supported measurable clock. -/
theorem hasSafeLaw_ret_of_plumbing_indicator (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    (htype : ∀ ω ∈ F, FCDet.IsFlowType κ θ₂ (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω) (xL ω) (xR ω) ρL ρR)
    (ηc₁ ηc₂ : ℝ≥0 → Ω → ℝ≥0 → ℂ) (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hc₁ : ∀ t ω, Continuous (ηc₁ t ω)) (hc₂ : ∀ t ω, Continuous (ηc₂ t ω))
    (hm₁ : ∀ t s, Measurable fun ω => ηc₁ t ω s) (hm₂ : ∀ t s, Measurable fun ω => ηc₂ t ω s)
    (hag₁ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₁ t ω s = η₁ ω (capTime (Lemma76F.capR u (r + t)) (ζ₁ ω) s))
    (hag₂ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₂ t ω s = η₂ ω (capTime (Lemma76F.capR u (r + t)) (ζ₂ ω) s))
    (hg : ∀ t, LocalSets.IsLocalSetMean (Lemma76F.cstUnion (ηc₁ t) (ηc₂ t) u (r + t))
      (WholeField.centredField h u₀) P (g t))
    {𝓖 : Filtration ℝ≥0 mΩ} (hFm : MeasurableSet[𝓖 0] F)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
      fun ω => ((retFam G η₁' η₂' u r).chart ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
      fun ω => ((retFam G η₁' η₂' u r).chart ω).2.2 z))
    (hQa : ∀ t, Measurable[𝓖 t] (F.indicator (retClock G η₁' η₂' ζ₂ u r t)))
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t] (F ∩ lineSafe (retClock G η₁' η₂' ζ₂ u r)
      (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) (retLife G η₁' η₂' ζ₂ u r) (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω →
      tsupport φ ⊆ ((retFam G η₁' η₂' u r).chart ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
          (retClock G η₁' η₂' ζ₂ u r t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * ((g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)
            φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov (((retFam G η₁' η₂' u r).chart ω).2.1 ''
            (H \ fwdHull (fun s : ℝ => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ s.toNNReal ω)
              (retClock G η₁' η₂' ζ₂ u r t ω))) φ φ : ℝ) : ℂ))) :
    HasSafeLaw κ ρL ρR P (timeChange 𝓖 (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa)
      F (F.indicator (retLife G η₁' η₂' ζ₂ u r))
      (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      (PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xL)
      (PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xR)
      fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1 (θ₂ * QuantumZipper.chiC κ)
        (QuantumZipper.chiC κ) (h ω) :=
  hasSafeLaw_of_retLines_indicator hFm (fun ω => (hd r).isConformal_chart ω) hdom hfwd hliftm
    (fun ω => (hd r).continuousOn_lift_chart ω) hh.1 (θ₂ * QuantumZipper.chiC κ)
    (continuous_retClock G η₁' η₂' ζ₂ u r) (monotone_retClock G η₁' η₂' ζ₂ u r) (retClock_zero G η₁' η₂' ζ₂ u r)
    hQa (ae_retReach hκ hκ4 hη₂ ha₂ (hd r) hF)
    (Eventually.of_forall fun ω _ => isForceReg_ret G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ xL xR ω) hS 𝒢L h𝒢L h𝒢Lm
    (fun t ω => g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) hker
    (continuous_retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) (retDrv_zero G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
    (fun t ω => (hd (r + t)).isConformal_chart ω) (fun t ω => retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ (r + t) ω)
    (ae_retLine hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂ hd hG hu₀ hc₀ hc₀J hc₀b hF htype ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂
      hag₁ hag₂ hg)

/-- The landed retained (L) plumbing with the supported measurable clock. -/
theorem hasSafeMembers_ret_of_plumbing_indicator (hκ : 0 < κ) (hκ4 : κ < 4) (hx : x₂ < x₁)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    {𝓖 : Filtration ℝ≥0 mΩ}
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
      fun ω => ((retFam G η₁' η₂' u r).chart ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
      fun ω => ((retFam G η₁' η₂' u r).chart ω).2.2 z))
    (hQa : ∀ t, Measurable[𝓖 t] (F.indicator (retClock G η₁' η₂' ζ₂ u r t)))
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t] (F ∩ lineSafe (retClock G η₁' η₂' ζ₂ u r)
      (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) (retLife G η₁' η₂' ζ₂ u r) (Coupling.ballsK Fb) t))
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (hBm : ∀ t, Measurable[mΩ, hittingSigma] (retLineSet G η₁' η₂' u r t))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (retLineSet G η₁' η₂' u r t)
      (WholeField.centredField h u₀) P) :
    HasSafeMembers P (timeChange 𝓖 (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa)
      F (F.indicator (retLife G η₁' η₂' ζ₂ u r))
      (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1 (θ₂ * QuantumZipper.chiC κ)
        (QuantumZipper.chiC κ) (h ω) :=
  hasSafeMembers_of_lineLocal_indicator
    (VL := PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) fun _ => (Fin.elim0 : Fin 0 → ℝ))
    (VR := PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) fun _ => (Fin.elim0 : Fin 0 → ℝ)) hh.1 hu₀.1
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) (fun ω => (hd r).isConformal_chart ω) hdom
    hfwd hliftm (fun ω => (hd r).continuousOn_lift_chart ω) (fun ω => harmonicOnNhd_lift_chart (hd r) ω)
    (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ)
    (continuous_retClock G η₁' η₂' ζ₂ u r) (monotone_retClock G η₁' η₂' ζ₂ u r) (retClock_zero G η₁' η₂' ζ₂ u r)
    hQa (ae_retReach hκ hκ4 hη₂ ha₂ (hd r) hF)
    (Eventually.of_forall fun ω _ => isForceReg_ret G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ (fun _ => Fin.elim0)
      (fun _ => Fin.elim0) ω) hS ℋ h𝓖ℋ hℋ
    (retLineSet G η₁' η₂' u r) hBm (fun t ω => retLineSet_spec hd t ω) hloc
    (ae_retLineSet_eq hκ hκ4 hx hη₁ hη₂ ha₁ ha₂ hd hG hc₀ hF)

end InteractingSLE.Restart.RetAux79
