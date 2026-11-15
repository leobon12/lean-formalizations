/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualInputs
import InteractingSLE.Spec.Restart.RetPlumbProofResidualPlumbing

/-!
# Retained (S) and (L) with the supported physical clock

Packet PROVE-RETPLUMB. The landed chart, conditional line kernels and filled
history-local sets discharge every input except the displayed supported clock
and safe-event measurability. `retSafeInputs_of_flowLines` below discharges those
from the actual killed-history observations as well.
-/
set_option autoImplicit false
noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open Supp7 Sec7 Sec7.Lemma76F LocalSets WholeField DomainMarkov DomainMarkov.Aux79 K2
universe v
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {G : ℝ≥0 → Set Ω}
    {u r : ℝ≥0} {F : Set Ω} {c₀ : BoundaryWord}

/-- (S) from the landed line kernels, with the supported physical clock. -/
theorem hasSafeLaw_ret_of_physical_measurability_indicator
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
    (hFm : MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0] F)
    (hQa : ∀ t, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
      (F.indicator (retClock G η₁' η₂' ζ₂ u r t)))
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
        (F ∩ lineSafe (retClock G η₁' η₂' ζ₂ u r)
          (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
          (retLife G η₁' η₂' ζ₂ u r) (tsupport ψ) t)) :
    HasSafeLaw κ ρL ρR P
      (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r) (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa)
      F (F.indicator (retLife G η₁' η₂' ζ₂ u r)) (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      (PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xL)
      (PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xR)
      fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1
        (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ) (h ω) := by
  classical
  have hag : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω →
      (s : ℝ≥0∞) < ζ₂ ω → ω ∈ G s ∧
        (∀ t ≤ u, η₁' ω t = η₁ ω t) ∧ ∀ t ≤ s, η₂' ω t = η₂ ω t := by
    intro s
    filter_upwards [hG s, ha₁, ha₂] with ω hGω e₁ e₂ hu hs
    exact ⟨hGω hu hs, fun t ht => e₁ t ((ENNReal.coe_le_coe.2 ht).trans hu.le),
      fun t ht => e₂ t ((ENNReal.coe_le_coe.2 ht).trans hs.le)⟩
  choose ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ h0₁ h0₂ hag₁ hag₂ hg hker using
    fun t : ℝ≥0 => exists_retDomain_kernel hL75 hκ hκ4 hb hh hη₁ hη₂
      (hd (r + t)) (hag (r + t)) hu₀
  obtain ⟨α₁, α₂, hcα₁, hcα₂, hmα₁, hmα₂, h0α₁, h0α₂, haα₁, haα₂, _, _, _⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement
      hκ hκ4 hb hh hη₁ hη₂ hu₀ (capR u r) u r
  obtain ⟨hdom, hfwd, hlift⟩ := chart_measurability_retSigma76 (hd r)
    (measurable_lifetime_of_isFlowLine hη₁) (measurable_lifetime_of_isFlowLine hη₂)
    hGsub (hag r) hcα₁ hcα₂ hmα₁ hmα₂ h0α₁ h0α₂ haα₁ haα₂
  have hdom0 : ∀ z, MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0]
      {ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom} := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hdom
  have hfwd0 : ∀ z, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0]
      ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
        fun ω => ((retFam G η₁' η₂' u r).chart ω).1 z) := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hfwd
  have hlift0 : ∀ z, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0]
      ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
        fun ω => ((retFam G η₁' η₂' u r).chart ω).2.2 z) := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hlift
  apply hasSafeLaw_ret_of_plumbing_indicator hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂ hd hG
    hu₀ hc₀ hc₀J hc₀b hF htype ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
    hFm hdom0 hfwd0 hlift0 hQa hS
    (fun t => retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ (ηc₁ t) (ηc₂ t) u (r + t))
    (fun t => retPhysFiltration_le_retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ (ηc₁ t) (ηc₂ t) u r t)
    (fun t => retLineSigma_le hh.1 u₀ η₁ η₂ (measurable_lifetime_of_isFlowLine hη₁)
      (measurable_lifetime_of_isFlowLine hη₂) (hc₁ t) (hc₂ t) (hm₁ t) (hm₂ t) u (r + t))
  intro t φ
  filter_upwards [hker t φ, ae_retPairAt hκ hκ4 hη₁ hη₂ ha₁ ha₂ (hd r) hF t,
    ae_retLineSet_eq hκ hκ4 hx hη₁ hη₂ ha₁ ha₂ hd hG hc₀ hF t]
    with ω hkerω hpair hD hωF hlt hsupp
  have hDeq := (H_diff_retLineSet G η₁' η₂' u r t ω).symm.trans (hD hωF hlt)
  rw [← hDeq] at hsupp ⊢
  exact hkerω (hpair hωF hlt) hsupp

/-- (L) using a history-marked filled set and the supported clock. -/
theorem hasSafeMembers_ret_of_marked_filling_indicator {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    {η₁ η₂ η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    {G : ℝ≥0 → Set Ω} {u r : ℝ≥0} {F : Set Ω} {c₀ : BoundaryWord}
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
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u
      (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    (hQa : ∀ t, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
      (F.indicator (retClock G η₁' η₂' ζ₂ u r t)))
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
        (F ∩ lineSafe (retClock G η₁' η₂' ζ₂ u r)
          (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
          (retLife G η₁' η₂' ζ₂ u r) (Coupling.ballsK Fb) t))
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t)
      (B t) (centredField h u₀) P)
    (hBD : ∀ t, ∀ᵐ ω ∂P, ω ∈ F →
      (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω →
      H \ B t ω = (retFam G η₁' η₂' u (r + t)).D ω) :
    HasSafeMembers P
      (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r) (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa)
      F (F.indicator (retLife G η₁' η₂' ζ₂ u r)) (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1
        (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ) (h ω) := by
  have hag : ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω →
      ω ∈ G r ∧ (∀ t ≤ u, η₁' ω t = η₁ ω t) ∧ ∀ t ≤ r, η₂' ω t = η₂ ω t := by
    filter_upwards [hG r, ha₁, ha₂] with ω hGω e₁ e₂ hu hr
    exact ⟨hGω hu hr, fun t ht => e₁ t ((ENNReal.coe_le_coe.2 ht).trans hu.le),
      fun t ht => e₂ t ((ENNReal.coe_le_coe.2 ht).trans hr.le)⟩
  obtain ⟨α₁, α₂, hc₁, hc₂, hm₁, hm₂, h0₁, h0₂, haα₁, haα₂, _, _, _⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 retainedRangeEntranceStatement
      hκ hκ4 hb hh hη₁ hη₂ hu₀ (capR u r) u r
  obtain ⟨hdom, hfwd, hlift⟩ := chart_measurability_retSigma76 (hd r)
    (measurable_lifetime_of_isFlowLine hη₁) (measurable_lifetime_of_isFlowLine hη₂)
    hGsub hag hc₁ hc₂ hm₁ hm₂ h0₁ h0₂ haα₁ haα₂
  have hdom0 : ∀ z, MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0]
      {ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom} := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hdom
  have hfwd0 : ∀ z, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0]
      ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
        fun ω => ((retFam G η₁' η₂' u r).chart ω).1 z) := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hfwd
  have hlift0 : ∀ z, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0]
      ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
        fun ω => ((retFam G η₁' η₂' u r).chart ω).2.2 z) := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hlift
  apply hasSafeMembers_of_lineLocal_indicator
    (VL := PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      fun _ => (Fin.elim0 : Fin 0 → ℝ))
    (VR := PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      fun _ => (Fin.elim0 : Fin 0 → ℝ)) hh.1 hu₀.1
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀)
    (fun ω => (hd r).isConformal_chart ω) hdom0 hfwd0 hlift0
    (fun ω => (hd r).continuousOn_lift_chart ω)
    (fun ω => harmonicOnNhd_lift_chart (hd r) ω)
    (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ)
    (continuous_retClock G η₁' η₂' ζ₂ u r) (monotone_retClock G η₁' η₂' ζ₂ u r)
    (retClock_zero G η₁' η₂' ζ₂ u r) hQa
    (ae_retReach hκ hκ4 hη₂ ha₂ (hd r) hF)
    (Eventually.of_forall fun ω _ => isForceReg_ret G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀
      (fun _ => Fin.elim0) (fun _ => Fin.elim0) ω) hS
    (fun t => retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t) (fun _ => le_rfl)
    (fun t => (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r).le t) B hBm hBc hloc
  intro t
  filter_upwards [hBD t, ae_retLineSet_eq hκ hκ4 hx hη₁ hη₂ ha₁ ha₂ hd hG hc₀ hF t]
    with ω hBDω hBKω hωF hlt
  exact (hBDω hωF hlt).trans
    ((H_diff_retLineSet G η₁' η₂' u r t ω).symm.trans (hBKω hωF hlt))

/-- (L) with the filled-line input discharged for the supported clock. -/
theorem hasSafeMembers_ret_of_physical_measurability_indicator {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ η₁' η₂' : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {G : ℝ≥0 → Set Ω} {u r : ℝ≥0} {F : Set Ω} {c₀ : BoundaryWord}
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
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u
      (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    (hQa : ∀ t, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
      (F.indicator (retClock G η₁' η₂' ζ₂ u r t)))
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
        (F ∩ lineSafe (retClock G η₁' η₂' ζ₂ u r)
          (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
          (retLife G η₁' η₂' ζ₂ u r) (Coupling.ballsK Fb) t)) :
    HasSafeMembers P
      (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r) (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa)
      F (F.indicator (retLife G η₁' η₂' ζ₂ u r)) (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      (fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1
        (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ) (h ω)) := by
  have hag : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω →
      (s : ℝ≥0∞) < ζ₂ ω → ω ∈ G s ∧
        (∀ t ≤ u, η₁' ω t = η₁ ω t) ∧ ∀ t ≤ s, η₂' ω t = η₂ ω t := by
    intro s
    filter_upwards [hG s, ha₁, ha₂] with ω hGω e₁ e₂ hu hs
    exact ⟨hGω hu hs, fun t ht => e₁ t ((ENNReal.coe_le_coe.2 ht).trans hu.le),
      fun t ht => e₂ t ((ENNReal.coe_le_coe.2 ht).trans hs.le)⟩
  choose B hBm hBc hloc hBD using fun t : ℝ≥0 =>
    exists_ret_filled_line hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ (hd (r + t)) (hag (r + t))
  apply hasSafeMembers_ret_of_marked_filling_indicator hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂ hd hG
    hGsub hu₀ hc₀ hF hQa hS B
    (fun t => (hBm t).mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ u (r + t)) le_rfl)
    hBc hloc
  intro t
  filter_upwards [hBD t, ae_retPairAt hκ hκ4 hη₁ hη₂ ha₁ ha₂ (hd r) hF t]
    with ω hBω hp hωF hlt
  exact hBω (hp hωF hlt)

/-- Arbitrary compact safe tests reduce to compact subsets bounded away from
the real line. This includes the rational-ball tests not contained in `H`. -/
theorem RetPrefixObservations.measurableSet_safe_compact
    {𝓖 : Filtration ℝ≥0 mΩ} (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : F ⊆ G r)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    {W : ℝ≥0 → Ω → ℝ}
    (hgen : ∀ ω ∈ F, IsGeneratingTrace (fun s => W s ω)
      (retLife G η₁' η₂' ζ₂ u r ω) (retPath G η₁' η₂' ζ₂ u r ω))
    {C : Set ℂ} (hC : IsCompact C) (t : ℝ≥0) :
    MeasurableSet[𝓖 t]
      (F ∩ lineSafe (retClock G η₁' η₂' ζ₂ u r) W (retLife G η₁' η₂' ζ₂ u r) C t) := by
  let K : ℕ → Set ℂ := fun n => C ∩ {z | 1 / ((n : ℝ) + 1) ≤ z.im}
  have hK (n : ℕ) : IsCompact (K n) :=
    hC.inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hKH (n : ℕ) : K n ⊆ H := fun z hz =>
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) hz.2
  have he : F ∩ lineSafe (retClock G η₁' η₂' ζ₂ u r) W (retLife G η₁' η₂' ζ₂ u r) C t =
      ⋂ n : ℕ, F ∩ lineSafe (retClock G η₁' η₂' ζ₂ u r) W (retLife G η₁' η₂' ζ₂ u r) (K n) t := by
    ext ω
    constructor
    · rintro ⟨hω, hl, hdj⟩
      exact mem_iInter.2 fun n => ⟨hω, hl, hdj.mono_left inter_subset_left⟩
    · intro hω
      have hh := fun n => mem_iInter.1 hω n
      refine ⟨(hh 0).1, (hh 0).2.1, Set.disjoint_left.2 fun z hz hzh => ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < z.im from hzh.1)
      exact Set.disjoint_left.1 (hh n).2.2 ⟨hz, hn.le⟩ hzh
  rw [he]
  exact MeasurableSet.iInter fun n => ho.measurableSet_safe hd hG hp₂ hpair hgen (hK n) (hKH n) t

/-- Both stopped-K2 safe inputs, with every physical measurability, line-kernel
and filled-locality input constructed from the landed flow-line results. -/
theorem retSafeInputs_of_flowLines
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
      HasSafeLaw κ ρL ρR P
        (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r)
          (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa)
        F (F.indicator (retLife G η₁' η₂' ζ₂ u r)) (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
        (PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xL)
        (PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xR)
        (fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1
          (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ) (h ω)) ∧
      HasSafeMembers P
        (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r)
          (fun t => F.indicator (retClock G η₁' η₂' ζ₂ u r t)) hQa)
        F (F.indicator (retLife G η₁' η₂' ζ₂ u r)) (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
        (fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1
          (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ) (h ω)) := by
  have hpair : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r :=
    fun ω hω => (hF ω hω).1
  have hGF : F ⊆ G r := fun ω hω => (hF ω hω).2
  have hFm' : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] F := by
    simpa +instances only [retPhysFiltration_apply, add_zero] using hFm
  have ho := retPrefixObservations_of_flowLines hL75 hκ hκ4 hb hh hη₁ hη₂ ha₁ ha₂
    (hd r) hGsub (hG r) hFm' hGF hp₁ hp₂ hpair
  have hQa := ho.measurable_clock (hd r) hGF hp₂ hpair
  have hgen : ∀ ω ∈ F, IsGeneratingTrace
      (fun q => retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀ q ω)
      (retLife G η₁' η₂' ζ₂ u r ω) (retPath G η₁' η₂' ζ₂ u r ω) := by
    intro ω hω
    exact (isRetDriver_retDriver (exists_isRetDriver hd (hGF hω) (hp₁ ω hω) (hp₂ ω hω)
      hx (hpair ω hω) hc₀ hκ θ₂ (-sleLambda κ - θ₁ * QuantumZipper.chiC κ)
        (sleLambda κ - θ₁ * QuantumZipper.chiC κ))).2.2.1
  refine ⟨hQa, ?_, ?_⟩
  · exact hasSafeLaw_ret_of_physical_measurability_indicator hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂
      hd hG hGsub hu₀ hc₀ hc₀J hc₀b hF htype hFm hQa
      (fun ψ t => ho.measurableSet_safe_compact (hd r) hGF hp₂ hpair hgen ψ.hasCompactSupport.isCompact t)
  · exact hasSafeMembers_ret_of_physical_measurability_indicator hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂
      hd hG hGsub hu₀ hc₀ hF hQa
      (fun Fb t => ho.measurableSet_safe_compact (hd r) hGF hp₂ hpair hgen (Coupling.isCompact_ballsK Fb) t)

end InteractingSLE.Restart.RetAux79
