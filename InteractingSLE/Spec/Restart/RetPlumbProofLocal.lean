/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofS

/-!
# Marked locality and the remaining filled-line input

Packet PROVE-RETPLUMB. Null completion of the physical information preserves
history-marked locality of the actual stopped union. For (L), the required line
set must agree with the retained domain on the live event. It may be chosen
separately away from that event: `retLineSet` is empty off the chart event, while
the retained histories still record the explored paths there.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open Supp7 Sec7 Sec7.Lemma76F LocalSets WholeField DomainMarkov DomainMarkov.Aux79 K2

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- History-marked locality survives enlargement by information already present
up to null sets. -/
theorem isHistoryAvoidanceLocal_of_le_aeSigma {ℋ ℋ' : MeasurableSpace Ω}
    {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hle : ℋ' ≤ aeSigma ℋ P)
    (hloc : @IsHistoryAvoidanceLocal Ω ℋ mΩ A h P) :
    @IsHistoryAvoidanceLocal Ω ℋ' mΩ A h P := by
  let _ : MeasurableSpace Ω := mΩ
  intro U G hUH hG hd F hF
  obtain ⟨F₀, hF₀, he⟩ := hle F hF
  obtain ⟨g, hgm, hg⟩ := hloc U G hUH hG hd F₀ hF₀
  refine ⟨g, hgm, ?_⟩
  exact (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set
    (EventuallyEqSet.rfl.inter he))).trans hg

/-- The completed physical information is contained, up to null sets, in the
histories of any capped versions at this line. -/
theorem retSigma76_le_aeSigma_cstHist {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
    (ha₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR u r) (ζ₁ ω) t))
    (ha₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR u r) (ζ₂ ω) t)) :
    retSigma76 P η₁ η₂ ζ₁ ζ₂ u r ≤
      aeSigma (MeasurableSpace.comap (cstHist ηc₁ ηc₂
        (fun ω => cutLife (ζ₁ ω) (capR u r))
        (fun ω => cutLife (ζ₂ ω) (capR u r)) u r) inferInstance) P := by
  have he : retHist76 η₁ η₂ ζ₁ ζ₂ u r =ᵐ[P]
      cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR u r))
        (fun ω => cutLife (ζ₂ ω) (capR u r)) u r := by
    filter_upwards [ha₁, ha₂] with ω e₁ e₂
    have a₁ : cappedPath η₁ ζ₁ (capR u r) ω = ηc₁ ω := (funext e₁).symm
    have a₂ : cappedPath η₂ ζ₂ (capR u r) ω = ηc₂ ω := (funext e₂).symm
    simp only [retHist76, cstHist, a₁, a₂]
  exact inf_le_right.trans (StagedEntrance.aeSigma_le_aeSigma
    (WholeField.measurable_aeSigma_of_ae_eq' (comap_measurable _) he).comap_le)

variable [IsProbabilityMeasure P]

/-- The actual capped stopped union is local with the completed physical history
as its mark. This is the raw-union input to the still-needed filling step. -/
theorem exists_cstUnion_local_retSigma76 {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {x₁ x₂ θ₁ θ₂ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (u r : ℝ≥0) :
    ∃ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ,
      (∀ ω, Continuous (ηc₁ ω)) ∧ (∀ ω, Continuous (ηc₂ ω)) ∧
      (∀ t, Measurable fun ω => ηc₁ ω t) ∧ (∀ t, Measurable fun ω => ηc₂ ω t) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR u r) (ζ₁ ω) t)) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR u r) (ζ₂ ω) t)) ∧
      IsHistoryAvoidanceLocal (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r)
        (cstUnion ηc₁ ηc₂ u r) (centredField h u₀) P := by
  obtain ⟨ηc₁, hc₁, hm₁, h0₁, _, ha₁, hdet₁, hdetζ₁⟩ :=
    exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ (capR u r)
  obtain ⟨ηc₂, hc₂, hm₂, h0₂, _, ha₂, hdet₂, hdetζ₂⟩ :=
    exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ (capR u r)
  have hloc₁ := retainedRangeEntranceStatement κ hκ hκ4 b jumps hb x₁ θ₁ P h hh
    η₁ ζ₁ hη₁ u₀ hu₀ (capR u r) ηc₁ hc₁ hm₁ ha₁
  have hloc₂ := retainedRangeEntranceStatement κ hκ hκ4 b jumps hb x₂ θ₂ P h hh
    η₂ ζ₂ hη₂ u₀ hu₀ (capR u r) ηc₂ hc₂ hm₂ ha₂
  refine ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, ha₁, ha₂,
    isHistoryAvoidanceLocal_of_le_aeSigma (retSigma76_le_aeSigma_cstHist ha₁ ha₂) ?_⟩
  exact isHistoryAvoidanceLocal_cstUnion
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀).measurable
    hc₁ hc₂ h0₁ h0₂ hm₁ hm₂
    ((measurable_cutLife _).comp (measurable_lifetime_of_isFlowLine hη₁))
    ((measurable_cutLife _).comp (measurable_lifetime_of_isFlowLine hη₂))
    hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂

omit mΩ [IsProbabilityMeasure P] in
/-- The chart-domain line set erases the explored range off its chart event. -/
theorem retLineSet_eq_empty_of_notMem {G : ℝ≥0 → Set Ω}
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {u r t : ℝ≥0} {ω : Ω}
    (hω : ω ∉ (retFam G η₁' η₂' u (r + t)).E) :
    retLineSet G η₁' η₂' u r t ω = ∅ := by
  rw [retLineSet, RetData.D_of_notMem hω, sdiff_self]

/-- K2's (L) from a history-marked filled line set. The line set is allowed to
differ from `retLineSet` away from the live pre-contact event. This keeps the
missing filling/locality input explicit instead of imposing locality on the
chart's empty fallback set. -/
theorem hasSafeMembers_ret_of_marked_filling {κ : ℝ} {b : ℝ → ℝ}
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
      (retClock G η₁' η₂' ζ₂ u r t))
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
        (lineSafe (retClock G η₁' η₂' ζ₂ u r)
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
      (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r) (retClock G η₁' η₂' ζ₂ u r) hQa)
      F (retLife G η₁' η₂' ζ₂ u r) (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
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
  apply hasSafeMembers_of_lineLocal
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
    (fun _ _ hD t => measurableSet_inter_of_timeChange hD t)
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

end InteractingSLE.Restart.RetAux79
