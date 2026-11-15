/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetFinPair
import InteractingSLE.Spec.Restart.RetLeafModelCtor
import InteractingSLE.Spec.Restart.RetEndReal
import InteractingSLE.Spec.Restart.RetPlumbProofDriverSafe
import InteractingSLE.Spec.Restart.RetPlumbProofFinalPairings
import InteractingSLE.Spec.Restart.RetPlumbProofFinalNoncollision
import InteractingSLE.Spec.Restart.RetPlumbProofResidualInputs
import InteractingSLE.Spec.Restart.RetPlumbProofInputsTrace
import InteractingSLE.Spec.Sec7.Lemma76Kernel2Det

/-!
# The retained stopped model on one force-type event

Packet PROVE-T15-RET3. On an event `M` of the retained σ-algebra on which, pathwise,

* the two capped versions form a good disjoint pair in the good event `G r` of a retained family,
* the given retained data `d` agree with the versions on the prefixes,
* the given mean-identifying word `β` has the fixed force type `a`, and has the mean pairings of the explicit
  retained word `retWordAt` (both sorted),

the actual retained continuation of the second flow line (lifetime and path read in `d`'s chart, first
contact with `η₁[0,u] ∪ η₂[0,r] ∪ ℝ`, ruling R55) has a stopped model (`StoppedModelTransfer`) with word `β`
and field `d`'s chart field. This is PROVE-RETPLUMB's driver and safe-law construction
(`retAdaptedSafeInputs_of_flowLines`), applied with `β`'s fixed-type positions, fed to PROVE-T15-RET's model
constructor (`RetLeaf.stoppedModelTransfer_of_traceInputs`) with PROVE-T15-RET2's unconditional trace facts,
and transported to `d`'s chart, lifetime and path.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetFin

open LQGMetric (DistOn TestOn)
open Supp7 Sec7 Sec7.Lemma76F RetAux79 DomainMarkov DomainMarkov.Aux79

universe v

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The retained continuation in `d`'s chart is the retained continuation of the family**, on an event where
`d` and the family agree with the versions and the versions agree with the flow lines. -/
theorem retLife_retPath_eq_canon {d : RetData Ω} (hd : d.IsMeasGood) {η₁' η₂' : Ω → ℝ≥0 → ℂ}
    {G : ℝ≥0 → Set Ω} {ω : Ω} (hGd : ω ∈ d.G) (hG : ω ∈ G d.r)
    (a₁ : ∀ s ≤ d.u, d.η₁ ω s = η₁' ω s) (a₂ : ∀ t ≤ d.r, d.η₂ ω t = η₂' ω t)
    (hpair : Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) d.u (η₂' ω) (ζ₂ ω) d.r)
    (e₁ : ∀ s ≤ d.u, η₁' ω s = η₁ ω s) (e₂ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s) :
    retLife G η₁' η₂' ζ₂ d.u d.r ω = canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 ∧
      RetAux79.retPath G η₁' η₂' ζ₂ d.u d.r ω = canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 := by
  obtain ⟨hEiff, hD, hch⟩ := RetData.chart_eq_of_agree (d := d) (G' := G d.r) (η₁' := η₁') (η₂' := η₂')
    hGd hG (fun s hs => (a₁ s hs).symm) (fun t ht => (a₂ t ht).symm)
  have hE : ω ∈ d.E := mem_E_of_isDisjointPair hd hGd a₁ a₂ hpair
  have hE' : ω ∈ (retFam G η₁' η₂' d.u d.r).E := hEiff.2 hE
  have hD' : (retFam G η₁' η₂' d.u d.r).D ω = d.D ω := hD
  have hch' : (retFam G η₁' η₂' d.u d.r).chart ω = d.chart ω := hch
  have hfwd : (retFam G η₁' η₂' d.u d.r).fwd ω = d.fwd ω := by
    rw [RetData.chart_of_mem hE', RetData.chart_of_mem hE] at hch'
    exact congrArg Prod.fst hch'
  have hK : retStopSet η₁' η₂' d.u d.r ω = η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine := by
    have h1 : η₁' ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u := image_congr fun s hs => e₁ s hs.2
    have h2 : η₂' ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r :=
      image_congr fun t ht => e₂ t ((ENNReal.coe_le_coe.2 ht.2).trans hpair.2.1.le)
    rw [retStopSet, h1, h2]
  obtain ⟨eP, eL⟩ := canonRetPath_congr (D := d.D ω) (φ := d.fwd ω) (a := d.r)
    (K := η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) (c := 0) e₂
  refine ⟨?_, ?_⟩
  · rw [retLife, hD', hfwd, hK, eL]
  · rw [RetAux79.retPath, hD', hfwd, hK, eP]

/-- **The retained stopped model on one force-type event.** -/
theorem nonempty_stoppedModelTransfer_branch (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → BoundaryWord} (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdent κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    (hsort : ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).IsSorted)
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {G : ℝ≥0 → Set Ω}
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hdG : ∀ r', (retFam G η₁' η₂' d.u r').IsMeasGood)
    (hGae : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    (hGsub : G d.r ⊆ {ω | (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω})
    {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps)
    (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y) (a : ForceWordType) {M : Set Ω}
    (hMm : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M) (hPM : P M ≠ 0) (hMG : M ⊆ G d.r)
    (hMd : ∀ ω ∈ M, ω ∈ d.G ∧ (∀ s ≤ d.u, d.η₁ ω s = η₁' ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂' ω t)
    (hMpair : ∀ ω ∈ M, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) d.u (η₂' ω) (ζ₂ ω) d.r)
    (hMpairη : ∀ ω ∈ M, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    (hMp₁ : ∀ ω ∈ M, IsPathGood (η₁' ω) (ζ₁ ω) x₁) (hMp₂ : ∀ ω ∈ M, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hMa₁ : ∀ ω ∈ M, ∀ s ≤ d.u, η₁' ω s = η₁ ω s)
    (hMa₂ : ∀ ω ∈ M, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hMtype : ∀ ω ∈ M, β ω ∈ forceTypeSet κ θ₂ a)
    (hMword : ∀ ω ∈ M, (β ω).IsSorted ∧ (retWordAt G η₁' η₂' d.u κ θ₁ θ₂ c₀ d.r ω).IsSorted ∧
      ∀ φ : TestOn upperHalfPlaneOpens,
        ∫ z, (β ω).mean z * φ z = ∫ z, (retWordAt G η₁' η₂' d.u κ θ₁ θ₂ c₀ d.r ω).mean z * φ z) :
    Nonempty (StoppedModelTransfer κ θ₂ P M β (hd.chartField κ h)
      (fun ω => canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0)
      (fun ω => canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r
        (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0)) := by
  classical
  have hFm : MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0] M := by
    simpa +instances only [retPhysFiltration_apply, add_zero] using hMm
  let xL : Ω → Fin a.nL → ℝ := fun ω => FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω)
  let xR : Ω → Fin a.nR → ℝ := fun ω => FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β ω)
  have htype' : ∀ ω ∈ M, FCDet.IsFlowType κ θ₂ (retWordAt G η₁' η₂' d.u κ θ₁ θ₂ c₀ d.r ω) (xL ω) (xR ω)
      a.rhoL a.rhoR := fun ω hω =>
    isFlowType_of_mean_integrals a (hMword ω hω).1 (hMword ω hω).2.1 (hMword ω hω).2.2 (hMtype ω hω)
  obtain ⟨hQa, W, hW0, hWc, hWa, -, hVs, hS, hL, hgen⟩ := retAdaptedSafeInputs_of_flowLines (θ₁ := θ₁)
    hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂ hdG hGae hGsub hu₀ hc₀ hc₀J hc₀b (F := M)
    (fun ω hω => ⟨hMpair ω hω, hMG hω⟩) htype' hMp₁ hMp₂ hFm
  have hR0 : retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤
      timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r)
        (fun t => M.indicator (retClock G η₁' η₂' ζ₂ d.u d.r t)) hQa 0 := by
    refine le_trans ?_ le_timeChange_zero
    rw [retPhysFiltration_apply, add_zero]
  have ho := retPrefixObservations_of_flowLines hL75 hκ hκ4 hb hh hη₁ hη₂ ha₁ ha₂ (hdG d.r) hGsub
    (hGae d.r) hMm hMG hMp₁ hMp₂ hMpair
  obtain ⟨hγm, hVm, hγc⟩ := ho.trace_data (hdG d.r) hMG hMp₂ hMpair
  have hγ0 : ∀ ω, M.indicator (fun ω => RetAux79.retPath G η₁' η₂' ζ₂ d.u d.r ω 0) ω = 0 := by
    intro ω
    by_cases hω : ω ∈ M
    · rw [indicator_of_mem hω]
      exact (hgen ω hω).1
    · exact indicator_of_notMem hω _
  obtain ⟨Y, hY, hYsp⟩ := exists_retCanonicalReader (c := β) (Hc := hd.chartField κ h) (W := W)
    (V := M.indicator (retLife G η₁' η₂' ζ₂ d.u d.r))
    (γ := fun ω t => M.indicator (fun ω => RetAux79.retPath G η₁' η₂' ζ₂ d.u d.r ω t) ω)
    (hβ.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r) le_rfl) (hd.measurable_chartField κ hh.1)
    (fun t => (hWa t).measurable.mono (Filtration.le _ t) le_rfl) hWc hW0 hVm hγm hγc hγ0
  -- the shifted chart field of `d` is the field of the safe laws on `M`
  have hXe : ∀ᵐ ω ∂P, ω ∈ M →
      Exist.flowField 0 (θ₂ * QuantumZipper.chiC κ) (hd.chartField κ h ω) =
        Chart.chartTransport ((hdG d.r).isConformal_chart ω) 1 (θ₂ * QuantumZipper.chiC κ)
          (QuantumZipper.chiC κ) (h ω) := by
    refine Eventually.of_forall fun ω hω => ?_
    obtain ⟨hGd, a₁, a₂⟩ := hMd ω hω
    have hch : (retFam G η₁' η₂' d.u d.r).chart ω = d.chart ω :=
      (RetData.chart_eq_of_agree (d := d) (G' := G d.r) (η₁' := η₁') (η₂' := η₂') hGd (hMG hω)
        (fun s hs => (a₁ s hs).symm) (fun t ht => (a₂ t ht).symm)).2.2
    rw [RetData.IsMeasGood.chartField, flowField_chartTransport]
    exact Restart.chartTransport_congr_chart hch.symm _ _ _ _ _ _
  have hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Exist.flowField 0 (θ₂ * QuantumZipper.chiC κ) (hd.chartField κ h ω) φ)
        (P.restrict M) := by
    intro φ
    have hi := retPairing_integrable_of_meanIdent hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ hβ hmean hsort hMm
      (Eventually.of_forall hMpairη) θ₂ a φ
    have he : FCPlumb.fcTypeBranch κ θ₂ M β a = M := inter_eq_left.2 fun ω hω => hMtype ω hω
    rwa [he] at hi
  have hn := retPrelifeNonThreshold_of_retWordAt (P := P) hκ (hdG d.r) hMG hMp₁ hMp₂ hx hMpair hc₀ htype'
    hWc hW0 hgen
  obtain ⟨hH₀, hreal₀, hVpos⟩ := RetEnd.retained_traceInputs_of_flowLine hη₂ ha₂ (hdG d.r) (F := M)
    (fun ω hω => ⟨hMpair ω hω, hMG hω⟩) hMp₁ hMp₂
  have hg : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (M.indicator (retLife G η₁' η₂' ζ₂ d.u d.r) ω)
      (fun t => M.indicator (fun ω => RetAux79.retPath G η₁' η₂' ζ₂ d.u d.r ω t) ω) := by
    refine Eventually.of_forall fun ω hω => ?_
    have e : (fun t => M.indicator (fun ω => RetAux79.retPath G η₁' η₂' ζ₂ d.u d.r ω t) ω) =
        RetAux79.retPath G η₁' η₂' ζ₂ d.u d.r ω := funext fun t => indicator_of_mem hω _
    rw [e, indicator_of_mem hω]
    exact hgen ω hω
  have hH : ∀ᵐ ω ∂P, ω ∈ M → ∀ t : ℝ≥0, 0 < t →
      (t : ℝ≥0∞) < M.indicator (retLife G η₁' η₂' ζ₂ d.u d.r) ω →
        0 < (M.indicator (fun ω => RetAux79.retPath G η₁' η₂' ζ₂ d.u d.r ω t) ω).im := by
    filter_upwards [hH₀] with ω hω hωM t ht0 ht
    rw [indicator_of_mem hωM]
    exact hω hωM t ht0 ht
  have hreal : ∀ᵐ ω ∂P, ω ∈ M → M.indicator (retLife G η₁' η₂' ζ₂ d.u d.r) ω ≠ ⊤ →
      (M.indicator (fun ω' => RetAux79.retPath G η₁' η₂' ζ₂ d.u d.r ω'
        (M.indicator (retLife G η₁' η₂' ζ₂ d.u d.r) ω).toNNReal) ω).im = 0 := by
    filter_upwards [hreal₀] with ω hω hωM htop
    have := hω hωM htop
    rw [indicator_of_mem hωM (fun ω' => RetAux79.retPath G η₁' η₂' ζ₂ d.u d.r ω'
      (M.indicator (retLife G η₁' η₂' ζ₂ d.u d.r) ω).toNNReal)]
    exact this
  let T := RetLeaf.stoppedModelTransfer_of_traceInputs (κ := κ) (θ := θ₂) a (hR0 _ hMm) hPM
    (hβ.mono hR0 le_rfl) (X := fun ω => Exist.flowField 0 (θ₂ * QuantumZipper.chiC κ) (hd.chartField κ h ω))
    (xL := xL) (xR := xR) hWc hWa hVs hY (fun ω => (hYsp ω).1) (fun ω => (hYsp ω).2.1)
    (fun ω t => (hYsp ω).2.2.2.1 t) (fun ω => (hYsp ω).2.2.1) (fun ω => (hYsp ω).2.2.2.2)
    (fun ω => by
      show FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (RetCanonSpace.word (Y ω)) = _
      rw [(hYsp ω).1])
    (fun ω => by
      show FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (RetCanonSpace.word (Y ω)) = _
      rw [(hYsp ω).1])
    (fun ω => by rw [(hYsp ω).2.1]) (Eventually.of_forall hMtype) hint hn
    (hasSafeLaw_congr_field hXe hS) (hasSafeMembers_congr_field hXe hL) hg hH hreal hVpos
  refine ⟨T.of_indicator.congr_life_trace (Eventually.of_forall fun ω hω => ?_)⟩
  obtain ⟨hGd, a₁, a₂⟩ := hMd ω hω
  obtain ⟨eL, eP⟩ := retLife_retPath_eq_canon hd hGd (hMG hω) a₁ a₂ (hMpair ω hω) (hMa₁ ω hω)
    (hMa₂ ω hω)
  exact ⟨eL, fun t _ => by rw [eP]⟩

end InteractingSLE.Restart.RetFin
