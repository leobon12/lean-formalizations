import SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs.Assembly




 














set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs

open LQGMetric (DistC IsGFFPlusCont)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame

 

def C45BallsAt {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1) (R : AdmissibleRadii)
    (params : Parameters ξ)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ObjectAtV2 P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r) : Prop :=
  ∀ (μ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
    ∃ C : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
      ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ b : Set.Ioi (0 : ℝ),
      ∀ (z w : ℂ) (s : ℝ), 0 < s →
        Disjoint (Metric.closedBall z s) (Metric.closedBall w s) →
        Metric.closedBall z s ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
        Metric.closedBall w s ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
        ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤
          euclidSetDist (Metric.closedBall z s) (Metric.closedBall w s) →
        ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤
          euclidSetDist (Metric.closedBall z s) (Metric.sphere (0 : ℂ) b) →
        P (CountingBadEventV2 h D D' ξ Q cPlus R
          (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩
          (Metric.closedBall z s) (Metric.closedBall w s)) ≤
          ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ))

 

def C45BallsInput : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1) (R : AdmissibleRadii) (params : Parameters ξ)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ObjectAtV2 P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r),
    C45BallsAt P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict pbar R params family

 
theorem c45BallsAt_of_corrected {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D D' : DistC → LSCMetric} {hD : IsWeakLQGMetric ξ Q D} {hD' : IsWeakLQGMetric ξ Q D'}
    {hGFF : IsNormalizedWholePlaneGFF h P} {cMinus cPlus : ℝ≥0∞}
    {hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus}
    {hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus}
    {hstrict : cMinus < cPlus} {pbar : Set.Ioo (0 : ℝ) 1} {R : AdmissibleRadii}
    {params : Parameters ξ}
    {family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ObjectAtV2 P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r}
    (hC : C45CorrectedNonemptyInternal P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar R params family) :
    C45BallsAt P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict pbar R params family := by
  intro μ η
  obtain ⟨C, ε₀, hC⟩ := hC μ η
  exact ⟨C, ε₀, fun ε hε hεle b z w s hs hDisj h₁ h₂ h₃ h₄ =>
    hC ε hε hεle b _ _ ⟨z, Metric.mem_closedBall_self hs.le⟩
      ⟨w, Metric.mem_closedBall_self hs.le⟩ (isCompact_closedBall z s)
      (isCompact_closedBall w s) hDisj h₁ h₂ h₃ h₄⟩

 
theorem c45BallsInput_of_c45Input (hC45 : C45Input) : C45BallsInput :=
  fun P _ h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict pbar R params family =>
    c45BallsAt_of_corrected
      (hC45 P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict pbar R params family)

 

theorem c45BallsAt_of_interior {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D D' : DistC → LSCMetric} {hD : IsWeakLQGMetric ξ Q D} {hD' : IsWeakLQGMetric ξ Q D'}
    {hGFF : IsNormalizedWholePlaneGFF h P} {cMinus cPlus : ℝ≥0∞}
    {hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus}
    {hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus}
    {hstrict : cMinus < cPlus} {pbar : Set.Ioo (0 : ℝ) 1} {R : AdmissibleRadii}
    {params : Parameters ξ}
    {family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ObjectAtV2 P h D D' ξ Q (midpoint cMinus cPlus) params pbar z r}
    (hC : ∀ (μ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
      ∃ C : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
        ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ b : Set.Ioi (0 : ℝ),
        ∀ K₁ K₂ : Set ℂ,
          (interior K₁).Nonempty → (interior K₂).Nonempty → IsCompact K₁ → IsCompact K₂ →
          Disjoint K₁ K₂ →
          K₁ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
          K₂ ⊆ Metric.ball (0 : ℂ) (2 * (b : ℝ)) →
          ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ euclidSetDist K₁ K₂ →
          ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤
            euclidSetDist K₁ (Metric.sphere (0 : ℂ) b) →
          P (CountingBadEventV2 h D D' ξ Q cPlus R
            (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩ K₁ K₂) ≤
            ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ))) :
    C45BallsAt P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict pbar R params family := by
  intro μ η
  obtain ⟨C, ε₀, hC⟩ := hC μ η
  have hint : ∀ (x : ℂ) (s : ℝ), 0 < s → (interior (Metric.closedBall x s)).Nonempty :=
    fun x s hs => ⟨x, interior_mono Metric.ball_subset_closedBall
      (Metric.isOpen_ball.subset_interior_iff.mpr subset_rfl (Metric.mem_ball_self hs))⟩
  exact ⟨C, ε₀, fun ε hε hεle b z w s hs hDisj h₁ h₂ h₃ h₄ =>
    hC ε hε hεle b _ _ (hint z s hs) (hint w s hs) (isCompact_closedBall z s)
      (isCompact_closedBall w s) hDisj h₁ h₂ h₃ h₄⟩

 
theorem c45_closed_pair_bound_balls
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus) (pbar : Set.Ioo (0 : ℝ) 1)
    (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (hC45 : C45BallsAt P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar objs.radii objs.params objs.family)
    (μ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1) :
    ∃ C : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
      ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ →
      ∀ (b : Set.Ioi (0 : ℝ)) (z w : ℂ) (s : ℝ),
        0 < s → s ≤ (b : ℝ) →
        z ∈ Metric.ball (0 : ℂ) b → w ∈ Metric.ball (0 : ℂ) b →
        (η : ℝ) * (b : ℝ) + 2 * s ≤ dist z w →
        (η : ℝ) * (b : ℝ) + s ≤ Metric.infDist z (Metric.sphere (0 : ℂ) b) →
        P (CountingBadEventV2 h D D' ξ Q cPlus objs.radii
          (fun z r hr => (objs.family z r hr).E) b ⟨ε, hε⟩
          (Metric.closedBall z s) (Metric.closedBall w s)) ≤
          ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ)) := by
  obtain ⟨C, ε₀, hC⟩ := hC45 μ η
  refine ⟨C, ε₀, ?_⟩
  intro ε hε hεle b z w s hs hsb hz hw hsep hclear
  have hηb : 0 < (η : ℝ) * (b : ℝ) := mul_pos η.property.1 b.property
  have hDisj : Disjoint (Metric.closedBall z s) (Metric.closedBall w s) :=
    closedBalls_disjoint_of_two_radius_lt z w s (by linarith only [hsep, hηb])
  exact hC ε hε hεle b z w s hs hDisj (closedBall_subset_double_origin z b s hz hsb)
    (closedBall_subset_double_origin w b s hw hsb)
    (euclidSetDist_closedBalls_ge z w s ((η : ℝ) * (b : ℝ)) hsep)
    (euclidSetDist_closedBall_sphere_ge z b s ((η : ℝ) * (b : ℝ)) hclear)

 
theorem r52ClosedDyadic_of_extra_and_C45Balls
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus) (pbar : Set.Ioo (0 : ℝ) 1)
    (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (hExtra : ∀ (κ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
      ∃ ε₀ : Set.Ioo (0 : ℝ) 1, ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ → ∀ j : ℕ,
        ENNReal.ofReal (κ : ℝ) ≤
          P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' (dyadicRadius j) κ
            ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩) →
        ENNReal.ofReal (1 - (η : ℝ)) ≤
          P (AuxiliaryGoodV2 h ξ Q objs.radii
            (fun z r hr => (objs.family z r hr).E) (dyadicRadius j) ⟨ε, hε⟩))
    (hC45 : C45BallsAt P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar objs.radii objs.params objs.family) :
    R52ClosedEndSavingDyadic P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar objs := by
  intro ν κG κEnd η
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  let α : ℝ := 2 * (ξ : ℝ) * (Q + 3)
  have hα : 0 < α := by
    have hξ : 0 < (ξ : ℝ) := ξ.property
    have hQ3 : 0 < Q + 3 := by linarith only [hQ]
    dsimp [α]
    positivity
  let μ : Set.Ioi (0 : ℝ) := ⟨α * (4 * (ν : ℝ) + 1), by
    change 0 < α * (4 * (ν : ℝ) + 1)
    have hν : 0 < (ν : ℝ) := ν.property
    positivity⟩
  let ηHalf : Set.Ioo (0 : ℝ) 1 := ⟨(η : ℝ) / 2, by constructor <;> linarith [η.property.1, η.property.2]⟩
  let ηC : Set.Ioo (0 : ℝ) 1 :=
    ⟨min ((κEnd : ℝ) / 2) (1 / 2), by
      constructor
      · exact lt_min (div_pos κEnd.property (by norm_num)) (by norm_num)
      · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
  obtain ⟨εA, hA⟩ := hExtra κG ηHalf
  obtain ⟨C, εC, hPair⟩ := c45_closed_pair_bound_balls P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hMinus hPlus hstrict pbar objs hC45 μ ηC
  obtain ⟨δ₀, hδ₀⟩ := endpoint_delta_selection α ν εA εC C η κEnd
    hα ν.property εA.property.1 εC.property.1 C.property η.property.1 κEnd.property
  refine ⟨δ₀, ?_⟩
  intro δ hδ hδsmall j
  dsimp only
  intro hG
  let ε : ℝ := (2 * δ) ^ α⁻¹
  obtain ⟨hε, hεA, hεC, hxκ, hx1, hδrate⟩ := hδ₀ δ hδ hδsmall
  let b := dyadicRadius j
  let x : ℝ := δ ^ (ν : ℝ)
  let s : ℝ := x * (b : ℝ)
  let F : Finset ℂ := endpointSites (s / 100) b
  have hx : 0 < x := Real.rpow_pos_of_pos hδ _
  have hs : 0 < s := mul_pos hx b.property
  have hsb : s ≤ (b : ℝ) := by
    simpa only [s, x, one_mul] using
      (mul_le_mul_of_nonneg_right hx1 b.property.le)
  have hεpow : ε ^ α = 2 * δ := Real.rpow_inv_rpow (by positivity) hα.ne'
  let Aux : Set Ω := AuxiliaryGoodV2 h ξ Q objs.radii
    (fun z r hr => (objs.family z r hr).E) b ⟨ε, hε⟩
  let Good : Set Ω := ClosedEndSaving h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd
  let Eligible : ℂ → ℂ → Prop := fun z w =>
    z ∈ Metric.ball (0 : ℂ) b ∧ w ∈ Metric.ball (0 : ℂ) b ∧
      (κEnd : ℝ) * (b : ℝ) ≤ dist z w ∧
      (κEnd : ℝ) * (b : ℝ) ≤ Metric.infDist z (Metric.sphere (0 : ℂ) b)
  let Bad : ℂ → ℂ → Set Ω := fun z w =>
    {ω | Eligible z w ∧
      ω ∈ CountingBadEventV2 h D D' ξ Q cPlus objs.radii
        (fun z r hr => (objs.family z r hr).E) b ⟨ε, hε⟩
        (Metric.closedBall z s) (Metric.closedBall w s)}
  let BadUnion : Set Ω := ⋃ p ∈ F ×ˢ F, Bad p.1 p.2
  have hAux : ENNReal.ofReal (1 - (η : ℝ) / 2) ≤ P Aux :=
    hA ε hε hεA j hG
  have hPairBound : ∀ z ∈ F, ∀ w ∈ F,
      P (Bad z w) ≤ ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ)) := by
    intro z _ w _
    by_cases he : Eligible z w
    · rcases he with ⟨hz, hw, hsep, hclear⟩
      have hηCκ : (ηC : ℝ) ≤ (κEnd : ℝ) / 2 := min_le_left _ _
      have hsep' : (ηC : ℝ) * (b : ℝ) + 2 * s ≤ dist z w := by
        have h1 := mul_le_mul_of_nonneg_right hηCκ b.property.le
        have h2 := mul_le_mul_of_nonneg_right hxκ b.property.le
        dsimp [s, x] at *
        nlinarith only [h1, h2, hsep]
      have hclear' : (ηC : ℝ) * (b : ℝ) + s ≤
          Metric.infDist z (Metric.sphere (0 : ℂ) b) := by
        have h1 := mul_le_mul_of_nonneg_right hηCκ b.property.le
        have h2 := mul_le_mul_of_nonneg_right hxκ b.property.le
        dsimp [s, x] at *
        have hκb : 0 ≤ (κEnd : ℝ) * (b : ℝ) := mul_nonneg κEnd.property.le b.property.le
        linarith only [h1, h2, hclear, hκb]
      have hb := hPair ε hε hεC b z w s hs hsb hz hw hsep' hclear'
      exact (measure_mono (by intro ω hω; exact hω.2)).trans hb
    · have hempty : Bad z w = ∅ := by
        ext ω
        simp only [Bad, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hω => he hω.1
      rw [hempty, measure_empty]
      exact bot_le
  have hUnion : P BadUnion ≤ (F.card : ℝ≥0∞) ^ 2 *
      ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ)) :=
    measure_pair_union_le P F Bad _ hPairBound
  have hN : (F.card : ℝ) * x ^ 2 ≤ (203 : ℝ) ^ 2 := by
    simpa only [F, s] using endpointSites_card_scale_bound b x b.property hx hx1
  have hnum : (F.card : ℝ) ^ 2 * (C : ℝ) * ε ^ (μ : ℝ) ≤ (η : ℝ) / 2 := by
    exact endpoint_union_numeric α ν C η ε δ F.card hε hδ C.property
      (by positivity) hεpow hN hδrate
  have hBad : P BadUnion ≤ ENNReal.ofReal ((η : ℝ) / 2) := by
    calc
      P BadUnion ≤ (F.card : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ)) := hUnion
      _ = ENNReal.ofReal ((F.card : ℝ) ^ 2 * (C : ℝ) * ε ^ (μ : ℝ)) := by
        have hn : 0 ≤ (F.card : ℝ) := by positivity
        have hsq : (F.card : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((F.card : ℝ) ^ 2) := by
          rw [ENNReal.ofReal_pow hn 2, ENNReal.ofReal_natCast]
        rw [hsq, ← ENNReal.ofReal_mul (sq_nonneg (F.card : ℝ))]
        congr 1
        ring
      _ ≤ ENNReal.ofReal ((η : ℝ) / 2) := ENNReal.ofReal_le_ofReal hnum
  have hsub : Aux ⊆ Good ∪ BadUnion := by
    intro ω hω
    by_cases hGood : ω ∈ Good
    · exact Or.inl hGood
    · right
      by_contra hBadUnion
      have hAuxAt := hω
      obtain ⟨hbr, hcircle, _, _⟩ := hω
      apply hGood
      refine ⟨hbr, hcircle, ?_⟩
      intro i j
      dsimp only
      intro hzi hwj hsep hclear
      let z := LQGMetric.GM.gridPt (s / 100) i
      let w := LQGMetric.GM.gridPt (s / 100) j
      have hzF : z ∈ F := gridPt_mem_endpointSites (by dsimp [s]; positivity) hzi
      have hwF : w ∈ F := gridPt_mem_endpointSites (by dsimp [s]; positivity) hwj
      have he : Eligible z w := ⟨hzi, hwj, hsep, hclear⟩
      have hnotBad : ω ∉ Bad z w := by
        intro hbad
        apply hBadUnion
        change ω ∈ ⋃ p ∈ F ×ˢ F, Bad p.1 p.2
        exact Set.mem_biUnion (x := (z, w))
          (Finset.mem_product.mpr ⟨hzF, hwF⟩) hbad
      have hnotCounting : ω ∉ CountingBadEventV2 h D D' ξ Q cPlus objs.radii
          (fun z r hr => (objs.family z r hr).E) b ⟨ε, hε⟩
          (Metric.closedBall z s) (Metric.closedBall w s) := by
        intro hc
        exact hnotBad ⟨he, hc⟩
      have hAuxAt' : ω ∈ AuxiliaryGoodV2 h ξ Q objs.radii
          (fun z r hr => (objs.family z r hr).E) b ⟨ε, hε⟩ := hAuxAt
      obtain ⟨hbr', hcircle', hgap⟩ :=
        closed_gap_of_auxiliary_and_counting_exclusion_double h D D' ξ Q
          cPlus objs.radii (fun z r hr => (objs.family z r hr).E)
          b ⟨ε, hε⟩ ⟨δ, hδ⟩ (Metric.closedBall z s) (Metric.closedBall w s)
          ω hεpow hAuxAt' hnotCounting
      have heq : hbr' = hbr := tendsto_nhds_unique hcircle' hcircle
      rw [heq] at hgap
      exact hgap
  exact probability_splice P Aux Good BadUnion η hsub hAux hBad


 
theorem selected_endgame_dyadic_of_C45Balls :
    ∃ pbar : Set.Ioo (0 : ℝ) 1,
      ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
        (hD : IsWeakLQGMetric ξ Q D) → (hD' : IsWeakLQGMetric ξ Q D') →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), (hGFF : IsNormalizedWholePlaneGFF h P) →
      ∀ cMinus cPlus : ℝ≥0∞,
        (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∀ hstrict : cMinus < cPlus,
      ∀ objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar,
        C45BallsAt P h ξ Q D D' hD
          hD' hGFF
          cMinus cPlus hMinus
          hPlus
          hstrict pbar objs.radii objs.params objs.family →
        R52ClosedEndSavingDyadic P h ξ Q D D'
          hD hD'
          hGFF cMinus cPlus
          hMinus
          hPlus
          hstrict pbar objs ∧
        ∀ θ : Set.Ioi (0 : ℝ),
          R53OfObjectsDyadic P h ξ Q D D'
            hD hD'
            hGFF cMinus cPlus
            hMinus
            hPlus
            hstrict pbar objs θ := by
  obtain ⟨pbar, hExtra⟩ := EndSaving.MainExtraV2.lemMainExtraV2
  refine ⟨pbar, ?_⟩
  intro ξ Q D D' hD hD' Ω _ P _ h hGFF cMinus cPlus hMinus hPlus hstrict objs hC45
  have hExtraHere := hExtra ξ Q D D' hD hD' P h hGFF cMinus cPlus
    hMinus hPlus hstrict objs
  have hR52 := r52ClosedDyadic_of_extra_and_C45Balls P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hMinus hPlus hstrict pbar objs hExtraHere hC45
  exact ⟨hR52, fun θ => r53OfClosedR52Dyadic P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hMinus hPlus hstrict pbar objs θ hR52⟩


 
theorem hMAIN_fixed_from_selected_endgame_C45Balls {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hS36upper : ∃ θ : Set.Ioi (0 : ℝ),
      ∃ a : Set.Ioo (3 / 4 : ℝ) 1,
      ∃ p : Set.Ioo (0 : ℝ) 1,
        ∀ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
          ∃ n₁ : ℕ, ∀ n ≥ n₁,
            3 * n ≤ 4 * (upperGood P h D D' ξ Q a θ
              ⟨Ctop, Ctop.property.1⟩ p n).card)
    (hS36lower : ∀ Cmid : {x : ℝ // cMinus.toReal < x},
      ∃ κ : Set.Ioi (0 : ℝ), ∃ n₂ : ℕ, ∀ n ≥ n₂,
        3 * n ≤ 4 * (lowerGood P h D D' κ
          ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ n).card)
    (hT58 : ∀ pbar : Set.Ioo (0 : ℝ) 1, cMinus < cPlus →
      ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (hC45 : ∀ (hstrict : cMinus < cPlus) (pbar : Set.Ioo (0 : ℝ) 1)
      (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar),
        C45BallsAt P h ξ Q D D' hD hD' hGFF
          cMinus cPlus hMinus hPlus hstrict pbar objs.radii objs.params objs.family) :
    cMinus = cPlus := by
  obtain ⟨pbar, hEndgame⟩ := selected_endgame_dyadic_of_C45Balls
  apply hMAIN_fixed_common_exists_theta_v2 P h D D' ξ Q cMinus cPlus
    hPlusPos hMinus hPlus pbar hS36upper hS36lower
    (fun hstrict => hT58 pbar hstrict)
  intro hstrict θ objs a κ p
  have hC := hC45 hstrict pbar objs
  have hR53 := (hEndgame ξ Q D D' hD hD' P h hGFF cMinus cPlus
    hMinus hPlus hstrict objs hC).2 θ
  exact r53Dyadic_to_collision P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hMinus hPlus hstrict pbar objs θ hR53 a κ p


 

theorem hMAIN_of_inputs_balls (hS36 : S36Input) (hT58 : T58Input) (hC45 : C45BallsInput) :
    ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric), IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus = cPlus := by
  intro ξ Q hQ D D' hD hD' Ω _ P _ h hGFF cMinus cPlus hMinus hPlus
  obtain ⟨m, M, hmPos, hmFin, hMPos, hMFin, hm, hM⟩ :=
    OptimalConstants.Determinism.hDET_proved ξ Q hQ D D' hD hD' P h hGFF
  obtain ⟨θ, a, p, hUpper⟩ :=
    hS36.1 ξ Q hQ D D' hD hD' P h hGFF M hMPos hMFin hM
  have hLower := hS36.2 ξ Q hQ D D' hD hD' P h hGFF m hmPos hmFin hm
  have hObjects : ∀ pbar : Set.Ioo (0 : ℝ) 1, m < M →
      ObjectsExistV2 P h D D' ξ Q m M pbar := fun pbar hstrict =>
    Classical.choice (hT58 P h ξ Q D D' hD hD' hGFF m M hm hM hstrict pbar)
  have hmEqM := hMAIN_fixed_from_selected_endgame_C45Balls P h D D' ξ Q hD hD'
    hGFF m M hMPos hm hM ⟨θ, a, p, hUpper⟩ hLower hObjects
    (fun hstrict pbar objs => hC45 P h ξ Q D D' hD hD' hGFF m M hm hM hstrict pbar
      objs.radii objs.params objs.family)
  have hcMinus : cMinus = m := by
    obtain ⟨ω, hω, hω'⟩ := (hMinus.and hm).exists
    exact hω.symm.trans hω'
  have hcPlus : cPlus = M := by
    obtain ⟨ω, hω, hω'⟩ := (hPlus.and hM).exists
    exact hω.symm.trans hω'
  exact hcMinus.trans (hmEqM.trans hcPlus.symm)

 

theorem weakLQGMetric_unique_of_inputs_balls (hS36 : S36Input) (hT58 : T58Input)
    (hC45 : C45BallsInput) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) :=
  Assembly.Root.weakLQGMetric_unique_of_main OptimalConstants.Determinism.hDET_proved (hMAIN_of_inputs_balls hS36 hT58 hC45)

 
example (hS36 : S36Input) (hT58 : T58Input) (hC45 : C45Input) :=
  weakLQGMetric_unique_of_inputs_balls hS36 hT58 (c45BallsInput_of_c45Input hC45)

end SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs

