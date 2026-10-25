import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.A16Scopes
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.C45Pair
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.GridCount
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.GapTransfer
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.ProbabilitySplice
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.FiniteUnion
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.UnionNumerics
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.DeltaSelection
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtraV2.PortMainExtra




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem r52ClosedDyadic_of_extra_and_C45
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
    (hC45 : C45CorrectedNonemptyInternal P h ξ Q D D' hD hD' hGFF
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
  obtain ⟨C, εC, hPair⟩ := c45_closed_pair_bound P h ξ Q D D' hD hD' hGFF
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

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
