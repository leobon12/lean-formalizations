import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath.R53
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.A16Scopes
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.AssemblyV2




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open LQGMetric (DistC)
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame

 
theorem r53OfClosedR52Dyadic
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (objs : EndSaving.InterfaceV2.ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (θ : Set.Ioi (0 : ℝ))
    (hR52 : R52ClosedEndSavingDyadic P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar objs) :
    R53OfObjectsDyadic P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar objs θ := by
  intro a κ p
  have hcReal : 0 < cPlus.toReal := by
    have hm : 0 ≤ cMinus.toReal := ENNReal.toReal_nonneg
    have hlow := objs.cMid'_lower
    have hupp := objs.cMid'_upper
    dsimp [EndSaving.Interfaces.midpoint] at hupp
    linarith
  have hcFinite : cPlus ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hcReal).2.ne
  let c : NNReal := ⟨cPlus.toReal, hcReal.le⟩
  have hc : 0 < c := hcReal
  have hcEq : (c : ℝ≥0∞) = cPlus := by
    rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal cPlus.toReal = cPlus
    exact ENNReal.ofReal_toReal hcFinite
  let ν : Set.Ioi (0 : ℝ) := ⟨2 / (θ : ℝ) + 1, by
    have ht : 0 < (θ : ℝ) := θ.property
    exact Set.mem_Ioi.mpr (add_pos_of_nonneg_of_pos
      (div_nonneg (by norm_num) ht.le) zero_lt_one)⟩
  have hν : 2 / (θ : ℝ) < (ν : ℝ) := by dsimp [ν]; linarith
  let κEnd : Set.Ioi (0 : ℝ) :=
    ⟨(1 - (a : ℝ)) / 2,
      div_pos (sub_pos.mpr a.property.2) (by norm_num)⟩
  let η : Set.Ioo (0 : ℝ) 1 :=
    ⟨(p : ℝ) / 4, by constructor <;> nlinarith [p.property.1, p.property.2]⟩
  obtain ⟨δDet, hδDet0, hδDet1, hdet⟩ :=
    EndSaving.FivePath.deterministic_five_path_gap h D D' ξ Q c hc a θ ν hν
  obtain ⟨δEnd, hδEndApply⟩ := hR52 ν κ κEnd η
  obtain ⟨δSmall, hδSmall0, hδSmall1, hsmall⟩ :=
    EndSaving.FivePath.exists_uniform_R53_scale a θ c hc ν hν
  let q : ℝ := (1 - (a : ℝ)) / 4
  have hq : 0 < q := div_pos (sub_pos.mpr a.property.2) (by norm_num)
  let m : ℝ := min δDet (min (δEnd : ℝ) δSmall)
  have hm : 0 < m := lt_min hδDet0 (lt_min δEnd.property.1 hδSmall0)
  let δ₀ : ℝ := q * m / 2
  have hδ₀pos : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hhalfpos : 0 < m / 2 := by positivity
  have hhalfsmall : m / 2 ≤ δSmall := by
    dsimp [m]
    nlinarith only [hm, min_le_right δDet (min (δEnd : ℝ) δSmall),
      min_le_right (δEnd : ℝ) δSmall]
  have hδ₀C : δ₀ < cPlus.toReal := by
    have h := (hsmall (m / 2) hhalfpos hhalfsmall).2.2.2
    change q * (m / 2) < cPlus.toReal at h
    simpa only [δ₀, mul_div_assoc] using h
  refine ⟨⟨δ₀, hδ₀pos, hδ₀C⟩, ?_⟩
  intro δOut hδOut hδOutSmall j
  dsimp only
  intro hG
  let b := EndSaving.Interfaces.dyadicRadius j
  let δ : ℝ := δOut / q
  have hδ : 0 < δ := div_pos hδOut hq
  have hδm : δ ≤ m / 2 := by
    dsimp [δ, δ₀] at *
    exact (div_le_iff₀ hq).2 (by nlinarith only [hδOutSmall, hq.ne'])
  have hδDet : δ ≤ δDet := by
    dsimp [m] at hδm
    nlinarith only [hδm, hm, min_le_left δDet (min (δEnd : ℝ) δSmall)]
  have hδEnd : δ ≤ (δEnd : ℝ) := by
    dsimp [m] at hδm
    nlinarith only [hδm, hm, min_le_right δDet (min (δEnd : ℝ) δSmall),
      min_le_left (δEnd : ℝ) δSmall]
  let Good := EndSaving.FivePath.closedSavingVersion h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd
  let Bad := h ⁻¹' {g | OptimalConstants.Ratios.HEvent D D' ξ Q b a
    ⟨cPlus.toReal - δOut, sub_pos.mpr
      (lt_of_le_of_lt hδOutSmall (show δ₀ < cPlus.toReal from hδ₀C))⟩ θ g}
  have hGoodMeas : MeasurableSet Good :=
    EndSaving.FivePath.measurable_closedSavingVersion h hGFF.1.measurable D D' hD.1 hD'.1
      ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd
  have hGoodProb : ENNReal.ofReal (1 - (η : ℝ)) ≤ P Good := by
    calc
      _ ≤ P (EndSaving.Interfaces.ClosedEndSaving h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd) :=
        hδEndApply δ hδ hδEnd j hG
      _ = P Good := EndSaving.FivePath.closedSaving_ae_eq P h D D' ξ Q cPlus b ν
        ⟨δ, hδ⟩ κEnd (ae_isCircleAverage_old hGFF.1 b 0)
  have hGoodAdd : 1 ≤ P Good + ENNReal.ofReal (η : ℝ) := by
    have hη0 : 0 ≤ (η : ℝ) := η.property.1.le
    have hη1 : 0 ≤ 1 - (η : ℝ) := sub_nonneg.mpr η.property.2.le
    calc
      1 = ENNReal.ofReal ((1 - (η : ℝ)) + (η : ℝ)) := by norm_num
      _ = ENNReal.ofReal (1 - (η : ℝ)) + ENNReal.ofReal (η : ℝ) :=
        ENNReal.ofReal_add hη1 hη0
      _ ≤ P Good + ENNReal.ofReal (η : ℝ) := add_le_add hGoodProb le_rfl
  have hPlusField : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.detGFFPlusCont hGFF.1
  have hDlenAe := hD.2.1 P h hPlusField
  have hD'lenAe := hD'.2.1 P h hPlusField
  have hQA : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hDregAe := BiLipschitz.Barrier.ae_curves_continuous hD hQA P h hGFF
  have hD'regAe := BiLipschitz.Barrier.ae_curves_continuous hD' hQA P h hGFF
  have hCompAe := EndSaving.InterfaceV2.optimal_global_upper P h ξ Q D D' hD hD'
    hGFF cMinus cPlus (ENNReal.toReal_pos_iff.mp hcReal).1 hMinus hPlus
  have hCircleAe := ae_isCircleAverage_old hGFF.1 b 0
  have hExclude : ∀ᵐ ω ∂P, ω ∈ Bad → ω ∉ Good := by
    filter_upwards [hDlenAe, hD'lenAe, hDregAe, hD'regAe,
      hCompAe, hCircleAe] with ω hDlen hD'len hDreg hD'reg hComp hωCircle
    intro hBad hGood
    change OptimalConstants.Ratios.HEvent D D' ξ Q b a
      ⟨cPlus.toReal - δOut, sub_pos.mpr
        (lt_of_le_of_lt hδOutSmall hδ₀C)⟩ θ (h ω) at hBad
    rcases hBad with ⟨hbrH, hCircleH, u, v, hu, hv, _, _, hLower,
      γ, s, t, hGeo, _, _, hDU, hLoopU, hLoopV⟩
    have hEnd : ω ∈ EndSaving.Interfaces.ClosedEndSaving h D D' ξ Q cPlus b ν
        ⟨δ, hδ⟩ κEnd := by
      refine ⟨LQGMetric.circleAvg (h ω) b 0, hωCircle, ?_⟩
      simpa only [Good, EndSaving.FivePath.closedSavingVersion, Set.mem_ofPred_eq] using hGood
    have hStrict := hdet δ hδ hδDet b ω hDlen hD'len hDreg.2.1
      hD'reg.2.1 (by simpa only [hcEq] using hComp)
      (by simpa only [hcEq, κEnd] using hEnd)
      u v hu hv hGeo.2.2.2.2 hLoopU hLoopV hbrH hCircleH hDU
    have hcoef : (c : ℝ) - ((1 - (a : ℝ)) / 4) * δ =
        cPlus.toReal - δOut := by
      have hcancel : q * δ = δOut := by
        dsimp [δ]
        exact mul_div_cancel₀ _ hq.ne'
      change cPlus.toReal - q * δ = cPlus.toReal - δOut
      rw [hcancel]
    have hStrict' : (D' (h ω)) (u, v) <
        ENNReal.ofReal (cPlus.toReal - δOut) * (D (h ω)) (u, v) := by
      simpa only [hcoef] using hStrict
    exact (not_lt_of_ge hLower) hStrict'
  have hBound := EndSaving.FivePath.outer_measure_le_of_ae_exclusion P Good Bad
    (ENNReal.ofReal (η : ℝ)) hGoodMeas hGoodAdd hExclude
  change P Bad < ENNReal.ofReal (p : ℝ)
  exact hBound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by
    have hp : 0 < (p : ℝ) := p.property.1
    positivity)).mpr (by dsimp [η]; nlinarith [p.property.1]))

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
