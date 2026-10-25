import SupercriticalLQGUniqueness.B2.Final.DG20CoupledCoords
import SupercriticalLQGUniqueness.B2.DG20Lim.GoodCircleCoupled
import SupercriticalLQGUniqueness.B2.DG20Lim.NestedGoodCostConv
import SupercriticalLQGUniqueness.B2.DG20Lim.GeometryLSCGlue

 


















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify CoordJ pairJ)
open SupercriticalLQGUniqueness.B2.Iface
open SupercriticalLQGUniqueness.B2.DG20Lim (RatCoords RData RatAnnulus finiteRatCoords
  normalizedContLFPP measurableRatCoordsVersion)

namespace SupercriticalLQGUniqueness.B2.Final

theorem continuous_pairJ_top : Continuous (pairJ ⊤ : DistC → CoordJ → ℝ) :=
  continuous_pi fun c => continuous_eval_const (LQGMetric.comb ⊤ c)

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
  {e : ℕ → Set.Ioi (0 : ℝ)} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
  {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {h' : Ω' → DistC}
  {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}

 
theorem coupled_good_circles [IsProbabilityMeasure P']
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate')
    (hB : DG20CouplingData ξ Q m e c V P' h' hN L)
    (Z : ℕ → Ω' → RatCoords) (Zlim : Ω' → RatCoords) (hZm : ∀ n, Measurable (Z n))
    (hZid : ∀ᵐ ω ∂P', ∀ n, Z n ω =
      finiteRatCoords (normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))))
    (hZconv : ∀ ω, Tendsto (fun n => Z n ω) atTop (𝓝 (Zlim ω)))
    (hLink : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O O' => (Zlim ω).1 (O, O')) ∧ R.around = (Zlim ω).2 ∧
      (L ω).toLSCFun.1 = R.toLSCFun.1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O O' => (Zlim ω).1 (O, O')) ∧ R.around = (Zlim ω).2 ∧
      (L ω).toLSCFun.1 = R.toLSCFun.1 ∧
      ∀ z : ℂ, ∃ B : ℕ → RatAnnulus,
        (∀ n, (B n).inner.Surrounds z ∧
          R.around (B n) ≤ C * R.across (B n).inner (B n).outer) ∧
        (∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer) ∧
        Tendsto (fun n => (((B n).outer.radius : ℝ))) atTop (𝓝 0) ∧
        ∀ w : ℂ, w ≠ z → (L ω) (z, w) < ⊤ →
          Tendsto (fun n => R.across (B n).inner (B n).outer) atTop (𝓝 0) ∧
          Tendsto (fun n => R.around (B n)) atTop (𝓝 0) := by
  obtain ⟨hprob, hcan⟩ := PfeAxioms.normalized_canonical_model
  have := hprob
  have hX : ∀ δ, IsHeatSmoothing normGFFLaw id δ (V δ) :=
    PfeLocal.l1_isHeatSmoothing_canonical V hB.heat_ae
  let Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords := fun n ω => (pairJ ⊤ (hN n ω), Z n ω)
  let Ylim : Ω' → (CoordJ → ℝ) × RatCoords := fun ω => (pairJ ⊤ (h' ω), Zlim ω)
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    ((LQGMetric.measurable_pairJ ⊤).comp (hB.field_measurable n)).prodMk (hZm n)
  have hLaw : ∀ n, P'.map (Y n) = normGFFLaw.map (fun ω =>
      (pairJ ⊤ (id ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) ω))
        (DG20Lim.aemeasurable_normalizedContLFPP_heat_version normGFFLaw id hcan
          (e n) (m (e n)) (ξ : ℝ) (V (e n)) (hX (e n))) ω)) := by
    intro n
    let hDa := DG20Lim.aemeasurable_normalizedContLFPP_heat_version normGFFLaw id hcan
      (e n) (m (e n)) (ξ : ℝ) (V (e n)) (hX (e n))
    let f : DistC → RatCoords := measurableRatCoordsVersion
      (fun ω => normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) ω)) hDa
    have hf : Measurable f := DG20Lim.measurable_measurableRatCoordsVersion _ hDa
    have hfae : ∀ᵐ g ∂normGFFLaw,
        finiteRatCoords (normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) g)) = f g :=
      (DG20Lim.aemeasurable_finiteRatCoords _ hDa).ae_eq_mk
    have hfae' : ∀ᵐ ω ∂P',
        finiteRatCoords (normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))) =
          f (hN n ω) := by
      have : ∀ᵐ g ∂(P'.map (hN n)),
          finiteRatCoords (normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) g)) = f g := by
        rw [hB.field_law n]
        exact hfae
      exact ae_of_ae_map (hB.field_measurable n).aemeasurable this
    have hG : Measurable (fun g : DistC => (pairJ ⊤ g, f g)) :=
      (LQGMetric.measurable_pairJ ⊤).prodMk hf
    calc P'.map (Y n) = P'.map ((fun g : DistC => (pairJ ⊤ g, f g)) ∘ hN n) := by
          refine Measure.map_congr ?_
          filter_upwards [hZid, hfae'] with ω hω hω'
          simp only [Y, Function.comp_apply, hω n, hω']
      _ = (P'.map (hN n)).map (fun g : DistC => (pairJ ⊤ g, f g)) :=
          (Measure.map_map hG (hB.field_measurable n)).symm
      _ = _ := by rw [hB.field_law n]; rfl
  have hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)) := by
    filter_upwards [hB.field_tendsto] with ω hω
    exact ((continuous_pairJ_top.tendsto (h' ω)).comp hω).prodMk_nhds (hZconv ω)
  have hRData : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧ R.around = (Ylim ω).2.2 :=
    hLink.mono fun _ hω => by
      obtain ⟨R, ha, hb, _⟩ := hω
      exact ⟨R, ha, hb⟩
  obtain ⟨C, -, hGood⟩ :=
    DG20Lim.exists_nested_good_circles_on_coupled_limit_of_inputs
      hS4 hPerc ξ Q hB.exponent m hB.normalizer normGFFLaw P' id hcan V hX e
      hB.scale_tendsto Y Ylim hYm hLaw hConv hRData
  let C' : ℝ≥0∞ := ENNReal.ofReal 2 *
    (ENNReal.ofReal 2 * ENNReal.ofReal C * ENNReal.ofReal 2) * ENNReal.ofReal 2
  have hC' : C' ≠ ∞ := by
    simp only [C']
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top)) ENNReal.ofReal_ne_top
  refine ⟨C', hC', ?_⟩
  filter_upwards [hGood, hLink] with ω hG hL
  obtain ⟨R, ha, hb, hz⟩ := hG
  obtain ⟨S, hSa, -, hLS⟩ := hL
  have hRS : R.across = S.across := ha.trans hSa.symm
  have hLR : (L ω).toLSCFun.1 = R.toLSCFun.1 := by
    rw [hLS]
    funext p
    simp only [DG20Lim.RData.toLSCFun, DG20Lim.RData.DfromR_eq_of_across hRS]
  refine ⟨R, ha, hb, hLR, fun z => ?_⟩
  obtain ⟨B, hBgood, hBnest, hBrad⟩ := hz z
  refine ⟨B, hBgood, hBnest, hBrad, fun w hwz hfin => ?_⟩
  have hD : R.DfromR z w ≠ ∞ := by
    have h1 := congrFun hLR (z, w)
    simp only [LSCMetric.toLSCFun, DG20Lim.RData.toLSCFun] at h1
    have h2 : (L ω) (z, w) = R.DfromR z w := EReal.coe_ennreal_injective h1
    rw [← h2]
    exact hfin.ne
  exact R.nested_good_annulus_costs_tendsto_zero B C' hC' z w hwz.symm hD hBgood hBnest hBrad

end SupercriticalLQGUniqueness.B2.Final
