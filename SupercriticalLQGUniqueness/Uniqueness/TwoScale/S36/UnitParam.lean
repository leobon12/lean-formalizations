import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.GeoCompact




 










set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)
open LQGMetric.MetricGeometry

 

theorem exists_unit_internal_param (d : LSCMetric) (z : ℂ) (r : ℝ) {P : ℝ → ℂ} {s t : ℝ}
    (hP : TwoScale.S36Events.InternalBoundaryGeodesic d z r P s t) :
    ∃ (Pth : ℝ → ℂ) (T : ℝ), 0 ≤ T ∧ d.IsCurve Pth 0 T ∧
      MapsTo Pth (Icc 0 T) (TwoScale.S36Events.eventCarrier z r) ∧
      (∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
        internalEDist (d.pt '' TwoScale.S36Events.eventCarrier z r) (d.pt (Pth u)) (d.pt (Pth v)) =
          ENNReal.ofReal (v - u)) ∧
      Pth 0 = P s ∧ Pth T = P t ∧
      ∀ w ∈ Icc s t, ∃ σ ∈ Icc 0 T, Pth σ = P w := by
  obtain ⟨hu, hv, hcurve, htr, -, -, hlen, hfin⟩ := hP
  set Y := TwoScale.S36Events.eventCarrier z r with hYdef
  have hst : s ≤ t := hcurve.1
  have hcont : ContinuousOn (d.pt ∘ P) (Icc s t) := hcurve.2
  have hL : curveLength (d.pt ∘ P) s t ≠ ⊤ := hfin.ne
  set T := (curveLength (d.pt ∘ P) s t).toReal with hTdef
  let Pth : ℝ → ℂ := fun τ => @lengthParam d.Space _ (d.pt ∘ P) s t τ
  have hPD : d.pt ∘ Pth = lengthParam (d.pt ∘ P) s t := by
    funext τ
    rfl
  have hunit := hasUnitSpeedOn_lengthParam hst hcont hL
  have hlip := lipschitzOnWith_lengthParam hst hcont hL
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have himage := variationOnFromTo_image_Icc hst hcont hL
  have himg : ∀ τ ∈ Icc 0 T, ∃ w ∈ Icc s t, Pth τ = P w := by
    intro τ hτ
    have hτ' : τ ∈ variationOnFromTo (d.pt ∘ P) (Icc s t) s '' Icc s t := by
      rw [himage]
      exact hτ
    obtain ⟨w, hw, hwτ⟩ := hτ'
    refine ⟨w, hw, ?_⟩
    have h2 := lengthParam_variationOnFromTo hL hw
    rw [hwτ] at h2
    exact h2
  have hpre : ∀ w ∈ Icc s t, ∃ σ ∈ Icc 0 T, Pth σ = P w := by
    intro w hw
    refine ⟨variationOnFromTo (d.pt ∘ P) (Icc s t) s w, ?_, lengthParam_variationOnFromTo hL hw⟩
    rw [← himage]
    exact ⟨w, hw, rfl⟩
  have hmaps : MapsTo Pth (Icc 0 T) Y := by
    intro τ hτ
    obtain ⟨w, hw, hEq⟩ := himg τ hτ
    rw [hEq]
    exact htr w hw
  have hP0 : Pth 0 = P s := by
    have h := lengthParam_variationOnFromTo hL (left_mem_Icc.mpr hst)
    rw [variationOnFromTo.self] at h
    exact h
  have hPT : Pth T = P t := by
    have h := lengthParam_variationOnFromTo hL (right_mem_Icc.mpr hst)
    have hσ : variationOnFromTo (d.pt ∘ P) (Icc s t) s t = T := by
      rw [variationOnFromTo.eq_of_le _ _ hst, inter_self]
      rfl
    rw [hσ] at h
    exact h
  have hcurve' : d.IsCurve Pth 0 T := ⟨hT0, by rw [hPD]; exact hlip.continuousOn⟩
  
  have hle : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (d.pt '' Y) (d.pt (Pth u)) (d.pt (Pth v)) ≤ ENNReal.ofReal (v - u) := by
    intro u v hu' hv' huv
    have hsub : Icc u v ⊆ Icc 0 T := Icc_subset_Icc hu'.1 hv'.2
    have hc : ContinuousOn (d.pt ∘ Pth) (Icc u v) := by
      rw [hPD]
      exact hlip.continuousOn.mono hsub
    have hm : MapsTo (d.pt ∘ Pth) (Icc u v) (d.pt '' Y) := fun τ hτ =>
      ⟨Pth τ, hmaps (hsub hτ), rfl⟩
    calc internalEDist (d.pt '' Y) (d.pt (Pth u)) (d.pt (Pth v))
        = internalEDist (d.pt '' Y) ((d.pt ∘ Pth) u) ((d.pt ∘ Pth) v) := rfl
      _ ≤ curveLength (d.pt ∘ Pth) u v := internalEDist_le_curveLength huv hc hm
      _ = ENNReal.ofReal (v - u) := by
        rw [hPD]
        exact curveLength_of_hasUnitSpeedOn hunit hu' hv'
  have htot : internalEDist (d.pt '' Y) (d.pt (Pth 0)) (d.pt (Pth T)) = ENNReal.ofReal T := by
    rw [hP0, hPT]
    have h1 := LSCMetric.internal_eq_internalEDist d Y (⟨P s, hu⟩, ⟨P t, hv⟩)
    rw [← h1, ← hlen, hTdef, ENNReal.ofReal_toReal hL]
    rfl
  have hge : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      ENNReal.ofReal (v - u) ≤ internalEDist (d.pt '' Y) (d.pt (Pth u)) (d.pt (Pth v)) := by
    intro u v hu' hv' huv
    by_contra hlt
    push Not at hlt
    have h1 := internalEDist_triangle (d.pt '' Y) (d.pt (Pth 0)) (d.pt (Pth u)) (d.pt (Pth T))
    have h2 := internalEDist_triangle (d.pt '' Y) (d.pt (Pth u)) (d.pt (Pth v)) (d.pt (Pth T))
    have h3 := hle 0 u ⟨le_rfl, hT0⟩ hu' hu'.1
    have h4 := hle v T hv' ⟨hT0, le_rfl⟩ hv'.2
    rw [htot] at h1
    rw [sub_zero] at h3
    have hsum : ENNReal.ofReal u + (ENNReal.ofReal (v - u) + ENNReal.ofReal (T - v)) =
        ENNReal.ofReal T := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith [hv'.2]),
        ← ENNReal.ofReal_add hu'.1 (by linarith [hv'.2])]
      congr 1
      ring
    have hstrict : ENNReal.ofReal u +
        (internalEDist (d.pt '' Y) (d.pt (Pth u)) (d.pt (Pth v)) + ENNReal.ofReal (T - v)) <
        ENNReal.ofReal T := by
      rw [← hsum]
      exact ENNReal.add_lt_add_left ENNReal.ofReal_ne_top
        (ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hlt)
    have hchain : ENNReal.ofReal T ≤ ENNReal.ofReal u +
        (internalEDist (d.pt '' Y) (d.pt (Pth u)) (d.pt (Pth v)) + ENNReal.ofReal (T - v)) :=
      h1.trans (add_le_add h3 (h2.trans (add_le_add le_rfl h4)))
    exact lt_irrefl _ (hchain.trans_lt hstrict)
  exact ⟨Pth, T, hT0, hcurve', hmaps, fun u v hu' hv' huv => le_antisymm (hle u v hu' hv' huv)
    (hge u v hu' hv' huv), hP0, hPT, hpre⟩

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
