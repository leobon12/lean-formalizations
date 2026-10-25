import SupercriticalLQGUniqueness.B2.PfeWeyl.LocalizedSampling
import SLUMetricAPI2

 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

theorem exists_near_min_ordinary_curve (D : LSCMetric)
    (hD : D.IsLengthSpace) (z w : ℂ) (hfin : D (z, w) < ⊤)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (P : ℝ → ℂ) (L : ℝ), D.IsCurve P 0 L ∧
      HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L) ∧
      P 0 = z ∧ P L = w ∧
      D.len P 0 L < D (z, w) + ENNReal.ofReal δ := by
  obtain ⟨Q, a, b, hQ, hQa, hQb, hlen⟩ :=
    hD z w hfin (δ / 2) (half_pos hδ)
  have hbound : D.len Q a b < D (z, w) + ENNReal.ofReal δ := by
    refine hlen.trans_lt ?_
    exact ENNReal.add_lt_add_left hfin.ne
      ((ENNReal.ofReal_lt_ofReal_iff hδ).2 (by linarith))
  have hlenfin : D.len Q a b ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
      ⟨hfin.ne, ENNReal.ofReal_ne_top⟩) hlen
  let L : ℝ := (LQGMetric.MetricGeometry.curveLength (D.pt ∘ Q) a b).toReal
  let P : ℝ → ℂ := fun t =>
    @LQGMetric.MetricGeometry.lengthParam D.Space _ (D.pt ∘ Q) a b t
  have hP_eq : D.pt ∘ P = LQGMetric.MetricGeometry.lengthParam (D.pt ∘ Q) a b := by
    funext t
    dsimp [P, Function.comp_def, LSCMetric.pt]
    rfl
  have hprops := HigherDimLQGMetric.lengthParam_props hQ.1 hQ.2 hlenfin
    (S := Set.univ) (fun _ _ => Set.mem_univ _)
  obtain ⟨hu, hc, hp0, hpL, _⟩ := hprops
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hplen : D.len P 0 L = ENNReal.ofReal L := by
    change LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) 0 L = _
    rw [hP_eq]
    simpa only [sub_zero] using
      (LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn
        hu ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩)
  refine ⟨P, L, ⟨hL, hc⟩, hu, ?_, ?_, ?_⟩
  · exact hp0.trans hQa
  · exact hpL.trans hQb
  · rw [hplen, show ENNReal.ofReal L = D.len Q a b from
      ENNReal.ofReal_toReal hlenfin]
    exact hbound

 
theorem exists_localized_near_min_ordinary_curve
    (D : LSCMetric) (hD : D.IsLengthSpace) (ξ : ℝ) (f : C(ℂ, ℝ))
    {K K' : Set ℂ} (hloc : LocalizedNearMinPaths D ξ f K K')
    (z : ℂ) (hz : z ∈ K) (w : ℂ) (hw : w ∈ K)
    (hfin : D (z, w) < ⊤) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (P : ℝ → ℂ) (L : ℝ), D.IsCurve P 0 L ∧
      HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L) ∧
      P 0 = z ∧ P L = w ∧ P '' Icc 0 L ⊆ K' ∧
      D.len P 0 L < D (z, w) + ENNReal.ofReal δ := by
  obtain ⟨P, L, hP, hu, hP0, hPL, hlen⟩ :=
    exists_near_min_ordinary_curve D hD z w hfin hδ
  have hδle : ENNReal.ofReal δ ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hδ1
  have hlen1 : D.len P 0 L < D (z, w) + 1 :=
    hlen.trans_le (by simpa only [add_comm] using
      (add_le_add_right hδle (D (z, w))))
  exact ⟨P, L, hP, hu, hP0, hPL,
    hloc z hz w hw P L hP hu hP0 hPL (Or.inl hlen1), hlen⟩

end SupercriticalLQGUniqueness.B2.PfeWeyl
