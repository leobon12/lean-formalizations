import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.RatioEvLocal




 















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric.MetricGeometry

 
theorem internal_geodesic_avoids (d : LSCMetric) (Y : Set ℂ) {P : ℝ → ℂ} {T : ℝ}
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (d.pt '' Y) (d.pt (P u)) (d.pt (P v)) = ENNReal.ofReal (v - u))
    {s : ℝ} (hs : 0 < s) (x : ℂ) (hBY : Metric.closedBall x (3 * s) ⊆ Y)
    (h0 : 3 * s ≤ dist (P 0) x) (hT : 3 * s ≤ dist (P T) x)
    (hlt : aroundDist d (annOut hs x) < acrossDist d (annIn hs x)) :
    ∀ t ∈ Icc 0 T, s ≤ dist (P t) x := by
  intro t₀ ht₀
  by_contra hin
  push Not at hin
  
  obtain ⟨π, a, b, hπ, htr, hsep, hlen⟩ : ∃ (π : ℝ → ℂ) (a b : ℝ), d.IsCurve π a b ∧
      (∀ τ ∈ Icc a b, π τ ∈ (annOut hs x).toSet) ∧
      Disconnects (π '' Icc a b) (annOut hs x).innerBoundary (annOut hs x).outerBoundary ∧
      d.len π a b < acrossDist d (annIn hs x) := by
    unfold aroundDist at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨π, a, b, hπ, htr, hsep, hlen⟩ := hlt
    exact ⟨π, a, b, hπ, htr, hsep, hlen⟩
  have hsep' : LQGMetric.Disconnects (π '' Icc a b)
      (Metric.sphere x (2 * s)) (Metric.sphere x (3 * s)) :=
    Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hsep
  have h2s : (0 : ℝ) < 2 * s := by positivity
  have h23 : 2 * s < 3 * s := by linarith
  have hout0 : P 0 ∈ (Metric.ball x (3 * s))ᶜ := by
    simp only [mem_compl_iff, Metric.mem_ball, not_lt]
    exact h0
  have houtT : P T ∈ (Metric.ball x (3 * s))ᶜ := by
    simp only [mem_compl_iff, Metric.mem_ball, not_lt]
    exact hT
  have hint₀ : P t₀ ∈ Metric.closedBall x (2 * s) := Metric.mem_closedBall.mpr (by linarith)
  obtain ⟨τ₁, hτ₁, hτ₁K⟩ := Toolkit.PlanarSeparation.pathHit_time ht₀.1 (hP.mono (Icc_subset_Icc le_rfl ht₀.2))
    (Toolkit.PlanarSeparation.annularPath_hit_reverse h2s h23 hsep') hout0 hint₀
  obtain ⟨τ₂, hτ₂, hτ₂K⟩ := Toolkit.PlanarSeparation.pathHit_time ht₀.2 (hP.mono (Icc_subset_Icc ht₀.1 le_rfl))
    (Toolkit.PlanarSeparation.annularPath_hit h2s h23 hsep') hint₀ houtT
  have hτ₁T : τ₁ ∈ Icc 0 T := ⟨hτ₁.1, hτ₁.2.trans ht₀.2⟩
  have hτ₂T : τ₂ ∈ Icc 0 T := ⟨ht₀.1.trans hτ₂.1, hτ₂.2⟩
  have hτ₁₂ : τ₁ ≤ τ₂ := hτ₁.2.trans hτ₂.1
  
  have htrY : ∀ τ ∈ Icc a b, π τ ∈ Y := by
    intro τ hτ
    apply hBY
    have := (htr τ hτ).1
    exact Metric.ball_subset_closedBall this
  obtain ⟨σ₁, hσ₁, hσ₁e⟩ := hτ₁K
  obtain ⟨σ₂, hσ₂, hσ₂e⟩ := hτ₂K
  have hsub : ∀ {u v : ℝ}, u ∈ Icc a b → v ∈ Icc a b → u ≤ v →
      internalEDist (d.pt '' Y) (d.pt (π u)) (d.pt (π v)) ≤ d.len π a b := by
    intro u v hu hv huv
    have hc : ContinuousOn (d.pt ∘ π) (Icc u v) := hπ.2.mono (Icc_subset_Icc hu.1 hv.2)
    have hm : MapsTo (d.pt ∘ π) (Icc u v) (d.pt '' Y) := fun τ hτ =>
      ⟨π τ, htrY τ ⟨hu.1.trans hτ.1, hτ.2.trans hv.2⟩, rfl⟩
    calc internalEDist (d.pt '' Y) (d.pt (π u)) (d.pt (π v))
        = internalEDist (d.pt '' Y) ((d.pt ∘ π) u) ((d.pt ∘ π) v) := rfl
      _ ≤ curveLength (d.pt ∘ π) u v := internalEDist_le_curveLength huv hc hm
      _ ≤ curveLength (d.pt ∘ π) a b := curveLength_mono (d.pt ∘ π) hu.1 hv.2
      _ = d.len π a b := rfl
  have hY12 : internalEDist (d.pt '' Y) (d.pt (P τ₁)) (d.pt (P τ₂)) ≤ d.len π a b := by
    rw [← hσ₁e, ← hσ₂e]
    rcases le_total σ₁ σ₂ with h | h
    · exact hsub hσ₁ hσ₂ h
    · rw [internalEDist_comm]
      exact hsub hσ₂ hσ₁ h
  rw [hgeo τ₁ τ₂ hτ₁T hτ₂T hτ₁₂] at hY12
  
  have hfar₁ : 2 * s ≤ dist (P τ₁) x := by
    rw [← hσ₁e]
    have hA := htr σ₁ hσ₁
    have hA' : π σ₁ ∈ Metric.ball x (3 * s) ∧ π σ₁ ∉ closure (Metric.ball x (2 * s)) := hA
    rw [closure_ball x h2s.ne', Metric.mem_closedBall, not_le] at hA'
    exact hA'.2.le
  have hfc : ContinuousOn (fun τ => dist (P τ) x) (Icc τ₁ t₀) :=
    continuous_dist.comp_continuousOn
      ((hP.mono (Icc_subset_Icc hτ₁T.1 ht₀.2)).prodMk continuousOn_const)
  obtain ⟨σ, σ', hτ₁σ, hσσ', hσ't₀, hσr, hσ'r, -⟩ :=
    LQGMetric.RectCross.exists_sub_crossing' hτ₁.2 hfc (by linarith : s ≤ 2 * s) hfar₁ hin.le
  have hσT : σ ∈ Icc 0 T := ⟨hτ₁T.1.trans hτ₁σ, (hσσ'.trans hσ't₀).trans ht₀.2⟩
  have hσ'T : σ' ∈ Icc 0 T := ⟨(hτ₁T.1.trans hτ₁σ).trans hσσ', hσ't₀.trans ht₀.2⟩
  have hcross : acrossDist d (annIn hs x) ≤ d (P σ', P σ) := by
    refine iInf₂_le_of_le (P σ') ?_ (iInf₂_le (P σ) ?_)
    · exact Metric.mem_sphere.mpr hσ'r
    · exact Metric.mem_sphere.mpr hσr
  have hd : d (P σ', P σ) ≤ ENNReal.ofReal (σ' - σ) := by
    calc d (P σ', P σ) = edist (d.pt (P σ)) (d.pt (P σ')) :=
          edist_comm (d.pt (P σ')) (d.pt (P σ))
      _ ≤ internalEDist (d.pt '' Y) (d.pt (P σ)) (d.pt (P σ')) := edist_le_internalEDist _ _ _
      _ = ENNReal.ofReal (σ' - σ) := hgeo σ σ' hσT hσ'T hσσ'
  have hle : ENNReal.ofReal (σ' - σ) ≤ ENNReal.ofReal (τ₂ - τ₁) :=
    ENNReal.ofReal_le_ofReal (by linarith [hτ₂.1])
  have hchain : acrossDist d (annIn hs x) < acrossDist d (annIn hs x) :=
    calc acrossDist d (annIn hs x) ≤ d (P σ', P σ) := hcross
      _ ≤ ENNReal.ofReal (σ' - σ) := hd
      _ ≤ ENNReal.ofReal (τ₂ - τ₁) := hle
      _ ≤ d.len π a b := hY12
      _ < acrossDist d (annIn hs x) := hlen
  exact lt_irrefl _ hchain

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
