import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Spent.Spent




 






set_option autoImplicit false
noncomputable section

open Set Metric Finset LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Spent

 
def spentConstant (ξ Cmax : ℝ) (Caround : NNReal) : NNReal :=
  ⟨2 * Real.exp (ξ * Cmax) * (Caround : ℝ), by positivity⟩

theorem spentConstant_coe (ξ Cmax : ℝ) (Caround : NNReal) :
    (spentConstant ξ Cmax Caround : ℝ≥0∞) =
      ENNReal.ofReal (Real.exp (ξ * Cmax)) * (Caround : ℝ≥0∞) * 2 := by
  rw [ENNReal.coe_nnreal_eq]
  change ENNReal.ofReal (2 * Real.exp (ξ * Cmax) * (Caround : ℝ)) = _
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  norm_num only [ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
  ring

theorem setDistLSC_mono (Dminus Dfull : LSCMetric)
    (hcomp : ∀ x y : ℂ, Dminus (x, y) ≤ Dfull (x, y))
    (K₁ K₂ : Set ℂ) :
    EndSaving.PathSurgery.setDistLSC Dminus K₁ K₂ ≤ EndSaving.PathSurgery.setDistLSC Dfull K₁ K₂ := by
  unfold EndSaving.PathSurgery.setDistLSC
  refine iInf_mono fun x => iInf_mono fun _hx =>
    iInf_mono fun y => iInf_mono fun _hy => ?_
  exact hcomp x y

 

theorem old_geodesic_spent
    (Dminus Dfull : LSCMetric) (ξ Cmax : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (hB : BiLipschitz.Barrier.Barrier Dminus)
    (hL : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x) (hfmax : ∀ x : ℂ, f x ≤ Cmax)
    (P : ℝ → ℂ) (V : ℕ → Set ℂ) (g : ℕ → C(ℂ, ℝ))
    (z : ℕ → ℂ) (r : ℝ) (τ σ : ℕ → ℝ) {T : ℝ} (m : ℕ)
    (K₁ K₂ : Set ℂ)
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 T))
    (hSetGeodesic : Dminus.len P 0 T = EndSaving.PathSurgery.setDistLSC Dminus K₁ K₂)
    (hbound : ∀ i < m, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T)
    (horder : ∀ i j, i < j → j < m → σ i < τ j)
    (hr : 0 < r)
    (hV : ∀ i < m, closure (V i) ⊆ ball (z i) (3 * r))
    (hP0 : ∀ i < m, 4 * r ≤ dist (P 0) (z i))
    (hPT : ∀ i < m, 4 * r ≤ dist (P T) (z i))
    (hne : ∀ i < m, (closedContactTimes P (V i) T).Nonempty)
    (hτ : ∀ i < m, τ i = firstClosedContact P (V i) T)
    (hσ : ∀ i < m, σ i = lastClosedContact P (V i) T)
    (hg : ∀ i < m, ∀ x : ℂ, x ∉ V i → g i x = 0)
    (hDecomp : ∀ x : ℂ, f x = ∑ i ∈ range m, g i x)
    (Caround : NNReal) (B : ℝ≥0∞) (N : ℕ → ℝ≥0∞)
    (hAround : ∀ i < m, aroundDist Dfull
      ⟨(z i, (3 * r, 4 * r)), by constructor <;> nlinarith [hr]⟩ ≤
        (Caround : ℝ≥0∞) * N i)
    (hCompare : ∀ i < m, N i ≤ 2 * B) :
    Dfull.len P 0 T ≤ EndSaving.PathSurgery.setDistLSC Dfull K₁ K₂ +
      (spentConstant ξ Cmax Caround : ℝ≥0∞) * B * m := by
  have hcont : ContinuousOn P (Icc 0 T) :=
    continuousOn_euclid_of_barrier Dminus hB hL ⟨hG.1, hG.2.1⟩
  have hP0No : ∀ i < m, P 0 ∉ closure (V i) := by
    intro i hi hmem
    have hnear : dist (P 0) (z i) < 3 * r := by
      simpa only [Metric.mem_ball, dist_comm] using hV i hi hmem
    linarith [hP0 i hi, hr]
  have hPTNo : ∀ i < m, P T ∉ closure (V i) := by
    intro i hi hmem
    have hnear : dist (P T) (z i) < 3 * r := by
      simpa only [Metric.mem_ball, dist_comm] using hV i hi hmem
    linarith [hPT i hi, hr]
  obtain ⟨hfGap, hfTail⟩ :=
    bump_zero_on_ordered_gaps P V g f τ σ m hcont hbound horder
      hne hτ hσ hP0No hPTNo hg hDecomp
  have hAgg := aggregate_spent_of_around_event Dminus Dfull ξ Cmax hξ
    f hB hL hWeyl hfn hfmax P V z r τ σ m hG hu hbound horder
    hr hV hP0 hPT hne hτ hσ hfGap hfTail (Caround : ℝ≥0∞) B N
    hAround hCompare
  have hMetric : ∀ x y : ℂ, Dminus (x, y) ≤ Dfull (x, y) :=
    metric_le_weyl Dminus Dfull ξ hξ f
      (continuous_euclidForget_of_barrier Dminus hB hL) hWeyl hfn
  have hSet : Dminus.len P 0 T ≤ EndSaving.PathSurgery.setDistLSC Dfull K₁ K₂ := by
    rw [hSetGeodesic]
    exact setDistLSC_mono Dminus Dfull hMetric K₁ K₂
  calc
    Dfull.len P 0 T ≤ Dminus.len P 0 T +
        (ENNReal.ofReal (Real.exp (ξ * Cmax)) * (Caround : ℝ≥0∞) * 2) * B * m :=
      hAgg
    _ ≤ EndSaving.PathSurgery.setDistLSC Dfull K₁ K₂ +
        (ENNReal.ofReal (Real.exp (ξ * Cmax)) * (Caround : ℝ≥0∞) * 2) * B * m := by
      exact add_le_add_left hSet _
    _ = EndSaving.PathSurgery.setDistLSC Dfull K₁ K₂ +
        (spentConstant ξ Cmax Caround : ℝ≥0∞) * B * m := by
      rw [spentConstant_coe]

 


theorem finite_surgery_ES_of_around_event
    (Dminus Dfull Dtilde : LSCMetric)
    (ξ Cmax : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hB : BiLipschitz.Barrier.Barrier Dminus) (hL : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x) (hfmax : ∀ x : ℂ, f x ≤ Cmax)
    (Cplus Cstar gap c : NNReal) (hC : Cstar + gap = Cplus)
    (hcomp : ∀ x y : ℂ,
      Dtilde (x, y) ≤ (Cplus : ℝ≥0∞) * Dfull (x, y))
    (P : ℝ → ℂ) (K₁ K₂ : Set ℂ) {T : ℝ}
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 T))
    (hSetGeodesic : Dminus.len P 0 T = EndSaving.PathSurgery.setDistLSC Dminus K₁ K₂)
    (hK₁ : P 0 ∈ K₁) (hK₂ : P T ∈ K₂)
    (V : ℕ → Set ℂ) (g : ℕ → C(ℂ, ℝ))
    (zSpend : ℕ → ℂ) (rSpend : ℝ) (τSpend σSpend : ℕ → ℝ)
    (m : ℕ)
    (hSpendBound : ∀ i < m, 0 ≤ τSpend i ∧ τSpend i ≤ σSpend i ∧ σSpend i ≤ T)
    (hSpendOrder : ∀ i j, i < j → j < m → σSpend i < τSpend j)
    (hrSpend : 0 < rSpend)
    (hV : ∀ i < m, closure (V i) ⊆ ball (zSpend i) (3 * rSpend))
    (hP0 : ∀ i < m, 4 * rSpend ≤ dist (P 0) (zSpend i))
    (hPT : ∀ i < m, 4 * rSpend ≤ dist (P T) (zSpend i))
    (hne : ∀ i < m, (closedContactTimes P (V i) T).Nonempty)
    (hτSpend : ∀ i < m, τSpend i = firstClosedContact P (V i) T)
    (hσSpend : ∀ i < m, σSpend i = lastClosedContact P (V i) T)
    (hg : ∀ i < m, ∀ x : ℂ, x ∉ V i → g i x = 0)
    (hDecomp : ∀ x : ℂ, f x = ∑ i ∈ range m, g i x)
    (Caround : NNReal) (B : ℝ≥0∞) (N : ℕ → ℝ≥0∞)
    (hAround : ∀ i < m, aroundDist Dfull
      ⟨(zSpend i, (3 * rSpend, 4 * rSpend)), by
        constructor <;> nlinarith [hrSpend]⟩ ≤
        (Caround : ℝ≥0∞) * N i)
    (hCompare : ∀ i < m, N i ≤ 2 * B)
    (zSel : ℕ → ℂ) (rSel τSel σSel : ℕ → ℝ) (n : ℕ)
    (hSelBound : ∀ i < n, 0 ≤ τSel i ∧ τSel i ≤ σSel i ∧ σSel i ≤ T)
    (hSelStrict : ∀ i < n, τSel i < σSel i)
    (hSelMono : ∀ i j, i < j → j < n → τSel i ≤ τSel j)
    (hSelBall : ∀ i < n, ∀ u ∈ Icc (τSel i) (σSel i),
      P u ∈ ball (zSel i) (4 * rSel i))
    (hSelDisj : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (ball (zSel i) (4 * rSel i))
        (ball (zSel j) (4 * rSel j)))
    (hfSelZero : ∀ i < n, ∀ x ∈ ball (zSel i) (4 * rSel i), f x = 0)
    (hTime : ∀ i < n,
      (c : ℝ≥0∞) * B ≤ ENNReal.ofReal (σSel i - τSel i))
    (hES : ∀ i (_hi : i < n)
      (hτ : P (τSel i) ∈ ball (zSel i) (4 * rSel i))
      (hσ : P (σSel i) ∈ ball (zSel i) (4 * rSel i)),
      Dtilde.internal (ball (zSel i) (4 * rSel i))
        (⟨P (τSel i), hτ⟩, ⟨P (σSel i), hσ⟩) ≤
      (Cstar : ℝ≥0∞) * ENNReal.ofReal (σSel i - τSel i)) :
    EndSaving.PathSurgery.setDistLSC Dtilde K₁ K₂ +
        (gap : ℝ≥0∞) * (c : ℝ≥0∞) * B * (n : ℝ≥0∞) ≤
      (Cplus : ℝ≥0∞) * EndSaving.PathSurgery.setDistLSC Dfull K₁ K₂ +
        (Cplus : ℝ≥0∞) *
          (spentConstant ξ Cmax Caround : ℝ≥0∞) * B * (m : ℝ≥0∞) := by
  have hforget := continuous_euclidForget_of_barrier Dminus hB hL
  have hSpent := old_geodesic_spent Dminus Dfull ξ Cmax hξ f
    hB hL hWeyl hfn hfmax P V g zSpend rSpend τSpend σSpend m
    K₁ K₂ hG hu hSetGeodesic hSpendBound hSpendOrder hrSpend
    hV hP0 hPT hne hτSpend hσSpend hg hDecomp Caround B N hAround hCompare
  exact EndSaving.PathSurgery.finite_surgery_ES_spent Dminus Dfull Dtilde ξ f hforget hWeyl
    Cplus Cstar gap c (spentConstant ξ Cmax Caround) hC hcomp
    P zSel rSel τSel σSel n m K₁ K₂ B hG hu hK₁ hK₂
    hSelBound hSelStrict hSelMono hSelBall hSelDisj hfSelZero
    hTime hSpent hES


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Spent
