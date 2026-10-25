import SupercriticalLQGUniqueness.B2.WeakStrong.ChainGeom
import SupercriticalLQGUniqueness.Frozen.LSCMetricInternalSetDist
import SLUMetricAPI2

 












set_option autoImplicit false

noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.WeakStrong

 
theorem internalEDist_trace_le (d : LSCMetric) (U : Set ℂ) {P : ℝ → ℂ} {a b : ℝ}
    (hP : d.IsCurve P a b) (hU : ∀ t ∈ Icc a b, P t ∈ U) {x y : ℂ} (hx : x ∈ P '' Icc a b)
    (hy : y ∈ P '' Icc a b) :
    internalEDist (d.pt '' U) (d.pt x) (d.pt y) ≤ d.len P a b := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  have key : ∀ {s t : ℝ}, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      internalEDist (d.pt '' U) (d.pt (P s)) (d.pt (P t)) ≤ d.len P a b := by
    intro s t hs ht hst
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    calc internalEDist (d.pt '' U) (d.pt (P s)) (d.pt (P t))
        ≤ curveLength (d.pt ∘ P) s t :=
          internalEDist_le_curveLength hst (hP.2.mono hsub) fun u hu => ⟨P u, hU u (hsub hu), rfl⟩
      _ ≤ curveLength (d.pt ∘ P) a b := curveLength_mono _ hs.1 ht.2
      _ = d.len P a b := rfl
  rcases le_total s t with h | h
  · exact key hs ht h
  · rw [internalEDist_comm]; exact key ht hs h

 
theorem internalSetDist_lt_top_of_chain (d : LSCMetric) (U : Set ℂ) (n : ℕ) (P : ℕ → ℝ → ℂ)
    (a b : ℕ → ℝ) (hP : ∀ i, d.IsCurve (P i) (a i) (b i))
    (hU : ∀ i, ∀ t ∈ Icc (a i) (b i), P i t ∈ U) (hlen : ∀ i, d.len (P i) (a i) (b i) < ⊤)
    (hmeet : ∀ i < n,
      ((P i '' Icc (a i) (b i)) ∩ (P (i + 1) '' Icc (a (i + 1)) (b (i + 1)))).Nonempty)
    {K₁ K₂ : Set ℂ} (hfirst : (K₁ ∩ P 0 '' Icc (a 0) (b 0)).Nonempty)
    (hlast : (K₂ ∩ P n '' Icc (a n) (b n)).Nonempty) :
    d.internalSetDist U (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) < ⊤ := by
  obtain ⟨x, hxK, hxP⟩ := hfirst
  have hreach : ∀ i ≤ n, ∃ y ∈ P i '' Icc (a i) (b i),
      internalEDist (d.pt '' U) (d.pt x) (d.pt y) < ⊤ := by
    intro i hi
    induction i with
    | zero => exact ⟨x, hxP, (internalEDist_trace_le d U (hP 0) (hU 0) hxP hxP).trans_lt (hlen 0)⟩
    | succ i ih =>
      obtain ⟨y, hy, hxy⟩ := ih (by omega)
      obtain ⟨z, hzi, hzn⟩ := hmeet i (by omega)
      have hyz := (internalEDist_trace_le d U (hP i) (hU i) hy hzi).trans_lt (hlen i)
      exact ⟨z, hzn, lt_of_le_of_lt (internalEDist_triangle _ _ _ _)
        (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩)⟩
  obtain ⟨y, hyK, hyP⟩ := hlast
  obtain ⟨z, hzP, hxz⟩ := hreach n le_rfl
  have hzy := (internalEDist_trace_le d U (hP n) (hU n) hzP hyP).trans_lt (hlen n)
  have hxy : internalEDist (d.pt '' U) (d.pt x) (d.pt y) < ⊤ :=
    lt_of_le_of_lt (internalEDist_triangle _ _ _ _) (ENNReal.add_lt_top.2 ⟨hxz, hzy⟩)
  have hxU : x ∈ U := by obtain ⟨s, hs, rfl⟩ := hxP; exact hU 0 s hs
  have hyU : y ∈ U := by obtain ⟨s, hs, rfl⟩ := hyP; exact hU n s hs
  calc d.internalSetDist U (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂)
      ≤ d.internal U (⟨x, hxU⟩, ⟨y, hyU⟩) :=
        iInf₂_le_of_le ⟨x, hxU⟩ hxK (iInf₂_le_of_le ⟨y, hyU⟩ hyK le_rfl)
    _ = internalEDist (d.pt '' U) (d.pt x) (d.pt y) := LSCMetric.internal_eq_internalEDist d U _
    _ < ⊤ := hxy

 
def annAt (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) : EuclideanAnnulus :=
  ⟨(c, (ρ, 2 * ρ)), hρ, by linarith⟩

theorem annAt_toSet_subset (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    (annAt c ρ hρ).toSet ⊆ closedBall c (2 * ρ) := fun _ hz => ball_subset_closedBall hz.1

 
theorem internalSetDist_lt_top_of_loops (d : LSCMetric) {U : Set ℂ} (n : ℕ) (c : ℕ → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : ∀ i, closedBall (c i) (2 * ρ) ⊆ U)
    (hstep : ∀ i < n, ρ ≤ ‖c (i + 1) - c i‖ ∧ ‖c (i + 1) - c i‖ ≤ 2 * ρ)
    {K₁ K₂ : Set ℂ} (hK₁ : IsPreconnected K₁) (hK₂ : IsPreconnected K₂) {x₁ y₁ x₂ y₂ : ℂ}
    (hx₁ : x₁ ∈ K₁) (hy₁ : y₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (hy₂ : y₂ ∈ K₂)
    (h₁ : ‖x₁ - c 0‖ ≤ ρ) (h₁' : 3 * ρ < ‖y₁ - x₁‖) (h₂ : ‖x₂ - c n‖ ≤ ρ)
    (h₂' : 3 * ρ < ‖y₂ - x₂‖)
    (hloop : ∀ i, ∃ (P : ℝ → ℂ) (a b : ℝ), d.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ (annAt (c i) ρ hρ).toSet) ∧
      Disconnects (P '' Icc a b) (annAt (c i) ρ hρ).innerBoundary
        (annAt (c i) ρ hρ).outerBoundary ∧ d.len P a b < ⊤) :
    d.internalSetDist U (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) < ⊤ := by
  choose P a b hPc hPA hPdisc hPlen using hloop
  have hdisc : ∀ i, Disconnects (P i '' Icc (a i) (b i)) (sphere (c i) ρ)
      (sphere (c i) (2 * ρ)) := hPdisc
  have hU : ∀ i, ∀ t ∈ Icc (a i) (b i), P i t ∈ U := fun i t ht =>
    hball i (annAt_toSet_subset _ hρ (hPA i t ht))
  have hfar : ∀ {x y z : ℂ}, ‖x - z‖ ≤ ρ → 3 * ρ < ‖y - x‖ → 2 * ρ ≤ ‖y - z‖ := by
    intro x y z hxz hyx
    have := norm_sub_le_norm_sub_add_norm_sub y z x
    rw [norm_sub_rev z x] at this
    linarith
  refine internalSetDist_lt_top_of_chain d U n P a b hPc hU hPlen (fun i hi => ?_)
    (preconnected_meets_separator hρ hK₁ hx₁ hy₁ h₁ (hfar h₁ h₁') (hdisc 0))
    (preconnected_meets_separator hρ hK₂ hx₂ hy₂ h₂ (hfar h₂ h₂') (hdisc n))
  exact separators_intersect hρ (hstep i hi).1 (hstep i hi).2
    (Uniqueness.Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit (hdisc i))
    (Uniqueness.Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit (hdisc (i + 1)))
    (Uniqueness.Geodesics.ClosedBalls.trace_pathConnected d _ (P (i + 1)) (a (i + 1)) (b (i + 1))
      (hPc (i + 1)) (hPA (i + 1)))

end SupercriticalLQGUniqueness.B2.WeakStrong
