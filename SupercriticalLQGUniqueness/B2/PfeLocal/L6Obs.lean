import SupercriticalLQGUniqueness.B2.PfeLocal.L5S3
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteGeometry
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableNormalizedEquality
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalizedLFPP
import LQGMetric.Papers.DFGPS.L2_1Ratio

 





















set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum

 
theorem l6_isCurve_lfpp_iff (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (P : ℝ → ℂ)
    {s t : ℝ} :
    (PfeWeyl.normalizedLFPPMetric ξ a φ).IsCurve P s t ↔ s ≤ t ∧ ContinuousOn P (Icc s t) := by
  set D := PfeWeyl.normalizedLFPPMetric ξ a φ
  constructor
  · rintro ⟨hst, hc⟩
    exact ⟨hst, (PfeAxioms.continuous_euclidForget_normalizedLFPPMetric ξ a φ).comp_continuousOn hc⟩
  · rintro ⟨hst, hc⟩
    refine ⟨hst, ?_⟩
    intro u hu
    change Tendsto (D.pt ∘ P) (𝓝[Icc s t] u) (𝓝 (D.pt (P u)))
    rw [EMetric.tendsto_nhds]
    intro ε hε
    have hcont : Continuous fun q : ℂ × ℂ => D q := by
      have : (fun q : ℂ × ℂ => D q) =
          fun q => ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDistance ξ φ q := by
        funext q; exact PfeWeyl.normalizedLFPPMetric_apply ξ a φ q
      rw [this]
      exact ENNReal.continuous_const_mul ENNReal.ofReal_ne_top |>.comp
        (LscTop.continuous_lfppDistance ξ φ)
    have h0 : D (P u, P u) = 0 := D.isExtMetric.1 _
    have htend : Tendsto (fun v => D (P v, P u)) (𝓝[Icc s t] u) (𝓝 0) := by
      rw [← h0]
      exact (hcont.tendsto _).comp ((hc u hu).prodMk_nhds tendsto_const_nhds)
    filter_upwards [htend.eventually (gt_mem_nhds hε)] with v hv
    exact hv

 
theorem l6_compactPathInf_lfpp_le (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)}
    {O : Set ℂ} (hO : IsOpen O) {δ : ℝ} (hδ : ∀ x ∈ O, |φ' x - φ x| ≤ δ)
    {Q E F : Set ℂ} (hQ : Q ⊆ O) :
    compactPathInf (PfeWeyl.normalizedLFPPMetric ξ a φ') Q E F ≤
      ENNReal.ofReal (Real.exp (|ξ| * δ)) *
        compactPathInf (PfeWeyl.normalizedLFPPMetric ξ a φ) Q E F := by
  set D := PfeWeyl.normalizedLFPPMetric ξ a φ
  set D' := PfeWeyl.normalizedLFPPMetric ξ a φ'
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * δ))
  have hk : k ≠ ∞ := ENNReal.ofReal_ne_top
  
  have hint : ∀ x y : ℂ, x ∈ O → y ∈ O →
      compactPathInf D' O {x} {y} ≤ k * compactPathInf D O {x} {y} := by
    intro x y hx hy
    have e : ∀ (E : LSCMetric), compactPathInf E O {x} {y} = E.internal O (⟨x, hx⟩, ⟨y, hy⟩) := by
      intro E
      unfold compactPathInf LSCMetric.internal
      simp only [mem_singleton_iff]
    rw [e D', e D, PfeAxioms.normalizedLFPPMetric_internal_eq_lfppDOn ξ a φ' hO,
      PfeAxioms.normalizedLFPPMetric_internal_eq_lfppDOn ξ a φ hO]
    calc ENNReal.ofReal ((a : ℝ)⁻¹) * LQGMetric.LFPP.lfppDOn ξ φ' O x y
        ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * (k * LQGMetric.LFPP.lfppDOn ξ φ O x y) := by
          gcongr
          exact LQGMetric.DFGPS.lfppDOn_le_of_abs_sub_le hδ x y
      _ = k * (ENNReal.ofReal ((a : ℝ)⁻¹) * LQGMetric.LFPP.lfppDOn ξ φ O x y) := by ring
  
  have hlen : ∀ (P : ℝ → ℂ) (s t : ℝ), D.IsCurve P s t → (∀ u ∈ Icc s t, P u ∈ O) →
      D'.len P s t ≤ k * D.len P s t := by
    intro P s t hP hPO
    have hP' : D'.IsCurve P s t :=
      (l6_isCurve_lfpp_iff ξ a φ' P).2 ((l6_isCurve_lfpp_iff ξ a φ P).1 hP)
    rw [l5_len_eq_iSup_compactPathInf D' P hP' hPO, l5_len_eq_iSup_compactPathInf D P hP hPO,
      ENNReal.mul_iSup]
    refine iSup_mono fun p => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => hint _ _ (hPO _ (p.2.2.2 i)) (hPO _ (p.2.2.2 (i + 1)))
  
  by_contra hnot
  have hlt : k * compactPathInf D Q E F < compactPathInf D' Q E F := lt_of_not_ge hnot
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hlt' : compactPathInf D Q E F < compactPathInf D' Q E F / k :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hk0) (Or.inl hk)).2 (by rw [mul_comm]; exact hlt)
  unfold compactPathInf at hlt'
  obtain ⟨P, s, t, hP, htr, hEs, hFt, hcost⟩ := (by simpa only [iInf_lt_iff] using hlt')
  have hP' : D'.IsCurve P s t :=
    (l6_isCurve_lfpp_iff ξ a φ' P).2 ((l6_isCurve_lfpp_iff ξ a φ P).1 hP)
  have h1 : compactPathInf D' Q E F ≤ D'.len P s t := l5_compactPathInf_le D' P s t hP' htr hEs hFt
  have h2 := hlen P s t hP fun u hu => hQ (htr u hu)
  have h3 : k * D.len P s t < compactPathInf D' Q E F :=
    calc k * D.len P s t < k * (compactPathInf D' Q E F / k) :=
          (ENNReal.mul_lt_mul_iff_right hk0 hk).2 hcost
      _ ≤ compactPathInf D' Q E F := ENNReal.mul_div_le
  exact (not_lt_of_ge (h1.trans h2)) h3

 
theorem l6_compactPathInf_lfpp_congr (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)}
    {O : Set ℂ} (hO : IsOpen O) (heq : ∀ x ∈ O, φ' x = φ x) {Q E F : Set ℂ} (hQ : Q ⊆ O) :
    compactPathInf (PfeWeyl.normalizedLFPPMetric ξ a φ') Q E F =
      compactPathInf (PfeWeyl.normalizedLFPPMetric ξ a φ) Q E F := by
  have h0 : ∀ x ∈ O, |φ' x - φ x| ≤ 0 := fun x hx => by rw [heq x hx, sub_self, abs_zero]
  have h0' : ∀ x ∈ O, |φ x - φ' x| ≤ 0 := fun x hx => by rw [heq x hx, sub_self, abs_zero]
  have e : ENNReal.ofReal (Real.exp (|ξ| * 0)) = 1 := by simp
  apply le_antisymm
  · simpa [e] using l6_compactPathInf_lfpp_le ξ a hO h0 hQ (E := E) (F := F)
  · simpa [e] using l6_compactPathInf_lfpp_le ξ a hO h0' hQ (E := E) (F := F)

end SupercriticalLQGUniqueness.B2.PfeLocal
