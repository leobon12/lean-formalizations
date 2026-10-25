import SupercriticalLQGUniqueness.B2.Median.Strip
import SupercriticalLQGUniqueness.B2.Normalizer.Shift

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (lfppLen)

namespace SupercriticalLQGUniqueness.B2.Median

theorem lfppLen_mono_field {ξ : ℝ} (hξ : 0 ≤ ξ)
    (φ ψ : ℂ → ℝ) (hφψ : ∀ z, φ z ≤ ψ z) (P : ℝ → ℂ) :
    lfppLen ξ φ P ≤ lfppLen ξ ψ P := by
  unfold lfppLen
  refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hφψ (P t)) hξ))
    (norm_nonneg _)

theorem lfppLen_penalty_lower {ξ δ : ℝ} (hξ : 0 ≤ ξ)
    (φ ψ : ℂ → ℝ) (P : ℝ → ℂ)
    (hψ : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ψ (P t)) :
    ENNReal.ofReal (Real.exp (ξ * δ)) * lfppLen ξ φ P ≤
      lfppLen ξ (fun z => φ z + ψ z) P := by
  rw [LQGMetric.LFPP.lfppLen_eq, LQGMetric.LFPP.lfppLen_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  rw [LQGMetric.LFPP.lenDens_add]
  exact mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hψ t ht) hξ))) zero_le

theorem crossing_le_shifted_strip_path {ξ : ℝ} (hξ : 0 ≤ ξ)
    (a : Set.Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ))
    {P : ℝ → ℂ} {z w : ℂ} (hP : LQGMetric.IsPiecewiseC1Path P z w)
    (hstrip : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (P t).im ∧ (P t).im ≤ 1)
    (hz : z.re ≤ 0) (hw : 1 ≤ w.re)
    (hψ : ∀ z, 0 ≤ ψ z) :
    ENNReal.ofReal ((a : ℝ)⁻¹) * lfppCrossingLength ξ φ ≤
      ENNReal.ofReal ((a : ℝ)⁻¹) * lfppLen ξ (fun z => φ z + ψ z) P := by
  obtain ⟨Q, hQ, hQlen⟩ :=
    exists_leftRightCrossing_of_strip ξ φ hP hstrip hz hw
  calc
    ENNReal.ofReal ((a : ℝ)⁻¹) * lfppCrossingLength ξ φ
        ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * lfppLen ξ φ Q := by
          apply mul_le_mul_of_nonneg_left _ zero_le
          exact iInf_le_of_le Q (iInf_le_of_le hQ le_rfl)
    _ ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * lfppLen ξ φ P :=
        mul_le_mul_of_nonneg_left hQlen zero_le
    _ ≤ ENNReal.ofReal ((a : ℝ)⁻¹) *
          lfppLen ξ (fun z => φ z + ψ z) P :=
        mul_le_mul_of_nonneg_left
          (lfppLen_mono_field hξ _ _ (fun z => le_add_of_nonneg_right (hψ z)) P) zero_le

theorem penalty_subpath_distance_lower {ξ δ : ℝ} (hξ : 0 ≤ ξ)
    (a : Set.Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ))
    {P : ℝ → ℂ} {z w : ℂ} (hP : LQGMetric.IsPiecewiseC1Path P z w)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1)
    (hψ : ∀ u ∈ Icc s t, δ ≤ ψ (P u)) :
    ENNReal.ofReal (Real.exp (ξ * δ)) *
        lfppMetric ξ a φ (P s, P t) ≤
      ENNReal.ofReal ((a : ℝ)⁻¹) *
        lfppLen ξ (fun z => φ z + ψ z) P := by
  let Q : ℝ → ℂ := LQGMetric.LFPP.subPath P s t
  have hQ : LQGMetric.IsPiecewiseC1Path Q (P s) (P t) :=
    LQGMetric.LFPP.isPiecewiseC1Path_subPath hP hs hst ht
  have hdist : lfppDistance ξ φ (P s, P t) ≤ lfppLen ξ φ Q := by
    rw [B2.LscTop.lfppDistance_eq_lfppD]
    exact LQGMetric.LFPP.lfppDOn_le hQ (fun _ _ => mem_univ _)
  have hψQ : ∀ u ∈ Icc (0 : ℝ) 1, δ ≤ ψ (Q u) := by
    intro u hu
    apply hψ
    constructor <;> nlinarith [hu.1, hu.2, sub_pos.mpr hst]
  have hpen := lfppLen_penalty_lower hξ φ ψ Q hψQ
  have hsub : lfppLen ξ (fun z => φ z + ψ z) Q ≤
      lfppLen ξ (fun z => φ z + ψ z) P := by
    rw [LQGMetric.LFPP.lfppLen_subPath P hst]
    change (∫⁻ x in Icc s t,
      LQGMetric.LFPP.lenDens ξ (fun z => φ z + ψ z) P x) ≤
      (∫⁻ x in Icc (0 : ℝ) 1,
        LQGMetric.LFPP.lenDens ξ (fun z => φ z + ψ z) P x)
    exact lintegral_mono_set (Icc_subset_Icc hs ht)
  let c : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ)⁻¹)
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * δ))
  calc
    e * lfppMetric ξ a φ (P s, P t)
        = e * (c * lfppDistance ξ φ (P s, P t)) := rfl
    _ ≤ e * (c * lfppLen ξ φ Q) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdist zero_le) zero_le
    _ = c * (e * lfppLen ξ φ Q) := by ac_rfl
    _ ≤ c * lfppLen ξ (fun z => φ z + ψ z) Q :=
      mul_le_mul_of_nonneg_left hpen zero_le
    _ ≤ c * lfppLen ξ (fun z => φ z + ψ z) P :=
      mul_le_mul_of_nonneg_left hsub zero_le

 


theorem path_avoids_barrier_of_pair_lower {ξ δ : ℝ} (hξ : 0 ≤ ξ)
    (a : Set.Ioi (0 : ℝ)) (φ ψ θ : C(ℂ, ℝ))
    {P : ℝ → ℂ} {z w : ℂ} (hP : LQGMetric.IsPiecewiseC1Path P z w)
    {μ : ℝ≥0∞} (hθ0 : θ (P 0) ≤ 1 / 2)
    (hψ : ∀ u ∈ Icc (0 : ℝ) 1,
      1 / 2 ≤ θ (P u) → θ (P u) ≤ 1 → δ ≤ ψ (P u))
    (hpair : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      θ (P u) = 1 / 2 → θ (P v) = 1 →
        μ ≤ lfppMetric ξ a φ (P u, P v))
    (hcost : ENNReal.ofReal ((a : ℝ)⁻¹) *
        lfppLen ξ (fun z => φ z + ψ z) P <
          ENNReal.ofReal (Real.exp (ξ * δ)) * μ) :
    ∀ u ∈ Icc (0 : ℝ) 1, θ (P u) < 1 := by
  intro u hu
  by_contra hnot
  have hu1 : 1 ≤ θ (P u) := le_of_not_gt hnot
  have hθc : ContinuousOn (fun v => θ (P v)) (Icc (0 : ℝ) u) :=
    θ.continuous.comp_continuousOn
      (hP.continuousOn.mono (Icc_subset_Icc le_rfl hu.2))
  obtain ⟨s, t, hs, hst, ht, hθs, hθt, hmid⟩ :=
    LQGMetric.RectCross.exists_sub_crossing (f := fun v => θ (P v))
      hu.1 hθc (by norm_num : (1 / 2 : ℝ) ≤ 1) hθ0 hu1
  have hst' : s < t := by
    by_contra h
    have heq : s = t := le_antisymm hst (le_of_not_gt h)
    rw [heq] at hθs
    linarith
  have hψseg : ∀ v ∈ Icc s t, δ ≤ ψ (P v) := by
    intro v hv
    exact hψ v ⟨hs.trans hv.1, hv.2.trans (ht.trans hu.2)⟩
      (hmid v hv).1 (hmid v hv).2
  have hμ : μ ≤ lfppMetric ξ a φ (P s, P t) :=
    hpair s ⟨hs, hst.trans (ht.trans hu.2)⟩ t
      ⟨hs.trans hst, ht.trans hu.2⟩ hθs hθt
  have hpen := penalty_subpath_distance_lower hξ a φ ψ hP hs hst'
    (ht.trans hu.2) hψseg
  exact (not_le_of_gt hcost) ((mul_le_mul_of_nonneg_left hμ zero_le).trans hpen)

end SupercriticalLQGUniqueness.B2.Median
