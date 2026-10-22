import HigherDimLQGMetric.Limits.ScaleLaws
import Mathlib.MeasureTheory.Measure.Interval

/-!
# Bounds on deterministic normalization ratios

If `ν_n = (b_n·)_* η_n`, the `η_n` converge to a law with a strictly positive
unit distance, and medians of `ν_n` stay in a fixed positive interval, then
the deterministic ratios `b_n` stay in a compact subinterval of `(0,∞)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- Upper boundedness of scaling ratios, from the lower tail of the limiting
point distance and the median upper bound on the rescaled laws. -/
theorem l6c_ratio_eventually_upper {d : ℕ}
    (ηn νn : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (η : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hη : Tendsto ηn atTop (𝓝 η))
    (hν : ∀ n, (νn n : Measure C(Rd d × Rd d, ℝ)) =
      (ηn n : Measure C(Rd d × Rd d, ℝ)).map (fun D => b n • D))
    (hmed : ∀ᶠ n in atTop,
      lowerMedian (νn n : Measure C(Rd d × Rd d, ℝ))
        (fun D => D (0, e₁ d)) ≤ 1)
    (hpos : ∀ᵐ D ∂(η : Measure C(Rd d × Rd d, ℝ)), 0 < D (0, e₁ d)) :
    ∃ U : ℝ, 0 < U ∧ ∀ᶠ n in atTop, b n ≤ U := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let e : C(Rd d × Rd d, ℝ) → ℝ := fun D => D (0, e₁ d)
  have he : Continuous e := continuous_eval_const _
  have hm : 0 < lowerMedian (η : Measure C(Rd d × Rd d, ℝ)) e :=
    l6c_lowerMedian_pos he.measurable.aemeasurable hpos
  let δ := lowerMedian (η : Measure C(Rd d × Rd d, ℝ)) e / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let F : Set C(Rd d × Rd d, ℝ) := {D | e D ≤ δ}
  have hF : IsClosed F := isClosed_Iic.preimage he
  have hηF : (η : Measure C(Rd d × Rd d, ℝ)) F < (2 : ℝ≥0∞)⁻¹ := by
    have hn : ¬ (2 : ℝ≥0∞)⁻¹ ≤ (η : Measure C(Rd d × Rd d, ℝ)) F := by
      intro hhalf
      have hq := (l6c_half_le_measure_iff_lowerMedian_le
        (P := (η : Measure C(Rd d × Rd d, ℝ))) he.measurable.aemeasurable).mp hhalf
      dsimp [δ] at hq
      linarith
    exact lt_of_not_ge hn
  have hηnF : ∀ᶠ n in atTop,
      (ηn n : Measure C(Rd d × Rd d, ℝ)) F < (2 : ℝ≥0∞)⁻¹ :=
    eventually_lt_of_limsup_lt
      ((ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hη hF).trans_lt hηF)
  refine ⟨δ⁻¹, inv_pos.mpr hδ, ?_⟩
  filter_upwards [hηnF, hmed] with n hsmall hmedn
  by_contra hnot
  have hbig : δ⁻¹ < b n := lt_of_not_ge hnot
  have hmul : 1 < b n * δ := by
    have hcancel : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
    nlinarith [mul_lt_mul_of_pos_right hbig hδ]
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ (νn n : Measure C(Rd d × Rd d, ℝ))
      {D | e D ≤ 1} :=
    (l6c_half_le_measure_iff_lowerMedian_le
      (P := (νn n : Measure C(Rd d × Rd d, ℝ))) he.measurable.aemeasurable).mpr
      hmedn
  have hsubset : {D : C(Rd d × Rd d, ℝ) | e (b n • D) ≤ 1} ⊆ F := by
    intro D hD
    have heq : e (b n • D) = b n * e D := by
      simp only [e, ContinuousMap.smul_apply, smul_eq_mul]
    dsimp [F]
    change e (b n • D) ≤ 1 at hD
    rw [heq] at hD
    by_contra hneg
    have hgt : δ < e D := lt_of_not_ge hneg
    nlinarith [mul_lt_mul_of_pos_left hgt (hb n)]
  have hle : (νn n : Measure C(Rd d × Rd d, ℝ)) {D | e D ≤ 1} ≤
      (ηn n : Measure C(Rd d × Rd d, ℝ)) F := by
    rw [hν n]
    change ((ηn n : Measure C(Rd d × Rd d, ℝ)).map (fun D => b n • D))
      (e ⁻¹' Iic 1) ≤ (ηn n : Measure C(Rd d × Rd d, ℝ)) F
    have hsm : AEMeasurable (fun D : C(Rd d × Rd d, ℝ) => b n • D)
        (ηn n : Measure C(Rd d × Rd d, ℝ)) :=
      (show Continuous (fun D : C(Rd d × Rd d, ℝ) => b n • D) from
        by fun_prop).measurable.aemeasurable
    have hmap : ((ηn n : Measure C(Rd d × Rd d, ℝ)).map (fun D => b n • D))
        (e ⁻¹' Iic (1 : ℝ)) =
        (ηn n : Measure C(Rd d × Rd d, ℝ))
          ((fun D => b n • D) ⁻¹' (e ⁻¹' Iic (1 : ℝ))) :=
      Measure.map_apply_of_aemeasurable hsm
        (isClosed_Iic.preimage he).measurableSet
    rw [hmap]
    exact measure_mono hsubset
  exact (not_lt_of_ge (hhalf.trans hle)) hsmall

/-- Lower boundedness of scaling ratios, from an upper-tail event of the
limiting law and the positive median lower bound on the rescaled laws. -/
theorem l6c_ratio_eventually_lower {d : ℕ}
    (ηn νn : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (η : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hη : Tendsto ηn atTop (𝓝 η))
    (hν : ∀ n, (νn n : Measure C(Rd d × Rd d, ℝ)) =
      (ηn n : Measure C(Rd d × Rd d, ℝ)).map (fun D => b n • D))
    (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmed : ∀ᶠ n in atTop,
      m₀ ≤ lowerMedian (νn n : Measure C(Rd d × Rd d, ℝ))
        (fun D => D (0, e₁ d))) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ n in atTop, L ≤ b n := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let e : C(Rd d × Rd d, ℝ) → ℝ := fun D => D (0, e₁ d)
  have he : Continuous e := continuous_eval_const _
  let ηe : Measure ℝ := (η : Measure C(Rd d × Rd d, ℝ)).map e
  have hηe : IsProbabilityMeasure ηe :=
    (Measure.isProbabilityMeasure_map_iff he.measurable.aemeasurable).mpr inferInstance
  have htend : Tendsto (fun T : ℝ => ηe (Iic T)) atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [measure_univ] using tendsto_measure_Iic_atTop ηe
  obtain ⟨T, hT⟩ := (htend.eventually (lt_mem_nhds
    (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1))).exists
  let U : ℝ := max T 1 + 1
  have hU : 0 < U := by dsimp [U]; linarith [le_max_right T 1]
  let G : Set C(Rd d × Rd d, ℝ) := {D | e D < U}
  have hG : IsOpen G := isOpen_Iio.preimage he
  have hηG : (2 : ℝ≥0∞)⁻¹ < (η : Measure C(Rd d × Rd d, ℝ)) G := by
    have hsub : Iic T ⊆ Iio U := by
      intro x hx
      dsimp [U]
      exact lt_of_le_of_lt (hx.trans (le_max_left T 1)) (lt_add_one _)
    have hsub' : (ηe (Iic T)) ≤ ηe (Iio U) := measure_mono hsub
    have hmap : ηe (Iio U) = (η : Measure C(Rd d × Rd d, ℝ)) G := by
      exact Measure.map_apply_of_aemeasurable he.measurable.aemeasurable
        measurableSet_Iio
    exact hT.trans_le (hsub'.trans_eq hmap)
  have hev : ∀ᶠ n in atTop,
      (2 : ℝ≥0∞)⁻¹ < (ηn n : Measure C(Rd d × Rd d, ℝ)) G :=
    eventually_lt_of_lt_liminf
      (hηG.trans_le (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hη hG))
  let t := m₀ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  refine ⟨t / U, div_pos ht hU, ?_⟩
  filter_upwards [hev, hmed] with n hlarge hmedn
  by_contra hnot
  have hsmall : b n < t / U := lt_of_not_ge hnot
  have hmul : b n * U < t := (lt_div_iff₀ hU).mp hsmall
  have hνt : (νn n : Measure C(Rd d × Rd d, ℝ)) {D | e D ≤ t} <
      (2 : ℝ≥0∞)⁻¹ := by
    have hn : ¬ (2 : ℝ≥0∞)⁻¹ ≤
        (νn n : Measure C(Rd d × Rd d, ℝ)) {D | e D ≤ t} := by
      intro hhalf
      have hq := (l6c_half_le_measure_iff_lowerMedian_le
        (P := (νn n : Measure C(Rd d × Rd d, ℝ)))
        he.measurable.aemeasurable).mp hhalf
      dsimp [t] at hq
      linarith
    exact lt_of_not_ge hn
  have hsubset : G ⊆ {D : C(Rd d × Rd d, ℝ) | e (b n • D) ≤ t} := by
    intro D hD
    change e D < U at hD
    change e (b n • D) ≤ t
    have heq : e (b n • D) = b n * e D := by
      simp only [e, ContinuousMap.smul_apply, smul_eq_mul]
    rw [heq]
    exact (mul_lt_mul_of_pos_left hD (hb n)).le.trans hmul.le
  have hle : (ηn n : Measure C(Rd d × Rd d, ℝ)) G ≤
      (νn n : Measure C(Rd d × Rd d, ℝ)) {D | e D ≤ t} := by
    rw [hν n]
    have hsm : AEMeasurable (fun D : C(Rd d × Rd d, ℝ) => b n • D)
        (ηn n : Measure C(Rd d × Rd d, ℝ)) :=
      (show Continuous (fun D : C(Rd d × Rd d, ℝ) => b n • D) from
        by fun_prop).measurable.aemeasurable
    have hmap : ((ηn n : Measure C(Rd d × Rd d, ℝ)).map (fun D => b n • D))
        (e ⁻¹' Iic t) =
        (ηn n : Measure C(Rd d × Rd d, ℝ))
          ((fun D => b n • D) ⁻¹' (e ⁻¹' Iic t)) :=
      Measure.map_apply_of_aemeasurable hsm
        (isClosed_Iic.preimage he).measurableSet
    change (ηn n : Measure C(Rd d × Rd d, ℝ)) G ≤
      ((ηn n : Measure C(Rd d × Rd d, ℝ)).map (fun D => b n • D))
        (e ⁻¹' Iic t)
    rw [hmap]
    exact measure_mono hsubset
  exact (not_lt_of_ge (hle.trans_lt hνt).le) hlarge

/-- A positive subsequential limit of the deterministic ratios exists, and its
scaled metric law is one of the compact LFPP limit laws. -/
theorem l6c_ratio_cluster {d : ℕ}
    (ηn νn : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (η : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hη : Tendsto ηn atTop (𝓝 η))
    (hν : ∀ n, (νn n : Measure C(Rd d × Rd d, ℝ)) =
      (ηn n : Measure C(Rd d × Rd d, ℝ)).map (fun D => b n • D))
    (K : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ))) (hK : IsCompact K)
    (hνK : ∀ᶠ n in atTop, νn n ∈ K)
    (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmedlo : ∀ᶠ n in atTop,
      m₀ ≤ lowerMedian (νn n : Measure C(Rd d × Rd d, ℝ))
        (fun D => D (0, e₁ d)))
    (hmedhi : ∀ᶠ n in atTop,
      lowerMedian (νn n : Measure C(Rd d × Rd d, ℝ))
        (fun D => D (0, e₁ d)) ≤ 1)
    (hpos : ∀ᵐ D ∂(η : Measure C(Rd d × Rd d, ℝ)), 0 < D (0, e₁ d)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ β : ℝ, 0 < β ∧
      Tendsto (b ∘ φ) atTop (𝓝 β) ∧
      η.map (fun D => β • D) ∈ K ∧
      Tendsto (νn ∘ φ) atTop (𝓝 (η.map (fun D => β • D))) := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  obtain ⟨L, hL, hbl⟩ :=
    l6c_ratio_eventually_lower ηn νn η b hb hη hν m₀ hm₀ hmedlo
  obtain ⟨U, hU, hbu⟩ :=
    l6c_ratio_eventually_upper ηn νn η b hb hη hν hmedhi hpos
  have hLU : L ≤ U := by
    obtain ⟨n, hn⟩ := (hbl.and hbu).exists
    exact hn.1.trans hn.2
  have hI : ∀ᶠ n in atTop, b n ∈ Icc L U := by
    filter_upwards [hbl, hbu] with n hn hnu
    exact ⟨hn, hnu⟩
  obtain ⟨β, hβ, φ, hφ, hφβ⟩ := isCompact_Icc.tendsto_subseq' hI.frequently
  have hβpos : 0 < β := hL.trans_le hβ.1
  have hηφ : Tendsto (ηn ∘ φ) atTop (𝓝 η) := hη.comp hφ.tendsto_atTop
  have hpair : Tendsto (fun n => (b (φ n), ηn (φ n))) atTop (𝓝 (β, η)) :=
    hφβ.prodMk_nhds hηφ
  have hνeq (n : ℕ) : νn n = (ηn n).map (fun D => b n • D) :=
    Subtype.ext (hν n)
  have hνφ : Tendsto (νn ∘ φ) atTop (𝓝 (η.map (fun D => β • D))) := by
    have ht := ((l6c_continuous_law_smul (d := d)).tendsto (β, η)).comp hpair
    convert ht using 1
    funext n
    exact hνeq (φ n)
  have hmem : η.map (fun D => β • D) ∈ K :=
    hK.isClosed.mem_of_tendsto hνφ (hφ.tendsto_atTop.eventually hνK)
  exact ⟨φ, hφ, β, hβpos, hφβ, hmem, hνφ⟩

end HigherDimLQGMetric
