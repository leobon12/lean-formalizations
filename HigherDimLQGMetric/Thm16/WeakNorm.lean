import HigherDimLQGMetric.Thm16.CompactPath
import HigherDimLQGMetric.Sharp.TightLower
import HigherDimLQGMetric.Sharp.TightUpper
import HigherDimLQGMetric.Sphere.Cont
import HigherDimLQGMetric.Sphere.Conv
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.Frozen.IsWeakExpMetric
import HigherDimLQGMetric.Metric.ContMetric
import HigherDimLFPP.Paths.DistOn

/-! # Compact-scale bounds for weak metric normalizers. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

private def rawAt {d : ℕ} (ξ : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) (r : ℝ) : ℝ :=
  Real.exp (-ξ * sphereAvg g r 0) * (D g).1 (0, r • e₁ d)

private theorem rawAt_measurable {d : ℕ} (ξ : ℝ) {D : DistRd d → ContMetric d}
    (hD : Measurable D) (r : ℝ) :
    Measurable fun g : DistRd d => rawAt ξ D g r := by
  let E : C(Rd d × Rd d, ℝ) → ℝ := fun f => f (0, r • e₁ d)
  have he : Measurable E := (continuous_eval_const _).measurable
  have h1 : Measurable fun g : DistRd d => -ξ * sphereAvg g r 0 := by
    convert ((measurable_const : Measurable (fun _ : DistRd d => -ξ)).mul
      (measurable_sphereAvg_left r 0)) using 1
    funext g
    rfl
  change Measurable fun g : DistRd d =>
    Real.exp (-ξ * sphereAvg g r 0) * E ((D g).1)
  exact (Real.measurable_exp.comp h1).mul
    (he.comp (measurable_subtype_coe.comp hD))

private theorem rawAt_continuousOn {d : ℕ} (ξ : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) {a b : ℝ} (ha : 0 < a)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg g p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (rawAt ξ D g) (Icc a b) := by
  have havg : ContinuousOn (fun r : ℝ => sphereAvg g r 0) (Icc a b) := by
    have hpair : Continuous fun r : ℝ => (r, (0 : Rd d)) := continuous_id.prodMk continuous_const
    apply hcont.comp hpair.continuousOn
    intro r hr
    exact ⟨ha.trans_le hr.1, mem_univ 0⟩
  have hdist : Continuous fun r : ℝ => (D g).1 (0, r • e₁ d) :=
    (D g).1.continuous.comp (continuous_const.prodMk (continuous_id.smul continuous_const))
  have havg' : ContinuousOn (fun r : ℝ => -ξ * sphereAvg g r 0) (Icc a b) := by
    convert ((continuousOn_const : ContinuousOn (fun _ : ℝ => -ξ) (Icc a b)).mul havg) using 1
    funext r
    rfl
  change ContinuousOn (fun r : ℝ =>
    Real.exp (-ξ * sphereAvg g r 0) * (D g).1 (0, r • e₁ d)) (Icc a b)
  exact (Real.continuous_exp.comp_continuousOn havg').mul hdist.continuousOn

private theorem rawAt_pos {d : ℕ} (hd : 0 < d) (ξ : ℝ)
    (D : DistRd d → ContMetric d) (g : DistRd d) {r : ℝ} (hr : 0 < r) :
    0 < rawAt ξ D g r := by
  have he : r • e₁ d ≠ (0 : Rd d) := smul_ne_zero hr.ne' (HigherDimLFPP.e₁_ne_zero hd)
  exact mul_pos (Real.exp_pos _) ((D g).apply_pos he.symm)

private theorem rawAt_uniform {d : ℕ} (hd : 3 ≤ d) (ξ : ℝ)
    {D : DistRd d → ContMetric d} (hD : Measurable D)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ m M : ℝ, 0 < m ∧ ∀ r ∈ Icc a b,
      (4⁻¹ : ℝ≥0∞) <
        (normLGFLaw d) {g | m ≤ rawAt ξ D g r ∧ rawAt ξ D g r ≤ M} := by
  have hd2 : 2 ≤ d := by omega
  let _ : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).2.1
  have hcont := hn.1.ae_continuousOn_sphereAvg hd2
  have hAE : ∀ᵐ g ∂(normLGFLaw d),
      ContinuousOn (rawAt ξ D g) (Icc a b) ∧
        ∀ r ∈ Icc a b, 0 < rawAt ξ D g r := by
    filter_upwards [hcont] with g hg
    exact ⟨rawAt_continuousOn ξ D g ha hg.2,
      fun r hr => rawAt_pos (by omega : 0 < d) ξ D g (ha.trans_le hr.1)⟩
  exact l9c_uniform_bounds_of_ae_continuousOn (normLGFLaw d)
    (rawAt ξ D) (rawAt_measurable ξ hD) hab hAE

private theorem rawAt_eq_c_mul_norm {d : ℕ} (ξ : ℝ)
    (D : DistRd d → ContMetric d) (c : ℝ → ℝ)
    (g : DistRd d) {r : ℝ} (hc : c r ≠ 0) :
    rawAt ξ D g r = c r * normalizedAtScale ξ D c g r (0, e₁ d) := by
  simp only [rawAt, normalizedAtScale, ContinuousMap.smul_apply,
    ContinuousMap.comp_apply, smul_eq_mul]
  field_simp
  simp only [ContinuousMap.coe_mk, smul_zero]

theorem weakNormalizer_locBdd {d : ℕ} (hd : 3 ≤ d) {ξ : ℝ}
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ B : ℝ, 0 < B ∧ ∀ r ∈ Icc a b, B⁻¹ ≤ c r ∧ c r ≤ B := by
  have hd2 : 2 ≤ d := by omega
  let P : Measure (DistRd d) := normLGFLaw d
  let _ : IsProbabilityMeasure P := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id P := (normLGFLaw_spec_holds d hd2).2.1
  obtain ⟨m,M,hm,hraw⟩ := rawAt_uniform hd ξ hD.measurable ha hab
  let R : ℝ := b + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hT : TightOver P (fun r g => normalizedAtScale ξ D c g r) (Ioo 0 R) :=
    hD.tight P id hn.1.isLGFPlusCont R hR
  let p : Rd d × Rd d := (0, e₁ d)
  have hpne : p.1 ≠ p.2 := (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm
  obtain ⟨η,hη,hlo⟩ := hT.lower_offDiag (A := {p}) isCompact_singleton
    (by intro q hq; simpa only [mem_singleton_iff] using hq ▸ hpne)
    (by norm_num : (0 : ℝ≥0∞) < 4⁻¹)
  let K : Set (Rd d) := {0, e₁ d}
  have hK : IsCompact K := isCompact_singleton.insert _
  obtain ⟨T,hTpos,hup⟩ := hT.upper_compact hK
    (by norm_num : (0 : ℝ≥0∞) < 4⁻¹)
  have hrange (r : ℝ) (hr : r ∈ Icc a b) : r ∈ Ioo (0 : ℝ) R :=
    ⟨ha.trans_le hr.1, by dsimp [R]; linarith [hr.2]⟩
  have hcupper (r : ℝ) (hr : r ∈ Icc a b) : c r ≤ M / η := by
    by_contra hnot
    have hratio : M < c r * η := (div_lt_iff₀ hη).mp (lt_of_not_ge hnot)
    let A : Set (DistRd d) := {g | m ≤ rawAt ξ D g r ∧ rawAt ξ D g r ≤ M}
    let Bad : Set (DistRd d) :=
      {g | ¬ ∀ q ∈ ({p} : Set (Rd d × Rd d)), η < normalizedAtScale ξ D c g r q}
    have hsub : A ⊆ Bad := by
      intro g hg hgood
      have hnorm : η < normalizedAtScale ξ D c g r p :=
        hgood p (mem_singleton p)
      have hcmp := mul_lt_mul_of_pos_left hnorm (hD.c_pos r (hrange r hr).1)
      rw [← rawAt_eq_c_mul_norm ξ D c g (hD.c_pos r (hrange r hr).1).ne'] at hcmp
      exact (not_lt_of_ge hg.2) (hratio.trans hcmp)
    have hlt := (hraw r hr).trans_le (measure_mono hsub)
    exact (lt_irrefl (4⁻¹ : ℝ≥0∞)) (hlt.trans (hlo r (hrange r hr)))
  have hclower (r : ℝ) (hr : r ∈ Icc a b) : m / T ≤ c r := by
    by_contra hnot
    have hratio : c r * T < m := (lt_div_iff₀ hTpos).mp (lt_of_not_ge hnot)
    let A : Set (DistRd d) := {g | m ≤ rawAt ξ D g r ∧ rawAt ξ D g r ≤ M}
    let Bad : Set (DistRd d) :=
      {g | ¬ ∀ u ∈ K, ∀ v ∈ K, normalizedAtScale ξ D c g r (u, v) < T}
    have hsub : A ⊆ Bad := by
      intro g hg hgood
      have hnorm : normalizedAtScale ξ D c g r p < T :=
        hgood 0 (by simp [K]) (e₁ d) (by simp [K])
      have hcmp := mul_lt_mul_of_pos_left hnorm (hD.c_pos r (hrange r hr).1)
      rw [← rawAt_eq_c_mul_norm ξ D c g (hD.c_pos r (hrange r hr).1).ne'] at hcmp
      exact (not_lt_of_ge hg.1) (hcmp.trans hratio)
    have hlt := (hraw r hr).trans_le (measure_mono hsub)
    exact (lt_irrefl (4⁻¹ : ℝ≥0∞)) (hlt.trans (hup r (hrange r hr)))
  let B : ℝ := max 1 (max (M / η) (T / m))
  have hB : 0 < B := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨B,hB,fun r hr => ?_⟩
  constructor
  · have hTm : 0 < T / m := div_pos hTpos hm
    have hle : T / m ≤ B := (le_max_right _ _).trans (le_max_right _ _)
    have hinv : B⁻¹ ≤ (T / m)⁻¹ := inv_anti₀ hTm hle
    rw [inv_div] at hinv
    exact hinv.trans (hclower r hr)
  · exact (hcupper r hr).trans ((le_max_left _ _).trans (le_max_right _ _))

end HigherDimLQGMetric
