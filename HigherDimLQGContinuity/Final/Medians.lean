import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Norm.Rho
import HigherDimLQGMetric.Sec10.Lemma101
import HigherDimLQGMetric.Sec10.Lemma103
import HigherDimLQGMetric.Frozen.Theorem12
import GaussianLQG.Probability.Medians

/-!
# Medians of the positive-parameter version

Packet E4. This module identifies the median of the jointly measurable positive
version with the unique median of the mean-log normalized strong metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

namespace HigherDimLQGContinuity

theorem e4_median_mul_iff {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {c : ℝ} (hc : 0 < c) (m : ℝ) :
    LQGMetric.IsMedian (P.map (fun ω => c * X ω)) (c * m) ↔
      LQGMetric.IsMedian (P.map X) m := by
  have hY : AEMeasurable (fun ω => c * X ω) P := hX.const_mul c
  rw [LQGMetric.isMedian_map_iff hY, LQGMetric.isMedian_map_iff hX]
  simp only [mul_le_mul_iff_of_pos_left hc]

/-- The median of the version at one parameter. Its value off the positive
subcritical set is unused. -/
noncomputable def medianXi (d : ℕ)
    (X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)) (ξ : ℝ) : ℝ :=
  LQGMetric.lowerMedianLaw ((normLGFLaw d).map fun g => X ξ g (0, e₁ d))

private theorem e4_measurable_pin {d : ℕ}
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : Measurable (Function.uncurry X)) (ξ : ℝ) :
    Measurable fun g => X ξ g (0, e₁ d) := by
  have hξ : Measurable (fun g : DistRd d => X ξ g) :=
    hX.comp (measurable_const.prodMk measurable_id)
  exact (ContinuousMap.measurable_eval (0, e₁ d)).comp hξ

private theorem e4_median_rho_iff {d : ℕ} (hd : 3 ≤ d) {ξ : ℝ} (_hξ : 0 < ξ)
    {E : DistRd d → ContMetric d}
    (hE : IsStrongExpMetric d ξ (distExp d ξ) E) {m : ℝ} :
    LQGMetric.IsMedian ((normLGFLaw d).map fun g => (rho E g).1 (0, e₁ d)) m ↔
      LQGMetric.IsMedian ((normLGFLaw d).map fun g => (E g).1 (0, e₁ d))
        (m / Real.exp (-logMean E)) := by
  haveI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d (by omega)).1
  have hc : 0 < Real.exp (-logMean E) := Real.exp_pos _
  have hX : AEMeasurable (fun g => (E g).1 (0, e₁ d)) (normLGFLaw d) :=
    (p2_measurable_contMetric_apply hE.measurable _).aemeasurable
  have hmul := e4_median_mul_iff hX hc (m / Real.exp (-logMean E))
  have heq : Real.exp (-logMean E) * (m / Real.exp (-logMean E)) = m := by
    field_simp
  simpa only [heq, rho_apply] using hmul

/-- Every strong metric gives the same unique median to its normalized unit
distance, and that median is positive. -/
theorem medianXi_spec {d : ℕ} (hd : 3 ≤ d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {E : DistRd d → ContMetric d}
    (hE : IsStrongExpMetric d ξ (distExp d ξ) E) :
    0 < medianXi d X ξ ∧
      LQGMetric.IsMedian ((normLGFLaw d).map fun g => (rho E g).1 (0, e₁ d))
        (medianXi d X ξ) ∧
      ∀ m : ℝ,
        LQGMetric.IsMedian ((normLGFLaw d).map fun g => (rho E g).1 (0, e₁ d)) m →
        m = medianXi d X ξ := by
  haveI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d (by omega)).1
  have hXm : Measurable (fun g => X ξ g (0, e₁ d)) := e4_measurable_pin hX.1 ξ
  have hY : (fun g => X ξ g (0, e₁ d)) =ᵐ[normLGFLaw d]
      (fun g => (rho E g).1 (0, e₁ d)) := by
    filter_upwards [hX.2.1 ξ hξ hsub E hE] with g hg
    exact congrArg (fun F : C(Rd d × Rd d, ℝ) => F (0, e₁ d)) hg
  have hlaw : (normLGFLaw d).map (fun g => X ξ g (0, e₁ d)) =
      (normLGFLaw d).map (fun g => (rho E g).1 (0, e₁ d)) := Measure.map_congr hY
  have hm : LQGMetric.IsMedian ((normLGFLaw d).map fun g => (rho E g).1 (0, e₁ d))
      (medianXi d X ξ) := by
    rw [← hlaw]
    exact LQGMetric.isMedian_lowerMedianLaw
  have huniq : ∀ m : ℝ,
      LQGMetric.IsMedian ((normLGFLaw d).map fun g => (rho E g).1 (0, e₁ d)) m →
      m = medianXi d X ξ := by
    intro m hmed
    have he1 := (e4_median_rho_iff hd hξ hE).1 hmed
    have he2 := (e4_median_rho_iff hd hξ hE).1 hm
    have hD : IsWeakExpMetric d ξ E (fun r => r ^ (ξ * distExp d ξ)) :=
      lemma101 (by omega) hξ hE
    have hEmeas : AEMeasurable (fun g => (E g).1 (0, e₁ d)) (normLGFLaw d) :=
      (p2_measurable_contMetric_apply hE.measurable _).aemeasurable
    have hq := lemma103_median_unique (by omega) hξ hD (normLGFLaw d) id
      (normLGFLaw_spec_holds d (by omega)).2.1
      ((LQGMetric.isMedian_map_iff hEmeas).1 he1)
      ((LQGMetric.isMedian_map_iff hEmeas).1 he2)
    have hc : Real.exp (-logMean E) ≠ 0 := (Real.exp_pos _).ne'
    exact (div_left_inj' hc).1 hq
  have hpos : 0 < medianXi d X ξ := by
    have hYmeas : AEMeasurable (fun g => (rho E g).1 (0, e₁ d)) (normLGFLaw d) :=
      (p2_measurable_contMetric_apply (measurable_rho hE.measurable) _).aemeasurable
    have hYpos : ∀ᵐ g ∂(normLGFLaw d), 0 < (rho E g).1 (0, e₁ d) := by
      exact Filter.Eventually.of_forall fun g =>
        (rho E g).apply_pos (p2_zero_ne_e₁ (by omega))
    exact GaussianLQG.IsMedian.pos_of_ae_pos hYmeas hYpos hm
  exact ⟨hpos, hm, huniq⟩

private theorem e4_tendsto_median_seq {d : ℕ} (hd : 3 ≤ d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) {u : ℕ → ℝ} {Z : DistRd d → ℝ} {q : ℝ}
    (hZ : AEMeasurable Z (normLGFLaw d))
    (hconv : ∀ᵐ g ∂(normLGFLaw d),
      Tendsto (fun n => X (u n) g (0, e₁ d)) atTop (𝓝 (Z g)))
    (huniq : ∀ m : ℝ, LQGMetric.IsMedian ((normLGFLaw d).map Z) m → m = q) :
    Tendsto (fun n => medianXi d X (u n)) atTop (𝓝 q) := by
  haveI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d (by omega)).1
  have hXm (n : ℕ) : AEStronglyMeasurable
      (fun g => X (u n) g (0, e₁ d)) (normLGFLaw d) :=
    (e4_measurable_pin hX.1 (u n)).aestronglyMeasurable
  have hmeasure : TendstoInMeasure (normLGFLaw d)
      (fun n g => X (u n) g (0, e₁ d)) atTop Z :=
    tendstoInMeasure_of_tendsto_ae hXm hconv
  exact GaussianLQG.tendsto_of_isMedian_of_tendstoInMeasure hmeasure
    (Eventually.of_forall fun n => (hXm n).aemeasurable) hZ huniq
    (Eventually.of_forall fun n => LQGMetric.isMedian_lowerMedianLaw)

private theorem e4_const_one_median_unique {d : ℕ} (_hd : 3 ≤ d) (m : ℝ)
    (hm : LQGMetric.IsMedian ((normLGFLaw d).map fun _ : DistRd d => (1 : ℝ)) m) : m = 1 := by
  haveI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d (by omega)).1
  obtain ⟨hlo, hhi⟩ := (LQGMetric.isMedian_map_iff
    (measurable_const : Measurable fun _ : DistRd d => (1 : ℝ)).aemeasurable).1 hm
  rcases lt_trichotomy m 1 with hlt | heq | hgt
  · have : (normLGFLaw d) {g : DistRd d | (1 : ℝ) ≤ m} = 0 := by
      simp [not_le.mpr hlt]
    rw [this] at hlo
    exact absurd hlo (not_le.mpr LQGMetric.inv_two_pos')
  · exact heq
  · have : (normLGFLaw d) {g : DistRd d | m ≤ (1 : ℝ)} = 0 := by
      simp [not_le.mpr hgt]
    rw [this] at hhi
    exact absurd hhi (not_le.mpr LQGMetric.inv_two_pos')

/-- Continuity of the unique medians on the positive subcritical set. -/
theorem continuousOn_medianXi {d : ℕ} (hd : 3 ≤ d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) :
    ContinuousOn (medianXi d X)
      {ξ : ℝ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ} := by
  intro ξ₀ hξ₀
  apply tendsto_iff_seq_tendsto.2
  intro u hu
  obtain ⟨⟨E, hE, -⟩, -⟩ := theorem12 d ξ₀ hd hξ₀.1 hξ₀.2
  have huniq := (medianXi_spec hd hX hξ₀.1 hξ₀.2 hE).2.2
  have hconv : ∀ᵐ g ∂(normLGFLaw d),
      Tendsto (fun n => X (u n) g (0, e₁ d)) atTop
        (𝓝 (X ξ₀ g (0, e₁ d))) := by
    filter_upwards [hX.2.2] with g hg
    have hfield : Tendsto (fun ξ => X ξ g)
        (𝓝[{ξ : ℝ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ}] ξ₀)
        (𝓝 (X ξ₀ g)) := hg ξ₀ hξ₀
    exact ((continuous_eval_const (0, e₁ d)).tendsto _).comp (hfield.comp hu)
  have hlaw : (normLGFLaw d).map (fun g => X ξ₀ g (0, e₁ d)) =
      (normLGFLaw d).map (fun g => (rho E g).1 (0, e₁ d)) := by
    apply Measure.map_congr
    filter_upwards [hX.2.1 ξ₀ hξ₀.1 hξ₀.2 E hE] with g hg
    exact congrArg (fun F : C(Rd d × Rd d, ℝ) => F (0, e₁ d)) hg
  exact e4_tendsto_median_seq hd hX
    (e4_measurable_pin hX.1 ξ₀).aemeasurable hconv
    (fun m hm => huniq m (hlaw ▸ hm))

/-- At the Euclidean endpoint, the medians converge to one. -/
theorem tendsto_medianXi_zero {d : ℕ} (hd : 3 ≤ d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) (hE : EndpointStmt d X) :
    Tendsto (medianXi d X)
      (𝓝[{ξ : ℝ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ}] 0) (𝓝 1) := by
  apply tendsto_iff_seq_tendsto.2
  intro u hu
  have hconv : ∀ᵐ g ∂(normLGFLaw d),
      Tendsto (fun n => X (u n) g (0, e₁ d)) atTop (𝓝 (1 : ℝ)) := by
    filter_upwards [hE] with g hg
    have h := ((continuous_eval_const (0, e₁ d)).tendsto _).comp (hg.comp hu)
    have hd0 : 0 < d := by omega
    simpa only [euclidDistC, ContinuousMap.coe_mk, Function.comp_def, dist_zero_left,
      HigherDimLFPP.norm_e₁ hd0] using h
  exact e4_tendsto_median_seq hd hX measurable_const.aemeasurable hconv
    (e4_const_one_median_unique hd)

end HigherDimLQGContinuity
