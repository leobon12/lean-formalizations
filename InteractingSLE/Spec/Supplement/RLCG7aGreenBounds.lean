/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aMeanIdentGreen

/-!
# Uniform bounds for the active-domain Green correction

Packet PROVE-G7A-MEANIDENT, continuation. The source may be swallowed. The
landed half-plane logarithmic-potential bound and Green monotonicity give the
boundedness clause of `AliveGreenRegularityStatement` without any input.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap greenH)

namespace InteractingSLE.Restart.FlowLocalityGen
open FlowStopIdentCMI

/-- The time-zero source adapter permits use of the landed half-plane bound.
The auxiliary constant driver is chosen outside the source's bounding ball;
no hypothesis on the actual Loewner evolution is added. -/
theorem isSrc_zero_const_of_bounded {v : ℂ → ℝ} (hv : Measurable v)
    {C R : ℝ} (hR : 0 ≤ R) (hC : ∀ z, |v z| ≤ C)
    (hvH : ∀ z, v z ≠ 0 → z ∈ H) (hvR : ∀ z, v z ≠ 0 → ‖z‖ ≤ R) :
    GB7a.IsSrc (fun _ => R + 1) v 0 C R 1 := by
  have hfar : ∀ z, v z ≠ 0 → 1 ≤ ‖z - ((R + 1 : ℝ) : ℂ)‖ := by
    intro z hz
    have htri := norm_add_le (((R + 1 : ℝ) : ℂ) - z) z
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ R + 1), norm_sub_rev] at htri
    linarith [hvR z hz]
  refine ⟨hv, hC, zero_lt_one, ?_, hvR, ?_⟩
  · intro z hz
    rw [QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const, sdiff_empty]
    exact hvH z hz
  · intro z hz s hs
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst s
    have hu : QuantumZipper.IsForwardSol (fun _ => R + 1) z 0
        (fun _ => z - ((R + 1 : ℝ) : ℂ)) := by
      refine ⟨continuousOn_const, ?_⟩
      intro r hr
      have hr0 : r = 0 := le_antisymm hr.2 hr.1
      subst r
      refine ⟨?_, ?_⟩
      · intro he
        have hn := hfar z hz
        change 1 ≤ ‖z - ((R + 1 : ℝ) : ℂ)‖ at hn
        change z - ((R + 1 : ℝ) : ℂ) = 0 at he
        rw [he, norm_zero] at hn
        exact (not_le_of_gt zero_lt_one) hn
      · simp only [intervalIntegral.integral_same, add_zero]
    rw [QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu ⟨le_rfl, le_rfl⟩]
    exact hfar z hz

/-- The cutoff density has a bounded compact envelope on H. -/
theorem exists_density_source_bounds (F : CMCut) :
    ∃ C R : ℝ, 0 ≤ R ∧
      GB7a.IsSrc (fun _ => R + 1)
        (H.indicator (QuantumZipper.K3.greenDensity F.f)) 0 C R 1 := by
  classical
  obtain ⟨C, hC⟩ := F.hasCompactSupport_greenDensity.exists_bound_of_continuous F.continuous_greenDensity
  obtain ⟨R₀, hR₀⟩ := F.hasCompactSupport_greenDensity.isCompact.isBounded.subset_closedBall 0
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  refine ⟨max C 0, R, hR, isSrc_zero_const_of_bounded
    (F.continuous_greenDensity.measurable.indicator QuantumZipper.isOpen_H.measurableSet) hR ?_ ?_ ?_⟩
  · intro z
    by_cases hz : z ∈ H
    · rw [indicator_of_mem hz, ← Real.norm_eq_abs]
      exact (hC z).trans (le_max_left _ _)
    · rw [indicator_of_notMem hz, abs_zero]
      exact le_max_right _ _
  · intro z hz
    by_contra hnot
    exact hz (indicator_of_notMem hnot _)
  · intro z hz
    have hzH : z ∈ H := by
      by_contra hnot
      exact hz (indicator_of_notMem hnot _)
    have hzn : QuantumZipper.K3.greenDensity F.f z ≠ 0 := by
      rwa [indicator_of_mem hzH] at hz
    have hball := hR₀ (subset_tsupport _ hzn)
    rw [mem_closedBall, dist_zero_right] at hball
    exact hball.trans (le_max_left _ _)

/-- A single constant bounds the active potential at every active point.
No survival or separation hypothesis is placed on the cutoff density. -/
theorem exists_abs_aliveGreenPot_le (F : CMCut) :
    ∃ B : ℝ, ∀ (w : ℝ → ℝ), Continuous w → ∀ t : ℝ, 0 ≤ t →
      ∀ z ∈ H \ fwdHull w t, |aliveGreenPot F w t z| ≤ B := by
  classical
  obtain ⟨C, R, _, hs⟩ := exists_density_source_bounds F
  refine ⟨GB7a.IsSrc.greenBound C R, ?_⟩
  intro w hw t ht z hz
  have hi := (hs.integrable_greenH_mul z).abs
  have hbound := hs.integral_abs_greenH_mul_le hz.1
  refine (abs_integral_le_integral_abs).trans
    ((integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hi ?_).trans hbound)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton z)] with a haz
  by_cases ha : a ∈ H \ fwdHull w t
  · have hga := GB7a.greenH_fwdMap_le hw ht hz ha (Ne.symm haz)
    have hg0 := QuantumZipper.greenH_nonneg (show z ∈ Hbar from le_of_lt (show 0 < z.im from hz.1))
      (show a ∈ Hbar from le_of_lt (show 0 < a.im from ha.1)) (Ne.symm haz)
    rw [indicator_of_mem ha, indicator_of_mem ha.1, abs_mul, abs_mul,
      abs_of_nonneg hga.1, abs_of_nonneg hg0]
    exact mul_le_mul_of_nonneg_right hga.2 (abs_nonneg _)
  · rw [indicator_of_notMem ha, mul_zero, abs_zero]
    exact abs_nonneg _

/-- The boundedness clause in `AliveGreenRegularityStatement` is unconditional. -/
theorem isBounded_greenCorrection (F : CMCut) {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {Ψ : ℂ → ℂ}
    (hΨ : EqOn Ψ (QuantumZipper.fwdMapInv w t) H) :
    Bornology.IsBounded (greenCorrection F w t Ψ '' H) := by
  obtain ⟨B, hB⟩ := exists_abs_aliveGreenPot_le F
  obtain ⟨C, hC⟩ := F.compact.exists_bound_of_continuous F.smooth.continuous
  refine isBounded_iff_forall_norm_le.2 ⟨C + B, ?_⟩
  rintro _ ⟨ξ, hξ, rfl⟩
  have hz : Ψ ξ ∈ H \ fwdHull w t := by
    rw [hΨ hξ]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht hξ
  rw [greenCorrection, Real.norm_eq_abs]
  exact (abs_sub _ _).trans (add_le_add (by simpa only [Real.norm_eq_abs] using hC (Ψ ξ))
    (hB w hw t ht _ hz))

end InteractingSLE.Restart.FlowLocalityGen
