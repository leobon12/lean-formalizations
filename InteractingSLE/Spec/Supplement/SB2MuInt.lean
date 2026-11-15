/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuK2

/-!
# Chart-pairing integrability from a conditional GFF law with bounded data

Packet PROVE-SB2-LCMEAN, round 13 (K2's integrability input `hint` of `Mu.ae_isStopDrvMatch_of_lines`). If, given a
sub-σ-algebra `𝒢`, the field read in a random chart is on a `𝒢`-event `G` a GFF with the data of a word bounded by
one constant, then every pairing of the chart field (with any constant shift) is integrable on every measurable
`F ⊆ G`: the conditional first moment is bounded uniformly (`BW1In.lintegral_enorm_apply_le_of_isGFF`), and the
disintegration over `𝒢` integrates the bound. This is SB2(1)'s `Lv.integrableOn_chartPairing` with the conditional
law as a hypothesis; for SB2(2) the law is the retained kernel law at B's stage (REVIEW-FABLE-T14's F3 route).

* **`integrableOn_chartPairing_of_law`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mu

open Restart

/-- **Chart-pairing integrability from a conditional GFF law with uniformly bounded data.** -/
theorem integrableOn_chartPairing_of_law {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {G F : Set Ω}
    (hG : MeasurableSet[𝒢] G) (hF : MeasurableSet F) (hFG : F ⊆ G) {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    (k : ℝ) {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : ∀ᵐ ω ∂P, ω ∈ G → Y ω = Chart.chartTransport (hc ω) 1 0 k (h ω)) {β : Ω → BoundaryWord} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ ω, ∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Y (β ω₀).fn (β ω₀).jumps)
    (a : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    IntegrableOn (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) φ) F P := by
  have hXm : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) φ :=
    (LQGMetric.measurable_distOn_apply φ).comp
      (Chart.measurable_chartTransport_random' hc hdom hfwd hliftm hliftc hhm 1 a k)
  set K : ℝ≥0∞ := ‖a * Chart.oneDist φ‖ₑ with hK
  set C : ℝ≥0∞ := ENNReal.ofReal (M * ∫ z, |φ z|) +
    ∫⁻ x, ‖x‖ₑ ∂(gaussianReal 0 (QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ).toNNReal) + K
    with hC
  have hCtop : C < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
    BW1In.lintegral_enorm_gaussianReal_lt_top _⟩, enorm_lt_top⟩
  set f : Ω → ℝ≥0∞ := F.indicator fun ω => ‖Chart.chartTransport (hc ω) 1 a k (h ω) φ‖ₑ with hfdef
  have hfm : Measurable f := hXm.enorm.indicator hF
  have hYK := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hY
  have hbound : ∀ᵐ ω₀ ∂P, ∫⁻ ω, f ω ∂(condExpKernel P 𝒢 ω₀) ≤ C := by
    filter_upwards [KernelTower.ae_condExpKernel_compl_eq_zero (P := P) h𝒢 hG, hlaw, hYK] with ω₀ hc0 hl hyk
    by_cases hω₀ : ω₀ ∈ G
    · have hGK : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ G := by
        rw [ae_iff]
        exact hc0.1 hω₀
      have hpt : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), f ω ≤ ‖Y ω φ‖ₑ + K := by
        filter_upwards [hyk, hGK] with ω hω hωG
        by_cases hωF : ω ∈ F
        · rw [hfdef, indicator_of_mem hωF]
          have hsplit : Chart.chartTransport (hc ω) 1 a k (h ω) φ =
              Chart.chartTransport (hc ω) 1 0 k (h ω) φ + a * Chart.oneDist φ := by
            rw [Chart.chartTransport_apply', Chart.chartTransport_apply']
            ring
          rw [hsplit, ← hω hωG]
          exact enorm_add_le _ _
        · rw [hfdef, indicator_of_notMem hωF]
          exact zero_le
      calc ∫⁻ ω, f ω ∂(condExpKernel P 𝒢 ω₀) ≤ ∫⁻ ω, (‖Y ω φ‖ₑ + K) ∂(condExpKernel P 𝒢 ω₀) :=
            lintegral_mono_ae hpt
        _ = ∫⁻ ω, ‖Y ω φ‖ₑ ∂(condExpKernel P 𝒢 ω₀) + K := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ C := add_le_add_left
            (BW1In.lintegral_enorm_apply_le_of_isGFF (β ω₀).isPiecewiseConstantBoundaryData (hl hω₀) hM0
              (hM ω₀) φ) K
    · have h0 : condExpKernel P 𝒢 ω₀ F = 0 := measure_mono_null hFG (hc0.2 hω₀)
      rw [hfdef, lintegral_indicator hF, setLIntegral_measure_zero _ _ h0]
      exact zero_le
  refine ⟨hXm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [← lintegral_indicator hF]
  change ∫⁻ ω, f ω ∂P < ⊤
  rw [← KernelTower.lintegral_lintegral_condExpKernel h𝒢 hfm]
  calc ∫⁻ ω₀, ∫⁻ ω, f ω ∂(condExpKernel P 𝒢 ω₀) ∂P ≤ ∫⁻ _, C ∂P := lintegral_mono_ae hbound
    _ = C := by rw [lintegral_const, measure_univ, mul_one]
    _ < ⊤ := hCtop

end InteractingSLE.Theorem14.SB.Mu
