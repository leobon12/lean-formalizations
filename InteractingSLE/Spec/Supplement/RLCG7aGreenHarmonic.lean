/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aGreenIntegrals

/-!
# Harmonicity reduced to integration of nonnegative harmonic kernels

Packet PROVE-G7A-MEANIDENT. All Loewner and Green-specific facts are proved.
`NonnegativeHarmonicIntegralStatement` is the explicit remaining analytic
input: a finite-valued integral of nonnegative harmonic sections is harmonic.
The positive and negative cutoff densities reduce the correction to this input.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Restart.FlowLocalityGen
open FlowStopIdentCMI

/-- **Unproved analytic input.** Integration preserves harmonicity for a
nonnegative kernel with harmonic sections and finite integrals at every point.
This is the usual positive harmonic-function integration theorem, independent
of Loewner evolutions, Green kernels, cutoffs, and finite force words. -/
def NonnegativeHarmonicIntegralStatement : Prop :=
  ∀ U : Set ℂ, IsOpen U → ∀ k : ℂ → ℂ → ℝ,
    (∀ a, InnerProductSpace.HarmonicOnNhd (k a) U) →
    (∀ a, ∀ z ∈ U, 0 ≤ k a z) →
    (∀ z ∈ U, Integrable (fun a => k a z) volume) →
    InnerProductSpace.HarmonicOnNhd (fun z => ∫ a, k a z) U

/-- The physical correction is harmonic from positive harmonic-kernel integration. -/
theorem harmonicOnNhd_physicalGreenCorrection_of_integral
    (hInt : NonnegativeHarmonicIntegralStatement) (F : CMCut) {w : ℝ → ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    InnerProductSpace.HarmonicOnNhd (fun z => F.f z - aliveGreenPot F w t z) (H \ fwdHull w t) := by
  let p : ℂ → ℝ := fun a => max (QuantumZipper.K3.greenDensity F.f a) 0
  let n : ℂ → ℝ := fun a => max (-QuantumZipper.K3.greenDensity F.f a) 0
  have hp : Measurable p := F.continuous_greenDensity.measurable.max measurable_const
  have hn : Measurable n := F.continuous_greenDensity.measurable.neg.max measurable_const
  have hp0 : ∀ a, 0 ≤ p a := fun _ => le_max_right _ _
  have hn0 : ∀ a, 0 ≤ n a := fun _ => le_max_right _ _
  have hpb : ∀ a, |p a| ≤ |QuantumZipper.K3.greenDensity F.f a| := fun a => by
    rw [abs_of_nonneg (hp0 a)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnb : ∀ a, |n a| ≤ |QuantumZipper.K3.greenDensity F.f a| := fun a => by
    rw [abs_of_nonneg (hn0 a)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hpn : ∀ a, p a - n a = QuantumZipper.K3.greenDensity F.f a := by
    intro a
    dsimp only [p, n]
    rcases le_total 0 (QuantumZipper.K3.greenDensity F.f a) with ha | ha
    · rw [max_eq_left ha, max_eq_right (neg_nonpos.2 ha), sub_zero]
    · rw [max_eq_right ha, max_eq_left (neg_nonneg.2 ha), zero_sub, neg_neg]
  have hiP : ∀ z ∈ H \ fwdHull w t, Integrable (fun a => p a * residualGreenKernel w t a z) :=
    fun _ hz => integrable_residualGreenKernel_mul F hw ht hz hp hpb
  have hiN : ∀ z ∈ H \ fwdHull w t, Integrable (fun a => n a * residualGreenKernel w t a z) :=
    fun _ hz => integrable_residualGreenKernel_mul F hw ht hz hn hnb
  have hP := hInt (H \ fwdHull w t) (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht)
    (fun a z => p a * residualGreenKernel w t a z)
    (fun a z hz => by
      exact (harmonicOnNhd_residualGreenKernel hw ht a z hz).const_smul (c := p a))
    (fun a z hz => mul_nonneg (hp0 a) (residualGreenKernel_nonneg hw ht a hz)) hiP
  have hN := hInt (H \ fwdHull w t) (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht)
    (fun a z => n a * residualGreenKernel w t a z)
    (fun a z hz => by
      exact (harmonicOnNhd_residualGreenKernel hw ht a z hz).const_smul (c := n a))
    (fun a z hz => mul_nonneg (hn0 a) (residualGreenKernel_nonneg hw ht a hz)) hiN
  have heq : EqOn (fun z => (∫ a, p a * residualGreenKernel w t a z) -
      ∫ a, n a * residualGreenKernel w t a z) (fun z => F.f z - aliveGreenPot F w t z)
      (H \ fwdHull w t) := by
    intro z hz
    dsimp only
    rw [← integral_sub (hiP z hz) (hiN z hz), ← integral_residualGreenKernel_density F hw hw0 ht hz]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    dsimp only
    rw [← sub_mul, hpn]
  intro z hz
  have hev : (fun y => (∫ a, p a * residualGreenKernel w t a y) -
      ∫ a, n a * residualGreenKernel w t a y) =ᶠ[𝓝 z]
      (fun y => F.f y - aliveGreenPot F w t y) := by
    filter_upwards [(QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht).mem_nhds hz]
      with y hy using heq hy
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).1 ((hP.sub hN) z hz)

/-- The harmonicity clause in the inverse chart, from the isolated positive-integral input. -/
theorem harmonicOnNhd_greenCorrection_of_integral
    (hInt : NonnegativeHarmonicIntegralStatement) (F : CMCut) {w : ℝ → ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {Ψ : ℂ → ℂ}
    (hΨeq : EqOn Ψ (fwdMapInv w t) H) :
    InnerProductSpace.HarmonicOnNhd (greenCorrection F w t Ψ) H := by
  have hΨd : DifferentiableOn ℂ Ψ H :=
    (QuantumZipper.RS.differentiableOn_fwdMapInv hw hw0 ht).congr hΨeq
  have hΨD : MapsTo Ψ H (H \ fwdHull w t) := fun ξ hξ => by
    rw [hΨeq hξ]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht hξ
  exact LQGMetric.harmonicOnNhd_comp_holo (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht)
    QuantumZipper.isOpen_H (harmonicOnNhd_physicalGreenCorrection_of_integral hInt F hw hw0 ht) hΨd hΨD

/-- The exact original analytic obligation, with bounds and boundary values discharged. -/
theorem aliveGreenRegularityStatement_of_nonnegativeIntegral
    (hInt : NonnegativeHarmonicIntegralStatement) : AliveGreenRegularityStatement := by
  intro w hw hw0 t ht F Ψ hΨeq hΨc
  exact ⟨harmonicOnNhd_greenCorrection_of_integral hInt F hw hw0 ht hΨeq,
    isBounded_greenCorrection F hw hw0 ht hΨeq,
    tendsto_greenCorrection_boundary F hw hw0 ht hΨeq hΨc⟩

end InteractingSLE.Restart.FlowLocalityGen
