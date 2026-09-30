import QuantumZipper.Proofs.Zipper.SWCoreVAMod
import QuantumZipper.Proofs.Zipper.XPCSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-VA (ii): the dyadic regularization tails of pushed circles, uniformly over an area class

Task SWC-VA (`handoff/SW-CORE.md` §5). For a rational area class there are `R₀ > 0` and, for
`0 < r ≤ R₀`, an explicit constant `A(r)` (class data only) such that for every `ψ` of the class,
`z ∈ K` and smoothing radii `σ, σ' ∈ [0,1]`,

  `|kernelCov2 neumannH (μ^σ − μ^{σ'})| ≤ A(r) |σ − σ'|^{1/6}`,  `μ = ψ_* fc(z, r)`,
  `μ^σ = bindFc μ σ` (`swcVA_bindFc_le`).

With `σ = 2^{-j}, σ' = 2^{-j-1}` this is the variance of `∫ (h_{2^{-j}} − h_{2^{-j-1}}) dμ`, the
tail of the regularization `evalReg` along the pushed circles (SW Lemma 3.5 (3.21)–(3.22),
p. 16, input of the chaining SWC-NA): summable in `j`, uniformly over the class.

Proof: the pushed circle is `1`-Frostman with constant `12/((m/2) r)`
(`swcVA_isFrostman_push`: the class maps are `m/2`-bi-Lipschitz from below on small discs by the
divided-difference bound of `swcVA_qt_lip`; the argument of `E6.XAreaPC.isFrostman_muP_of_lower`),
hence `1/3`-Frostman; then the repository's radius modulus `RegCont.abs_kernelCov2_bindFc_le`
(Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 type estimate). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

open E6 E6.XAreaPC

/-- **Frostman bound for a pushed circle** from a lower Lipschitz bound of a measurable map. -/
theorem swcVA_isFrostman_push {ψ : ℂ → ℂ} (hψm : Measurable ψ) {K : Set ℂ} {m r : ℝ}
    (hr : 0 < r) (hm : 0 < m) (hlow : ∀ x ∈ K, ∀ y ∈ K, m * ‖x - y‖ ≤ ‖ψ x - ψ y‖)
    {z : ℂ} (hz : r ≤ z.im) (hzK : closedBall z r ⊆ K) :
    TwoPoint.IsFrostman ((foldedCircle z r).map ψ) 1 (12 / (m * r)) := by
  intro p ρ hρ
  rw [Measure.map_apply hψm measurableSet_closedBall]
  have hsph : ∀ᵐ u ∂foldedCircle z r, u ∈ sphere z r := by
    rw [foldedCircle_eq_circleUnif hr.le hz]
    filter_upwards [CircleMV.ae_circleUnif z r] with u hu
    rw [mem_sphere_iff_norm, hu, abs_of_pos hr]
  have hC : 0 ≤ 12 / (m * r) * ρ ^ (1 : ℝ) := by positivity
  by_cases h : ∃ u₀ ∈ sphere z r, ψ u₀ ∈ closedBall p ρ
  · obtain ⟨u₀, hu₀, hψu₀⟩ := h
    have hle : foldedCircle z r (ψ ⁻¹' closedBall p ρ) ≤
        foldedCircle z r (closedBall u₀ (2 * ρ / m)) := by
      refine measure_mono_ae (hsph.mono fun u hu hus => ?_)
      have hus' : ψ u ∈ closedBall p ρ := hus
      have hk := hlow u (hzK (sphere_subset_closedBall hu)) u₀
        (hzK (sphere_subset_closedBall hu₀))
      rw [mem_closedBall, dist_eq_norm] at hus' hψu₀
      have hd : ‖ψ u - ψ u₀‖ ≤ 2 * ρ := by
        calc ‖ψ u - ψ u₀‖ = ‖(ψ u - p) - (ψ u₀ - p)‖ := by congr 1; ring
          _ ≤ ‖ψ u - p‖ + ‖ψ u₀ - p‖ := norm_sub_le _ _
          _ ≤ 2 * ρ := by linarith
      show u ∈ closedBall u₀ (2 * ρ / m)
      rw [mem_closedBall, dist_eq_norm, le_div_iff₀ hm]
      linarith
    have h2 := RegCont.foldedCircle_closedBall_le_arc z u₀ hr
      (by positivity : (0 : ℝ) ≤ 2 * ρ / m)
    have e : 6 * (2 * ρ / m) / r = 12 / (m * r) * ρ ^ (1 : ℝ) := by
      rw [Real.rpow_one]; field_simp; ring
    rw [e] at h2
    exact ENNReal.toReal_le_of_le_ofReal hC (hle.trans h2)
  · push Not at h
    have hae : ∀ᵐ u ∂foldedCircle z r, u ∉ ψ ⁻¹' closedBall p ρ := by
      filter_upwards [hsph] with u hu hus
      exact h u hu hus
    have h0 : foldedCircle z r (ψ ⁻¹' closedBall p ρ) = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hae)
      intro u hu hn
      exact hn hu
    rw [h0, ENNReal.toReal_zero]
    exact hC

end SWCore
end QuantumZipper
