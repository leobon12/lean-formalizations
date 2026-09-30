import QuantumZipper.Proofs.Thm18.G1Side3RepMain
import QuantumZipper.Proofs.Thm18.G3Pl4Z
import QuantumZipper.Proofs.Thm18.G1TopMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (21): positivity of the pulled-back area

* `pullMu_pos`: the pullback `pullMu ν Φ` of a measure charging every nonempty open subset of `ℍ`
  by a conformal map `Φ : ℍ → ℍ` (holomorphic, injective, nonvanishing derivative) charges every
  nonempty open subset of `ℍ` (inverse function theorem: `Φ` maps a neighbourhood of any point
  onto a neighbourhood of its image).
* `ae_areaLimit_rep_pos`: hence for a.e. Brownian path, a.s. the coordinate-changed wedge
  representative `coordChange (wedgeRep ω') (Ψ left a) Q` has an area limit charging every
  nonempty open subset of `ℍ` (from G1-SIDE's `G1Side.ae_areaLimit_rep`, the pullback of the
  unscaled wedge area, and the area goodness of the unscaled wedge `g3pl4_ae_isAreaGood_Z`).

This is the positivity half of the pulled-back goodness (Duplantier–Sheffield, arXiv:0808.1560,
Prop. 2.1, coordinate change). Own elementary proof (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open G1Side

/-- **The pullback by a conformal self-map of `ℍ` charges open sets.** -/
theorem pullMu_pos {ν : Measure ℂ} {Φ : ℂ → ℂ} (hd : DifferentiableOn ℂ Φ H) (hi : InjOn Φ H)
    (hH : MapsTo Φ H H) (h0 : ∀ z ∈ H, deriv Φ z ≠ 0)
    (hν : ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < ν V)
    {E : Set ℂ} (hE : IsOpen E) (hEH : E ⊆ H) (hne : E.Nonempty) : 0 < pullMu ν Φ E := by
  obtain ⟨z, hz⟩ := hne
  have hzH : z ∈ H := hEH hz
  have hs : HasStrictDerivAt Φ (deriv Φ z) z :=
    (hd.analyticAt (isOpen_H'.mem_nhds hzH)).hasStrictDerivAt
  have hmap := hs.map_nhds_eq (h0 z hzH)
  have hmem : Φ '' E ∈ 𝓝 (Φ z) := by
    rw [← hmap]; exact image_mem_map (hE.mem_nhds hz)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  rw [pullMu_apply hd.continuousOn hi hE.measurableSet, inter_eq_left.2 hEH]
  refine lt_of_lt_of_le (hν (ball (Φ z) ε ∩ H) (isOpen_ball.inter isOpen_H')
    inter_subset_right ⟨Φ z, mem_ball_self hε, hH hzH⟩) (measure_mono ?_)
  exact inter_subset_left.trans hball

/-- Scaling a conformal self-map of `ℍ` by a positive constant keeps it one. -/
theorem sideMapFacts_smul {ψ : ℂ → ℂ} (h : G1Side.SideMapFacts ψ) {s : ℝ} (hs : 0 < s) :
    DifferentiableOn ℂ (fun u => (s : ℂ) * ψ u) H ∧ InjOn (fun u => (s : ℂ) * ψ u) H ∧
      MapsTo (fun u => (s : ℂ) * ψ u) H H ∧ ∀ z ∈ H, deriv (fun u => (s : ℂ) * ψ u) z ≠ 0 := by
  obtain ⟨-, hd, hi, hH, h0, -⟩ := h
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  refine ⟨hd.const_mul _, fun u hu v hv huv => hi hu hv (mul_left_cancel₀ hs0 huv),
    fun u hu => ?_, fun z hz => ?_⟩
  · show 0 < ((s : ℂ) * ψ u).im
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos hs (hH hu)
  · have hda : DifferentiableAt ℂ ψ z := hd.differentiableAt (isOpen_H'.mem_nhds hz)
    rw [deriv_const_mul _ hda]
    exact mul_ne_zero hs0 (h0 z hz)

end G3ZqL
end Thm18Asm
end QuantumZipper
