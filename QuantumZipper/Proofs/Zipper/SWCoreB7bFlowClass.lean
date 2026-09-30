import QuantumZipper.Proofs.Zipper.SWCoreB7bFlowShift
import QuantumZipper.Proofs.Zipper.SWCoreDefs
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b-FLOW (3): a translated reverse map with good solutions lies in a boundary class

`b7bf_mem_bdryClass`: if every point of a `ρ`-ball around every point of the translated
thickening `thickening ρ (segC a b) + d` has a complex reverse solution with clearance `c`,
the map `z ↦ revMapExt W L (z + d)` (`d` real) is in `BdryClass a b ρ M 1`, with the explicit
bound `M ≥ R + B + 2L/c` and a derivative lower bound `≥ 1` supplied on the segment.

Own elementary argument from `RevMapExtension.hasDerivAt_revMapExt` (holomorphy),
`RegUnif.norm_isCRevSol_le` (bound), `RevMapExtension.revMapExt_conj` (reality) and positivity
of the derivative on the segment (monotonicity).
-/

noncomputable section

open Complex Filter MeasureTheory Set Metric
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace SWCore

open RevMapExtension

theorem b7bf_mem_bdryClass {W : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) {a b ρ M c R B : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) (d : ℝ)
    (hgood : ∀ z ∈ thickening ρ (segC a b), ∀ y ∈ ball (z + d) ρ,
      ∃ u, IsCRevSol W y L u ∧ ∀ r ∈ Icc (0 : ℝ) L, c ≤ ‖u r‖)
    (hR : ∀ z ∈ thickening ρ (segC a b), ‖z + d‖ ≤ R) (hB : |W L| ≤ B)
    (hM : R + B + 2 / c * L ≤ M)
    (hder : ∀ t ∈ Icc a b, 1 ≤ ‖deriv (revMapExt W L) ((t : ℂ) + d)‖ ∧
      0 < (deriv (revMapExt W L) ((t : ℂ) + d)).re) :
    (fun z => revMapExt W L (z + d)) ∈ BdryClass a b ρ M 1 := by
  have hHD : ∀ z ∈ thickening ρ (segC a b), HasDerivAt (fun z => revMapExt W L (z + d))
      (deriv (revMapExt W L) (z + d)) z := by
    intro z hz
    obtain ⟨u₀, hu₀, -⟩ := hgood z hz (z + d) (mem_ball_self hρ)
    have h := hasDerivAt_revMapExt hL hρ hc (hgood z hz) hu₀
    exact (h.differentiableAt.hasDerivAt).comp_add_const z (d : ℂ)
  have hseg : ∀ t ∈ Icc a b, (t : ℂ) ∈ thickening ρ (segC a b) := fun t ht =>
    self_subset_thickening hρ _ ⟨t, ht, rfl⟩
  refine ⟨fun z hz => (hHD z hz).differentiableAt.differentiableWithinAt, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨u, hu, hub⟩ := hgood z hz (z + d) (mem_ball_self hρ)
    show ‖revMapExt W L (z + d)‖ ≤ M
    rw [revMapExt_eq hu hL]
    have h1 := RegUnif.norm_isCRevSol_le hc hu hub ⟨hL, le_rfl⟩
    have h2 := hR z hz
    linarith
  · intro t _
    show (revMapExt W L ((t : ℂ) + d)).im = 0
    have e : ((t : ℂ) + d) = ((t + d : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    have h := revMapExt_conj (W := W) hL ((t + d : ℝ) : ℂ)
    rw [Complex.conj_ofReal] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  · have hg : ∀ t ∈ Icc a b, HasDerivAt (fun t : ℝ => (revMapExt W L ((t : ℂ) + d)).re)
        (deriv (revMapExt W L) ((t : ℂ) + d)).re t := fun t ht =>
      (hHD t (hseg t ht)).real_of_complex
    refine strictMonoOn_of_deriv_pos (convex_Icc a b)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt) fun t ht => ?_
    have ht' := interior_subset ht
    rw [(hg t ht').deriv]
    exact (hder t ht').2
  · intro t ht
    rw [(hHD t (hseg t ht)).deriv]
    exact (hder t ht).1

end SWCore
end QuantumZipper
