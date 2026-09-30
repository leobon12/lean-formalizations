import QuantumZipper.Proofs.Zipper.SWCoreVAReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-VA (iii), map direction: the energy modulus of pushed circles in the map

Task SWC-VA (`handoff/SW-CORE.md` §5). For two maps `ψ, φ` of a rational area class that are
`ε`-close on the circle `∂B(z, r)` (`z ∈ K`, `0 < r ≤ R₀`),

  `|kernelCov2 neumannH (ψ_* fc(z,r) − φ_* fc(z,r))| ≤ A(r) ε^{1/2}`

with `A(r)` depending only on the class data and `r` (`swcVA_push_map_le`). Together with the
centre modulus (`swcVA_push_push_le`) this is the variance modulus in `(ψ, z)` needed to chain over
the class (SW Lemma 3.5, (3.21)–(3.22), p. 16).

Proof (generic, `swcVA_kernelCov2_map_map_le`): for `μ = σ.map f`, `ν = σ.map g`,
`kernelCov2 (μ − ν) = ∫ (U_μ ∘ f − U_μ ∘ g) dσ − ∫ (U_ν ∘ f − U_ν ∘ g) dσ` with the Neumann
potentials `U_κ = neuPot κ`, which are `1/2`-Hölder for `1`-Frostman `κ`
(`TwoPoint.abs_neuPot_sub_le`, the Duplantier–Sheffield Prop. 3.1-type potential bound of the
repository). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

open E6 E6.XAreaPC TwoPoint

/-- The Hölder constant of the Neumann potential of a `1`-Frostman probability measure with
constant `C`, supported in `B̄(0,B)`, on `B̄(0,B)`. -/
def swcPotK (C B : ℝ) : ℝ := 2 * (1 + 4 * C / 1) + 2 * (2 * (C / 1) + 2 * (Real.log (B + B + 1) * 1))

open Classical in
/-- The measurable version of a class map on a small circle: same pushforward, `1`-Frostman with
constant `12/((m/2) r)`, values bounded by `|M|` and equal to `ψ` on the circle. -/
theorem swcVA_push_facts {a b c d ρ M m : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ z ∈ rectC a b c d,
      ∀ r : ℝ, 0 < r → r ≤ R₀ → ∃ ψt : ℂ → ℂ, Measurable ψt ∧
        (foldedCircle z r).map ψ = (foldedCircle z r).map ψt ∧
        IsFrostman ((foldedCircle z r).map ψt) 1 (12 / (m / 2 * r)) ∧
        (∀ᵐ x ∂foldedCircle z r, ‖ψt x‖ ≤ |M| ∧ ρ ≤ (ψt x).im ∧ ψt x = ψ x ∧ x ∈ sphere z r) := by
  obtain ⟨L, R₀, -, hR₀, h⟩ := swcVA_qt_lip (a := a) (b := b) (d := d) (M := M) hc hρ hm
  refine ⟨min R₀ c, lt_min hR₀ hc, fun ψ hψ z hz r hr hrr => ?_⟩
  obtain ⟨hlow, -, hKU, -⟩ := h ψ hψ z hz R₀ hR₀.le le_rfl
  have hψd : DifferentiableOn ℂ ψ (thickening ρ (rectC a b c d)) := hψ.1
  have hψb := hψ.2.2.1
  set U := thickening ρ (rectC a b c d) with hU
  set K := closedBall z R₀ with hKdef
  have hKc : Convex ℝ K := convex_closedBall z R₀
  set ψt := U.piecewise ψ 0 with hψt
  have hEq : EqOn ψt ψ U := fun x hx => piecewise_eq_of_mem _ _ _ hx
  have hψtm : Measurable ψt :=
    hψd.continuousOn.measurable_piecewise continuousOn_const isOpen_thickening.measurableSet
  have hm2 : 0 < m / 2 := by positivity
  have hlow' : ∀ x ∈ K, ∀ y ∈ K, m / 2 * ‖x - y‖ ≤ ‖ψt x - ψt y‖ := by
    intro x hx y hy
    rw [hEq (hKU hx), hEq (hKU hy), ← ddq_mul isOpen_thickening hψd hKc hKU hx hy, norm_mul]
    exact mul_le_mul_of_nonneg_right (hlow x hx y hy) (norm_nonneg _)
  have hrR : r ≤ R₀ := hrr.trans (min_le_left _ _)
  have hrc : r ≤ z.im := (hrr.trans (min_le_right _ _)).trans hz.2.1
  have hzK : closedBall z r ⊆ K := closedBall_subset_closedBall hrR
  have hsph : ∀ᵐ u ∂foldedCircle z r, u ∈ sphere z r := by
    rw [foldedCircle_eq_circleUnif hr.le hrc]
    filter_upwards [CircleMV.ae_circleUnif z r] with u hu
    rw [mem_sphere_iff_norm, hu, abs_of_pos hr]
  have hU' : ∀ u ∈ sphere z r, u ∈ U := fun u hu => hKU (hzK (sphere_subset_closedBall hu))
  refine ⟨ψt, hψtm, ?_, swcVA_isFrostman_push hψtm hr hm2 hlow' hrc hzK, ?_⟩
  · refine Measure.map_congr ?_
    filter_upwards [hsph] with u hu
    exact (hEq (hU' u hu)).symm
  · filter_upwards [hsph] with u hu
    refine ⟨?_, ?_, hEq (hU' u hu), hu⟩
    · rw [hEq (hU' u hu)]
      exact (hψb u (hU' u hu)).1.trans (le_abs_self M)
    · rw [hEq (hU' u hu)]
      exact (hψb u (hU' u hu)).2

end SWCore
end QuantumZipper
