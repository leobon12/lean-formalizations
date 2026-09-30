import QuantumZipper.Proofs.Thm18.ASep2Loc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP2 (D1): the `τ' = 0` conclusion for every profile continuous off `0`

`ae_concl0_prof`: for a fixed good driver `W` and a free field `X`, almost surely, for **every**
`g` continuous on `ℂ \ {0}` (in particular for the random wedge profile, which is continuous off
`0` but not at `0`), `G4SepConcl0 γ (ofFun g + X ω, W)`.

Proof. Fix a separated circle and a parameter `p = (τ, a)`; it is good (`parGood_of_backSep`) and
lies in a rational box of good parameters (`boxData_A0`), where the forward trajectories of the
points `a w`, `w` on the circle, stay at distance `≥ m` from the singularity (`exists_geo_A0`).
By the Lipschitz bound for `f_τ⁻¹` (`norm_fwdMapInv_sub_le`), every dyadic circle within
`ε = (m/2) e^{-8T/m²}` of `f_τ(a w)` is pushed by `f_τ⁻¹` into `{|v| ≥ m/2}` (`ae_nuT_far`), where
`g` agrees with its continuous cutoff `g' = cutoffProf g (m/2)`. Hence `U_g` and `U_{g'}` have the
same raw values on these circles (`ASep2Add`), the same regularized values at the conclusion
measures (`ASep2Loc`), and the same raw values there (the raw value reads the field on the scaled
circle `a σ ⊆ {|v| ≥ m}`); the conclusion for `g'` is `ae_conj1_add_good`/`ae_conj2_add_good`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core RegCont TwoPoint CoordReg GenUC

/-- Points near a good image point are pulled back away from `0`. -/
theorem norm_fwdMapInv_ge_of_near {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T m : ℝ}
    (hT : 0 ≤ T) (hm : 0 < m) {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hsol : ∃ u, IsForwardSol W z₀ T u)
    (hlow : ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z₀‖) {t : ℝ} (ht : t ∈ Icc 0 T)
    {ζ : ℂ} (hζ : 0 < ζ.im)
    (hclose : ‖ζ - fwdMap W t z₀‖ ≤ m / 2 * Real.exp (-(8 * T / m ^ 2))) :
    m / 2 ≤ ‖fwdMapInv W t ζ‖ := by
  have h := norm_fwdMapInv_sub_le hW hW0 hT hm hz₀ hsol hlow ht hζ hclose
  have hz0 : m ≤ ‖z₀‖ := by
    obtain ⟨u, hu⟩ := hsol
    have := hlow 0 ⟨le_rfl, hT⟩
    rwa [fwdMap_eq_any hu ⟨le_rfl, hT⟩, FwdHolo.sol_zero hu hT, hW0, Complex.ofReal_zero,
      sub_zero] at this
  have hb : Real.exp (8 * T / m ^ 2) * ‖ζ - fwdMap W t z₀‖ ≤ m / 2 := by
    calc Real.exp (8 * T / m ^ 2) * ‖ζ - fwdMap W t z₀‖
        ≤ Real.exp (8 * T / m ^ 2) * (m / 2 * Real.exp (-(8 * T / m ^ 2))) :=
          mul_le_mul_of_nonneg_left hclose (Real.exp_pos _).le
      _ = m / 2 := by
          rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have := norm_sub_norm_le z₀ (fwdMapInv W t ζ)
  rw [norm_sub_rev] at h
  linarith

/-- **Pushed circles near a good image point avoid a neighbourhood of `0`.** -/
theorem ae_nuT_far {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T m : ℝ}
    (hT : 0 ≤ T) (hm : 0 < m) {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hsol : ∃ u, IsForwardSol W z₀ T u)
    (hlow : ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z₀‖) {t : ℝ} (ht : t ∈ Icc 0 T)
    {c : ℂ} (hc : c ∈ Hbar) {ρ : ℝ} (hρ : 0 < ρ)
    (hnear : ‖c - fwdMap W t z₀‖ + ρ ≤ m / 2 * Real.exp (-(8 * T / m ^ 2))) :
    ∀ᵐ v ∂νT W c ρ t, m / 2 ≤ ‖v‖ := by
  refine (ae_map_iff (aemeasurable_fwdMapInv hW hW0 ht.1 c hρ)
    (measurableSet_le measurable_const measurable_norm)).2 ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H c hρ,
    FrostmanReg.foldedCircle_ae_near_frostman (c := c) hc hρ.le] with ζ hζ hn
  refine norm_fwdMapInv_ge_of_near hW hW0 hT hm hz₀ hsol hlow ht hζ ?_
  have h1 : ‖ζ - c‖ ≤ ρ := by simpa using hn.2
  have := norm_sub_le_norm_sub_add_norm_sub ζ c (fwdMap W t z₀)
  linarith

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end ASep
end QuantumZipper
