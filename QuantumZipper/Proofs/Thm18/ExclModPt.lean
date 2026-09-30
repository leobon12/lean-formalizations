import QuantumZipper.Proofs.Thm18.ExactClRTX
import QuantumZipper.Proofs.Zipper.JointModKolm
import QuantumZipper.Proofs.Zipper.UnifUCE2Mix
import QuantumZipper.Proofs.Zipper.UnifUC1RadBasic
import QuantumZipper.Proofs.Zipper.UnifUCE2Large

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# EXCL-2 (1): per-point and mixture energy moduli for circle-smoothed pushed families

Building blocks for the `GenFam` energy moduli of the round-trip (RTX) family
`μ_{p,ρ} = (f_τ⁻¹)_* (ν_p ⋆ fc(·, ρ))`, `ν_p = σ.map w_p` (handoff/G4-CORE.md §8, D72):

* `goodM_νT`: the pushed circle `νT W z ρ u = (f_u⁻¹)_* fc(z, ρ)` is `GoodM` with constants
  uniform in `u ∈ [0,T]`, `ρ ≥ r₀`, `‖z‖ + ρ ≤ R`;
* `energy_νT_pair_le`: joint time/space/radius modulus of `νT`: the triangle inequality for the
  Neumann energy through `νT W w r s'`, with the JointMod time modulus
  `RegUnif.abs_kernelCov2_νT_time_unif` and space modulus `RegUnif.abs_kernelCov2_νT_space_unif`;
* `energy_mix_νT_le`: the same bound for the mixtures `(f_s⁻¹)_* ((A.map w) ⋆ fc(·, ρ))` and
  `(f_{s'}⁻¹)_* ((A.map w') ⋆ fc(·, ρ'))` over one base `A`, with `Λ ≥ ‖w − w'‖` `A`-a.e.
  (`RegUnif.abs_kernelCov2_mix_le_two`). This covers the radius modulus (`w = w'`, `s = s'`) and
  the parameter modulus at radii `≥ r₀` of any family of this form, in particular of the RTX family
  once the centre modulus `‖w_p − w_{p'}‖` is known.

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 (through the JointMod moduli);
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1. The combination is own elementary
bookkeeping (as the D33 E2 argument, `UnifUCE2Large`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

open RegCont RegUnif TwoPoint B2

variable {W : ℝ → ℝ}

/-- The pushed circle `νT W z ρ u` is `GoodM`, uniformly in `u ∈ [0,T]`, `ρ ≥ r₀`,
`‖z‖ + ρ ≤ R`. -/
theorem goodM_νT (hW : Continuous W) (hW0 : W 0 = 0) {T M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {z : ℂ}
    {r₀ ρ R : ℝ} (hr₀ : 0 < r₀) (hρ : r₀ ≤ ρ) (hzR : ‖z‖ + ρ ≤ R) :
    GoodM (νT W z ρ u) (1 / 3) (frostC T r₀ R) (revBound (2 * M) T R) := by
  obtain ⟨e, g⟩ := goodM_pushed_circle hW hW0 hM hu hr₀ hρ hzR
  rw [e]; exact g

/-- **Joint time/space/radius modulus of the pushed circles.** -/
theorem energy_νT_pair_le (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R a CH : ℝ}
    (hr₀ : 0 < r₀) (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) (ha : 0 < a) (ha1 : a ≤ 1)
    (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a)
    {w w' : ℂ} {r r' : ℝ} (hr : r₀ ≤ r) (hr' : r₀ ≤ r') (hwR : ‖w‖ + r ≤ R)
    (hwR' : ‖w'‖ + r' ≤ R) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (hs' : s' ∈ Icc (0 : ℝ) T) :
    kernelCov2 neumannH (νT W w r s, νT W w' r' s') (νT W w r s, νT W w' r' s') ≤
      2 * (timeK M T r₀ R CH * |s - s'| ^ (a / 12)) +
        2 * (spaceK M T r₀ R * (‖w - w'‖ + |r - r'|) ^ (1 / 12 : ℝ)) := by
  have g1 := goodM_νT hW hW0 hM hs hr₀ hr hwR
  have g2 := goodM_νT hW hW0 hM hs' hr₀ hr hwR
  have g3 := goodM_νT hW hW0 hM hs' hr₀ hr' hwR'
  have := g1.prob; have := g2.prob; have := g3.prob
  have t := kernelCov2_self_triangle (g1.admissible (by norm_num))
    (g2.admissible (by norm_num)) (g3.admissible (by norm_num))
    (by rw [measure_univ, measure_univ]) (by rw [measure_univ, measure_univ])
  have e1 := (le_abs_self _).trans
    (abs_kernelCov2_νT_time_unif hW hW0 hr₀ hM ha ha1 hCH hH hr hwR hs hs')
  have e2 := (le_abs_self _).trans
    (abs_kernelCov2_νT_space_unif hW hW0 hr₀ hM (β := 1 / 12) (by norm_num) le_rfl hs' hr hr'
      hwR hwR')
  linarith

/-- **Mixture modulus.** For two circle-smoothed pushed mixtures over the same base `A`, with
centre maps `w, w'` (`‖w − w'‖ ≤ Λ` `A`-a.e.), radii `ρ, ρ' ≥ r₀` and times `s, s' ∈ [0,T]`. -/
theorem energy_mix_νT_le (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R a CH : ℝ}
    (hr₀ : 0 < r₀) (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) (ha : 0 < a) (ha1 : a ≤ 1)
    (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a)
    {A : Measure ℂ} [IsProbabilityMeasure A] {w w' : ℂ → ℂ} (hw : Measurable w)
    (hw' : Measurable w') {ρ ρ' : ℝ} (hρ : r₀ ≤ ρ) (hρ' : r₀ ≤ ρ')
    (hwR : ∀ᵐ z ∂A, ‖w z‖ + ρ ≤ R ∧ ‖w' z‖ + ρ' ≤ R) {Λ : ℝ}
    (hΛ : ∀ᵐ z ∂A, ‖w z - w' z‖ ≤ Λ) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (hs' : s' ∈ Icc (0 : ℝ) T) :
    |kernelCov2 neumannH ((bindFc (A.map w) ρ).map (fwdMapInv W s),
        (bindFc (A.map w') ρ').map (fwdMapInv W s'))
      ((bindFc (A.map w) ρ).map (fwdMapInv W s),
        (bindFc (A.map w') ρ').map (fwdMapInv W s'))| ≤
      2 * (timeK M T r₀ R CH * |s - s'| ^ (a / 12)) +
        2 * (spaceK M T r₀ R * (Λ + |ρ - ρ'|) ^ (1 / 12 : ℝ)) := by
  have hT : 0 ≤ T := hs.1.trans hs.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hρ0 : 0 < ρ := hr₀.trans_le hρ
  have hρ0' : 0 < ρ' := hr₀.trans_le hρ'
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW s) hs.1
  have hRm' := TwoPoint.measurable_revMap (continuous_vrev hW s') hs'.1
  have hmeas : MeasurableSet {x : ℂ | ‖x‖ ≤ R} :=
    measurableSet_le measurable_norm measurable_const
  have hbd : ∀ᵐ x ∂(A.map w), ‖x‖ ≤ R :=
    (ae_map_iff hw.aemeasurable hmeas).2 (hwR.mono fun z hz => by linarith [hz.1])
  have hbd' : ∀ᵐ x ∂(A.map w'), ‖x‖ ≤ R :=
    (ae_map_iff hw'.aemeasurable hmeas).2 (hwR.mono fun z hz => by linarith [hz.2])
  have e : (bindFc (A.map w) ρ).map (fwdMapInv W s) =
      (bindFc (A.map w) ρ).map (revMap (vrev W s) s) := by
    refine Measure.map_congr ?_
    filter_upwards [CoordReg.bind_fc_mem_H_norm _ hρ0 hbd] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hs.1 hx.1
  have e' : (bindFc (A.map w') ρ').map (fwdMapInv W s') =
      (bindFc (A.map w') ρ').map (revMap (vrev W s') s') := by
    refine Measure.map_congr ?_
    filter_upwards [CoordReg.bind_fc_mem_H_norm _ hρ0' hbd'] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hs'.1 hx.1
  have hK1 := timeK_nonneg_E2 (R := R) hM0 hT hr₀ hCH
  have hK2 : 0 ≤ spaceK M T r₀ R := by
    have := spaceConst_nonneg (R := R) hM0 hT hr₀
    have := potC_nonneg (R := R) hM0 hT hr₀
    unfold spaceK; positivity
  have hΛ0 : 0 ≤ Λ + |ρ - ρ'| := by
    obtain ⟨z, hz⟩ := hΛ.exists
    linarith [norm_nonneg (w z - w' z), abs_nonneg (ρ - ρ')]
  rw [e, e']
  refine abs_kernelCov2_mix_le_two hw hw' hRm hRm' (α := 1 / 3) (C := frostC T r₀ R)
    (B := revBound (2 * M) T R) (by norm_num) (frostC_nonneg hT hr₀)
    (revBound_nonneg (by linarith) hT) (by positivity) ?_ ?_
  · filter_upwards [hwR] with z hz
    exact ⟨(goodM_pushed_circle hW hW0 hM hs hr₀ hρ hz.1).2,
      (goodM_pushed_circle hW hW0 hM hs' hr₀ hρ' hz.2).2⟩
  · filter_upwards [hwR, hΛ] with z hz hzΛ
    rw [← (goodM_pushed_circle hW hW0 hM hs hr₀ hρ hz.1).1,
      ← (goodM_pushed_circle hW hW0 hM hs' hr₀ hρ' hz.2).1]
    refine (energy_νT_pair_le hW hW0 hr₀ hM ha ha1 hCH hH hρ hρ' hz.1 hz.2 hs hs').trans ?_
    have hp := Real.rpow_le_rpow (by positivity) (show ‖w z - w' z‖ + |ρ - ρ'| ≤ Λ + |ρ - ρ'|
      by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 12)
    have := mul_le_mul_of_nonneg_left hp hK2
    linarith

end G4Core
end Thm18Asm
end QuantumZipper
