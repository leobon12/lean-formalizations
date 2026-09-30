import QuantumZipper.Proofs.Thm18.A1RSTime
import QuantumZipper.Proofs.RS.HullBasics

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (4): the mass bound of the pushed side circles, uniformly on parameter boxes

`a1rMassStmt_holds` (A1RMass.lean) gives, for each fixed `(t, d, s)`, `μ_t{Im ≤ δ} ≤ C δ^{1/2}`
for the pushed side circle `μ_t = (f_t ∘ ψ)_* fc(d, s)`, with `C` depending on `(t, d, s)`. The
Kolmogorov family behind `A1RFSmearContStmt` needs the constant uniform on boxes
`t ∈ (0, T]`, `‖d‖ ≤ R₀`, `s ∈ [s₀, R₀]`. The same proof gives it:

* `im_sidePush_ge_unif`: the Schwarz–Pick lower bound `Im Φ_t(u) ≥ c Im u` on `‖u‖ ≤ R`
  (`A1R.im_ge_of_mapsTo_H`; Ahlfors, *Complex Analysis*, 3rd ed., §4.3.4) holds with
  `c = Im Φ_T(i) / (R+1)²` for all `t ≤ T`, because `t ↦ Im f_t(z)` is nonincreasing
  (`RS.im_fwdMap_le_of_le`);
* `a1rMu_strip_le_unif`: hence `μ_t{Im ≤ δ} ≤ C δ^{1/2}` uniformly on the box (the strip bound
  `A1R.foldedCircle_strip_le` in the side chart).

Own elementary bookkeeping (the argument of `a1rMassStmt_holds` with the constants tracked).
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- **Uniform Schwarz–Pick lower bound for the pushing maps.** -/
theorem im_sidePush_ge_unif {W : ℝ → ℝ} (hG : G1zDrvGood W) {T : ℝ} (hT : 0 < T) (left : Bool)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Ioc (0 : ℝ) T, ∀ u ∈ H, ‖u‖ ≤ R →
      c * u.im ≤ (fwdMap W t (g1zSideMap left W u)).im := by
  have hIH : I ∈ H := by show 0 < I.im; simp
  have hmemT := sideMap_mem_compl_fwdHull hG hT.le left hIH
  have hposT : 0 < (fwdMap W T (g1zSideMap left W I)).im :=
    (RS.im_fwdMap_le_of_le hG.1 hT.le le_rfl hmemT).2
  have hR1 : 0 < R + 1 := by linarith
  refine ⟨(fwdMap W T (g1zSideMap left W I)).im / (R + 1) ^ 2, by positivity, ?_⟩
  intro t ht u hu huR
  obtain ⟨hdiff, hmaps, -⟩ := A1R.sidePush_props hG ht.1 left
  have h1 := A1R.im_ge_of_mapsTo_H hdiff hmaps hu
  have hmono : (fwdMap W T (g1zSideMap left W I)).im ≤ (fwdMap W t (g1zSideMap left W I)).im :=
    (RS.im_fwdMap_le_of_le hG.1 ht.1.le ht.2 hmemT).1
  have hu' : 0 < u.im := hu
  have huI : ‖u + I‖ ≤ R + 1 := by
    calc ‖u + I‖ ≤ ‖u‖ + ‖I‖ := norm_add_le _ _
      _ ≤ R + 1 := by rw [Complex.norm_I]; linarith
  have huI0 : 0 < ‖u + I‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := congrArg Complex.im h
    simp only [add_im, I_im, zero_im] at this
    linarith
  refine le_trans ?_ h1
  have hsq : ‖u + I‖ ^ 2 ≤ (R + 1) ^ 2 := pow_le_pow_left₀ huI0.le huI 2
  rw [div_mul_eq_mul_div]
  calc (fwdMap W T (g1zSideMap left W I)).im * u.im / (R + 1) ^ 2
      ≤ (fwdMap W t (g1zSideMap left W I)).im * u.im / (R + 1) ^ 2 := by
        gcongr
    _ ≤ (fwdMap W t (g1zSideMap left W I)).im * u.im / ‖u + I‖ ^ 2 := by
        apply div_le_div_of_nonneg_left _ (by positivity) hsq
        exact mul_nonneg (hposT.le.trans hmono) hu'.le

/-- **Uniform mass bound of the pushed side circles near `ℝ`.** -/
theorem a1rMu_strip_le_unif {W : ℝ → ℝ} (hG : G1zDrvGood W) {T : ℝ} (hT : 0 < T) (left : Bool)
    {R₀ s₀ : ℝ} (hs₀ : 0 < s₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) T, ∀ d : ℂ, ‖d‖ ≤ R₀ → ∀ s : ℝ, s₀ ≤ s → s ≤ R₀ →
      ∀ δ : ℝ, 0 < δ → (a1rMu W t left d s).real {z : ℂ | z.im ≤ δ} ≤ C * δ ^ (1 / 2 : ℝ) := by
  obtain ⟨c, hc0, hc⟩ := im_sidePush_ge_unif hG hT left (2 * max R₀ 0) (by positivity)
  refine ⟨3 / 2 * Real.sqrt (1 / (c * s₀)), by positivity, ?_⟩
  intro t ht d hd s hs hsR δ hδ
  have hs0 : 0 < s := hs₀.trans_le hs
  obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hG ht.1 left
  have hmapeq : a1rMu W t left d s = (foldedCircle d s).map g := by
    unfold a1rMu
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs0] with u hu
    exact hEq hu
  have hS : MeasurableSet {z : ℂ | z.im ≤ δ} :=
    measurableSet_le Complex.continuous_im.measurable measurable_const
  have hle : a1rMu W t left d s {z : ℂ | z.im ≤ δ} ≤
      ENNReal.ofReal (3 / 2 * Real.sqrt (δ / c / s)) := by
    rw [hmapeq, Measure.map_apply hgm hS]
    refine le_trans (measure_mono_ae ?_) (A1R.foldedCircle_strip_le d hs0 (by positivity))
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs0,
      TwoPoint.foldedCircle_ae_norm_le d hs0.le] with u hu hun hmem
    have hu' : 0 < u.im := hu
    have h1 : (fwdMap W t (g1zSideMap left W u)).im ≤ δ := by
      have : g u = fwdMap W t (g1zSideMap left W u) := (hEq hu).symm
      simpa [this] using hmem
    have hun' : ‖u‖ ≤ 2 * max R₀ 0 := by
      have := le_max_left R₀ 0
      linarith
    have h2 := hc t ht u hu hun'
    show |u.im| ≤ δ / c
    rw [abs_of_pos hu', le_div_iff₀ hc0]
    linarith
  have hreal : (a1rMu W t left d s).real {z : ℂ | z.im ≤ δ} ≤
      3 / 2 * Real.sqrt (δ / c / s) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hle
  refine hreal.trans ?_
  have hsq : Real.sqrt (δ / c / s) ≤ Real.sqrt (1 / (c * s₀)) * δ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_div, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left hδ.le (by positivity)
      (mul_le_mul_of_nonneg_left hs hc0.le)
  nlinarith

end A1RS
end R18
end QuantumZipper
