import QuantumZipper.Proofs.Thm18.A1RNodes
import QuantumZipper.Proofs.Thm18.A1RPick

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1R (mass): the mass node `A1RMassStmt` is proved

For a good driver, the pushing map `Φ = f_t ∘ ψ` (`ψ` the side map) is a holomorphic map of `ℍ`
into `ℍ`. By the Schwarz–Pick lower bound (`A1R.im_ge_of_mapsTo_H`; Ahlfors, *Complex
Analysis*, 3rd ed., §4.3.4), `Im Φ(u) ≥ c · Im u` on the bounded support of the folded circle,
so `Φ⁻¹{Im ≤ δ}` lies in the strip `{|Im u| ≤ δ/c}`, whose circle measure is
`≤ (3/2) √(δ/(c s))` (`RTBeur.circleUnif_strip_le`). Hence `β = 1/2`.

No Beurling estimate is needed: the strip bound in the side chart is enough. Own elementary
argument.
-/

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

namespace A1R

/-- The pushing map of the side circles: holomorphic from `ℍ` into `ℍ`, and equal on `ℍ` to a
measurable map. -/
theorem sidePush_props {W : ℝ → ℝ} (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) (left : Bool) :
    DifferentiableOn ℂ (fun w => fwdMap W t (g1zSideMap left W w)) H ∧
      MapsTo (fun w => fwdMap W t (g1zSideMap left W w)) H H ∧
      ∃ g : ℂ → ℂ, Measurable g ∧ EqOn (fun w => fwdMap W t (g1zSideMap left W w)) g H := by
  classical
  obtain ⟨hWc, hW0, hWm, hη, hK⟩ := hG
  set D := sideDom (trace W) left with hD
  have hU := G1ZA1a.isNormalizedUniformizer_sideDom hη left
  obtain ⟨hψd, -, hψm, hmaps⟩ := G1.invFunOn_props (G1ZA1a.isOpen_sideDom hη left) hU
  set U := H \ fwdHull W t with hUdef
  have hψU : MapsTo (g1zSideMap left W) H U := by
    intro w hw
    have hzD : g1zSideMap left W w ∈ D := hmaps hw
    refine ⟨G1ZA1a.sideDom_subset_H _ left hzD, ?_⟩
    rw [hK t ht.le]
    rintro ⟨u, hu, hzu⟩
    have hnot : g1zSideMap left W w ∉ trace W '' Ici (0 : ℝ) := by
      cases left
      · exact hzD.1.2
      · exact hzD.1.2
    exact hnot ⟨u, le_of_lt hu.1, hzu⟩
  have hfd := FwdHolo.differentiableOn_fwdMap hWc ht.le
  refine ⟨hfd.comp hψd hψU, fun w hw => FwdHolo.mapsTo_fwdMap hWc ht.le (hψU hw),
    (U.piecewise (fwdMap W t) fun _ => (0 : ℂ)) ∘ g1zSideMap left W, ?_, fun w hw => ?_⟩
  · exact (ContinuousOn.measurable_piecewise hfd.continuousOn continuousOn_const
      (FwdHolo.isOpen_compl_fwdHull hWc ht.le).measurableSet).comp hψm
  · show fwdMap W t (g1zSideMap left W w) =
      U.piecewise (fwdMap W t) (fun _ => (0 : ℂ)) (g1zSideMap left W w)
    rw [Set.piecewise_eq_of_mem _ _ _ (hψU hw)]

/-- The folded circle measure of a horizontal strip. -/
theorem foldedCircle_strip_le (d : ℂ) {s ε : ℝ} (hs : 0 < s) (hε : 0 ≤ ε) :
    foldedCircle d s {u : ℂ | |u.im| ≤ ε} ≤ ENNReal.ofReal (3 / 2 * Real.sqrt (ε / s)) := by
  have hG : MeasurableSet {u : ℂ | |u.im| ≤ ε} :=
    measurableSet_le (Complex.continuous_im.abs.measurable) measurable_const
  unfold foldedCircle
  rw [Measure.map_apply RTBeur.measurable_foldH_rt hG]
  have e : foldH ⁻¹' {u : ℂ | |u.im| ≤ ε} = {u : ℂ | |u.im| ≤ ε} := by
    ext v
    simp only [mem_preimage, mem_setOf_eq, TwoPoint.im_foldH, abs_abs]
  rw [e]
  exact RTBeur.circleUnif_strip_le d hs hε

end A1R

/-- **The mass node holds.** -/
theorem a1rMassStmt_holds : A1RMassStmt := by
  intro W hG t ht left d hd s hs
  obtain ⟨hdiff, hmaps, g, hgm, hEq⟩ := A1R.sidePush_props hG ht left
  set Φ : ℂ → ℂ := fun w => fwdMap W t (g1zSideMap left W w) with hΦ
  set R := ‖d‖ + s with hR
  have hIH : I ∈ H := by show 0 < I.im; simp
  have hp : 0 < (Φ I).im := hmaps hIH
  have hR1 : 0 < R + 1 := by positivity
  set c := (Φ I).im / (R + 1) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hlow : ∀ u ∈ H, ‖u‖ ≤ R → c * u.im ≤ (Φ u).im := by
    intro u hu huR
    have h1 := A1R.im_ge_of_mapsTo_H hdiff hmaps hu
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
    rw [hc, div_mul_eq_mul_div, mul_comm ((Φ I).im) u.im]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ huI0.le huI 2)
  refine ⟨3 / 2 * Real.sqrt (1 / (c * s)), 1 / 2, by norm_num, fun δ hδ hδ1 => ?_⟩
  have hmapeq : a1rMu W t left d s = (foldedCircle d s).map g := by
    unfold a1rMu
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with u hu
    exact hEq hu
  have hS : MeasurableSet {z : ℂ | z.im ≤ δ} :=
    measurableSet_le Complex.continuous_im.measurable measurable_const
  have hle : a1rMu W t left d s {z : ℂ | z.im ≤ δ} ≤
      ENNReal.ofReal (3 / 2 * Real.sqrt (δ / c / s)) := by
    rw [hmapeq, Measure.map_apply hgm hS]
    refine le_trans (measure_mono_ae ?_) (A1R.foldedCircle_strip_le d hs (by positivity))
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs,
      TwoPoint.foldedCircle_ae_norm_le d hs.le] with u hu hun hmem
    have hu' : 0 < u.im := hu
    have h1 : (Φ u).im ≤ δ := by
      have : g u = Φ u := (hEq hu).symm
      simpa [this] using hmem
    have h2 := hlow u hu hun
    show |u.im| ≤ δ / c
    rw [abs_of_pos hu', le_div_iff₀ hc0]
    linarith
  have hreal : (a1rMu W t left d s).real {z : ℂ | z.im ≤ δ} ≤
      3 / 2 * Real.sqrt (δ / c / s) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hle
  refine hreal.trans (le_of_eq ?_)
  rw [show δ / c / s = 1 / (c * s) * δ by field_simp, Real.sqrt_mul (by positivity),
    Real.sqrt_eq_rpow δ]
  ring

end R18
end QuantumZipper
