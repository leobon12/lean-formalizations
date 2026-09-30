import QuantumZipper.Proofs.Thm18.G1RegLogDeriv
import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Zipper.RegContDet
import QuantumZipper.Proofs.Zipper.UnzipInvariance
import QuantumZipper.Proofs.Zipper.B3dDet

/-!
# D29 (wedge unzipping), part 1: the B3(d) field identity under canonical rescaling

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.6 (a quantum surface is
an equivalence class under `h ↦ h ∘ ψ + Q log|ψ'|`; (1.8) fixes the scaling freedom
`h ↦ h(a·) + Q log a`) and §5.1 (pp. 60–62, Brownian scaling of the driver). The paper uses,
without comment, that unzipping commutes with canonical rescaling: the field unzipped in capacity
time `s` from the canonicalized configuration `canonConfig γ (y, W)` is the rescaling by
`a = scaleParam γ y` of the field unzipped from `(y, W)` in time `a² s`.

At the level of the raw pairings this is the chain rule for the two factorizations
`(a·) ∘ f^{W_a}_s⁻¹ = f^W_{a²s}⁻¹ ∘ (a·)` on `ℍ` (`RS.fwdMapInv_scale`, Loewner scaling). At the
regularized level (`RegEq`, all `avgReg` agree) it needs two regularity properties, which we keep
as explicit hypotheses (they are the D29 core statements for the wedge, see
`handoff/WEDGE-UNZIP.md`):

* `hsc` — **scale consistency** of the regularization of `y` at the images of folded circles
  under the unzipping map (`G1.ScaleConsistentAt`; it follows from a continuum limit of the
  circle smoothing, `G1.scaleConsistentAt_of_continuum`);
* `hexact` — **RC3** for the unzipped field at time `a² s`: its folded-circle values are its
  regularized ones.

The integrability of `log|ψ'|` on folded circles is deterministic
(`G1.integrable_log_norm_deriv_foldedCircle_of_injOn`, Koebe distortion).

Main results:
* `regEq_coordChange_rescale_of_scale`: abstract form, for any injective holomorphic `φ, ψ` on
  `ℍ` with `a φ(w) = ψ(a w)`;
* `regEq_unzippedField_canonConfig`: the B3(d) field identity of `F2.UnscaledB3dStmt`.

Own elementary bookkeeping (chain rule for dilations, `Measure.map` of folded circles), the same
pattern as `G1.regEq_coordChange_comp_mul` and `G1Meas.coordChange_rescale_apply`.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology

namespace QuantumZipper
namespace WedgeUnzip

open Thm18Asm

/-! ## Measurable modification on `ℍ` -/

open scoped Classical in
/-- `φ` on `ℍ`, `0` off `ℍ`: a measurable modification of a map continuous on `ℍ`. -/
def modH (φ : ℂ → ℂ) : ℂ → ℂ := H.piecewise φ fun _ => 0

theorem modH_eqOn (φ : ℂ → ℂ) : EqOn (modH φ) φ H := fun _ hw => by
  classical
  simp only [modH]
  exact Set.piecewise_eq_of_mem _ _ _ hw

theorem measurable_modH {φ : ℂ → ℂ} (hφ : ContinuousOn φ H) : Measurable (modH φ) := by
  classical
  unfold modH
  convert hφ.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) isOpen_H.measurableSet

theorem deriv_modH {φ : ℂ → ℂ} {w : ℂ} (hw : w ∈ H) : deriv (modH φ) w = deriv φ w :=
  Filter.EventuallyEq.deriv_eq <| Filter.eventually_of_mem (isOpen_H.mem_nhds hw) fun _ hz =>
    modH_eqOn φ hz

theorem differentiableOn_modH {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ H) :
    DifferentiableOn ℂ (modH φ) H :=
  hφ.congr fun _ hz => modH_eqOn φ hz

theorem injOn_modH {φ : ℂ → ℂ} (hφ : InjOn φ H) : InjOn (modH φ) H := fun a ha b hb h => by
  rw [modH_eqOn φ ha, modH_eqOn φ hb] at h; exact hφ ha hb h

/-- Folded circles do not see the modification. -/
theorem fc_map_modH (φ : ℂ → ℂ) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    (foldedCircle d r).map (modH φ) = (foldedCircle d r).map φ :=
  Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun _ hz => modH_eqOn φ hz)

/-! ## Raw values -/

theorem integral_log_deriv_const_mul' {ψ : ℂ → ℂ} {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (hd : ∀ᵐ z ∂μ, deriv ψ z ≠ 0)
    (hi : Integrable (fun z => Real.log ‖deriv ψ z‖) μ) :
    ∫ z, Real.log ‖deriv (fun z => (s : ℂ) * ψ z) z‖ ∂μ =
      Real.log s + ∫ z, Real.log ‖deriv ψ z‖ ∂μ := by
  have e : (fun z => Real.log ‖deriv (fun z => (s : ℂ) * ψ z) z‖) =ᵐ[μ]
      fun z => Real.log s + Real.log ‖deriv ψ z‖ := by
    filter_upwards [hd] with z hz
    rw [deriv_const_mul_field', norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le,
      Real.log_mul hs.ne' (norm_ne_zero_iff.2 hz)]
  rw [integral_congr_ae e, integral_add (integrable_const _) hi, integral_const, probReal_univ,
    one_smul]

/-- Raw values of a pulled-back rescaled field, given scale consistency (same computation as
`G1Meas.coordChange_rescale_apply`). -/
theorem coordChange_rescale_apply' (y : FieldSample) {φ : ℂ → ℂ} (hφ : Measurable φ) (Q : ℝ)
    {a : ℝ} (ha : 0 < a) (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (hsc : G1.ScaleConsistentAt y Q a (μ.map φ)) (hd : ∀ᵐ z ∂μ, deriv φ z ≠ 0)
    (hi : Integrable (fun z => Real.log ‖deriv φ z‖) μ) :
    coordChange (rescale y Q a) φ Q μ = coordChange y (fun z => (a : ℂ) * φ z) Q μ := by
  unfold coordChange
  unfold G1.ScaleConsistentAt at hsc
  rw [hsc, Measure.map_map (measurable_const_mul _) hφ, integral_log_deriv_const_mul' ha hd hi]
  have h1 : (μ.map φ).real univ = 1 := by
    rw [measureReal_def, Measure.map_apply hφ MeasurableSet.univ, preimage_univ, measure_univ,
      ENNReal.toReal_one]
  rw [h1]
  show _ = evalReg y (μ.map ((fun z : ℂ => (a : ℂ) * z) ∘ φ)) + _
  ring

/-! ## The abstract identity -/

/-- **Rescaling commutes with pulling back (raw values on folded circles).** Let `φ, ψ` be injective
and holomorphic on `ℍ` with nonvanishing derivative and `a φ(w) = ψ(a w)` on `ℍ`. If the
regularization of `y` is scale consistent (factor `a`) at the images `φ_* fc(d, r)` of all
folded circles, and the folded-circle values of `coordChange y ψ Q` are its regularized ones,
then `coordChange (rescale y Q a) φ Q` and `rescale (coordChange y ψ Q) Q a` agree on every
folded circle (hence are `RegEq`, and one is good iff the other is). -/
theorem coordChange_rescale_fc_of_scale (y : FieldSample) (Q : ℝ) {φ ψ : ℂ → ℂ} {a : ℝ}
    (ha : 0 < a)
    (hφd : DifferentiableOn ℂ φ H) (hφi : InjOn φ H) (hφ0 : ∀ w ∈ H, deriv φ w ≠ 0)
    (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0)
    (hscale : ∀ w ∈ H, (a : ℂ) * φ w = ψ ((a : ℂ) * w))
    (hsc : ∀ (d : ℂ) (r : ℝ), 0 < r → G1.ScaleConsistentAt y Q a ((foldedCircle d r).map φ))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (coordChange y ψ Q) (foldedCircle d r) = coordChange y ψ Q (foldedCircle d r)) :
    ∀ (d : ℂ) (r : ℝ), 0 < r → coordChange (rescale y Q a) φ Q (foldedCircle d r) =
      rescale (coordChange y ψ Q) Q a (foldedCircle d r) := by
  -- measurable modifications
  set φ' := modH φ
  set ψ' := modH ψ
  have hφm : Measurable φ' := measurable_modH hφd.continuousOn
  have hψm : Measurable ψ' := measurable_modH hψd.continuousOn
  have hφ'd : DifferentiableOn ℂ φ' H := differentiableOn_modH hφd
  have hψ'd : DifferentiableOn ℂ ψ' H := differentiableOn_modH hψd
  have hψ'0 : ∀ w ∈ H, deriv ψ' w ≠ 0 := fun w hw => by rw [deriv_modH hw]; exact hψ0 w hw
  -- the two pullbacks by `ψ`, `ψ'` agree on folded circles, hence everywhere after regularizing
  have eψ : ∀ d : ℂ, ∀ r > 0, coordChange y ψ' Q (foldedCircle d r) =
      coordChange y ψ Q (foldedCircle d r) := fun d r hr =>
    UnzipInvariance.coordChange_congr_of_eqOn (modH_eqOn ψ)
      (ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H d hr)) y Q
  have eφ : ∀ d : ℂ, ∀ r > 0, coordChange (rescale y Q a) φ' Q (foldedCircle d r) =
      coordChange (rescale y Q a) φ Q (foldedCircle d r) := fun d r hr =>
    UnzipInvariance.coordChange_congr_of_eqOn (modH_eqOn φ)
      (ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H d hr)) _ Q
  have key : ∀ d : ℂ, ∀ r > 0, coordChange (rescale y Q a) φ Q (foldedCircle d r) =
      rescale (coordChange y ψ Q) Q a (foldedCircle d r) := by
    intro d r hr
    have hbr : 0 < a * r := mul_pos ha hr
    have hH := CircleFubini.foldH_mem_Hbar' ((a : ℂ) * d)
    -- right side
    have hintψ : Integrable (fun z => Real.log ‖deriv ψ' z‖)
        (foldedCircle ((a : ℂ) * d) (a * r)) :=
      G1.integrable_log_norm_deriv_foldedCircle_of_injOn hψ'd (injOn_modH hψi) _ hbr
    have hR : rescale (coordChange y ψ Q) Q a (foldedCircle d r) =
        coordChange y (fun w => ψ' ((a : ℂ) * w)) Q (foldedCircle d r) := by
      rw [G1.rescale_fc_apply _ Q ha d r, hexact _ hH _ hbr, WedgeTK.fc_foldH_eq,
        ← eψ _ _ hbr, G1.coordChange_comp_mul_fc y Q hψ'd hψ'0 hψm ha d hr hintψ]
    -- left side
    have hintφ : Integrable (fun z => Real.log ‖deriv φ' z‖) (foldedCircle d r) :=
      G1.integrable_log_norm_deriv_foldedCircle_of_injOn hφ'd (injOn_modH hφi) _ hr
    have hdφ : ∀ᵐ z ∂foldedCircle d r, deriv φ' z ≠ 0 :=
      (TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz => by
        rw [deriv_modH hz]; exact hφ0 z hz
    have hscφ : G1.ScaleConsistentAt y Q a ((foldedCircle d r).map φ') := by
      rw [fc_map_modH φ d hr]; exact hsc d r hr
    have hL : coordChange (rescale y Q a) φ Q (foldedCircle d r) =
        coordChange y (fun z => (a : ℂ) * φ' z) Q (foldedCircle d r) := by
      rw [← eφ _ _ hr, coordChange_rescale_apply' y hφm Q ha _ hscφ hdφ hintφ]
    rw [hL, hR]
    refine UnzipInvariance.coordChange_congr_of_eqOn (fun w hw => ?_)
      (ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H d hr)) y Q
    have haw : (a : ℂ) * w ∈ H := by
      show 0 < ((a : ℂ) * w).im
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos ha hw
    show (a : ℂ) * φ' w = ψ' ((a : ℂ) * w)
    rw [show φ' w = φ w from modH_eqOn φ hw, show ψ' ((a : ℂ) * w) = ψ ((a : ℂ) * w) from
      modH_eqOn ψ haw, hscale w hw]
  exact key

/-- **Rescaling commutes with pulling back, at the regularized level** (`RegEq` form of
`coordChange_rescale_fc_of_scale`). -/
theorem regEq_coordChange_rescale_of_scale (y : FieldSample) (Q : ℝ) {φ ψ : ℂ → ℂ} {a : ℝ}
    (ha : 0 < a)
    (hφd : DifferentiableOn ℂ φ H) (hφi : InjOn φ H) (hφ0 : ∀ w ∈ H, deriv φ w ≠ 0)
    (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0)
    (hscale : ∀ w ∈ H, (a : ℂ) * φ w = ψ ((a : ℂ) * w))
    (hsc : ∀ (d : ℂ) (r : ℝ), 0 < r → G1.ScaleConsistentAt y Q a ((foldedCircle d r).map φ))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (coordChange y ψ Q) (foldedCircle d r) = coordChange y ψ Q (foldedCircle d r)) :
    RegEq (coordChange (rescale y Q a) φ Q) (rescale (coordChange y ψ Q) Q a) := by
  have key := coordChange_rescale_fc_of_scale y Q ha hφd hφi hφ0 hψd hψi hψ0 hscale hsc hexact
  intro k z
  unfold avgReg
  simp_rw [key _ _ (radius_pos k)]

/-! ## Specialization to unzipping (the B3(d) field identity) -/

/-- The unzipping map `f_t⁻¹` of a continuous driver with `W 0 = 0` is holomorphic, injective and
has nonvanishing derivative on `ℍ`. -/
theorem fwdMapInv_props {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableOn ℂ (fwdMapInv W t) H ∧ InjOn (fwdMapInv W t) H ∧
      ∀ w ∈ H, deriv (fwdMapInv W t) w ≠ 0 :=
  ⟨RS.differentiableOn_fwdMapInv hW hW0 ht, RS.injOn_fwdMapInv hW hW0 ht, fun w hw => by
    rw [RegCont.deriv_fwdMapInv_eq hW hW0 ht hw]
    exact deriv_revMap_ne_zero _ (RegCont.continuous_vRev hW t) ht hw⟩

/-- **B3(d) at the field level (`F2.UnscaledB3dStmt`, second clause), deterministic form.** For a
continuous driver `W` with `W 0 = 0` (normalized, `W (max s 0) = W s`) and `a = scaleParam γ y > 0`,
the field unzipped in time `s` from the canonicalized configuration `canonConfig γ (y, W)` is
`RegEq` to the rescaling by `a` of the field unzipped from `(y, W)` in time `a² s`, provided
(`hsc`) the regularization of `y` is scale consistent at the images of folded circles under the
unzipping map of the rescaled driver, and (`hexact`, RC3) the folded-circle values of the field
unzipped in time `a² s` are its regularized ones. -/
theorem regEq_unzippedField_canonConfig {γ : ℝ} {y : FieldSample} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hWmax : ∀ s, W (max s 0) = W s)
    (ha : 0 < scaleParam γ y) {s : ℝ} (hs : 0 ≤ s)
    (hsc : ∀ (d : ℂ) (r : ℝ), 0 < r → G1.ScaleConsistentAt y (Qc γ) (scaleParam γ y)
      ((foldedCircle d r).map (fwdMapInv (canonConfig γ (y, W)).2 s)))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField γ (y, W) (scaleParam γ y ^ 2 * s)) (foldedCircle d r) =
        unzippedField γ (y, W) (scaleParam γ y ^ 2 * s) (foldedCircle d r)) :
    RegEq (unzippedField γ (canonConfig γ (y, W)) s)
      (rescale (unzippedField γ (y, W) (scaleParam γ y ^ 2 * s)) (Qc γ) (scaleParam γ y)) := by
  set a := scaleParam γ y with ha_def
  have hdrv : (canonConfig γ (y, W)).2 = fun r => W (a ^ 2 * r) / a :=
    B3d.canonConfig_snd_of_max hWmax
  have hWa : Continuous fun r => W (a ^ 2 * r) / a := by fun_prop
  have hWa0 : (fun r => W (a ^ 2 * r) / a) 0 = 0 := by simp [hW0]
  have has : 0 ≤ a ^ 2 * s := mul_nonneg (sq_nonneg a) hs
  obtain ⟨hφd, hφi, hφ0⟩ := fwdMapInv_props hWa hWa0 hs
  obtain ⟨hψd, hψi, hψ0⟩ := fwdMapInv_props hW hW0 has
  have hscale : ∀ w ∈ H, (a : ℂ) * fwdMapInv (fun r => W (a ^ 2 * r) / a) s w =
      fwdMapInv W (a ^ 2 * s) ((a : ℂ) * w) := fun w hw => by
    rw [RS.fwdMapInv_scale hW hW0 ha hs hw]
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
    rw [mul_div_cancel₀ _ ha']
  have hsc' := hsc
  rw [hdrv] at hsc'
  show RegEq (coordChange (rescale y (Qc γ) a) (fwdMapInv (canonConfig γ (y, W)).2 s) (Qc γ))
    (rescale (coordChange y (fwdMapInv W (a ^ 2 * s)) (Qc γ)) (Qc γ) a)
  rw [hdrv]
  exact regEq_coordChange_rescale_of_scale y (Qc γ) ha hφd hφi hφ0 hψd hψi hψ0 hscale hsc' hexact

/-- Raw form of `regEq_unzippedField_canonConfig`: the two fields agree on every folded circle. -/
theorem unzippedField_canonConfig_fc {γ : ℝ} {y : FieldSample} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hWmax : ∀ s, W (max s 0) = W s)
    (ha : 0 < scaleParam γ y) {s : ℝ} (hs : 0 ≤ s)
    (hsc : ∀ (d : ℂ) (r : ℝ), 0 < r → G1.ScaleConsistentAt y (Qc γ) (scaleParam γ y)
      ((foldedCircle d r).map (fwdMapInv (canonConfig γ (y, W)).2 s)))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField γ (y, W) (scaleParam γ y ^ 2 * s)) (foldedCircle d r) =
        unzippedField γ (y, W) (scaleParam γ y ^ 2 * s) (foldedCircle d r)) :
    ∀ (d : ℂ) (r : ℝ), 0 < r → unzippedField γ (canonConfig γ (y, W)) s (foldedCircle d r) =
      rescale (unzippedField γ (y, W) (scaleParam γ y ^ 2 * s)) (Qc γ) (scaleParam γ y)
        (foldedCircle d r) := by
  set a := scaleParam γ y with ha_def
  have hdrv : (canonConfig γ (y, W)).2 = fun r => W (a ^ 2 * r) / a :=
    B3d.canonConfig_snd_of_max hWmax
  have hWa : Continuous fun r => W (a ^ 2 * r) / a := by fun_prop
  have hWa0 : (fun r => W (a ^ 2 * r) / a) 0 = 0 := by simp [hW0]
  have has : 0 ≤ a ^ 2 * s := mul_nonneg (sq_nonneg a) hs
  obtain ⟨hφd, hφi, hφ0⟩ := fwdMapInv_props hWa hWa0 hs
  obtain ⟨hψd, hψi, hψ0⟩ := fwdMapInv_props hW hW0 has
  have hscale : ∀ w ∈ H, (a : ℂ) * fwdMapInv (fun r => W (a ^ 2 * r) / a) s w =
      fwdMapInv W (a ^ 2 * s) ((a : ℂ) * w) := fun w hw => by
    rw [RS.fwdMapInv_scale hW hW0 ha hs hw]
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
    rw [mul_div_cancel₀ _ ha']
  have hsc' := hsc
  rw [hdrv] at hsc'
  show ∀ (d : ℂ) (r : ℝ), 0 < r →
    coordChange (rescale y (Qc γ) a) (fwdMapInv (canonConfig γ (y, W)).2 s) (Qc γ)
      (foldedCircle d r) =
    rescale (coordChange y (fwdMapInv W (a ^ 2 * s)) (Qc γ)) (Qc γ) a (foldedCircle d r)
  rw [hdrv]
  exact coordChange_rescale_fc_of_scale y (Qc γ) ha hφd hφi hφ0 hψd hψi hψ0 hscale hsc' hexact

end WedgeUnzip
end QuantumZipper
