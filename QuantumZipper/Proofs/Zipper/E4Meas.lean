import QuantumZipper.Proofs.Zipper.E1Main
import QuantumZipper.Proofs.Zipper.E1TransferMain
import QuantumZipper.Proofs.Zipper.E4MeasPath

/-!
# E4-MEAS: the Palm-zip right side is a measurable function of `(x, V^t, W⁰)`

`handoff/E-PLAN-2.md`, node E4-MEAS. For a free field `X'` on `(Ω', P')` and measurable `Φ`,

`e4_meas`: there is a measurable `H : ℝ × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) → ℝ≥0∞` with
`H (x, d) = ∫⁻ ω', Φ (coordsFull (targetField κ (stopDrive d) t ϖ x (X' ω'))) ∂P'`
whenever `d.1` is continuous and `x` is live at time `t` for the driver `stopDrive d`.

Route (own bookkeeping; the paper, Sheffield arXiv:1012.4797, Lemma 5.6 pp. 66–68, uses this
conditional expectation without discussing measurability):
* the driver is read through the measurable path map `E4Meas.stopPath` (`E4MeasPath`);
* `Fre`: `realRevMap v t x` at a live point is the limit of `Re F(x + i/(n+1))`
  (`RevMapExtension.exists_revMapExt_extension`: the extension is holomorphic near `x` and equals
  `revMap` on `ℍ`), so it is a measurable function of `(x, path)`;
* the coordinates of `targetField` are explicit (`E1.coordsFull_targetField`); every term is a
  parametric integral of a jointly measurable function (Tonelli-type
  `StronglyMeasurable.integral_prod_right'`), except `Y(ϖ_t)`, which is replaced by
  `evalReg Y ϖ_t` (a.s. equal by RC1 at the Frostman measure `ϖ_t`,
  `FrostmanReg.ae_tendsto_integral_avgReg_frostman`; jointly measurable,
  `UnzipFull.measurable_evalReg_push_gen`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Meas

open B2 E1 CoordsFull PalmNorm CharFun

variable {t : ℝ} (ht : 0 ≤ t)

/-- Measurable version of `realRevMap (Wof 1 t p) t x`: the limit of `Re F(x + i/(n+1))`. -/
def Fre (q : ℝ × C(Icc (0 : ℝ) t, ℝ)) : ℝ :=
  limUnder atTop fun n : ℕ =>
    (Fm 1 t ht (q.2, (q.1 : ℂ) + ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * Complex.I)).re

theorem measurable_Fre : Measurable (Fre ht) := by
  refine (StronglyMeasurable.limUnder fun n => Measurable.stronglyMeasurable ?_).measurable
  exact Complex.measurable_re.comp ((measurable_Fm 1 t ht).comp (measurable_snd.prodMk
    ((Complex.measurable_ofReal.comp measurable_fst).add_const _)))

omit ht in
theorem tendsto_add_inv_I (x : ℝ) : Tendsto (fun n : ℕ =>
    (x : ℂ) + ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * Complex.I) atTop (𝓝 (x : ℂ)) := by
  have h0 : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h1 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (x : ℂ)) atTop (𝓝 (x : ℂ))).add
    (((Complex.continuous_ofReal.tendsto 0).comp h0).mul_const Complex.I)
  simpa using h1

/-- At a live point, `Fre` is the real reverse map. -/
theorem Fre_eq {v : ℝ → ℝ} (hv : Continuous v) {p : C(Icc (0 : ℝ) t, ℝ)}
    (hvp : EqOn v (Wof 1 t ht p) (Icc 0 t)) {x : ℝ} (hx : IsLive v t x) :
    Fre ht (x, p) = realRevMap v t x := by
  obtain ⟨U, hUo, hxU, -, hd, hH, -, hR, -⟩ :=
    RevMapExtension.exists_revMapExt_extension hv ht {x}
      (fun y hy => by rw [mem_singleton_iff.1 hy]; exact hx)
  have hcont : ContinuousAt (RevMapExtension.revMapExt v t) (x : ℂ) :=
    (hd.differentiableAt (hUo.mem_nhds (hxU x rfl))).continuousAt
  have hlim := (Complex.continuous_re.tendsto _).comp (hcont.tendsto.comp (tendsto_add_inv_I x))
  rw [hR x rfl, Complex.ofReal_re] at hlim
  refine (hlim.congr fun n => ?_).limUnder_eq
  have him : 0 < ((x : ℂ) + ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * Complex.I).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
    positivity
  simp only [Function.comp_apply]
  rw [hH _ him, ReverseFlow.revMap_congr_drive _ hvp]
  rfl

variable (κ : ℝ) (ϖ : Measure ℂ)

/-- `k_{ϖ_t}(u)` read through the flow: `∫ neumannH u (F w) dϖ(w)`. -/
def kP (pu : C(Icc (0 : ℝ) t, ℝ) × ℂ) : ℝ := ∫ w, neumannH pu.2 (Fm 1 t ht (pu.1, w)) ∂ϖ

theorem measurable_kP [SFinite ϖ] : Measurable (kP ht ϖ) := by
  have hf : Measurable fun q : (C(Icc (0 : ℝ) t, ℝ) × ℂ) × ℂ =>
      neumannH q.1.2 (Fm 1 t ht (q.1.1, q.2)) :=
    measurable_neumannH.comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_Fm 1 t ht).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

/-- `ϖ_t` for the driver `Wof 1 t p`. -/
abbrev vt (p : C(Icc (0 : ℝ) t, ℝ)) : Measure ℂ := varpiT (Wof 1 t ht p) t ϖ

theorem integral_vt (p : C(Icc (0 : ℝ) t, ℝ)) {g : ℂ → ℝ} (hg : Measurable g) :
    ∫ u, g u ∂vt ht ϖ p = ∫ w, g (Fm 1 t ht (p, w)) ∂ϖ := by
  unfold vt varpiT
  rw [integral_map (TwoPoint.measurable_revMap (continuous_Wof 1 t ht p) ht).aemeasurable
    hg.aestronglyMeasurable]
  rfl

/-- The shifted mean at the measurable point `Fre`. -/
def sfun (q : (ℝ × C(Icc (0 : ℝ) t, ℝ)) × ℂ) : ℝ :=
  shiftFun (Real.sqrt κ) (h0rev κ) (vt ht ϖ q.1.2) (Fre ht q.1) q.2

theorem measurable_sfun [SFinite ϖ] : Measurable (sfun ht κ ϖ) := by
  have e : sfun ht κ ϖ = fun q => h0rev κ q.2 + Real.sqrt κ / 2 *
      (neumannH (Fre ht q.1 : ℂ) q.2 - kP ht ϖ (q.1.2, q.2)) := by
    funext q
    simp only [sfun, shiftFun, kPot]
    rw [integral_vt ht ϖ q.1.2 (g := fun v => neumannH q.2 v)
      (measurable_neumannH.comp (measurable_const.prodMk measurable_id))]
    rfl
  rw [e]
  exact ((UnzipInvariance.measurable_h0rev κ).comp measurable_snd).add (measurable_const.mul
    ((measurable_neumannH.comp ((Complex.measurable_ofReal.comp
      ((measurable_Fre ht).comp measurable_fst)).prodMk measurable_snd)).sub
      ((measurable_kP ht ϖ).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))

/-- The coordinate vector of `targetField` (in integral form), with `Y(ϖ_t)` replaced by
`evalReg Y ϖ_t`. -/
def cvec (q : (ℝ × C(Icc (0 : ℝ) t, ℝ)) × FieldSample) : ℕ → ℝ := fun j =>
  ((∫ u, sfun ht κ ϖ (q.1, u) ∂(foldedCircle (fullIndex j).1 (fullIndex j).2)) -
      (∫ w, sfun ht κ ϖ (q.1, Fm 1 t ht (q.1.2, w)) ∂ϖ) - qt κ (Wof 1 t ht q.1.2) t ϖ) +
    (q.2 (foldedCircle (fullIndex j).1 (fullIndex j).2) - evalReg q.2 (vt ht ϖ q.1.2))

theorem measurable_cvec_h1 [SFinite ϖ] (j : ℕ) : Measurable fun q1 : ℝ × C(Icc (0 : ℝ) t, ℝ) =>
    ∫ u, sfun ht κ ϖ (q1, u) ∂(foldedCircle (fullIndex j).1 (fullIndex j).2) :=
  (StronglyMeasurable.integral_prod_right' (f := sfun ht κ ϖ)
    (measurable_sfun ht κ ϖ).stronglyMeasurable).measurable

theorem measurable_cvec_h2 [SFinite ϖ] : Measurable fun q1 : ℝ × C(Icc (0 : ℝ) t, ℝ) =>
    ∫ w, sfun ht κ ϖ (q1, Fm 1 t ht (q1.2, w)) ∂ϖ :=
  (StronglyMeasurable.integral_prod_right'
    (f := fun r : (ℝ × C(Icc (0 : ℝ) t, ℝ)) × ℂ => sfun ht κ ϖ (r.1, Fm 1 t ht (r.1.2, r.2)))
    ((measurable_sfun ht κ ϖ).comp (measurable_fst.prodMk ((measurable_Fm 1 t ht).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))).stronglyMeasurable).measurable

theorem measurable_cvec_h3 [SFinite ϖ] (hϖH : ϖ Hᶜ = 0) :
    Measurable fun p : C(Icc (0 : ℝ) t, ℝ) => qt κ (Wof 1 t ht p) t ϖ :=
  measurable_const.mul (B1Full.measurable_integral_log_deriv_gen 1 t ht ϖ hϖH)

theorem measurable_cvec_h4 [SFinite ϖ] :
    Measurable fun q : C(Icc (0 : ℝ) t, ℝ) × FieldSample => evalReg q.2 (vt ht ϖ q.1) :=
  UnzipFull.measurable_evalReg_push_gen 1 t ht ϖ

theorem measurable_cvec_h5 (j : ℕ) : Measurable fun q : (ℝ × C(Icc (0 : ℝ) t, ℝ)) × FieldSample =>
    q.2 (foldedCircle (fullIndex j).1 (fullIndex j).2) :=
  (measurable_pi_apply (foldedCircle (fullIndex j).1 (fullIndex j).2)).comp measurable_snd

theorem measurable_cvec_g1 [SFinite ϖ] (j : ℕ) :
    Measurable fun q : (ℝ × C(Icc (0 : ℝ) t, ℝ)) × FieldSample =>
      ∫ u, sfun ht κ ϖ (q.1, u) ∂(foldedCircle (fullIndex j).1 (fullIndex j).2) :=
  (measurable_cvec_h1 ht κ ϖ j).comp measurable_fst

theorem measurable_cvec_g2 [SFinite ϖ] :
    Measurable fun q : (ℝ × C(Icc (0 : ℝ) t, ℝ)) × FieldSample =>
      ∫ w, sfun ht κ ϖ (q.1, Fm 1 t ht (q.1.2, w)) ∂ϖ :=
  (measurable_cvec_h2 ht κ ϖ).comp measurable_fst

theorem measurable_cvec_g3 [SFinite ϖ] (hϖH : ϖ Hᶜ = 0) :
    Measurable fun q : (ℝ × C(Icc (0 : ℝ) t, ℝ)) × FieldSample => qt κ (Wof 1 t ht q.1.2) t ϖ :=
  (measurable_cvec_h3 ht κ ϖ hϖH).comp (measurable_snd.comp measurable_fst)

theorem measurable_cvec_g4 [SFinite ϖ] :
    Measurable fun q : (ℝ × C(Icc (0 : ℝ) t, ℝ)) × FieldSample => evalReg q.2 (vt ht ϖ q.1.2) := by
  have hf : Measurable fun q : (ℝ × C(Icc (0 : ℝ) t, ℝ)) × FieldSample => (q.1.2, q.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  exact Measurable.comp (g := fun r : C(Icc (0 : ℝ) t, ℝ) × FieldSample => evalReg r.2 (vt ht ϖ r.1))
    (f := fun q : (ℝ × C(Icc (0 : ℝ) t, ℝ)) × FieldSample => (q.1.2, q.2))
    (measurable_cvec_h4 ht ϖ) hf

theorem measurable_cvec_apply [SFinite ϖ] (hϖH : ϖ Hᶜ = 0) (j : ℕ) :
    Measurable fun q => cvec ht κ ϖ q j :=
  (((measurable_cvec_g1 ht κ ϖ j).sub (measurable_cvec_g2 ht κ ϖ)).sub
    (measurable_cvec_g3 ht κ ϖ hϖH)).add ((measurable_cvec_h5 j).sub (measurable_cvec_g4 ht ϖ))

theorem measurable_cvec [SFinite ϖ] (hϖH : ϖ Hᶜ = 0) : Measurable (cvec ht κ ϖ) :=
  measurable_pi_iff.2 fun j => measurable_cvec_apply ht κ ϖ hϖH j

include ht in
/-- RC1 at `ϖ_t`: a.s. `evalReg Y ϖ_t = Y(ϖ_t)` for a free field. -/
theorem ae_evalReg_varpiT {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X' : Ω' → FieldSample} (hX' : IsFreeGFFModConstH X' P')
    {ϖ : Measure ℂ} (hϖ : IsNormalizer ϖ) {v : ℝ → ℝ} (hv : Continuous v) :
    ∀ᵐ ω' ∂P', evalReg (X' ω') (varpiT v t ϖ) = X' ω' (varpiT v t ϖ) := by
  have := hϖ.prob
  obtain ⟨K, hKc, hKH, hK0⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hfr⟩ := hϖ.frost
  obtain ⟨R, hR⟩ := B2.map_revMap_support_of_compact hv ht hKc hKH hK0
  obtain ⟨C', hC'⟩ := B2.isFrostman_map_revMap_of_compact hv ht hKc hKH hK0 hα.le hfr
  filter_upwards [FrostmanReg.ae_tendsto_integral_avgReg_frostman hX' hR hC' hα] with ω' h
  exact h.limUnder_eq

include ht in
/-- **E4-MEAS.** The Palm-zip right side is a measurable function of `(x, V^t, W⁰)` on the
live set. -/
theorem e4_meas (hϖ : IsNormalizer ϖ) {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X' : Ω' → FieldSample} (hX' : IsFreeGFFModConstH X' P')
    {Φ : (ℕ → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∃ H : ℝ × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) → ℝ≥0∞, Measurable H ∧
      ∀ x (d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)), Continuous d.1 → IsLive (stopDrive d) t x →
        H (x, d) = ∫⁻ ω', Φ (coordsFull (targetField κ (stopDrive d) t ϖ x (X' ω'))) ∂P' := by
  have := hϖ.prob
  obtain ⟨K, hKc, hKH, hK0⟩ := hϖ.cpt
  have hϖH : ϖ Hᶜ = 0 := measure_mono_null (compl_subset_compl.2 hKH) hK0
  have hX'm : Measurable X' := measurable_pi_iff.2 hX'.measurable_coord
  refine ⟨fun q => ∫⁻ ω', Φ (cvec ht κ ϖ ((q.1, stopPath t q.2.1), X' ω')) ∂P', ?_, ?_⟩
  · refine Measurable.lintegral_prod_right'
      (f := fun r : (ℝ × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))) × Ω' =>
        Φ (cvec ht κ ϖ ((r.1.1, stopPath t r.1.2.1), X' r.2)))
      (hΦ.comp ((measurable_cvec ht κ ϖ hϖH).comp ?_))
    exact ((measurable_fst.comp measurable_fst).prodMk ((measurable_stopPath t).comp
      ((measurable_fst.comp measurable_snd).comp measurable_fst))).prodMk
      (hX'm.comp measurable_snd)
  · intro x d hd hlive
    set p := stopPath t d.1 with hp
    have hv : Continuous (stopDrive d) := hd.comp continuous_real_toNNReal
    have heq : EqOn (stopDrive d) (Wof 1 t ht p) (Icc 0 t) := (eqOn_Wof_stopPath ht hd).symm
    have hrev : revMap (stopDrive d) t = revMap (Wof 1 t ht p) t :=
      funext fun z => ReverseFlow.revMap_congr_drive z heq
    have hvt : varpiT (stopDrive d) t ϖ = vt ht ϖ p := by simp only [vt, varpiT, hrev]
    have hqt : qt κ (stopDrive d) t ϖ = qt κ (Wof 1 t ht p) t ϖ := by simp only [qt, hrev]
    have hF := Fre_eq ht hv heq hlive
    refine lintegral_congr_ae ?_
    filter_upwards [ae_evalReg_varpiT ht hX' hϖ (continuous_Wof 1 t ht p)] with ω' hω'
    congr 1
    rw [coordsFull_targetField, hvt, hqt, ← hF]
    funext j
    simp only [cvec]
    rw [hω', ← integral_vt ht ϖ p (g := fun u => sfun ht κ ϖ ((x, p), u))
      ((measurable_sfun ht κ ϖ).comp (measurable_const.prodMk measurable_id))]
    rfl

end E4Meas
end QuantumZipper
