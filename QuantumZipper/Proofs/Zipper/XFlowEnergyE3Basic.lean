import QuantumZipper.Proofs.Zipper.XFlowEnergyDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-ENERGY, E3 (1/2): pathwise ingredients of the circle modulus

* `e3_flowNu_ae_facts`, `e3_flowMu_eq_map`, `e3_flowMu_zero_eq`: the D33 facts `alphaUS_ae_facts`,
  `muUS_eq_map`, `muUS_zero_eq` for the general circle `fc(d, r)`
  (`μ_{p,0} = (ψ_{u+s})_* fc(d, r) = νT W d r (u+s)`);
* `flowNu_eq_mix`: `(R_{u,s})_* fc(d, r) = A.map (z ↦ R_{u,s}(foldH(circleMap d r (Re z))))`
  with the fixed base `A = circLeb.map ofReal` (the circle parametrization of `UnifUCTrBasic`),
  so that the two circles of the modulus are mixtures over the **same** base;
* `norm_revMap_sub_le_strip`: the reverse map is Lipschitz on the strip `{τ ≤ Im ≤ K}`, with
  constant `S(1/τ + K)` polynomial in `1/τ` (mean value inequality with the derivative bound
  `TwoPoint.abs_log_norm_deriv_revMap_le`).

Own elementary bookkeeping (as `UnifUC1RadBasic`, `UnifUCE2Basic`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint RegUnif B2 CharFun MeasUnzip

variable {W : ℝ → ℝ}

theorem e3_flowNu_ae_facts (hW : Continuous W) {T Mw : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw)
    {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ z ∂foldedCircle d r, z ∈ H ∧ ‖z‖ ≤ ‖d‖ + r ∧
      z.im ≤ (revMap (vrev W (u + s)) s z).im ∧ revMap (vrev W (u + s)) s z ∈ H ∧
      ‖revMap (vrev W (u + s)) s z‖ ≤ revBound (2 * Mw) T (‖d‖ + r) := by
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr,
    TwoPoint.foldedCircle_ae_norm_le d hr.le] with z hz hzn
  have hV := continuous_vrev hW (u + s)
  refine ⟨hz, hzn, im_le_im_revMap _ hV z hz hs, TwoPoint.im_revMap_pos hV hz hs, ?_⟩
  exact (norm_revMap_le_revBound hV hs
    (fun t _ => abs_vrev_le hM ⟨add_nonneg hu hs, hus⟩ t) _ hzn).trans
    (revBound_mono (by linarith))

theorem e3_flowNu_ae_H_norm (hW : Continuous W) {T Mw : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw)
    {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂flowNu W (u, s, d, r), x ∈ H ∧ ‖x‖ ≤ revBound (2 * Mw) T (‖d‖ + r) := by
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (u + s)) hs
  exact (ae_map_iff hRm.aemeasurable (measurableSet_H_norm_le _)).2
    ((e3_flowNu_ae_facts hW hM hu hs hus d hr).mono fun z hz => ⟨hz.2.2.2.1, hz.2.2.2.2⟩)

theorem e3_isProb_flowNu (hW : Continuous W) {u s : ℝ} (hs : 0 ≤ s) (d : ℂ) (r : ℝ) :
    IsProbabilityMeasure (flowNu W (u, s, d, r)) := by
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (u + s)) hs
  unfold flowNu
  infer_instance

/-- `μ_{p,ρ} = (revMap (vrev W u) u)_* (ν_p ⋆ fc(·,ρ))` for `ρ > 0`. -/
theorem e3_flowMu_eq_map (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T)
    (d : ℂ) {r : ℝ} (hr : 0 < r) {ρ : ℝ} (hρ : 0 < ρ) :
    flowMu W (u, s, d, r) ρ =
      (bindFc (flowNu W (u, s, d, r)) ρ).map (revMap (vrev W u) u) := by
  have := e3_isProb_flowNu hW (u := u) hs d r
  refine Measure.map_congr ?_
  filter_upwards [CoordReg.bind_fc_mem_H_norm _ hρ
    ((e3_flowNu_ae_H_norm hW hM hu hs hus d hr).mono fun x hx => hx.2)] with x hx
  exact fwdMapInv_eq_revMap_vrev hW hW0 hu hx.1

/-- `μ_{p,0} = νT W d r (u+s)` (cocycle `ψ_u ∘ R_{u,s} = ψ_{u+s}`). -/
theorem e3_flowMu_zero_eq (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T)
    (d : ℂ) {r : ℝ} (hr : 0 < r) :
    flowMu W (u, s, d, r) 0 = νT W d r (u + s) := by
  have := e3_isProb_flowNu hW (u := u) hs d r
  have hαH := (e3_flowNu_ae_H_norm hW hM hu hs hus d hr).mono fun x hx => hx.1
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (u + s)) hs
  have hψm := TwoPoint.measurable_revMap (continuous_vrev hW u) hu
  show (bindFc (flowNu W (u, s, d, r)) 0).map (fwdMapInv W u) = _
  rw [bindFc_zero_of_ae_H hαH]
  have e1 : (flowNu W (u, s, d, r)).map (fwdMapInv W u) =
      (flowNu W (u, s, d, r)).map (revMap (vrev W u) u) := by
    refine Measure.map_congr ?_
    filter_upwards [hαH] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hu hx
  rw [e1, ← revMap_map_eq_nuT hW hW0 (add_nonneg hu hs) hr]
  unfold flowNu
  rw [Measure.map_map hψm hRm]
  refine Measure.map_congr ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with z hz
  exact (revMap_vrev_split hW hu hu hs le_rfl hz).symm

/-- The base measure of the circle parametrization, on `ℂ`. -/
def circA : Measure ℂ := circLeb.map (fun θ : ℝ => (θ : ℂ))

instance : IsProbabilityMeasure circA := by
  unfold circA
  have := Complex.measurable_ofReal
  infer_instance

/-- The centre map of the pushed circle in the circle parametrization. -/
def cenM (W : ℝ → ℝ) (u s : ℝ) (d : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  revMap (vrev W (u + s)) s (foldH (circleMap d r z.re))

theorem measurable_cenM (hW : Continuous W) {u s : ℝ} (hs : 0 ≤ s) (d : ℂ) (r : ℝ) :
    Measurable (cenM W u s d r) :=
  (TwoPoint.measurable_revMap (continuous_vrev hW (u + s)) hs).comp
    (measurable_foldH.comp ((measurable_circleMap d r).comp Complex.measurable_re))

/-- **The pushed circle as a mixture over the fixed base `circA`.** -/
theorem flowNu_eq_mix (hW : Continuous W) {u s : ℝ} (hs : 0 ≤ s) (d : ℂ) (r : ℝ) :
    flowNu W (u, s, d, r) = circA.map (cenM W u s d r) := by
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (u + s)) hs
  unfold flowNu circA
  rw [foldedCircle, circleUnif_eq_map_circLeb, Measure.map_map measurable_foldH
    (measurable_circleMap d r), Measure.map_map hRm (measurable_foldH.comp
    (measurable_circleMap d r)), Measure.map_map (measurable_cenM hW hs d r)
    Complex.measurable_ofReal]
  rfl

theorem circA_ae_eq (d : ℂ) {r : ℝ} {P : ℂ → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ᵐ z ∂foldedCircle d r, P z) :
    ∀ᵐ z ∂circA, P (foldH (circleMap d r z.re)) := by
  have hf : Measurable fun z : ℂ => foldH (circleMap d r z.re) :=
    measurable_foldH.comp ((measurable_circleMap d r).comp Complex.measurable_re)
  have e : circA.map (fun z : ℂ => foldH (circleMap d r z.re)) = foldedCircle d r := by
    unfold circA
    rw [foldedCircle, circleUnif_eq_map_circLeb, Measure.map_map measurable_foldH
      (measurable_circleMap d r), Measure.map_map hf Complex.measurable_ofReal]
    rfl
  rw [← e] at h
  exact (ae_map_iff hf.aemeasurable hP).1 h

theorem exp_abs_log_le {y : ℝ} (hy : 0 < y) : Real.exp |Real.log y| ≤ y + 1 / y := by
  rcases le_total 0 (Real.log y) with h | h
  · rw [abs_of_nonneg h, Real.exp_log hy]; have : 0 < 1 / y := by positivity
    linarith
  · rw [abs_of_nonpos h, Real.exp_neg, Real.exp_log hy, inv_eq_one_div]; linarith

/-- **The reverse map is Lipschitz on a strip** `{τ ≤ Im ≤ K}`. -/
theorem norm_revMap_sub_le_strip {V : ℝ → ℝ} (hV : Continuous V) {s : ℝ} (hs : 0 ≤ s)
    {τ K : ℝ} (hτ : 0 < τ) {a b : ℂ} (ha : τ ≤ a.im) (ha' : a.im ≤ K) (hb : τ ≤ b.im)
    (hb' : b.im ≤ K) :
    ‖revMap V s a - revMap V s b‖ ≤
      (Real.exp |Real.log (Real.sqrt (K ^ 2 + 4 * s))| * (K + 1 / τ)) * ‖a - b‖ := by
  set S : Set ℂ := {z | τ ≤ z.im ∧ z.im ≤ K} with hS
  have hconv : Convex ℝ S := by
    intro x hx y hy c e hc he hce
    simp only [hS, mem_ofPred_eq, Complex.add_im, Complex.smul_im, smul_eq_mul] at hx hy ⊢
    constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
  have hH : ∀ z ∈ S, z ∈ H := fun z hz => show 0 < z.im from hτ.trans_le hz.1
  have hdiff : ∀ z ∈ S, DifferentiableAt ℂ (revMap V s) z := fun z hz =>
    (QuantumZipper.differentiableOn_revMap V hV hs).differentiableAt
      (isOpen_H.mem_nhds (hH z hz))
  have hbound : ∀ z ∈ S, ‖deriv (revMap V s) z‖ ≤
      Real.exp |Real.log (Real.sqrt (K ^ 2 + 4 * s))| * (K + 1 / τ) := by
    intro z hz
    have hz0 : 0 < z.im := hH z hz
    have hl := abs_log_norm_deriv_revMap_le hV hs (hH z hz) hz.2
    have hy : z.im + 1 / z.im ≤ K + 1 / τ := by
      have : 1 / z.im ≤ 1 / τ := one_div_le_one_div_of_le hτ hz.1
      linarith [hz.2]
    have he := exp_abs_log_le hz0
    rcases (norm_nonneg (deriv (revMap V s) z)).eq_or_lt with h0 | h0
    · rw [← h0]
      have : 0 < 1 / τ := by positivity
      exact mul_nonneg (Real.exp_pos _).le (by linarith [hz.1, hz.2])
    calc ‖deriv (revMap V s) z‖ = Real.exp (Real.log ‖deriv (revMap V s) z‖) :=
          (Real.exp_log h0).symm
      _ ≤ Real.exp (|Real.log (Real.sqrt (K ^ 2 + 4 * s))| + |Real.log z.im|) :=
          Real.exp_le_exp.2 ((le_abs_self _).trans hl)
      _ = Real.exp |Real.log (Real.sqrt (K ^ 2 + 4 * s))| * Real.exp |Real.log z.im| :=
          Real.exp_add _ _
      _ ≤ Real.exp |Real.log (Real.sqrt (K ^ 2 + 4 * s))| * (K + 1 / τ) :=
          mul_le_mul_of_nonneg_left (he.trans hy) (Real.exp_pos _).le
  have := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbound (show b ∈ S from ⟨hb, hb'⟩)
    (show a ∈ S from ⟨ha, ha'⟩)
  exact this

end F1
end QuantumZipper
