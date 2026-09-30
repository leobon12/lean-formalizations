import QuantumZipper.Proofs.Zipper.SWCoreB7dEv
import QuantumZipper.Proofs.Zipper.WedgeUnzipScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8F (4): offset proxies and the countable offset transfer event

Offset analogue of SWCoreB7dEv (D70 transfer, SWC-B8 plan (b)). On `C([0,T']) × FieldSample`:

* `RawQc`, `AvgQc`: the raw folded-circle value and the regularized circle average of the dilated
  unzipped field `coordChange (𝔥₀ + y) (f_σ⁻¹ ∘ (c ·)) Q`, read through the jointly measurable
  flow proxies `MeasUnzip.flowJ`, `MeasUnzip.logJ` (the factor `c` enters as `flowJ(·, c w)` and
  `logJ(·, c w) + log c`, kept inside one integral, so no integrability of `log |ψ'|` is needed);
  `RawQc_eq`, `AvgQc_eq_avgReg`: the identification for a path with `W 0 = 0`;
* `densQc`, `IQc`: the dilated transported test integral `∫ awProxy(F_σ) u v f (c x) · dens`;
* `EvQc`: Cauchy property in `k` over rational local times `σ ∈ [0,T']`, **across rational
  offsets `c, c' ∈ [1,2]`** (`|IQc σ c j − IQc σ c' j'|` small); `measurableSet_EvQc`.

Same scheme as `SWCore.EvQ` with `c` as one more countable event parameter. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open CharFun

variable (κ : ℝ) {T' : ℝ} (hT' : 0 ≤ T')

/-- Raw value of the dilated unzipped field at `fc(q.2, 2^{-j})`, through the flow proxies. -/
def RawQc (c σ : ℝ) (j : ℕ) (q : (C(Icc (0 : ℝ) T', ℝ) × FieldSample) × ℂ) : ℝ :=
  limUnder atTop (fun k => ∫ w, avgReg (ofFun (h0rev κ) + q.1.2) k
      (MeasUnzip.flowJ hT' κ (q.1.1, (σ, (c : ℂ) * w))) ∂foldedCircle q.2 (radius j)) +
    Qc (Real.sqrt κ) * ∫ w, (MeasUnzip.logJ hT' κ (q.1.1, (σ, (c : ℂ) * w)) + Real.log c)
      ∂foldedCircle q.2 (radius j)

theorem measurable_RawQc (c σ : ℝ) (j : ℕ) : Measurable (RawQc κ hT' c σ j) := by
  have hG : ∀ k : ℕ, Measurable fun z : (C(Icc (0 : ℝ) T', ℝ) × FieldSample) × ℂ =>
      avgReg (ofFun (h0rev κ) + z.1.2) k
        (MeasUnzip.flowJ hT' κ (z.1.1, (σ, (c : ℂ) * z.2))) := by
    intro k
    refine (measurable_avgReg k).comp ((measurable_const.add
      (measurable_snd.comp measurable_fst)).prodMk ?_)
    exact (MeasUnzip.measurable_flowJ hT' κ).comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_const.prodMk (measurable_const.mul measurable_snd)))
  have hL : Measurable fun z : (C(Icc (0 : ℝ) T', ℝ) × FieldSample) × ℂ =>
      MeasUnzip.logJ hT' κ (z.1.1, (σ, (c : ℂ) * z.2)) + Real.log c :=
    ((MeasUnzip.measurable_logJ hT' κ).comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_const.prodMk (measurable_const.mul measurable_snd)))).add measurable_const
  exact ((StronglyMeasurable.limUnder fun k =>
    (RegUnif.measurable_integral_foldedCircle (hG k) (radius j)).stronglyMeasurable).measurable).add
    ((RegUnif.measurable_integral_foldedCircle hL (radius j)).const_mul _)

/-- The proxy of the regularized circle average of the dilated unzipped field. -/
def AvgQc (c σ : ℝ) (j : ℕ) (q : (C(Icc (0 : ℝ) T', ℝ) × FieldSample) × ℂ) : ℝ :=
  limUnder atTop fun n => RawQc κ hT' c σ j (q.1, dyadicRoundC n q.2)

theorem measurable_AvgQc (c σ : ℝ) (j : ℕ) : Measurable (AvgQc κ hT' c σ j) :=
  (StronglyMeasurable.limUnder fun n => ((measurable_RawQc κ hT' c σ j).comp
    (measurable_id.fst.prodMk ((RegUnif.measurable_dyadicRoundC_tr n).comp
      measurable_id.snd))).stronglyMeasurable).measurable

theorem mul_mem_H_of_pos {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : w ∈ H) : (c : ℂ) * w ∈ H := by
  show (0 : ℝ) < ((c : ℂ) * w).im
  rw [Complex.im_ofReal_mul]
  exact mul_pos hc hw

/-- **The proxy is the raw value** (path with `W 0 = 0`). -/
theorem RawQc_eq {e : C(Icc (0 : ℝ) T', ℝ)} (he : e ∈ MeasUnzip.PZ hT' κ) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) T') {c : ℝ} (hc : 0 < c) (x : FieldSample) (d : ℂ) (j : ℕ) :
    coordChange (ofFun (h0rev κ) + x)
        (fun w => fwdMapInv (Wof κ T' hT' e) σ ((c : ℂ) * w)) (Qc (Real.sqrt κ))
        (foldedCircle d (radius j)) = RawQc κ hT' c σ j ((e, x), d) := by
  set μ := foldedCircle d (radius j) with hμ
  have hae : ∀ᵐ w ∂μ, w ∈ H := TwoPoint.foldedCircle_ae_mem_H d (radius_pos j)
  have hW : Continuous (Wof κ T' hT' e) := continuous_Wof κ T' hT' e
  have hne := (WedgeUnzip.fwdMapInv_props hW he hσ.1).2.2
  have hfl : (fun w => fwdMapInv (Wof κ T' hT' e) σ ((c : ℂ) * w)) =ᵐ[μ]
      fun w => MeasUnzip.flowJ hT' κ (e, (σ, (c : ℂ) * w)) := by
    filter_upwards [hae] with w hw
    simp only [MeasUnzip.flowJ,
      if_pos (And.intro he (show (σ, (c : ℂ) * w) ∈ MeasUnzip.KT T' from
        ⟨hσ, mul_mem_H_of_pos hc hw⟩))]
  have hmf : Measurable fun w => MeasUnzip.flowJ hT' κ (e, (σ, (c : ℂ) * w)) :=
    (MeasUnzip.measurable_flowJ hT' κ).comp (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.mul measurable_id)))
  have hint : ∀ k, ∫ z, avgReg (ofFun (h0rev κ) + x) k z
      ∂(μ.map fun w => fwdMapInv (Wof κ T' hT' e) σ ((c : ℂ) * w)) =
      ∫ w, avgReg (ofFun (h0rev κ) + x) k (MeasUnzip.flowJ hT' κ (e, (σ, (c : ℂ) * w))) ∂μ := by
    intro k
    rw [Measure.map_congr hfl, integral_map hmf.aemeasurable
      (show Measurable fun w => avgReg (ofFun (h0rev κ) + x) k w from
        (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
  have hlog : ∫ w, Real.log ‖deriv (fun w => fwdMapInv (Wof κ T' hT' e) σ ((c : ℂ) * w)) w‖ ∂μ =
      ∫ w, (MeasUnzip.logJ hT' κ (e, (σ, (c : ℂ) * w)) + Real.log c) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw
    have hcw := mul_mem_H_of_pos hc hw
    simp only [MeasUnzip.logJ,
      if_pos (And.intro he (show (σ, (c : ℂ) * w) ∈ MeasUnzip.KT T' from ⟨hσ, hcw⟩))]
    rw [deriv_comp_mul_left, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le,
      Real.log_mul hc.ne' (norm_ne_zero_iff.2 (hne _ hcw)), add_comm]
  simp only [coordChange, evalReg, hint, hlog]
  rfl

/-- **The proxy is the regularized circle average of the dilated unzipped field.** -/
theorem AvgQc_eq_avgReg {e : C(Icc (0 : ℝ) T', ℝ)} (he : e ∈ MeasUnzip.PZ hT' κ) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) T') {c : ℝ} (hc : 0 < c) (x : FieldSample) (j : ℕ) (z : ℂ) :
    AvgQc κ hT' c σ j ((e, x), z) =
      avgReg (coordChange (ofFun (h0rev κ) + x)
        (fun w => fwdMapInv (Wof κ T' hT' e) σ ((c : ℂ) * w)) (Qc (Real.sqrt κ))) j z := by
  unfold AvgQc avgReg
  exact congrArg (limUnder atTop) (funext fun n => (RawQc_eq κ hT' he hσ hc x _ j).symm)

/-- The offset boundary density read through `AvgQc`. -/
def densQc (σ c : ℝ) (k : ℕ) (p : (C(Icc (0 : ℝ) T', ℝ) × FieldSample) × ℝ) : ℝ :=
  radius k ^ (Real.sqrt κ ^ 2 / 4) *
    Real.exp (Real.sqrt κ / 2 * AvgQc κ hT' c σ k (p.1, (p.2 : ℂ)))

/-- The dilated transported test integral, read through the proxies. -/
def IQc (u v : ℝ) (f : ℝ → ℝ) (σ c : ℝ) (k : ℕ) (p : C(Icc (0 : ℝ) T', ℝ) × FieldSample) : ℝ :=
  ∫ x, awProxy (fun y => FmR hT' κ (T' - σ) y p.1) u v f (c * x) * densQc κ hT' σ c k (p, x)

theorem measurable_densQc (σ c : ℝ) (k : ℕ) : Measurable (densQc κ hT' σ c k) := by
  unfold densQc
  refine measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul ?_))
  exact (measurable_AvgQc κ hT' c σ k).comp
    (measurable_fst.prodMk (Complex.measurable_ofReal.comp measurable_snd))

theorem measurable_IQc (u v : ℝ) {f : ℝ → ℝ} (hf : Measurable f) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) T') (c : ℝ) (k : ℕ) : Measurable (IQc κ hT' u v f σ c k) := by
  have hσ' : T' - σ ∈ Icc (0 : ℝ) T' := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hA : Measurable fun p : (C(Icc (0 : ℝ) T', ℝ) × FieldSample) × ℝ =>
      awProxy (fun y => FmR hT' κ (T' - σ) y p.1.1) u v f (c * p.2) := by
    have := measurable_awProxy (E := C(Icc (0 : ℝ) T', ℝ) × FieldSample)
      (Fe := fun p y => FmR hT' κ (T' - σ) y p.1)
      (fun y => (measurable_FmR hT' κ hσ' y).comp measurable_fst) u v hf
    exact this.comp (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  have hG := (hA.mul (measurable_densQc κ hT' σ c k)).stronglyMeasurable
  exact (hG.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

/-- **The countable offset event**: uniform Cauchy property over rational local times and
rational offsets. -/
def EvQc (u v : ℝ) (f : ℝ → ℝ) (p : C(Icc (0 : ℝ) T', ℝ) × FieldSample) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ j' : ℕ, N ≤ j' → ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) T' →
    ∀ c : ℚ, (c : ℝ) ∈ Icc (1 : ℝ) 2 → ∀ c' : ℚ, (c' : ℝ) ∈ Icc (1 : ℝ) 2 →
      |IQc κ hT' u v f σ c j p - IQc κ hT' u v f σ c' j' p| ≤ 1 / ((n : ℝ) + 1)

theorem measurableSet_EvQc (u v : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    MeasurableSet {p | EvQc κ hT' u v f p} := by
  refine measurableSet_setOfPred.2 ?_
  unfold EvQc
  refine Measurable.forall fun n => Measurable.exists fun N => Measurable.forall fun j =>
    Measurable.forall fun _ => Measurable.forall fun j' => Measurable.forall fun _ =>
    Measurable.forall fun σ => ?_
  by_cases hσ : (σ : ℝ) ∈ Icc (0 : ℝ) T'
  · simp only [hσ, true_implies]
    refine Measurable.forall fun c => ?_
    by_cases hc : (c : ℝ) ∈ Icc (1 : ℝ) 2
    · simp only [hc, true_implies]
      refine Measurable.forall fun c' => ?_
      by_cases hc' : (c' : ℝ) ∈ Icc (1 : ℝ) 2
      · simp only [hc', true_implies]
        exact measurableSet_setOfPred.1 (measurableSet_le (continuous_abs.measurable.comp
          ((measurable_IQc κ hT' u v hf hσ c j).sub (measurable_IQc κ hT' u v hf hσ c' j')))
          measurable_const)
      · simp only [hc', false_implies]
        exact measurable_const
    · simp only [hc, false_implies]
      exact measurable_const
  · simp only [hσ, false_implies]
    exact measurable_const

end SWCore
end QuantumZipper
