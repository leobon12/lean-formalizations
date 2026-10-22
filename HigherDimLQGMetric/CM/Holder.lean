import HigherDimLQGMetric.CM.Norm
import LQGMetric.Dimension.GMCMomentPos2Exp
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Gaussian exponential moments and the Cameron–Martin event bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Exponential moment of a centered Gaussian density. -/
private theorem cmDensityMoment {Y : Ω → ℝ} (hY : HasGaussianLaw Y P)
    (hY0 : ∫ ω, Y ω ∂P = 0) (p : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (p * (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2))) ∂P =
      ENNReal.ofReal (Real.exp ((p ^ 2 - p) * (∫ ω, Y ω ^ 2 ∂P) / 2)) := by
  have hY2 : Var[Y; P] = ∫ ω, Y ω ^ 2 ∂P := by
    rw [variance_eq_sub hY.memLp_two, hY0]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
    congr 1
  obtain ⟨hi, hm⟩ := LQGMetric.DGMC.integral_exp_mul_of_hasGaussianLaw hY hY0 p
  rw [hY2] at hm
  have hm' : ∫⁻ ω, ENNReal.ofReal (Real.exp (p * Y ω)) ∂P =
      ENNReal.ofReal (Real.exp (p ^ 2 * (∫ ω, Y ω ^ 2 ∂P) / 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun ω => (Real.exp_pos _).le), hm]
  have he (ω : Ω) :
      Real.exp (p * (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2)) =
        Real.exp (p * Y ω) * Real.exp (-(p * (∫ ω', Y ω' ^ 2 ∂P) / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  simp_rw [he, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (p * Y ω))) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.measurable_exp.comp_aemeasurable (hY.aemeasurable.const_mul p))
  rw [lintegral_mul_const'' _ hmeas]
  rw [hm', ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 1
  ring_nf

/-- Hölder's inequality with the exact centered Gaussian moment. -/
private theorem cmEventHolder {Y : Ω → ℝ} (hY : HasGaussianLaw Y P)
    (hY0 : ∫ ω, Y ω ∂P = 0) {C p : ℝ} (hC : ∫ ω, Y ω ^ 2 ∂P ≤ C ^ 2)
    (hp : 1 < p) (E : Set Ω) (hE : MeasurableSet E) :
    (∫⁻ ω, E.indicator (fun _ => (1 : ℝ≥0∞)) ω *
      ENNReal.ofReal (Real.exp (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2)) ∂P) ≤
        ENNReal.ofReal (Real.exp ((p - 1) / 2 * C ^ 2)) * P E ^ (1 - p⁻¹) := by
  let q := p.conjExponent
  have hpq : q.HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
  have hqpos : 0 < q := hpq.pos
  have hqrec : 1 / q = 1 - p⁻¹ := by
    have hiff := (Real.holderConjugate_iff.mp hpq).2
    rw [one_div]
    linarith
  let D : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2))
  have hDm : AEMeasurable D P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.measurable_exp.comp_aemeasurable (hY.aemeasurable.sub_const _))
  have hIm : AEMeasurable (E.indicator fun _ => (1 : ℝ≥0∞)) P :=
    (measurable_const.indicator hE).aemeasurable
  have hIp : (∫⁻ ω, (E.indicator (fun _ => (1 : ℝ≥0∞)) ω) ^ q ∂P) = P E := by
    rw [← lintegral_indicator_one hE]
    apply lintegral_congr
    intro ω
    classical
    by_cases hω : ω ∈ E <;> simp [hω, hqpos]
  have hDp : (∫⁻ ω, D ω ^ p ∂P) =
      ENNReal.ofReal (Real.exp ((p ^ 2 - p) * (∫ ω, Y ω ^ 2 ∂P) / 2)) := by
    calc
      (∫⁻ ω, D ω ^ p ∂P) =
          ∫⁻ ω, ENNReal.ofReal (Real.exp (p * (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2))) ∂P := by
            apply lintegral_congr
            intro ω
            change (ENNReal.ofReal (Real.exp (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2))) ^ p = _
            rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by linarith : 0 ≤ p),
              ← Real.exp_mul]
            congr 1
            ring_nf
      _ = _ := cmDensityMoment hY hY0 p
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hIm hDm
  simp only [Pi.mul_apply] at hH
  rw [hIp, hDp, hqrec] at hH
  have hpe : (ENNReal.ofReal
      (Real.exp ((p ^ 2 - p) * (∫ ω, Y ω ^ 2 ∂P) / 2))) ^ (1 / p) =
      ENNReal.ofReal (Real.exp ((p - 1) / 2 * (∫ ω, Y ω ^ 2 ∂P))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
      ← Real.exp_mul]
    congr 1
    field_simp
  rw [hpe] at hH
  calc
    _ ≤ P E ^ (1 - p⁻¹) *
      ENNReal.ofReal (Real.exp ((p - 1) / 2 * (∫ ω, Y ω ^ 2 ∂P))) := hH
    _ ≤ P E ^ (1 - p⁻¹) * ENNReal.ofReal (Real.exp ((p - 1) / 2 * C ^ 2)) := by
      gcongr
    _ = _ := mul_comm _ _

variable {d : ℕ}

/-- The deterministic translation on mean-zero pairing paths. -/
def cmShiftPath (F : C(Rd d, ℝ)) (a : TestRd0 d → ℝ) : TestRd0 d → ℝ :=
  fun φ => a φ + ∫ x, F x * φ.1 x

theorem measurable_cmShiftPath (F : C(Rd d, ℝ)) : Measurable (cmShiftPath F) :=
  measurable_pi_iff.mpr fun φ => (measurable_pi_apply φ).add_const _

theorem cmShiftPath_pair0 (g : DistRd d) (F : C(Rd d, ℝ)) :
    cmShiftPath F (pair0Rd g) = pair0Rd (addFun g F) := by
  funext φ
  exact (cmPair0_addFun g F φ).symm

private theorem cmShiftPath_neg_pair0 (g : DistRd d) (F : C(Rd d, ℝ)) :
    cmShiftPath F (pair0Rd (addFun g (-F))) = pair0Rd g := by
  funext φ
  rw [cmShiftPath, cmPair0_addFun]
  have hi : Integrable (fun x => F x * φ.1 x) :=
    (F.continuous.mul φ.1.continuous).integrable_of_hasCompactSupport
      φ.1.hasCompactSupport.mul_left
  have he : (∫ x, (-F) x * φ.1 x) = -∫ x, F x * φ.1 x := by
    simp only [ContinuousMap.neg_apply, neg_mul, integral_neg]
  rw [he]
  simp [pair0Rd]

theorem lemma71_pair0 {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (F : C(Rd d, ℝ)) {C pH : ℝ} (hF : IsCMBounded F C) (hp : 1 < pH)
    (A : Set (TestRd0 d → ℝ)) (hA : MeasurableSet A) :
    P {ω | pair0Rd (h ω) ∈ A} ≤
      ENNReal.ofReal (Real.exp ((pH - 1) / 2 * C ^ 2)) *
        P {ω | pair0Rd (addFun (h ω) F) ∈ A} ^ (1 - pH⁻¹) := by
  have hneg : IsCMBounded (-F) C := by
    convert hF.mul_const (-1) using 1
    · funext x
      simp
    · simp
  obtain ⟨Y, hYm, hY2, _, hYgp, hY0, hformula⟩ :=
    lgf_cameronMartin_aug hh (-F) hneg
  let A' : Set (TestRd0 d → ℝ) := (cmShiftPath F) ⁻¹' A
  have hA' : MeasurableSet A' := hA.preimage (measurable_cmShiftPath F)
  have hΦ : Measurable (A'.indicator fun _ => (1 : ℝ≥0∞)) :=
    measurable_const.indicator hA'
  have hmeasBase : Measurable (fun ω => pair0Rd (h ω)) :=
    measurable_pi_iff.mpr fun φ => (measurable_distOn_apply φ.1).comp hh.measurable
  have hmeasShift : Measurable (fun ω => pair0Rd (addFun (h ω) F)) := by
    rw [show (fun ω => pair0Rd (addFun (h ω) F)) =
      cmShiftPath F ∘ (fun ω => pair0Rd (h ω)) from by
        funext ω; exact (cmShiftPath_pair0 (h ω) F).symm]
    exact (measurable_cmShiftPath F).comp hmeasBase
  have hE : MeasurableSet {ω | pair0Rd (addFun (h ω) F) ∈ A} :=
    hA.preimage hmeasShift
  have hE0 : MeasurableSet {ω | pair0Rd (h ω) ∈ A} := hA.preimage hmeasBase
  have heq := hformula (A'.indicator fun _ => (1 : ℝ≥0∞)) hΦ
  have hleft : (∫⁻ ω, A'.indicator (fun _ => (1 : ℝ≥0∞))
      (pair0Rd (addFun (h ω) (-F))) ∂P) = P {ω | pair0Rd (h ω) ∈ A} := by
    rw [← lintegral_indicator_one hE0]
    apply lintegral_congr
    intro ω
    have e : (cmShiftPath F (pair0Rd (addFun (h ω) (-F))) ∈ A) ↔
        pair0Rd (h ω) ∈ A := by rw [cmShiftPath_neg_pair0]
    classical
    by_cases hω : pair0Rd (h ω) ∈ A <;> simp [A', e, hω]
  have hright : (∫⁻ ω, A'.indicator (fun _ => (1 : ℝ≥0∞)) (pair0Rd (h ω)) *
      ENNReal.ofReal (Real.exp (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2)) ∂P) =
      ∫⁻ ω, ({ω | pair0Rd (addFun (h ω) F) ∈ A} : Set Ω).indicator
        (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (Real.exp (Y ω - (∫ ω', Y ω' ^ 2 ∂P) / 2)) ∂P := by
    apply lintegral_congr
    intro ω
    have e : (cmShiftPath F (pair0Rd (h ω)) ∈ A) ↔
        pair0Rd (addFun (h ω) F) ∈ A := by rw [cmShiftPath_pair0]
    classical
    by_cases hω : pair0Rd (addFun (h ω) F) ∈ A <;> simp [A', e, hω]
  rw [hleft, hright] at heq
  rw [heq]
  exact cmEventHolder (hYgp.hasGaussianLaw_eval (Sum.inl ())) hY0 hY2 hp _ hE

theorem lemma71_pair0_reverse {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    (F : C(Rd d, ℝ)) {C pH : ℝ} (hF : IsCMBounded F C) (hp : 1 < pH)
    (A : Set (TestRd0 d → ℝ)) (hA : MeasurableSet A) :
    P {ω | pair0Rd (addFun (h ω) F) ∈ A} ≤
      ENNReal.ofReal (Real.exp ((pH - 1) / 2 * C ^ 2)) *
        P {ω | pair0Rd (h ω) ∈ A} ^ (1 - pH⁻¹) := by
  have hneg : IsCMBounded (-F) C := by
    convert hF.mul_const (-1) using 1
    · funext x
      simp
    · simp
  let A' : Set (TestRd0 d → ℝ) := (cmShiftPath F) ⁻¹' A
  have hA' : MeasurableSet A' := hA.preimage (measurable_cmShiftPath F)
  have hbound := lemma71_pair0 hh (-F) hneg hp A' hA'
  have hleft : {ω | pair0Rd (h ω) ∈ A'} =
      {ω | pair0Rd (addFun (h ω) F) ∈ A} := by
    ext ω
    change cmShiftPath F (pair0Rd (h ω)) ∈ A ↔ _
    rw [cmShiftPath_pair0]
    rfl
  have hright : {ω | pair0Rd (addFun (h ω) (-F)) ∈ A'} =
      {ω | pair0Rd (h ω) ∈ A} := by
    ext ω
    change cmShiftPath F (pair0Rd (addFun (h ω) (-F))) ∈ A ↔ _
    rw [cmShiftPath_neg_pair0]
    rfl
  rwa [hleft, hright] at hbound

/-- Lemma 7.1 for the normalized LGF. The dimension hypothesis ensures that the spherical
normalization is a probability average and converges almost surely. -/
theorem lemma71 (hd : 2 ≤ d) {h : Ω → DistRd d} (hh : IsNormalizedLGF h P)
    (F : C(Rd d, ℝ)) {C pH : ℝ} (hF : IsCMBounded F C) (hp : 1 < pH)
    (A : Set (DistRd d)) (hA : MeasurableSet A) :
    P {ω | h ω ∈ A} ≤ ENNReal.ofReal (Real.exp ((pH - 1) / 2 * C ^ 2)) *
      P {ω | shiftNorm (h ω) F ∈ A} ^ (1 - pH⁻¹) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨A0, hA0, hrepr⟩ := exists_pair0_event_of_normalized hd1 A hA
  have hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d :=
    hh.1.ae_exists_tendsto_sphereAvgSeq hd (by norm_num) 0
  have hbase : {ω | h ω ∈ A} =ᵐ[P] {ω | pair0Rd (h ω) ∈ A0} := by
    filter_upwards [hconv, hh.2] with ω hc hn
    exact propext (hrepr (h ω) hc hn)
  have hshift : {ω | shiftNorm (h ω) F ∈ A} =ᵐ[P]
      {ω | pair0Rd (addFun (h ω) F) ∈ A0} := by
    filter_upwards [hconv, hh.2] with ω hc hn
    rw [← pair0Rd_shiftNorm]
    exact propext (hrepr (shiftNorm (h ω) F) (shiftNorm_mem_convSet hd1 hc F)
      (sphereAvg_shiftNorm_zero hd1 hc hn F))
  rw [measure_congr hbase, measure_congr hshift]
  exact lemma71_pair0 hh.1 F hF hp A0 hA0

private theorem lemma71_reverse (hd : 2 ≤ d) {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) (F : C(Rd d, ℝ)) {C pH : ℝ}
    (hF : IsCMBounded F C) (hp : 1 < pH) (A : Set (DistRd d))
    (hA : MeasurableSet A) :
    P {ω | shiftNorm (h ω) F ∈ A} ≤
      ENNReal.ofReal (Real.exp ((pH - 1) / 2 * C ^ 2)) *
        P {ω | h ω ∈ A} ^ (1 - pH⁻¹) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨A0, hA0, hrepr⟩ := exists_pair0_event_of_normalized hd1 A hA
  have hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d :=
    hh.1.ae_exists_tendsto_sphereAvgSeq hd (by norm_num) 0
  have hbase : {ω | h ω ∈ A} =ᵐ[P] {ω | pair0Rd (h ω) ∈ A0} := by
    filter_upwards [hconv, hh.2] with ω hc hn
    exact propext (hrepr (h ω) hc hn)
  have hshift : {ω | shiftNorm (h ω) F ∈ A} =ᵐ[P]
      {ω | pair0Rd (addFun (h ω) F) ∈ A0} := by
    filter_upwards [hconv, hh.2] with ω hc hn
    rw [← pair0Rd_shiftNorm]
    exact propext (hrepr (shiftNorm (h ω) F) (shiftNorm_mem_convSet hd1 hc F)
      (sphereAvg_shiftNorm_zero hd1 hc hn F))
  rw [measure_congr hbase, measure_congr hshift]
  exact lemma71_pair0_reverse hh.1 F hF hp A0 hA0

/-- Mutual absolute continuity of the normalized LGF and its Cameron–Martin shift.
The dimension hypothesis is necessary for the sphere normalization. -/
theorem map_shiftNorm_ac (hd : 2 ≤ d) {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) (F : C(Rd d, ℝ)) {C : ℝ}
    (hF : IsCMBounded F C) :
    P.map (fun ω => shiftNorm (h ω) F) ≪ P.map h ∧
      P.map h ≪ P.map (fun ω => shiftNorm (h ω) F) := by
  have hmShift : Measurable (fun ω => shiftNorm (h ω) F) :=
    (measurable_addConst_left _).comp
      ((measurable_addFun_left F).comp hh.1.measurable)
  constructor
  · apply Measure.AbsolutelyContinuous.mk
    intro A hA hzero
    rw [Measure.map_apply hh.1.measurable hA] at hzero
    rw [Measure.map_apply hmShift hA]
    have hbound := lemma71_reverse hd hh F hF (by norm_num : 1 < (2 : ℝ)) A hA
    have hz : P {ω | h ω ∈ A} = 0 := hzero
    rw [hz] at hbound
    norm_num at hbound
    exact hbound
  · apply Measure.AbsolutelyContinuous.mk
    intro A hA hzero
    rw [Measure.map_apply hmShift hA] at hzero
    rw [Measure.map_apply hh.1.measurable hA]
    have hbound := lemma71 hd hh F hF (by norm_num : 1 < (2 : ℝ)) A hA
    have hz : P {ω | shiftNorm (h ω) F ∈ A} = 0 := hzero
    rw [hz] at hbound
    norm_num at hbound
    exact hbound

end HigherDimLQGMetric
