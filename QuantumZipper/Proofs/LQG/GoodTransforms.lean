import QuantumZipper.Proofs.LQG.AllOffsets
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Real.Pointwise

/-!
# M4-T2 (area half) and M4-T3: good samples under translation, reflection and rescaling

Deterministic statements about good samples.

* Area half of T2: `hasAreaLimit_translate`, `hasAreaLimit_reflectH`; hence
  `IsLQGGood.translate`, `IsLQGGood.reflectH`, and `qAreaMeasure_translate`,
  `qAreaMeasure_reflectH`.
* `HasBdryLimit.tendsto_nhdsGT`, `HasAreaLimit.tendsto_nhdsGT`: a limit along `a 2^{-k}`
  uniformly in `a ∈ [1,2]` is a continuum limit as `r → 0⁺`.
* M4-T3: for a good sample and every `a > 0`, `rescale x Q a` (`Q = Qc γ`) is good, with
  `ν = (·/a)_* ν_x` and `μ = (·/a)_* μ_x` (`qBoundaryMeasure_rescale`, `qAreaMeasure_rescale`),
  using `γQ/2 − γ²/4 = 1` and `γQ − γ²/2 = 2`; `scaleParam_rescale`,
  `canonical_rescale_regEq`.
-/

noncomputable section

open MeasureTheory Filter Topology Real Set
open scoped NNReal ENNReal ComplexConjugate Pointwise

namespace QuantumZipper
namespace GoodTransforms

open GoodSample RegClosure AllOffsets GaussTK

variable {x : FieldSample} {γ : ℝ}

/-! ## Preliminaries on `ℍ` -/

theorem tsupport_comp_subset {f : ℂ → ℝ} {h : ℂ → ℂ} (hh : Continuous h) :
    tsupport (f ∘ h) ⊆ h ⁻¹' tsupport f :=
  closure_minimal (fun z hz => subset_closure hz) ((isClosed_tsupport f).preimage hh)

theorem integral_H_comp_add_real (g : ℂ → ℝ) (t : ℝ) :
    ∫ z in H, g (z + t) = ∫ z in H, g z := by
  rw [← integral_indicator isOpen_H.measurableSet, ← integral_indicator isOpen_H.measurableSet]
  have e : H.indicator (fun z => g (z + t)) = fun z => H.indicator g (z + t) := by
    funext z
    by_cases hz : z ∈ H
    · have : z + t ∈ H := by
        show 0 < (z + t).im; rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hz
      rw [indicator_of_mem hz, indicator_of_mem this]
    · have : z + t ∉ H := fun h => hz (by
        have h' : 0 < (z + t).im := h
        rwa [Complex.add_im, Complex.ofReal_im, add_zero] at h')
      rw [indicator_of_notMem hz, indicator_of_notMem this]
  rw [e, integral_add_right_eq_self (fun z => H.indicator g z) (t : ℂ)]

theorem measurePreserving_neg_conj : MeasurePreserving (fun z : ℂ => -conj z) := by
  have h1 := Complex.volume_preserving_equiv_real_prod
  have h2 : MeasurePreserving (fun p : ℝ × ℝ => (-p.1, p.2)) (volume.prod volume)
      (volume.prod volume) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id volume)
  have h3 := (h1.symm Complex.measurableEquivRealProd)
  have e : (fun z : ℂ => -conj z) =
      Complex.measurableEquivRealProd.symm ∘ (fun p : ℝ × ℝ => (-p.1, p.2)) ∘
        Complex.measurableEquivRealProd := by
    funext z
    apply Complex.ext <;> simp
  rw [e]
  exact h3.comp (h2.comp h1)

theorem integral_H_comp_neg_conj (g : ℂ → ℝ) :
    ∫ z in H, g (-conj z) = ∫ z in H, g z := by
  rw [← integral_indicator isOpen_H.measurableSet, ← integral_indicator isOpen_H.measurableSet]
  have e : H.indicator (fun z => g (-conj z)) = fun z => H.indicator g (-conj z) := by
    funext z
    have hiff : -conj z ∈ H ↔ z ∈ H := by
      show 0 < (-conj z).im ↔ 0 < z.im; simp
    by_cases hz : z ∈ H
    · rw [indicator_of_mem hz, indicator_of_mem (hiff.2 hz)]
    · rw [indicator_of_notMem hz, indicator_of_notMem (fun h => hz (hiff.1 h))]
  rw [e]
  have hemb : MeasurableEmbedding (fun z : ℂ => -conj z) := by
    have : (fun z : ℂ => -conj z) =
        ((Homeomorph.neg ℂ).trans Complex.conjCLE.toHomeomorph) := by
      funext z; simp
    rw [this]; exact Homeomorph.measurableEmbedding _
  exact measurePreserving_neg_conj.integral_comp hemb _

theorem integral_H_comp_mul (g : ℂ → ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ z in H, g ((a : ℂ) * z) = (a ^ 2)⁻¹ * ∫ z in H, g z := by
  rw [← integral_indicator isOpen_H.measurableSet, ← integral_indicator isOpen_H.measurableSet]
  have e : H.indicator (fun z => g ((a : ℂ) * z)) = fun z => H.indicator g (a • z) := by
    funext z
    have hiff : a • z ∈ H ↔ z ∈ H := by
      show 0 < (a • z).im ↔ 0 < z.im
      rw [Complex.real_smul, Complex.im_ofReal_mul]
      exact ⟨fun h => pos_of_mul_pos_right h ha.le, fun h => mul_pos ha h⟩
    by_cases hz : z ∈ H
    · rw [indicator_of_mem hz, indicator_of_mem (hiff.2 hz), Complex.real_smul]
    · rw [indicator_of_notMem hz, indicator_of_notMem (fun h => hz (hiff.1 h))]
  rw [e, Measure.integral_comp_smul, Complex.finrank_real_complex, smul_eq_mul,
    abs_of_pos (by positivity)]

/-! ## Area half of M4-T2 -/

theorem areaDens_translate {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (γ t : ℝ) {r : ℝ}
    (hr : 0 < r) (z : ℂ) : areaDens γ (translate x (t : ℂ)) r z = areaDens γ x r (z + t) := by
  rw [areaDens, areaDens, (hF.translate' t).evalReg_fc z hr, hF.evalReg_fc _ hr,
    foldH_add_real]

theorem integral_areaR_translate {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (γ t : ℝ) {r : ℝ}
    (hr : 0 < r) (f : ℂ → ℝ) :
    ∫ z, f z ∂areaR γ (translate x (t : ℂ)) r = ∫ w, f (w - t) ∂areaR γ x r := by
  have hFt := hF.translate' t
  rw [areaR, areaR, integral_withDensity_ofReal (continuous_areaDens γ hFt hr).measurable
      (fun z => areaDens_nonneg γ _ hr z),
    integral_withDensity_ofReal (continuous_areaDens γ hF hr).measurable
      (fun z => areaDens_nonneg γ _ hr z)]
  simp_rw [areaDens_translate hF γ t hr]
  have h := integral_H_comp_add_real (fun w => areaDens γ x r w * f (w - t)) t
  simp only [add_sub_cancel_right] at h
  exact h

theorem areaDens_reflectH {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (γ : ℝ) {r : ℝ}
    (hr : 0 < r) (z : ℂ) :
    areaDens γ (RegClosure.reflectH x) r z = areaDens γ x r (-conj z) := by
  rw [areaDens, areaDens, hF.reflectH'.evalReg_fc z hr, hF.evalReg_fc _ hr, foldH_neg_conj]

theorem integral_areaR_reflectH {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (γ : ℝ) {r : ℝ}
    (hr : 0 < r) (f : ℂ → ℝ) :
    ∫ z, f z ∂areaR γ (RegClosure.reflectH x) r = ∫ w, f (-conj w) ∂areaR γ x r := by
  rw [areaR, areaR,
    integral_withDensity_ofReal (continuous_areaDens γ hF.reflectH' hr).measurable
      (fun z => areaDens_nonneg γ _ hr z),
    integral_withDensity_ofReal (continuous_areaDens γ hF hr).measurable
      (fun z => areaDens_nonneg γ _ hr z)]
  simp_rw [areaDens_reflectH hF γ hr]
  have h := integral_H_comp_neg_conj (fun w => areaDens γ x r w * f (-conj w))
  simp only [map_neg, Complex.conj_conj, neg_neg] at h
  exact h

/-- Transfer of `HasAreaLimit` along a homeomorphism `h` of `ℂ` preserving `ℍ`. -/
theorem hasAreaLimit_map {x' : FieldSample} {μ : Measure ℂ} (hμ : HasAreaLimit γ x μ)
    (h : ℂ ≃ₜ ℂ) (hH : ∀ z, h z ∈ H ↔ z ∈ H)
    (hint : ∀ f : ℂ → ℝ, ∀ᶠ i in goodFilter,
      ∫ z, f z ∂areaR γ x' (goodRad i) = ∫ w, f (h.symm w) ∂areaR γ x (goodRad i)) :
    HasAreaLimit γ x' (μ.map h.symm) := by
  have hmeas : Measurable h.symm := h.symm.continuous.measurable
  have hHs : ∀ z, h.symm z ∈ H ↔ z ∈ H := fun z => by
    rw [← hH (h.symm z), Homeomorph.apply_symm_apply]
  refine ⟨?_, fun K hK hKH => ?_, fun f hf hfc hfH => ?_⟩
  · rw [Measure.map_apply hmeas isOpen_H.measurableSet.compl]
    have : h.symm ⁻¹' Hᶜ = Hᶜ := by ext z; simp [hHs]
    rw [this]; exact hμ.1
  · rw [Measure.map_apply hmeas hK.isClosed.measurableSet]
    refine hμ.2.1 _ (h.symm.isCompact_preimage.2 hK) fun z hz => ?_
    exact (hHs z).1 (hKH hz)
  · rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
    have hfc' : HasCompactSupport (f ∘ h.symm) := hfc.comp_homeomorph h.symm
    have hfH' : tsupport (f ∘ h.symm) ⊆ H := fun z hz =>
      (hHs z).1 (hfH (tsupport_comp_subset h.symm.continuous hz))
    exact (hμ.2.2 _ (hf.comp h.symm.continuous) hfc' hfH').congr'
      ((hint f).mono fun i hi => hi.symm)

theorem hasAreaLimit_translate (hx : IsRegularSample x) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ x μ) (t : ℝ) :
    HasAreaLimit γ (translate x (t : ℂ)) (μ.map (· - (t : ℂ))) := by
  obtain ⟨F, hF⟩ := hx
  have := hasAreaLimit_map (x' := translate x (t : ℂ)) hμ (Homeomorph.addRight (t : ℂ))
    (fun z => show 0 < (z + t).im ↔ 0 < z.im by simp)
    (fun f => eventually_goodRad_pos.mono fun i hi => integral_areaR_translate hF γ t hi f)
  exact this

theorem hasAreaLimit_reflectH (hx : IsRegularSample x) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ x μ) :
    HasAreaLimit γ (RegClosure.reflectH x) (μ.map fun z => -conj z) := by
  obtain ⟨F, hF⟩ := hx
  set h : ℂ ≃ₜ ℂ := (Homeomorph.neg ℂ).trans Complex.conjCLE.toHomeomorph with hh
  have hcoe : ∀ z, h z = -conj z := fun z => by simp [hh]
  have hsymm : ∀ z, h.symm z = -conj z := fun z => by
    rw [Homeomorph.symm_apply_eq, hcoe]; simp
  have hmap : (fun z : ℂ => -conj z) = h.symm := funext fun z => (hsymm z).symm
  rw [hmap]
  refine hasAreaLimit_map hμ h (fun z => by rw [hcoe]; show 0 < (-conj z).im ↔ 0 < z.im; simp)
    (fun f => eventually_goodRad_pos.mono fun i hi => ?_)
  rw [integral_areaR_reflectH hF γ hi f]
  simp_rw [hsymm]

theorem _root_.QuantumZipper.IsLQGGood.translate (hx : IsLQGGood γ x) (t : ℝ) :
    IsLQGGood γ (translate x (t : ℂ)) :=
  ⟨hx.1.translate' t, ⟨_, hasBdryLimit_translate hx.1 hx.qBoundaryMeasure_spec t⟩,
    ⟨_, hasAreaLimit_translate hx.1 hx.qAreaMeasure_spec t⟩⟩

theorem _root_.QuantumZipper.IsLQGGood.reflectH (hx : IsLQGGood γ x) :
    IsLQGGood γ (RegClosure.reflectH x) :=
  ⟨hx.1.reflectH', ⟨_, hasBdryLimit_reflectH hx.1 hx.qBoundaryMeasure_spec⟩,
    ⟨_, hasAreaLimit_reflectH hx.1 hx.qAreaMeasure_spec⟩⟩

theorem qAreaMeasure_translate (hx : IsLQGGood γ x) (t : ℝ) :
    qAreaMeasure γ (translate x (t : ℂ)) = (qAreaMeasure γ x).map (· - (t : ℂ)) :=
  qAreaMeasure_eq_of_hasAreaLimit (hx.1.translate' t)
    (hasAreaLimit_translate hx.1 hx.qAreaMeasure_spec t)

theorem qAreaMeasure_reflectH (hx : IsLQGGood γ x) :
    qAreaMeasure γ (RegClosure.reflectH x) = (qAreaMeasure γ x).map fun z => -conj z :=
  qAreaMeasure_eq_of_hasAreaLimit hx.1.reflectH'
    (hasAreaLimit_reflectH hx.1 hx.qAreaMeasure_spec)

/-! ## Continuum limits -/

/-- The index `(k, a)` with `a ∈ (1, 2]` and `a 2^{-k} = r`, for `r ∈ (0, 1]`. -/
def idx (r : ℝ) : ℕ × ℝ :=
  if h : 0 < r ∧ r ≤ 1 then
    ((exists_nat_pow_near (x := 1 / r) (y := (2 : ℝ))
      ((one_le_div h.1).2 h.2) one_lt_two).choose + 1,
     r * 2 ^ ((exists_nat_pow_near (x := 1 / r) (y := (2 : ℝ))
      ((one_le_div h.1).2 h.2) one_lt_two).choose + 1))
  else (0, 1)

theorem idx_spec {r : ℝ} (h : 0 < r ∧ r ≤ 1) :
    goodRad (idx r) = r ∧ (idx r).2 ∈ Icc (1 : ℝ) 2 ∧ 1 / r < 2 ^ (idx r).1 := by
  have hs := (exists_nat_pow_near (x := 1 / r) (y := (2 : ℝ)) ((one_le_div h.1).2 h.2)
    one_lt_two).choose_spec
  set n := (exists_nat_pow_near (x := 1 / r) (y := (2 : ℝ)) ((one_le_div h.1).2 h.2)
    one_lt_two).choose
  have e : idx r = (n + 1, r * 2 ^ (n + 1)) := by simp only [idx, dif_pos h]; rfl
  rw [e]
  refine ⟨?_, ⟨?_, ?_⟩, hs.2⟩
  · simp only [goodRad, radius]
    rw [mul_assoc, ← mul_pow]; norm_num
  · have := hs.2
    rw [div_lt_iff₀ h.1] at this; linarith
  · have := hs.1
    rw [le_div_iff₀ h.1] at this
    show r * 2 ^ (n + 1) ≤ 2
    rw [pow_succ]; nlinarith

theorem tendsto_idx : Tendsto idx (𝓝[>] 0) goodFilter := by
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r ≤ 1 :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT one_pos) fun r hr => ⟨hr.1, hr.2.le⟩
  refine Tendsto.prodMk ?_ (tendsto_principal.2 (hev.mono fun r hr => (idx_spec hr).2.1))
  refine tendsto_atTop.2 fun K => ?_
  have hK : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < (2 ^ K)⁻¹ :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT (inv_pos.2 (by positivity : (0 : ℝ) < 2 ^ K)))
      fun r hr => hr.2
  filter_upwards [hev, hK] with r hr hrK
  have h1 := (idx_spec hr).2.2
  have h2 : (2 : ℝ) ^ K < 1 / r := by
    rw [lt_div_iff₀ hr.1]; rw [lt_inv_comm₀ hr.1 (by positivity)] at hrK
    calc (2 : ℝ) ^ K * r < (1 / r) * r := mul_lt_mul_of_pos_right (by rwa [one_div]) hr.1
      _ = 1 := by rw [one_div, inv_mul_cancel₀ hr.1.ne']
  exact (pow_lt_pow_iff_right₀ one_lt_two).1 (h2.trans h1) |>.le

theorem HasBdryLimit.tendsto_nhdsGT {ν : Measure ℝ} (h : HasBdryLimit γ x ν) {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun r => ∫ t, f t ∂bdryR γ x r) (𝓝[>] 0) (𝓝 (∫ t, f t ∂ν)) := by
  refine ((h.2 f hf hfc).comp tendsto_idx).congr' ?_
  filter_upwards [(Ioo_mem_nhdsGT one_pos : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)] with r hr
  simp only [Function.comp, (idx_spec ⟨hr.1, hr.2.le⟩).1]

theorem HasAreaLimit.tendsto_nhdsGT {μ : Measure ℂ} (h : HasAreaLimit γ x μ) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfH : tsupport f ⊆ H) :
    Tendsto (fun r => ∫ z, f z ∂areaR γ x r) (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ)) := by
  refine ((h.2.2 f hf hfc hfH).comp tendsto_idx).congr' ?_
  filter_upwards [(Ioo_mem_nhdsGT one_pos : Ioo (0 : ℝ) 1 ∈ 𝓝[>] 0)] with r hr
  simp only [Function.comp, (idx_spec ⟨hr.1, hr.2.le⟩).1]

theorem tendsto_mul_goodRad {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => a * goodRad i) goodFilter (𝓝[>] 0) := by
  have h := tendsto_goodRad
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_goodRad_pos.mono fun i hi => mul_pos ha hi⟩
  have := (tendsto_nhdsWithin_iff.1 h).1.const_mul a
  rwa [mul_zero] at this

/-! ## M4-T3: rescaling -/

theorem gammaQ_bdry {γ : ℝ} (hγ : 0 < γ) : γ / 2 * Qc γ = 1 + γ ^ 2 / 4 := by
  unfold Qc; field_simp; ring

theorem gammaQ_area {γ : ℝ} (hγ : 0 < γ) : γ * Qc γ = 2 + γ ^ 2 / 2 := by
  unfold Qc; field_simp

theorem bdryDens_rescale {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (hγ : 0 < γ) {a : ℝ}
    (ha : 0 < a) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    bdryDens γ (rescale x (Qc γ) a) r t = a * bdryDens γ x (a * r) (a * t) := by
  rw [bdryDens, bdryDens, (hF.rescale' (Qc γ) ha).evalReg_fc_of_mem (ofReal_mem_Hbar t) hr,
    hF.evalReg_fc_of_mem (ofReal_mem_Hbar _) (mul_pos ha hr)]
  simp only [Complex.ofReal_mul]
  have hQ : exp (γ / 2 * (Qc γ * Real.log a)) = a * a ^ (γ ^ 2 / 4) := by
    have h1 := gammaQ_bdry hγ
    rw [rpow_def_of_pos ha, show γ / 2 * (Qc γ * Real.log a) =
      Real.log a + Real.log a * (γ ^ 2 / 4) by linear_combination (Real.log a) * h1,
      exp_add, exp_log ha]
  rw [mul_rpow ha.le hr.le, mul_add, exp_add, hQ]; ring

theorem integral_bdryR_rescale {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (hγ : 0 < γ) {a : ℝ}
    (ha : 0 < a) {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ t, f t ∂bdryR γ (rescale x (Qc γ) a) r = ∫ u, f (u / a) ∂bdryR γ x (a * r) := by
  have hFa := hF.rescale' (Qc γ) ha
  rw [bdryR, bdryR, integral_withDensity_ofReal (continuous_bdryDens γ hFa hr).measurable
      (fun s => bdryDens_nonneg γ _ hr s),
    integral_withDensity_ofReal (continuous_bdryDens γ hF (mul_pos ha hr)).measurable
      (fun s => bdryDens_nonneg γ _ (mul_pos ha hr) s)]
  simp_rw [bdryDens_rescale hF hγ ha hr]
  have h := Measure.integral_comp_mul_left (fun u => bdryDens γ x (a * r) u * f (u / a)) a
  simp only [mul_div_cancel_left₀ _ ha.ne', smul_eq_mul, abs_inv, abs_of_pos ha] at h
  have e : ∫ t, a * bdryDens γ x (a * r) (a * t) * f t =
      a * ∫ t, bdryDens γ x (a * r) (a * t) * f t := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  rw [e, h]; field_simp

theorem areaDens_rescale {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (hγ : 0 < γ) {a : ℝ}
    (ha : 0 < a) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    areaDens γ (rescale x (Qc γ) a) r z = a ^ 2 * areaDens γ x (a * r) ((a : ℂ) * z) := by
  rw [areaDens, areaDens, (hF.rescale' (Qc γ) ha).evalReg_fc z hr,
    hF.evalReg_fc _ (mul_pos ha hr), foldH_mul_pos _ ha]
  dsimp only
  have hQ : exp (γ * (Qc γ * Real.log a)) = a ^ 2 * a ^ (γ ^ 2 / 2) := by
    have h1 := gammaQ_area hγ
    rw [rpow_def_of_pos ha, show γ * (Qc γ * Real.log a) =
      Real.log (a ^ 2) + Real.log a * (γ ^ 2 / 2) by
        rw [Real.log_pow]; push_cast; linear_combination (Real.log a) * h1,
      exp_add, exp_log (by positivity)]
  rw [mul_rpow ha.le hr.le, mul_add, exp_add, hQ]; ring

theorem integral_areaR_rescale {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (hγ : 0 < γ) {a : ℝ}
    (ha : 0 < a) {r : ℝ} (hr : 0 < r) (f : ℂ → ℝ) :
    ∫ z, f z ∂areaR γ (rescale x (Qc γ) a) r = ∫ w, f (w / a) ∂areaR γ x (a * r) := by
  have hFa := hF.rescale' (Qc γ) ha
  rw [areaR, areaR, integral_withDensity_ofReal (continuous_areaDens γ hFa hr).measurable
      (fun s => areaDens_nonneg γ _ hr s),
    integral_withDensity_ofReal (continuous_areaDens γ hF (mul_pos ha hr)).measurable
      (fun s => areaDens_nonneg γ _ (mul_pos ha hr) s)]
  simp_rw [areaDens_rescale hF hγ ha hr]
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h := integral_H_comp_mul (fun w => areaDens γ x (a * r) w * f (w / a)) ha
  simp only [mul_div_cancel_left₀ _ hac] at h
  have e : ∫ z in H, a ^ 2 * areaDens γ x (a * r) ((a : ℂ) * z) * f z =
      a ^ 2 * ∫ z in H, areaDens γ x (a * r) ((a : ℂ) * z) * f z := by
    rw [← integral_const_mul]; congr 1; funext z; ring
  rw [e, h]; field_simp

theorem hasBdryLimit_rescale (hx : IsRegularSample x) (hγ : 0 < γ) {ν : Measure ℝ}
    (hν : HasBdryLimit γ x ν) {a : ℝ} (ha : 0 < a) :
    HasBdryLimit γ (rescale x (Qc γ) a) (ν.map fun u => u / a) := by
  obtain ⟨F, hF⟩ := hx
  have := hν.1
  have hmeas : Measurable (fun u : ℝ => u / a) := measurable_id.div_const a
  have hK : ∀ K : Set ℝ, IsCompact K → IsCompact ((fun u : ℝ => u / a) ⁻¹' K) := fun K hK => by
    have : (fun u : ℝ => u / a) ⁻¹' K = (fun v => a * v) '' K := by
      ext u; constructor
      · intro hu; exact ⟨u / a, hu, by field_simp⟩
      · rintro ⟨v, hv, rfl⟩; show a * v / a ∈ K; rwa [mul_div_cancel_left₀ _ ha.ne']
    rw [this]; exact hK.image (continuous_const_mul a)
  have : IsFiniteMeasureOnCompacts (ν.map fun u => u / a) := ⟨fun K hKc => by
    rw [Measure.map_apply hmeas hKc.isClosed.measurableSet]
    exact (hK K hKc).measure_lt_top⟩
  refine ⟨inferInstance, fun f hf hfc => ?_⟩
  rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
  have hfc' : HasCompactSupport (fun u => f (u / a)) := by
    have hh : (fun u : ℝ => u / a) = (Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne')) := by
      funext u; simp [div_eq_mul_inv]
    have := hfc.comp_homeomorph (Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne'))
    rw [← hh] at this; exact this
  have ht := (HasBdryLimit.tendsto_nhdsGT hν (hf.comp (continuous_id.div_const a)) hfc').comp
    (tendsto_mul_goodRad ha)
  refine ht.congr' (eventually_goodRad_pos.mono fun i hi => ?_)
  exact (integral_bdryR_rescale hF hγ ha hi f).symm

theorem hasAreaLimit_rescale (hx : IsRegularSample x) (hγ : 0 < γ) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ x μ) {a : ℝ} (ha : 0 < a) :
    HasAreaLimit γ (rescale x (Qc γ) a) (μ.map fun z : ℂ => z / (a : ℂ)) := by
  obtain ⟨F, hF⟩ := hx
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set h : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ (a : ℂ) hac with hh
  have hsymm : ∀ z, h.symm z = z / a := fun z => by simp [hh, div_eq_inv_mul]
  have hmap : (fun z : ℂ => z / (a : ℂ)) = h.symm := funext fun z => (hsymm z).symm
  rw [hmap]
  have hH : ∀ z, h.symm z ∈ H ↔ z ∈ H := fun z => by
    rw [hsymm]
    show 0 < (z / (a : ℂ)).im ↔ 0 < z.im
    rw [Complex.div_ofReal_im]
    exact ⟨fun h => by have := mul_pos h ha; rwa [div_mul_cancel₀ _ ha.ne'] at this,
      fun h => div_pos h ha⟩
  have hmeas : Measurable h.symm := h.symm.continuous.measurable
  refine ⟨?_, fun K hK hKH => ?_, fun f hf hfc hfH => ?_⟩
  · rw [Measure.map_apply hmeas isOpen_H.measurableSet.compl]
    have : h.symm ⁻¹' Hᶜ = Hᶜ := by ext z; simp [hH]
    rw [this]; exact hμ.1
  · rw [Measure.map_apply hmeas hK.isClosed.measurableSet]
    exact hμ.2.1 _ (h.symm.isCompact_preimage.2 hK) fun z hz => (hH z).1 (hKH hz)
  · rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
    have hfc' : HasCompactSupport (f ∘ h.symm) := hfc.comp_homeomorph h.symm
    have hfH' : tsupport (f ∘ h.symm) ⊆ H := fun z hz =>
      (hH z).1 (hfH (tsupport_comp_subset h.symm.continuous hz))
    have ht := (HasAreaLimit.tendsto_nhdsGT hμ (hf.comp h.symm.continuous) hfc' hfH').comp
      (tendsto_mul_goodRad ha)
    refine ht.congr' (eventually_goodRad_pos.mono fun i hi => ?_)
    simp only [Function.comp]
    rw [integral_areaR_rescale hF hγ ha hi f]
    simp_rw [hsymm]

theorem _root_.QuantumZipper.IsLQGGood.rescale (hx : IsLQGGood γ x) (hγ : 0 < γ) {a : ℝ}
    (ha : 0 < a) : IsLQGGood γ (rescale x (Qc γ) a) :=
  ⟨hx.1.rescale' (Qc γ) ha, ⟨_, hasBdryLimit_rescale hx.1 hγ hx.qBoundaryMeasure_spec ha⟩,
    ⟨_, hasAreaLimit_rescale hx.1 hγ hx.qAreaMeasure_spec ha⟩⟩

/-- **M4-T3 (boundary)**: `ν_{rescale x Q a} = (·/a)_* ν_x`, for every `a > 0`. -/
theorem qBoundaryMeasure_rescale (hx : IsLQGGood γ x) (hγ : 0 < γ) {a : ℝ} (ha : 0 < a) :
    qBoundaryMeasure γ (rescale x (Qc γ) a) = (qBoundaryMeasure γ x).map fun u => u / a :=
  qBoundaryMeasure_eq_of_hasBdryLimit (hx.1.rescale' (Qc γ) ha)
    (hasBdryLimit_rescale hx.1 hγ hx.qBoundaryMeasure_spec ha)

/-- **M4-T3 (area)**: `μ_{rescale x Q a} = (·/a)_* μ_x`, for every `a > 0`. -/
theorem qAreaMeasure_rescale (hx : IsLQGGood γ x) (hγ : 0 < γ) {a : ℝ} (ha : 0 < a) :
    qAreaMeasure γ (rescale x (Qc γ) a) = (qAreaMeasure γ x).map fun z : ℂ => z / (a : ℂ) :=
  qAreaMeasure_eq_of_hasAreaLimit (hx.1.rescale' (Qc γ) ha)
    (hasAreaLimit_rescale hx.1 hγ hx.qAreaMeasure_spec ha)

theorem preimage_div_ball_inter_H {a b : ℝ} (hb : 0 < b) :
    (fun z : ℂ => z / b) ⁻¹' (Metric.ball 0 a ∩ H) = Metric.ball 0 (a * b) ∩ H := by
  ext z
  simp only [mem_preimage, mem_inter_iff, Metric.mem_ball, dist_zero_right]
  have hbn : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb.le]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [norm_div, hbn, div_lt_iff₀ hb] at h1; exact h1
    · have : 0 < (z / (b : ℂ)).im := h2
      rw [Complex.div_ofReal_im] at this
      show 0 < z.im
      have := mul_pos this hb; rwa [div_mul_cancel₀ _ hb.ne'] at this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [norm_div, hbn, div_lt_iff₀ hb]; exact h1
    · show 0 < (z / (b : ℂ)).im
      rw [Complex.div_ofReal_im]; exact div_pos h2 hb

/-- **M4-T3 consequence**: `scaleParam γ (rescale x Q b) = scaleParam γ x / b`. -/
theorem scaleParam_rescale (hx : IsLQGGood γ x) (hγ : 0 < γ) {b : ℝ} (hb : 0 < b) :
    scaleParam γ (rescale x (Qc γ) b) = scaleParam γ x / b := by
  unfold scaleParam
  rw [qAreaMeasure_rescale hx hγ hb]
  have hmeas : Measurable (fun z : ℂ => z / (b : ℂ)) := measurable_id.div_const _
  have e : {a : ℝ | 0 < a ∧ 1 ≤ ((qAreaMeasure γ x).map fun z : ℂ => z / (b : ℂ))
      (Metric.ball (0 : ℂ) a ∩ H)} =
      b⁻¹ • {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ x (Metric.ball (0 : ℂ) a ∩ H)} := by
    ext a
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hb.ne'), inv_inv, smul_eq_mul]
    simp only [mem_setOf_eq]
    rw [Measure.map_apply hmeas (Metric.isOpen_ball.inter isOpen_H).measurableSet,
      preimage_div_ball_inter_H hb, mul_comm b a]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨mul_pos h1 hb, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨pos_of_mul_pos_left h1 hb.le, h2⟩
  rw [e, Real.sInf_smul_of_nonneg (inv_nonneg.2 hb.le), smul_eq_mul, div_eq_inv_mul]

end GoodTransforms
end QuantumZipper
