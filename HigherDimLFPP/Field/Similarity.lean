import HigherDimLFPP.Field.LogCov

/-!
# Similarity invariance of the band covariances (packet P-F2, target T3)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.1 ("`H_{ra,rb} ∘ T` has the law of
`H_{a,b}`"; "the all-scale covariance is exactly invariant under similarities on mass-zero
measures"); planning audit HA2 (`planning/audits/HA2-section-3.md`), finding HA2-05, Details D2
(Lemma D2.2) and the Lean block (c) (`simMap`, `SimilarityCov`); interface (I3) of HA3 §7.
HA2's `simMap x r O` is named `simAffine x r O` here, because `HigherDimLFPP.simMap O x₀ r`
(other argument order) is defined in `HigherDimLFPP/Paths/Compare.lean`; the two are
definitionally equal: `simAffine x r O = simMap O x r`.

For the similarity `T z = x + r O z` (`O` a linear isometry, `r > 0`):

* `scalePair_map_simAffine`: `scalePair κ t (T_*μ) … = r⁻¹ scalePair κ (t/r) μ …` (radiality of `C`);
* `isPairable_map_simAffine_iff`: `IsPairable κ S (T_*μ) (T_*ν) ↔ IsPairable κ (r⁻¹ • S) μ ν`;
* `scaleCov_map_simAffine` (HA2-05's measure-level identity):
  `scaleCov κ S (T_*μ) (T_*ν) (T_*μ') (T_*ν') = scaleCov κ (r⁻¹ • S) μ ν μ' ν'`, for all finite
  measures and measurable `S ⊆ (0, ∞)` (no pairability hypothesis: both sides are the junk `0`
  simultaneously);
* `scaleCov_map_simAffine_Ioi`: exact invariance of the all-scale covariance;
* `logCov_map_simAffine`: `logCov (T_*μ) (T_*ν) (T_*μ') (T_*ν') = logCov μ ν μ' ν'` for log-pairable
  measures with `μ(ℝ^d) = ν(ℝ^d)` (directly from `log|Tz - Tw| = log r + log|z - w|`).

2D template: `LQGDimension/LFPP/SimilarityCov.lean` (`similarityCov`, `SimCov.similarityCov_logCov`)
for finite segment combinations in `ℂ`; here for finite measures on `ℝ^d` and every scale set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Pointwise

namespace HigherDimLFPP

variable {d : ℕ}

/-- The similarity `z ↦ x + r O z` (HA2's `simMap x r O`). -/
def simAffine (x : Rd d) (r : ℝ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (z : Rd d) : Rd d := x + r • O z

theorem simAffine_sub (x : Rd d) (r : ℝ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (z w : Rd d) :
    simAffine x r O z - simAffine x r O w = r • O (z - w) := by
  simp only [simAffine, map_sub, smul_sub]
  abel

theorem continuous_simAffine (x : Rd d) (r : ℝ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) :
    Continuous (simAffine x r O) :=
  continuous_const.add (O.continuous.const_smul r)

theorem measurable_simAffine (x : Rd d) (r : ℝ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) :
    Measurable (simAffine x r O) :=
  (continuous_simAffine x r O).measurable

theorem norm_simAffine_sub (x : Rd d) {r : ℝ} (hr : 0 < r) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (z w : Rd d) :
    ‖simAffine x r O z - simAffine x r O w‖ = r * ‖z - w‖ := by
  rw [simAffine_sub, norm_smul, O.norm_map, Real.norm_of_nonneg hr.le]

/-! ### Rescaled scale sets -/

theorem FieldAux.measurableSet_inv_smul {r : ℝ} {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (r⁻¹ • S) :=
  hS.const_smul₀ r⁻¹

theorem FieldAux.inv_smul_subset_Ioi {r : ℝ} (hr : 0 < r) {S : Set ℝ} (hS0 : S ⊆ Ioi 0) :
    r⁻¹ • S ⊆ Ioi 0 := by
  rintro s ⟨t, ht, rfl⟩
  show 0 < r⁻¹ * t
  exact mul_pos (inv_pos.2 hr) (hS0 ht)

theorem FieldAux.inv_smul_Ioi_zero {r : ℝ} (hr : 0 < r) : r⁻¹ • Ioi (0 : ℝ) = Ioi 0 := by
  ext s
  rw [mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr.ne'), inv_inv, smul_eq_mul, mem_Ioi, mem_Ioi]
  exact mul_pos_iff_of_pos_left hr

/-- `∫⁻ G(t/r) dt = r ∫⁻ G` for `r > 0`. -/
theorem FieldAux.lintegral_comp_inv_mul_left_of_pos {r : ℝ} (hr : 0 < r) (G : ℝ → ℝ≥0∞) :
    ∫⁻ t, G (r⁻¹ * t) = ENNReal.ofReal r * ∫⁻ s, G s := by
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  have h := lintegral_map_equiv G (Homeomorph.mulLeft₀ r⁻¹ hr').toMeasurableEquiv
    (μ := (volume : Measure ℝ))
  simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.coe_mulLeft₀] at h
  rw [Real.map_volume_mul_left hr', inv_inv, abs_of_pos hr, lintegral_smul_measure] at h
  rw [← h, smul_eq_mul]

/-! ### The band covariance under similarities -/

section Band

variable {κ : Rd d → ℝ}

theorem measurable_autoCorr_div (hκ : IsLFPPKernel κ) (t : ℝ) :
    Measurable fun p : Rd d × Rd d => autoCorr κ (t⁻¹ • (p.1 - p.2)) / t :=
  ((continuous_autoCorr hκ).comp ((continuous_fst.sub continuous_snd).const_smul t⁻¹)).measurable.div_const t

/-- **Scale density under similarities**: `scalePair κ t (T_*·) = r⁻¹ scalePair κ (r⁻¹ t) (·)`. -/
theorem scalePair_map_simAffine (hκ : IsLFPPKernel κ) (x : Rd d) {r : ℝ} (hr : r ≠ 0)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (t : ℝ) (μ ν μ' ν' : Measure (Rd d)) [SFinite μ] [SFinite ν]
    [SFinite μ'] [SFinite ν'] :
    scalePair κ t (μ.map (simAffine x r O)) (ν.map (simAffine x r O)) (μ'.map (simAffine x r O))
        (ν'.map (simAffine x r O)) =
      r⁻¹ * scalePair κ (r⁻¹ * t) μ ν μ' ν' := by
  unfold scalePair
  rw [mixInt_map (measurable_simAffine x r O) (measurable_autoCorr_div hκ t) μ ν μ' ν',
    ← mixInt_const_mul]
  congr 1
  funext z w
  rw [simAffine_sub, smul_smul, ← LinearIsometryEquiv.map_smul, autoCorr_linearIsometryEquiv hκ,
    mul_inv_rev, inv_inv]
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [inv_zero, zero_mul, mul_zero, div_zero]
  · field_simp

/-- `∫_S scalePair(T_*·) = ∫_{r⁻¹ S} scalePair(·)` in `ℝ≥0∞`. -/
theorem lintegral_scalePair_map_simAffine (hκ : IsLFPPKernel κ) (x : Rd d) {r : ℝ} (hr : 0 < r)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) {S : Set ℝ} (hS : MeasurableSet S) (μ ν μ' ν' : Measure (Rd d))
    [SFinite μ] [SFinite ν] [SFinite μ'] [SFinite ν'] :
    ∫⁻ t in S, ENNReal.ofReal (scalePair κ t (μ.map (simAffine x r O)) (ν.map (simAffine x r O))
        (μ'.map (simAffine x r O)) (ν'.map (simAffine x r O))) =
      ∫⁻ s in r⁻¹ • S, ENNReal.ofReal (scalePair κ s μ ν μ' ν') := by
  have hS' : MeasurableSet (r⁻¹ • S) := FieldAux.measurableSet_inv_smul hS
  simp_rw [scalePair_map_simAffine hκ x hr.ne' O]
  rw [← lintegral_indicator hS, ← lintegral_indicator hS']
  set G : ℝ → ℝ≥0∞ := (r⁻¹ • S).indicator fun s => ENNReal.ofReal (scalePair κ s μ ν μ' ν')
    with hG
  have e : ∀ t, S.indicator (fun t => ENNReal.ofReal (r⁻¹ * scalePair κ (r⁻¹ * t) μ ν μ' ν')) t =
      ENNReal.ofReal r⁻¹ * G (r⁻¹ * t) := by
    intro t
    by_cases ht : t ∈ S
    · have hmem : r⁻¹ * t ∈ r⁻¹ • S := smul_mem_smul_set ht
      rw [indicator_of_mem ht, hG, indicator_of_mem hmem, ENNReal.ofReal_mul (inv_nonneg.2 hr.le)]
    · have hmem : r⁻¹ * t ∉ r⁻¹ • S := fun h =>
        ht ((smul_mem_smul_set_iff₀ (inv_ne_zero hr.ne') S t).1 h)
      rw [indicator_of_notMem ht, hG, indicator_of_notMem hmem, mul_zero]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, FieldAux.lintegral_comp_inv_mul_left_of_pos hr,
    ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hr.le), inv_mul_cancel₀ hr.ne',
    ENNReal.ofReal_one, one_mul]

/-- **Pairability under similarities**:
`IsPairable κ S (T_*μ) (T_*ν) ↔ IsPairable κ (r⁻¹ • S) μ ν`. -/
theorem isPairable_map_simAffine_iff (hκ : IsLFPPKernel κ) (x : Rd d) {r : ℝ} (hr : 0 < r)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsPairable κ S (μ.map (simAffine x r O)) (ν.map (simAffine x r O)) ↔ IsPairable κ (r⁻¹ • S) μ ν := by
  rw [isPairable_iff_lintegral hκ hS hS0,
    isPairable_iff_lintegral hκ (FieldAux.measurableSet_inv_smul hS) (FieldAux.inv_smul_subset_Ioi hr hS0),
    lintegral_scalePair_map_simAffine hκ x hr O hS]

/-- **Similarity identity at the level of measures** (target T3; HA2 D2.2, HA2-05):
for `T z = x + r O z` with `r > 0`, every measurable scale set `S ⊆ (0, ∞)` and finite measures,
`Cov_S(T_*μ - T_*ν, T_*μ' - T_*ν') = Cov_{r⁻¹ S}(μ - ν, μ' - ν')`. -/
theorem scaleCov_map_simAffine (hκ : IsLFPPKernel κ) (x : Rd d) {r : ℝ} (hr : 0 < r)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0)
    (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] :
    scaleCov κ S (μ.map (simAffine x r O)) (ν.map (simAffine x r O)) (μ'.map (simAffine x r O))
        (ν'.map (simAffine x r O)) =
      scaleCov κ (r⁻¹ • S) μ ν μ' ν' := by
  have hS' : MeasurableSet (r⁻¹ • S) := FieldAux.measurableSet_inv_smul hS
  have hS0' : r⁻¹ • S ⊆ Ioi 0 := FieldAux.inv_smul_subset_Ioi hr hS0
  by_cases h1 : IsPairable κ (r⁻¹ • S) μ ν
  · by_cases h2 : IsPairable κ (r⁻¹ • S) μ' ν'
    · have h1' := (isPairable_map_simAffine_iff hκ x hr O hS hS0 μ ν).2 h1
      have h2' := (isPairable_map_simAffine_iff hκ x hr O hS hS0 μ' ν').2 h2
      rw [scaleCov_eq_integral hκ hS hS0 h1' h2', scaleCov_eq_integral hκ hS' hS0' h1 h2]
      simp_rw [scalePair_map_simAffine hκ x hr.ne' O]
      rw [← integral_indicator hS, ← integral_indicator hS']
      set G : ℝ → ℝ := (r⁻¹ • S).indicator fun s => scalePair κ s μ ν μ' ν' with hG
      have e : ∀ t, S.indicator (fun t => r⁻¹ * scalePair κ (r⁻¹ * t) μ ν μ' ν') t =
          r⁻¹ * G (r⁻¹ * t) := by
        intro t
        by_cases ht : t ∈ S
        · have hmem : r⁻¹ * t ∈ r⁻¹ • S := smul_mem_smul_set ht
          rw [indicator_of_mem ht, hG, indicator_of_mem hmem]
        · have hmem : r⁻¹ * t ∉ r⁻¹ • S := fun h =>
            ht ((smul_mem_smul_set_iff₀ (inv_ne_zero hr.ne') S t).1 h)
          rw [indicator_of_notMem ht, hG, indicator_of_notMem hmem, mul_zero]
      simp_rw [e]
      rw [integral_const_mul, Measure.integral_comp_inv_mul_left G r, abs_of_pos hr, smul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    · rw [scaleCov, scaleCov, bandVecM_of_not h2,
        bandVecM_of_not (mt (isPairable_map_simAffine_iff hκ x hr O hS hS0 μ' ν').1 h2),
        inner_zero_right, inner_zero_right]
  · rw [scaleCov, scaleCov, bandVecM_of_not h1,
      bandVecM_of_not (mt (isPairable_map_simAffine_iff hκ x hr O hS hS0 μ ν).1 h1),
      inner_zero_left, inner_zero_left]

/-- **Exact similarity invariance of the all-scale covariance** (HA2 D2, Corollary (i)). -/
theorem scaleCov_map_simAffine_Ioi (hκ : IsLFPPKernel κ) (x : Rd d) {r : ℝ} (hr : 0 < r)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] :
    scaleCov κ (Ioi 0) (μ.map (simAffine x r O)) (ν.map (simAffine x r O)) (μ'.map (simAffine x r O))
        (ν'.map (simAffine x r O)) =
      scaleCov κ (Ioi 0) μ ν μ' ν' := by
  rw [scaleCov_map_simAffine hκ x hr O measurableSet_Ioi subset_rfl, FieldAux.inv_smul_Ioi_zero hr]

/-- All-scale pairability is invariant under similarities. -/
theorem isPairable_map_simAffine_Ioi_iff (hκ : IsLFPPKernel κ) (x : Rd d) {r : ℝ} (hr : 0 < r)
    (O : Rd d ≃ₗᵢ[ℝ] Rd d) (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsPairable κ (Ioi 0) (μ.map (simAffine x r O)) (ν.map (simAffine x r O)) ↔
      IsPairable κ (Ioi 0) μ ν := by
  rw [isPairable_map_simAffine_iff hκ x hr O measurableSet_Ioi subset_rfl, FieldAux.inv_smul_Ioi_zero hr]

end Band

/-! ### The log covariance under similarities -/

/-- **Similarity invariance of the log covariance** (target T3, interface (I3) of HA3 §7):
for log-pairable finite measures with `μ(ℝ^d) = ν(ℝ^d)` and `T z = x + r O z`, `r > 0`,
`logCov (T_*μ) (T_*ν) (T_*μ') (T_*ν') = logCov μ ν μ' ν'`.  No kernel is involved. -/
theorem logCov_map_simAffine (x : Rd d) {r : ℝ} (hr : 0 < r) (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] (hmass : μ.real univ = ν.real univ) (hlog : LogPairable μ ν μ' ν') :
    logCov (μ.map (simAffine x r O)) (ν.map (simAffine x r O)) (μ'.map (simAffine x r O))
        (ν'.map (simAffine x r O)) =
      logCov μ ν μ' ν' := by
  have h1 : NullSingletonClass μ := hlog.1
  have h2 : NullSingletonClass ν := hlog.2.1
  have hm : Measurable fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖ :=
    (measurable_fst.sub measurable_snd).norm.log.neg
  have l1 := FieldAux.le_add_four₁ μ ν μ' ν'
  have l2 := FieldAux.le_add_four₂ μ ν μ' ν'
  have l3 := FieldAux.le_add_four₃ μ ν μ' ν'
  have l4 := FieldAux.le_add_four₄ μ ν μ' ν'
  have hint : ∀ α β : Measure (Rd d), (α = μ ∨ α = ν) → (β = μ' ∨ β = ν') →
      Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖) (α.prod β) := by
    rintro α β (rfl | rfl) (rfl | rfl) <;>
      exact (LogPairable.integrable_prod hlog (by assumption) (by assumption)).neg
  rw [logCov_eq_mixInt, logCov_eq_mixInt, mixInt_map (measurable_simAffine x r O) hm μ ν μ' ν']
  have hae : mixInt (fun z w => -Real.log ‖simAffine x r O z - simAffine x r O w‖) μ ν μ' ν' =
      mixInt (fun z w => -Real.log ‖z - w‖ + -Real.log r) μ ν μ' ν' := by
    refine mixInt_congr_ae ?_
    rintro α β (rfl | rfl) (rfl | rfl) <;>
    · filter_upwards [FieldAux.ae_ne_of_nullSingletonClass _ _] with p hp
      rw [norm_simAffine_sub x hr O, Real.log_mul hr.ne' (norm_ne_zero_iff.2 (sub_ne_zero.2 hp))]
      ring
  rw [hae, mixInt_add (g₁ := fun z w => -Real.log ‖z - w‖) (g₂ := fun _ _ => -Real.log r) hint
    (by rintro α β (rfl | rfl) (rfl | rfl) <;> exact integrable_const _), mixInt_const, hmass,
    sub_self, zero_mul, mul_zero, add_zero]

end HigherDimLFPP
