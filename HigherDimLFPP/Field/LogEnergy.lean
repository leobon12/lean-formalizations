import HigherDimLFPP.Field.Transport

/-!
# Growth-bounded measures are log-pairable (packet P-F2, complement to targets T2 and T4)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.1 ("⟨h, η⟩ for curve measures"); planning
audit HA2 (`planning/audits/HA2-section-3.md`), §2.3 and Details D3, Remark (b): measures with the
growth bound (3.4) have no atoms and finite logarithmic energy (layer cake).

* `GrowthBound.nullSingletonClass`: a finite measure with a growth bound has no atoms;
* `FieldAux.lintegral_log_inv_le`: if `λ(B̄(z, s)) ≤ A s` for all `s > 0`, then
  `∫ log⁺(1/|z - w|) dλ(w) ≤ A` (layer cake, `lintegral_eq_lintegral_meas_lt`);
* `integrable_log_norm_sub_of_smallBall`: hence `log|z - w|` is `λ ⊗ λ`-integrable when moreover
  `λ` has bounded support;
* `logPairable_of_growthBound`: growth-bounded finite measures with bounded supports are
  `LogPairable`.

Bounded supports are needed for the large distances: the growth bound only controls small balls, and
`log|z - w|` need not be integrable for heavy-tailed measures.  Consequences:
`scaleCov_eq_logCov_of_growthBound` ((3.2) for such measures) and
`transport_logCov_bound_of_support` (Lemma 3.1 for the log covariance without a `LogPairable`
hypothesis).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace HigherDimLFPP

variable {d : ℕ}

/-- A finite measure with a growth bound has no atoms. -/
theorem GrowthBound.nullSingletonClass {μ : Measure (Rd d)} [IsFiniteMeasure μ] {B R : ℝ}
    (hR : 0 < R) (h : GrowthBound μ B R) : NullSingletonClass μ := by
  constructor
  intro z
  have hB := h.max_zero hR
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hle : ∀ s > 0, μ.real {z} ≤ B' * (s / R) := fun s hs =>
    (measureReal_mono (singleton_subset_iff.2 (mem_closedBall_self hs.le))).trans
      (hB.le_div hB'0 z hs)
  have h0 : μ.real {z} ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 := hle (ε * R / (B' + 1)) (by positivity)
    have h2 : B' * (ε * R / (B' + 1) / R) ≤ ε := by
      rw [show ε * R / (B' + 1) / R = ε / (B' + 1) by field_simp]
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (le_antisymm h0 measureReal_nonneg)

/-- **Layer cake** (HA2 D3, Remark (b)): if `λ(B̄(z, s)) ≤ A s` for all `s > 0`, then
`∫ log⁺(1/|z - w|) dλ(w) ≤ A`. -/
theorem FieldAux.lintegral_log_inv_le {lam : Measure (Rd d)} [IsFiniteMeasure lam] {A : ℝ}
    (hA : 0 ≤ A) (hball : ∀ z : Rd d, ∀ s > 0, lam.real (closedBall z s) ≤ A * s) (z : Rd d) :
    ∫⁻ w, ENNReal.ofReal (max 0 (-Real.log ‖z - w‖)) ∂lam ≤ ENNReal.ofReal A := by
  have hm : Measurable fun w : Rd d => max 0 (-Real.log ‖z - w‖) :=
    measurable_const.max (measurable_const.sub measurable_id).norm.log.neg
  rw [lintegral_eq_lintegral_meas_lt (f := fun w => max 0 (-Real.log ‖z - w‖)) lam
    (Eventually.of_forall fun w => le_max_left _ _) hm.aemeasurable]
  have hsub : ∀ t > (0 : ℝ), {w : Rd d | t < max 0 (-Real.log ‖z - w‖)} ⊆
      closedBall z (Real.exp (-t)) := by
    intro t ht w hw
    simp only [mem_ofPred_eq] at hw
    have hw' : t < -Real.log ‖z - w‖ := by
      rcases le_total 0 (-Real.log ‖z - w‖) with h | h
      · rwa [max_eq_right h] at hw
      · rw [max_eq_left h] at hw
        exact absurd hw (not_lt.2 ht.le)
    have hpos : 0 < ‖z - w‖ := by
      by_contra hc
      have h0 : ‖z - w‖ = 0 := le_antisymm (not_lt.1 hc) (norm_nonneg _)
      rw [h0, Real.log_zero, neg_zero] at hw'
      exact absurd hw' (not_lt.2 ht.le)
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
    have : Real.log ‖z - w‖ < -t := by linarith
    exact ((Real.log_lt_iff_lt_exp hpos).1 this).le
  calc ∫⁻ t in Ioi 0, lam {w | t < max 0 (-Real.log ‖z - w‖)}
      ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (A * Real.exp (-t)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        calc lam {w | t < max 0 (-Real.log ‖z - w‖)} ≤ lam (closedBall z (Real.exp (-t))) :=
              measure_mono (hsub t ht)
          _ = ENNReal.ofReal (lam.real (closedBall z (Real.exp (-t)))) :=
              (ofReal_measureReal (measure_ne_top _ _)).symm
          _ ≤ ENNReal.ofReal (A * Real.exp (-t)) :=
              ENNReal.ofReal_le_ofReal (hball z _ (Real.exp_pos _))
    _ = ENNReal.ofReal (∫ t in Ioi 0, A * Real.exp (-t)) := by
        rw [ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_neg_Ioi 0).const_mul A)]
        exact (ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall fun t _ => mul_nonneg hA (Real.exp_pos _).le)
    _ = ENNReal.ofReal A := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

/-- `|log r| ≤ log⁺(1/r) + log⁺(2D)` for `0 ≤ r ≤ 2D`. -/
theorem FieldAux.abs_log_le {r D : ℝ} (hr : 0 ≤ r) (hrD : r ≤ 2 * D) :
    |Real.log r| ≤ max 0 (-Real.log r) + max 0 (Real.log (2 * D)) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [Real.log_zero, abs_zero]
    positivity
  rcases le_total r 1 with h1 | h1
  · rw [abs_of_nonpos (Real.log_nonpos hr.le h1)]
    exact le_add_of_le_of_nonneg (le_max_right _ _) (le_max_left _ _)
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    exact le_add_of_nonneg_of_le (le_max_left _ _)
      ((Real.log_le_log hr hrD).trans (le_max_right _ _))

/-- If `λ(B̄(z, s)) ≤ A s` for all `s > 0` and `λ` has bounded support, then `log|z - w|` is
`λ ⊗ λ`-integrable. -/
theorem integrable_log_norm_sub_of_smallBall {lam : Measure (Rd d)} [IsFiniteMeasure lam]
    {A D : ℝ} (hA : 0 ≤ A) (hball : ∀ z : Rd d, ∀ s > 0, lam.real (closedBall z s) ≤ A * s)
    (hD : ∀ᵐ z ∂lam, ‖z‖ ≤ D) :
    Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖) (lam.prod lam) := by
  have hm : Measurable fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖ :=
    (measurable_fst.sub measurable_snd).norm.log
  have hf : Measurable fun p : Rd d × Rd d => ENNReal.ofReal (max 0 (-Real.log ‖p.1 - p.2‖)) :=
    (measurable_const.max hm.neg).ennreal_ofReal
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have hbd : ∀ᵐ p ∂(lam.prod lam), ‖Real.log ‖p.1 - p.2‖‖ₑ ≤
      ENNReal.ofReal (max 0 (-Real.log ‖p.1 - p.2‖)) +
        ENNReal.ofReal (max 0 (Real.log (2 * D))) := by
    filter_upwards [FieldAux.ae_prod_norm_le hD hD] with p hp
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_left _ _) (le_max_left _ _)]
    exact ENNReal.ofReal_le_ofReal (FieldAux.abs_log_le (norm_nonneg _) hp)
  have hint : ∫⁻ p, ENNReal.ofReal (max 0 (-Real.log ‖p.1 - p.2‖)) ∂(lam.prod lam) < ⊤ := by
    rw [lintegral_prod _ hf.aemeasurable]
    calc ∫⁻ z, ∫⁻ w, ENNReal.ofReal (max 0 (-Real.log ‖(z, w).1 - (z, w).2‖)) ∂lam ∂lam
        ≤ ∫⁻ _z, ENNReal.ofReal A ∂lam :=
          lintegral_mono fun z => FieldAux.lintegral_log_inv_le hA hball z
      _ = ENNReal.ofReal A * lam univ := lintegral_const _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  calc ∫⁻ p, ‖Real.log ‖p.1 - p.2‖‖ₑ ∂(lam.prod lam)
      ≤ ∫⁻ p, (ENNReal.ofReal (max 0 (-Real.log ‖p.1 - p.2‖)) +
          ENNReal.ofReal (max 0 (Real.log (2 * D)))) ∂(lam.prod lam) := lintegral_mono_ae hbd
    _ = ∫⁻ p, ENNReal.ofReal (max 0 (-Real.log ‖p.1 - p.2‖)) ∂(lam.prod lam) +
          ENNReal.ofReal (max 0 (Real.log (2 * D))) * (lam.prod lam) univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hint, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (measure_lt_top _ _)⟩

/-- **Growth-bounded measures are log-pairable** (HA2 D3, Remark (b), with bounded supports):
finite measures `μ, ν` (growth bound (3.4) at scale `R`) and `μ', ν'` (at scale `r`), all with
supports in `B̄(0, D)`, are `LogPairable`. -/
theorem logPairable_of_growthBound {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] {B R r D : ℝ} (hR : 0 < R)
    (hr : 0 < r) (gμ : GrowthBound μ B R) (gν : GrowthBound ν B R) (gμ' : GrowthBound μ' B r)
    (gν' : GrowthBound ν' B r) (sμ : ∀ᵐ z ∂μ, ‖z‖ ≤ D) (sν : ∀ᵐ z ∂ν, ‖z‖ ≤ D)
    (sμ' : ∀ᵐ z ∂μ', ‖z‖ ≤ D) (sν' : ∀ᵐ z ∂ν', ‖z‖ ≤ D) : LogPairable μ ν μ' ν' := by
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  refine ⟨gμ.nullSingletonClass hR, gν.nullSingletonClass hR, gμ'.nullSingletonClass hr,
    gν'.nullSingletonClass hr, ?_⟩
  refine integrable_log_norm_sub_of_smallBall (A := 2 * (B' / R) + 2 * (B' / r)) (D := D)
    (by positivity) (fun z s hs => ?_) ?_
  · have e1 := (gμ.max_zero hR).le_div hB'0 z hs
    have e2 := (gν.max_zero hR).le_div hB'0 z hs
    have e3 := (gμ'.max_zero hr).le_div hB'0 z hs
    have e4 := (gν'.max_zero hr).le_div hB'0 z hs
    rw [measureReal_add_apply, measureReal_add_apply, measureReal_add_apply]
    have : B' * (s / R) = B' / R * s := by ring
    have : B' * (s / r) = B' / r * s := by ring
    nlinarith
  · simp only [ae_add_measure_iff]
    exact ⟨⟨⟨sμ, sν⟩, sμ'⟩, sν'⟩

variable {κ : Rd d → ℝ}

/-- **(3.2) for growth-bounded measures with bounded supports.** -/
theorem scaleCov_eq_logCov_of_growthBound (hκ : IsLFPPKernel κ) {μ ν μ' ν' : Measure (Rd d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν'] {B R r D : ℝ} (hR : 0 < R) (hr : 0 < r) (gμ : GrowthBound μ B R)
    (gν : GrowthBound ν B R) (gμ' : GrowthBound μ' B r) (gν' : GrowthBound ν' B r)
    (sμ : ∀ᵐ z ∂μ, ‖z‖ ≤ D) (sν : ∀ᵐ z ∂ν, ‖z‖ ≤ D) (sμ' : ∀ᵐ z ∂μ', ‖z‖ ≤ D)
    (sν' : ∀ᵐ z ∂ν', ‖z‖ ≤ D) :
    IsPairable κ (Ioi 0) μ ν ∧ IsPairable κ (Ioi 0) μ' ν' ∧
      scaleCov κ (Ioi 0) μ ν μ' ν' = logCov μ ν μ' ν' :=
  scaleCov_eq_logCov hκ (by rw [probReal_univ, probReal_univ])
    (by rw [probReal_univ, probReal_univ])
    (logPairable_of_growthBound hR hr gμ gν gμ' gν' sμ sν sμ' sν')

/-- **Lemma 3.1 for the log covariance, bounded supports** (interface (I4) of HA3 §7): as
`transport_logCov_bound`, with the `LogPairable` hypothesis replaced by bounded supports. -/
theorem transport_logCov_bound_of_support (d : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (μR νR μr νr : Measure (Rd d)) [IsProbabilityMeasure μR] [IsProbabilityMeasure νR]
        [IsProbabilityMeasure μr] [IsProbabilityMeasure νr] (R r u v D : ℝ),
        0 < R → 0 < r → 0 ≤ u → 0 ≤ v →
        GrowthBound μR B R → GrowthBound νR B R → GrowthBound μr B r → GrowthBound νr B r →
        CoupledWithin μR νR u → CoupledWithin μr νr v →
        (∀ᵐ z ∂μR, ‖z‖ ≤ D) → (∀ᵐ z ∂νR, ‖z‖ ≤ D) → (∀ᵐ z ∂μr, ‖z‖ ≤ D) →
        (∀ᵐ z ∂νr, ‖z‖ ≤ D) →
        |logCov μR νR μr νr| ≤ C * Real.sqrt (u * v) / R := by
  obtain ⟨C, hC0, hC⟩ := transport_logCov_bound d B
  exact ⟨C, hC0, fun μR νR μr νr _ _ _ _ R r u v D hR hr hu hv gR gR' gr gr' cR cr s1 s2 s3 s4 =>
    hC μR νR μr νr R r u v hR hr hu hv gR gR' gr gr' cR cr
      (logPairable_of_growthBound hR hr gR gR' gr gr' s1 s2 s3 s4)⟩

end HigherDimLFPP
