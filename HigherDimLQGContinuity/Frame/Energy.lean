import HigherDimLQGContinuity.Frame.Potential
import HigherDimLQGMetric.Sphere.Var

/-!
# Pairing frame V: logarithmic energy under a Hölder ball bound

Packet N3 (NA4 Details (a) A2, item 10; blueprint Part C `c:lem-energy`). A `σ`-growth version of HigherDimLFPP's
`integrable_log_norm_sub_of_smallBall` / `logPairable_of_growthBound`.

Let `ν` be a probability measure on `ℝ^d` (`d ≥ 2`) carried by `B̄_S`, `S ≥ 1`, with `ν(B̄_r(z)) ≤ B r^σ` for
`0 < r ≤ 1/2` (`B ≥ 1`, `σ > 0`).

* `frame_lintegral_log_inv_le` (layer cake): for every finite measure `λ` with `λ(B̄_r(z)) ≤ A r^σ` (`r ≤ 1/2`),
  `λ(ℝ^d) ≤ m` and every `t₁ ≥ log 2`: `∫ log⁺(1/|x - y|) dλ(y) ≤ m t₁ + A e^{-σ t₁}/σ`.
* `frame_integrable_log_norm_sub`: a uniform bound on `∫ log⁺(1/|x - y|) dλ(y)` and a bounded support give the
  integrability of `log|x - y|` for `λ ⊗ λ`.
* `frame_logPairable_posM` and `frame_logPairable_self`: `ψ^± dx, ν, σ₁` and `ν, σ₁, ν, σ₁` are `LogPairable`.
* `frame_logCov_self_le` (Part C `c:lem-energy`(b)):
  `logCov(ν, σ₁, ν, σ₁) ≤ log 2 + (log B + 1)/σ + 2 log(S + 1) + |sphEnergy d|`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Layer cake under a Hölder ball bound -/

theorem frame_setOf_lt_log_inv_subset (x : Rd d) {t : ℝ} (ht : 0 < t) :
    {y : Rd d | t < max 0 (-Real.log ‖x - y‖)} ⊆ closedBall x (Real.exp (-t)) := by
  intro y hy
  simp only [mem_ofPred_eq] at hy
  have hy' : t < -Real.log ‖x - y‖ := by
    rcases le_total 0 (-Real.log ‖x - y‖) with h | h
    · rwa [max_eq_right h] at hy
    · rw [max_eq_left h] at hy
      exact absurd hy (not_lt.2 ht.le)
  have hpos : 0 < ‖x - y‖ := by
    by_contra hc
    have h0 : ‖x - y‖ = 0 := le_antisymm (not_lt.1 hc) (norm_nonneg _)
    rw [h0, Real.log_zero, neg_zero] at hy'
    exact absurd hy' (not_lt.2 ht.le)
  rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
  have : Real.log ‖x - y‖ < -t := by linarith
  exact ((Real.log_lt_iff_lt_exp hpos).1 this).le

/-- **Layer cake under a Hölder ball bound.** -/
theorem frame_lintegral_log_inv_le {lam : Measure (Rd d)} [IsFiniteMeasure lam] {A σ m t₁ : ℝ}
    (hσ : 0 < σ) (hA : 0 ≤ A) (hm : lam.real univ ≤ m) (ht₁ : Real.log 2 ≤ t₁)
    (hball : ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → lam.real (closedBall z r) ≤ A * r ^ σ)
    (x : Rd d) :
    ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) ∂lam ≤
      ENNReal.ofReal (m * t₁ + A * Real.exp (-σ * t₁) / σ) := by
  have hm0 : 0 ≤ m := measureReal_nonneg.trans hm
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht₁0 : 0 ≤ t₁ := hlog2.le.trans ht₁
  have hmeas : Measurable fun y : Rd d => max 0 (-Real.log ‖x - y‖) :=
    measurable_const.max (measurable_const.sub measurable_id).norm.log.neg
  rw [lintegral_eq_lintegral_meas_lt (f := fun y => max 0 (-Real.log ‖x - y‖)) lam
    (Eventually.of_forall fun y => le_max_left _ _) hmeas.aemeasurable]
  rw [← Ioc_union_Ioi_eq_Ioi ht₁0]
  refine (lintegral_union_le _ _ _).trans ?_
  -- the small levels: total mass
  have h1 : ∫⁻ t in Ioc 0 t₁, lam {y | t < max 0 (-Real.log ‖x - y‖)} ≤
      ENNReal.ofReal (m * t₁) := by
    calc ∫⁻ t in Ioc 0 t₁, lam {y | t < max 0 (-Real.log ‖x - y‖)}
        ≤ ∫⁻ _t in Ioc 0 t₁, ENNReal.ofReal m := by
          refine lintegral_mono fun t => ?_
          calc lam {y | t < max 0 (-Real.log ‖x - y‖)} ≤ lam univ := measure_mono (subset_univ _)
            _ = ENNReal.ofReal (lam.real univ) := (ofReal_measureReal (measure_ne_top _ _)).symm
            _ ≤ ENNReal.ofReal m := ENNReal.ofReal_le_ofReal hm
      _ = ENNReal.ofReal (m * t₁) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hm0]
  -- the large levels: the ball bound
  have h2 : ∫⁻ t in Ioi t₁, lam {y | t < max 0 (-Real.log ‖x - y‖)} ≤
      ENNReal.ofReal (A * Real.exp (-σ * t₁) / σ) := by
    calc ∫⁻ t in Ioi t₁, lam {y | t < max 0 (-Real.log ‖x - y‖)}
        ≤ ∫⁻ t in Ioi t₁, ENNReal.ofReal (A * Real.exp (-σ * t)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := ht₁0.trans_lt ht
          have hr : Real.exp (-t) ≤ 1 / 2 := by
            have h1 : Real.exp (-t) ≤ Real.exp (-Real.log 2) :=
              Real.exp_le_exp.2 (by linarith [show t₁ < t from ht])
            have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
              rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
            exact h1.trans h2.le
          calc lam {y | t < max 0 (-Real.log ‖x - y‖)}
              ≤ lam (closedBall x (Real.exp (-t))) :=
                measure_mono (frame_setOf_lt_log_inv_subset x ht0)
            _ = ENNReal.ofReal (lam.real (closedBall x (Real.exp (-t)))) :=
                (ofReal_measureReal (measure_ne_top _ _)).symm
            _ ≤ ENNReal.ofReal (A * Real.exp (-t) ^ σ) :=
                ENNReal.ofReal_le_ofReal (hball x _ (Real.exp_pos _) hr)
            _ = ENNReal.ofReal (A * Real.exp (-σ * t)) := by
                rw [← Real.exp_mul, show -t * σ = -σ * t by ring]
      _ = ENNReal.ofReal (∫ t in Ioi t₁, A * Real.exp (-σ * t)) := by
          rw [ofReal_integral_eq_lintegral_ofReal
            ((integrableOn_exp_mul_Ioi (neg_lt_zero.2 hσ) t₁).const_mul A)]
          exact (ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun t _ => mul_nonneg hA (Real.exp_pos _).le)
      _ = ENNReal.ofReal (A * Real.exp (-σ * t₁) / σ) := by
          rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.2 hσ), neg_div, div_neg,
            neg_neg, mul_div_assoc]
  refine (add_le_add h1 h2).trans ?_
  rw [← ENNReal.ofReal_add (mul_nonneg hm0 ht₁0)
    (div_nonneg (mul_nonneg hA (Real.exp_pos _).le) hσ.le)]

/-! ## Integrability of the log kernel -/

/-- A uniform bound on `∫ log⁺(1/|x - y|) dλ(y)` and a bounded support give `log|x - y| ∈ L¹(λ ⊗ λ)` (the proof of
HigherDimLFPP's `integrable_log_norm_sub_of_smallBall`, with the layer-cake bound as a hypothesis). -/
theorem frame_integrable_log_norm_sub {lam : Measure (Rd d)} [IsFiniteMeasure lam] {K D : ℝ}
    (hK : ∀ x, ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) ∂lam ≤ ENNReal.ofReal K)
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
    filter_upwards [HigherDimLFPP.FieldAux.ae_prod_norm_le hD hD] with p hp
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_left _ _) (le_max_left _ _)]
    exact ENNReal.ofReal_le_ofReal (HigherDimLFPP.FieldAux.abs_log_le (norm_nonneg _) hp)
  have hint : ∫⁻ p, ENNReal.ofReal (max 0 (-Real.log ‖p.1 - p.2‖)) ∂(lam.prod lam) < ⊤ := by
    rw [lintegral_prod _ hf.aemeasurable]
    calc ∫⁻ z, ∫⁻ w, ENNReal.ofReal (max 0 (-Real.log ‖(z, w).1 - (z, w).2‖)) ∂lam ∂lam
        ≤ ∫⁻ _z, ENNReal.ofReal K ∂lam := lintegral_mono fun z => hK z
      _ = ENNReal.ofReal K * lam univ := lintegral_const _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  calc ∫⁻ p, ‖Real.log ‖p.1 - p.2‖‖ₑ ∂(lam.prod lam)
      ≤ ∫⁻ p, (ENNReal.ofReal (max 0 (-Real.log ‖p.1 - p.2‖)) +
          ENNReal.ofReal (max 0 (Real.log (2 * D)))) ∂(lam.prod lam) := lintegral_mono_ae hbd
    _ = ∫⁻ p, ENNReal.ofReal (max 0 (-Real.log ‖p.1 - p.2‖)) ∂(lam.prod lam) +
          ENNReal.ofReal (max 0 (Real.log (2 * D))) * (lam.prod lam) univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hint, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (measure_lt_top _ _)⟩

/-- Four finite measures without atoms, with uniform layer-cake bounds and bounded supports, are `LogPairable`. -/
theorem frame_logPairable_of_bounds {μ₁ μ₂ μ₃ μ₄ : Measure (Rd d)} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (n₁ : NullSingletonClass μ₁) (n₂ : NullSingletonClass μ₂) (n₃ : NullSingletonClass μ₃)
    (n₄ : NullSingletonClass μ₄) {K₁ K₂ K₃ K₄ D : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃)
    (hK₄ : 0 ≤ K₄)
    (h₁ : ∀ x, ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) ∂μ₁ ≤ ENNReal.ofReal K₁)
    (h₂ : ∀ x, ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) ∂μ₂ ≤ ENNReal.ofReal K₂)
    (h₃ : ∀ x, ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) ∂μ₃ ≤ ENNReal.ofReal K₃)
    (h₄ : ∀ x, ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) ∂μ₄ ≤ ENNReal.ofReal K₄)
    (s₁ : ∀ᵐ z ∂μ₁, ‖z‖ ≤ D) (s₂ : ∀ᵐ z ∂μ₂, ‖z‖ ≤ D) (s₃ : ∀ᵐ z ∂μ₃, ‖z‖ ≤ D)
    (s₄ : ∀ᵐ z ∂μ₄, ‖z‖ ≤ D) : HigherDimLFPP.LogPairable μ₁ μ₂ μ₃ μ₄ := by
  refine ⟨n₁, n₂, n₃, n₄, frame_integrable_log_norm_sub (K := K₁ + K₂ + K₃ + K₄) (D := D)
    (fun x => ?_) ?_⟩
  · rw [lintegral_add_measure, lintegral_add_measure, lintegral_add_measure,
      ENNReal.ofReal_add (by positivity) hK₄, ENNReal.ofReal_add (by positivity) hK₃,
      ENNReal.ofReal_add hK₁ hK₂]
    exact add_le_add (add_le_add (add_le_add (h₁ x) (h₂ x)) (h₃ x)) (h₄ x)
  · simp only [ae_add_measure_iff]
    exact ⟨⟨⟨s₁, s₂⟩, s₃⟩, s₄⟩

/-! ## Measures with a Hölder ball bound -/

/-- A finite measure with a Hölder ball bound has no atoms. -/
theorem frame_nullSingletonClass_of_ballBound {ν : Measure (Rd d)} [IsFiniteMeasure ν] {B σ : ℝ}
    (hσ : 0 < σ)
    (hball : ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → (ν (closedBall z r)).toReal ≤ B * r ^ σ) :
    NullSingletonClass ν := by
  constructor
  intro x
  have hlim : Filter.Tendsto (fun r : ℝ => B * r ^ σ) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hc : ContinuousAt (fun r : ℝ => B * r ^ σ) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const 0 σ (Or.inr hσ.le))
    have := hc.tendsto
    rw [Real.zero_rpow hσ.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), (ν {x}).toReal ≤ B * r ^ σ := by
    have h12 : Ioo (0 : ℝ) (1 / 2) ∈ nhdsWithin (0 : ℝ) (Ioi 0) :=
      Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [h12] with r hr
    exact (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (singleton_subset_iff.2 (mem_closedBall_self hr.1.le)))).trans
      (hball x r hr.1 hr.2.le)
  have h0 : (ν {x}).toReal ≤ 0 := ge_of_tendsto hlim hev
  exact ((ENNReal.toReal_eq_zero_iff _).1 (le_antisymm h0 ENNReal.toReal_nonneg)).resolve_right
    (measure_ne_top _ _)

/-- The layer-cake bound for a ball-bounded probability measure, at the level `t₁ = log 2`. -/
theorem frame_lintegral_log_inv_le_of_ballBound {ν : Measure (Rd d)} [IsProbabilityMeasure ν]
    {B σ : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B)
    (hball : ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → (ν (closedBall z r)).toReal ≤ B * r ^ σ)
    (x : Rd d) :
    ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) ∂ν ≤
      ENNReal.ofReal (Real.log 2 + B * Real.exp (-σ * Real.log 2) / σ) := by
  have h := frame_lintegral_log_inv_le (lam := ν) (m := 1) (t₁ := Real.log 2) hσ hB
    (by rw [probReal_univ]) le_rfl hball x
  rwa [one_mul] at h

theorem frame_ae_norm_le_of_compl {ν : Measure (Rd d)} {S : ℝ}
    (hsupp : ν (closedBall (0 : Rd d) S)ᶜ = 0) : ∀ᵐ z ∂ν, ‖z‖ ≤ S := by
  rw [ae_iff]
  have e : {z : Rd d | ¬‖z‖ ≤ S} = (closedBall (0 : Rd d) S)ᶜ := by
    ext z
    simp only [mem_ofPred_eq, mem_compl_iff, mem_closedBall, dist_zero_right]
  rw [e]
  exact hsupp

theorem frame_nullSingletonClass_sphere (hd : 2 ≤ d) : NullSingletonClass (unitSphereProb d) :=
  ⟨fun x => measure_singleton_eq_zero_of_smallBall (unitSphereProb_smallBall hd) x⟩

theorem frame_ae_mono_norm {μ : Measure (Rd d)} {D D' : ℝ} (h : ∀ᵐ z ∂μ, ‖z‖ ≤ D) (hD : D ≤ D') :
    ∀ᵐ z ∂μ, ‖z‖ ≤ D' := by
  filter_upwards [h] with z hz
  exact hz.trans hD

theorem frame_ballBound_const_nonneg {B σ : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B) :
    0 ≤ Real.log 2 + B * Real.exp (-σ * Real.log 2) / σ :=
  add_nonneg (Real.log_nonneg (by norm_num)) (div_nonneg (mul_nonneg hB (Real.exp_pos _).le) hσ.le)

/-- `ψ^± dx, ν, σ₁` are `LogPairable` (Part C `c:lem-energy`(a)). -/
theorem frame_logPairable_posM (hd : 2 ≤ d) (ψ : TestRd d) (ν : Measure (Rd d))
    [IsProbabilityMeasure ν] {S B σ : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B)
    (hsupp : ν (closedBall (0 : Rd d) S)ᶜ = 0)
    (hball : ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → (ν (closedBall z r)).toReal ≤ B * r ^ σ) :
    HigherDimLFPP.LogPairable (posM ⇑ψ) (posM (-⇑ψ)) ν (unitSphereProb d) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨M, D, hψ⟩ := exists_isBddSupp_testOn ψ
  have := isFiniteMeasure_posM hψ
  have := isFiniteMeasure_posM hψ.neg
  have hD1 : D ≤ |D| + |S| + 1 := by linarith [le_abs_self D, abs_nonneg S]
  have hS1 : S ≤ |D| + |S| + 1 := by linarith [le_abs_self S, abs_nonneg D]
  have h11 : (1 : ℝ) ≤ |D| + |S| + 1 := by linarith [abs_nonneg S, abs_nonneg D]
  exact frame_logPairable_of_bounds (nullSingletonClass_posM _) (nullSingletonClass_posM _)
    (frame_nullSingletonClass_of_ballBound hσ hball) (frame_nullSingletonClass_sphere hd)
    (frame_smallBall_const_nonneg hψ) (frame_smallBall_const_nonneg hψ.neg)
    (frame_ballBound_const_nonneg hσ hB) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d)
    (fun x => HigherDimLFPP.FieldAux.lintegral_log_inv_le (frame_smallBall_const_nonneg hψ)
      (fun z s hs => posM_real_closedBall_le hψ z hs) x)
    (fun x => HigherDimLFPP.FieldAux.lintegral_log_inv_le (frame_smallBall_const_nonneg hψ.neg)
      (fun z s hs => posM_real_closedBall_le hψ.neg z hs) x)
    (frame_lintegral_log_inv_le_of_ballBound hσ hB hball)
    (fun x => HigherDimLFPP.FieldAux.lintegral_log_inv_le (by positivity)
      (unitSphereProb_smallBall hd) x)
    (frame_ae_mono_norm (ae_posM_norm_le hψ) hD1) (frame_ae_mono_norm (ae_posM_norm_le hψ.neg) hD1)
    (frame_ae_mono_norm (frame_ae_norm_le_of_compl hsupp) hS1)
    (frame_ae_mono_norm (ae_unitSphereProb_norm_le d) h11)

/-- `ν, σ₁, ν, σ₁` are `LogPairable` (Part C `c:lem-energy`(a)). -/
theorem frame_logPairable_self (hd : 2 ≤ d) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    {S B σ : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B) (hsupp : ν (closedBall (0 : Rd d) S)ᶜ = 0)
    (hball : ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → (ν (closedBall z r)).toReal ≤ B * r ^ σ) :
    HigherDimLFPP.LogPairable ν (unitSphereProb d) ν (unitSphereProb d) := by
  have hS1 : S ≤ |S| + 1 := by linarith [le_abs_self S]
  have h11 : (1 : ℝ) ≤ |S| + 1 := by linarith [abs_nonneg S]
  exact frame_logPairable_of_bounds (frame_nullSingletonClass_of_ballBound hσ hball)
    (frame_nullSingletonClass_sphere hd) (frame_nullSingletonClass_of_ballBound hσ hball)
    (frame_nullSingletonClass_sphere hd)
    (frame_ballBound_const_nonneg hσ hB) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d)
    (frame_ballBound_const_nonneg hσ hB) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d)
    (frame_lintegral_log_inv_le_of_ballBound hσ hB hball)
    (fun x => HigherDimLFPP.FieldAux.lintegral_log_inv_le (by positivity)
      (unitSphereProb_smallBall hd) x)
    (frame_lintegral_log_inv_le_of_ballBound hσ hB hball)
    (fun x => HigherDimLFPP.FieldAux.lintegral_log_inv_le (by positivity)
      (unitSphereProb_smallBall hd) x)
    (frame_ae_mono_norm (frame_ae_norm_le_of_compl hsupp) hS1)
    (frame_ae_mono_norm (ae_unitSphereProb_norm_le d) h11)
    (frame_ae_mono_norm (frame_ae_norm_le_of_compl hsupp) hS1)
    (frame_ae_mono_norm (ae_unitSphereProb_norm_le d) h11)

/-! ## The energy bound -/

theorem frame_log_le_log_of_norm_le {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (hR : 1 ≤ R) :
    Real.log r ≤ Real.log R := by
  rcases hr.eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]
    exact Real.log_nonneg hR
  · exact Real.log_le_log hpos hrR

theorem frame_sphMeas_one_zero : sphMeas 1 (0 : Rd d) = unitSphereProb d := by
  simp only [sphMeas, zero_add, one_smul]
  exact Measure.map_id'

/-- **The energy bound** (Part C `c:lem-energy`(b)):
`logCov(ν, σ₁, ν, σ₁) ≤ log 2 + (log B + 1)/σ + 2 log(S + 1) + |sphEnergy d|`. -/
theorem frame_logCov_self_le (hd : 2 ≤ d) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    {S B σ : ℝ} (hS : 1 ≤ S) (hB : 1 ≤ B) (hσ : 0 < σ) (hsupp : ν (closedBall (0 : Rd d) S)ᶜ = 0)
    (hball : ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → (ν (closedBall z r)).toReal ≤ B * r ^ σ) :
    HigherDimLFPP.logCov ν (unitSphereProb d) ν (unitSphereProb d) ≤
      Real.log 2 + (Real.log B + 1) / σ + 2 * Real.log (S + 1) + |sphEnergy d| := by
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have hP := frame_logPairable_self hd ν hσ (by linarith) hsupp hball
  have iνν : Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖) (ν.prod ν) :=
    (hP.integrable_prod (HigherDimLFPP.FieldAux.le_add_four₁ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₃ _ _ _ _)).neg
  have iνσ : Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖)
      (ν.prod (unitSphereProb d)) :=
    (hP.integrable_prod (HigherDimLFPP.FieldAux.le_add_four₁ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₄ _ _ _ _)).neg
  have iσν : Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖)
      ((unitSphereProb d).prod ν) :=
    (hP.integrable_prod (HigherDimLFPP.FieldAux.le_add_four₂ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₃ _ _ _ _)).neg
  -- (1) the self-energy of `ν`
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := Real.log 2 + (Real.log B + 1) / σ with hKdef
  have hK0 : 0 ≤ K := add_nonneg hlog2.le (div_nonneg (by linarith) hσ.le)
  set t₁ : ℝ := Real.log 2 + Real.log B / σ with ht₁def
  have ht₁ : Real.log 2 ≤ t₁ := le_add_of_nonneg_right (div_nonneg hlogB hσ.le)
  have hK : ∀ x, ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖x - y‖)) ∂ν ≤ ENNReal.ofReal K := by
    intro x
    refine (frame_lintegral_log_inv_le (m := 1) hσ (by linarith) (by rw [probReal_univ]) ht₁
      hball x).trans (ENNReal.ofReal_le_ofReal ?_)
    have e : B * Real.exp (-σ * t₁) = Real.exp (-σ * Real.log 2) := by
      have hB0 : 0 < B := by linarith
      have : -σ * t₁ = -σ * Real.log 2 + -Real.log B := by
        rw [ht₁def]
        field_simp
        ring
      rw [this, Real.exp_add, Real.exp_neg, Real.exp_log hB0]
      field_simp
    have h2 : Real.exp (-σ * Real.log 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    have h3 : Real.exp (-σ * Real.log 2) / σ ≤ 1 / σ := div_le_div_of_nonneg_right h2 hσ.le
    rw [e, hKdef, ht₁def, add_div]
    linarith
  have h1 : ∫ p, -Real.log ‖p.1 - p.2‖ ∂(ν.prod ν) ≤ K := by
    have hi' : Integrable (fun p : Rd d × Rd d => max 0 (-Real.log ‖p.1 - p.2‖)) (ν.prod ν) :=
      (integrable_const 0).sup iνν
    refine (integral_mono iνν hi' fun p => le_max_right _ _).trans ?_
    rw [← ENNReal.ofReal_le_ofReal_iff hK0,
      ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ fun p => le_max_left _ _)]
    have hf : Measurable fun p : Rd d × Rd d => ENNReal.ofReal (max 0 (-Real.log ‖p.1 - p.2‖)) :=
      (measurable_const.max ((measurable_fst.sub measurable_snd).norm.log.neg)).ennreal_ofReal
    rw [lintegral_prod _ hf.aemeasurable]
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (max 0 (-Real.log ‖(x, y).1 - (x, y).2‖)) ∂ν ∂ν
        ≤ ∫⁻ _x, ENNReal.ofReal K ∂ν := lintegral_mono fun x => hK x
      _ = ENNReal.ofReal K := by rw [lintegral_const, measure_univ, mul_one]
  -- (2) the cross energies
  have hsν := frame_ae_norm_le_of_compl hsupp
  have hσ1 := ae_unitSphereProb_norm_le d
  have h2 : -Real.log (S + 1) ≤ ∫ p, -Real.log ‖p.1 - p.2‖ ∂(ν.prod (unitSphereProb d)) := by
    have hb : ∀ᵐ p ∂(ν.prod (unitSphereProb d)), -Real.log (S + 1) ≤ -Real.log ‖p.1 - p.2‖ := by
      have e1 : ∀ᵐ p ∂(ν.prod (unitSphereProb d)), ‖p.1‖ ≤ S :=
        Measure.quasiMeasurePreserving_fst.ae hsν
      have e2 : ∀ᵐ p ∂(ν.prod (unitSphereProb d)), ‖p.2‖ ≤ 1 :=
        Measure.quasiMeasurePreserving_snd.ae hσ1
      filter_upwards [e1, e2] with p hp1 hp2
      rw [neg_le_neg_iff]
      exact frame_log_le_log_of_norm_le (norm_nonneg _)
        ((norm_sub_le _ _).trans (by linarith)) (by linarith)
    have := integral_mono_ae (integrable_const (-Real.log (S + 1))) iνσ hb
    rwa [integral_const, probReal_univ, one_smul] at this
  have h3 : -Real.log (S + 1) ≤ ∫ p, -Real.log ‖p.1 - p.2‖ ∂((unitSphereProb d).prod ν) := by
    have hb : ∀ᵐ p ∂((unitSphereProb d).prod ν), -Real.log (S + 1) ≤ -Real.log ‖p.1 - p.2‖ := by
      have e1 : ∀ᵐ p ∂((unitSphereProb d).prod ν), ‖p.1‖ ≤ 1 :=
        Measure.quasiMeasurePreserving_fst.ae hσ1
      have e2 : ∀ᵐ p ∂((unitSphereProb d).prod ν), ‖p.2‖ ≤ S :=
        Measure.quasiMeasurePreserving_snd.ae hsν
      filter_upwards [e1, e2] with p hp1 hp2
      rw [neg_le_neg_iff]
      exact frame_log_le_log_of_norm_le (norm_nonneg _)
        ((norm_sub_le _ _).trans (by linarith)) (by linarith)
    have := integral_mono_ae (integrable_const (-Real.log (S + 1))) iσν hb
    rwa [integral_const, probReal_univ, one_smul] at this
  -- (3) the energy of `σ₁`
  have h4 : ∫ p, -Real.log ‖p.1 - p.2‖ ∂((unitSphereProb d).prod (unitSphereProb d)) =
      sphEnergy d := by
    have e := logEnergy_sphMeas_self hd one_pos (0 : Rd d)
    rw [frame_sphMeas_one_zero, Real.log_one, neg_zero, zero_add] at e
    exact e
  unfold HigherDimLFPP.logCov
  rw [h4]
  linarith [le_abs_self (sphEnergy d)]

end HigherDimLQGContinuity
