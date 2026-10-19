import GaussianLQG.Field.Realization.Potential
import LQGMetric.Field.CircleAvgRate

/-!
# Mollified measures and the energy decay of mollification (blueprint Lemmas 1.10, 2.4)

For a finite measure `ρ` on `ℂ` and the mollifier `ψ_m = bumpTest m 0` of `LQGMetric` (radius
`2^{-m}`), `moll m ρ` is the law of `X + Y` with `X ∼ ρ` and `Y ∼ ψ_m` independent, i.e.
`ρ * ψ_m`. It has the same mass and ball-mass bound as `ρ` (`ballBound_moll`,
`isRegular_moll`), and `∫ f d(moll m ρ) = ∫ (∫ ψ_{m,x} f) dρ(x)` (`integral_moll_eq`).

`abs_energy_moll_sub_le`: `|ℰ(ρ * ψ_m, ν) - ℰ(ρ, ν)| ≤ ρ(ℂ) K 2^{-ms}`, from the Hölder
continuity of the potential `G_ν` (`Potential.lean`). With a GFF frame this gives the geometric
decay `∑_k (∫ e_k d(ρ * ψ_m) - ∫ e_k dρ)² ≤ 2 ρ(ℂ) K 2^{-ms}` (`tsum_sq_frame_moll_sub_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace GaussianLQG
namespace Realization

open LQGMetric

/-! ### The mollifier law -/

/-- The probability law with density `ψ_m = bumpTest m 0`. -/
def bumpLaw (m : ℕ) : Measure ℂ := volume.withDensity fun y => ENNReal.ofReal (bumpTest m 0 y)

lemma measurable_bumpTest (m : ℕ) (x : ℂ) : Measurable fun y => bumpTest m x y :=
  (bumpTest m x).continuous.measurable

lemma integrable_bumpTest (m : ℕ) (x : ℂ) : Integrable fun y => bumpTest m x y :=
  (bumpTest m x).continuous.integrable_of_hasCompactSupport (bumpTest m x).hasCompactSupport

lemma bumpLaw_univ (m : ℕ) : bumpLaw m univ = 1 := by
  rw [bumpLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_bumpTest m 0)
      (Eventually.of_forall fun y => CircleAvg.bumpTest_nonneg m 0 y),
    CircleAvg.integral_bumpTest', ENNReal.ofReal_one]

instance (m : ℕ) : IsProbabilityMeasure (bumpLaw m) := ⟨bumpLaw_univ m⟩

lemma integral_bumpLaw (m : ℕ) (f : ℂ → ℝ) :
    ∫ y, f y ∂bumpLaw m = ∫ y, bumpTest m 0 y * f y := by
  rw [bumpLaw, integral_withDensity_eq_integral_toReal_smul
    (measurable_bumpTest m 0).ennreal_ofReal
    (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (CircleAvg.bumpTest_nonneg m 0 y)]

lemma bumpLaw_compl_closedBall (m : ℕ) :
    bumpLaw m (closedBall (0 : ℂ) ((2 : ℝ)⁻¹ ^ m))ᶜ = 0 := by
  rw [bumpLaw, withDensity_apply _ measurableSet_closedBall.compl]
  refine (setLIntegral_eq_zero_iff measurableSet_closedBall.compl
    (measurable_bumpTest m 0).ennreal_ofReal).mpr
    (Eventually.of_forall fun y hy => ?_)
  rw [mem_compl_iff, mem_closedBall, not_le] at hy
  rw [CircleAvg.bumpTest_eq_zero_of_le m hy.le, ENNReal.ofReal_zero]

lemma ae_bumpLaw_norm_le (m : ℕ) : ∀ᵐ y ∂bumpLaw m, ‖y‖ ≤ (2 : ℝ)⁻¹ ^ m := by
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) (bumpLaw_compl_closedBall m)
  simp only [not_le, mem_ofPred_eq] at hy
  simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
  exact hy

/-! ### The mollified measure -/

/-- The mollified measure `ρ * ψ_m`: the law of `X + Y`, `X ∼ ρ`, `Y ∼ ψ_m`. -/
def moll (m : ℕ) (ρ : Measure ℂ) : Measure ℂ :=
  (ρ.prod (bumpLaw m)).map fun p => p.1 + p.2

variable {ρ : Measure ℂ} {m : ℕ}

lemma measurable_add_pair : Measurable fun p : ℂ × ℂ => p.1 + p.2 :=
  measurable_fst.add measurable_snd

lemma moll_apply {s : Set ℂ} (hs : MeasurableSet s) :
    moll m ρ s = (ρ.prod (bumpLaw m)) ((fun p : ℂ × ℂ => p.1 + p.2) ⁻¹' s) :=
  Measure.map_apply measurable_add_pair hs

lemma moll_univ [SFinite ρ] : moll m ρ univ = ρ univ := by
  rw [moll_apply MeasurableSet.univ, preimage_univ, ← univ_prod_univ, Measure.prod_prod,
    bumpLaw_univ, mul_one]

instance [IsFiniteMeasure ρ] : IsFiniteMeasure (moll m ρ) := by
  rw [moll]; infer_instance

lemma moll_real_univ [IsFiniteMeasure ρ] : (moll m ρ).real univ = ρ.real univ := by
  simp only [measureReal_def, moll_univ]

lemma moll_ball [SFinite ρ] (u : ℂ) (r : ℝ) :
    moll m ρ (ball u r) = ∫⁻ y, ρ (ball (u - y) r) ∂bumpLaw m := by
  rw [moll_apply measurableSet_ball,
    Measure.prod_apply_symm (measurable_add_pair measurableSet_ball)]
  refine lintegral_congr fun y => ?_
  congr 1
  ext x
  simp only [mem_preimage, mem_ball, dist_eq_norm]
  rw [show x + y - u = x - (u - y) by ring]

/-- The mollified measure satisfies the same ball-mass bound. -/
lemma ballBound_moll [IsFiniteMeasure ρ] {C α : ℝ} (hb : BallBound ρ C α) :
    BallBound (moll m ρ) C α := fun u r hr hr1 => by
  have h : moll m ρ (ball u r) ≤ ENNReal.ofReal (C * r ^ α) := by
    rw [moll_ball]
    calc ∫⁻ y, ρ (ball (u - y) r) ∂bumpLaw m ≤ ∫⁻ _, ENNReal.ofReal (C * r ^ α) ∂bumpLaw m :=
          lintegral_mono fun y => hb.measure_ball_le (u - y) hr hr1
      _ = ENNReal.ofReal (C * r ^ α) := by rw [lintegral_const, measure_univ, mul_one]
  have h0 : 0 ≤ C * r ^ α := mul_nonneg hb.nonneg (Real.rpow_nonneg hr.le _)
  exact ENNReal.toReal_le_of_le_ofReal h0 h

lemma moll_compl_closedBall [IsFiniteMeasure ρ] {R : ℝ} (hR : ρ (closedBall (0 : ℂ) R)ᶜ = 0) :
    moll m ρ (closedBall (0 : ℂ) (R + 1))ᶜ = 0 := by
  rw [moll_apply measurableSet_closedBall.compl]
  have hsub : (fun p : ℂ × ℂ => p.1 + p.2) ⁻¹' (closedBall (0 : ℂ) (R + 1))ᶜ ⊆
      ((closedBall (0 : ℂ) R)ᶜ ×ˢ univ) ∪ (univ ×ˢ (closedBall (0 : ℂ) ((2 : ℝ)⁻¹ ^ m))ᶜ) := by
    intro p hp
    simp only [mem_preimage, mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hp
    by_contra hcon
    simp only [mem_union, mem_prod, mem_compl_iff, mem_closedBall, dist_zero_right, not_le,
      mem_univ, and_true, true_and, not_or, not_lt] at hcon
    have h2 : (2 : ℝ)⁻¹ ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have := norm_add_le p.1 p.2
    linarith [hcon.1, hcon.2]
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hR, zero_mul]
  · rw [Measure.prod_prod, bumpLaw_compl_closedBall, mul_zero]

/-- The mollified measure of a regular measure is regular. -/
theorem isRegular_moll {ρ : Measure ℂ} (hρ : IsRegular ρ) (m : ℕ) : IsRegular (moll m ρ) := by
  obtain ⟨hfin, ⟨R, hR⟩, C, α, hα, hb⟩ := hρ
  exact ⟨inferInstance, ⟨R + 1, moll_compl_closedBall hR⟩, C, α, hα, ballBound_moll hb⟩

/-! ### Integrals against the mollified measure -/

/-- A continuous function is integrable against a finite measure concentrated on a ball. -/
lemma integrable_of_continuous_of_compl_closedBall {μ : Measure ℂ} [IsFiniteMeasure μ]
    {f : ℂ → ℝ} (hf : Continuous f) {R : ℝ} (hR : μ (closedBall (0 : ℂ) R)ᶜ = 0) :
    Integrable f μ := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hf.continuousOn
  refine (integrable_const M).mono' hf.aestronglyMeasurable ?_
  filter_upwards [ae_norm_le_of_compl_closedBall_eq_zero hR] with x hx
  exact hM x (by rwa [mem_closedBall, dist_zero_right])

lemma integral_moll [SFinite ρ] {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f (moll m ρ)) :
    ∫ z, f z ∂moll m ρ = ∫ x, ∫ y, f (x + y) ∂bumpLaw m ∂ρ := by
  rw [moll, integral_map measurable_add_pair.aemeasurable hf.aestronglyMeasurable]
  have hi : Integrable (fun p : ℂ × ℂ => f (p.1 + p.2)) (ρ.prod (bumpLaw m)) :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_add_pair.aemeasurable).mp hfi
  exact integral_prod _ hi

lemma integral_bumpLaw_add (m : ℕ) (f : ℂ → ℝ) (x : ℂ) :
    ∫ y, f (x + y) ∂bumpLaw m = ∫ y, bumpTest m x y * f y := by
  rw [integral_bumpLaw]
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℂ))
    (fun y => bumpTest m 0 y * f (x + y)) x
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [CircleAvg.bumpTest_eq_sub m x y, add_sub_cancel]

/-- `∫ f d(ρ * ψ_m) = ∫ (∫ ψ_{m,x} f) dρ(x)`. -/
theorem integral_moll_eq [SFinite ρ] {f : ℂ → ℝ} (hf : Measurable f)
    (hfi : Integrable f (moll m ρ)) :
    ∫ z, f z ∂moll m ρ = ∫ x, (∫ y, bumpTest m x y * f y) ∂ρ := by
  rw [integral_moll hf hfi]
  exact integral_congr_ae (Eventually.of_forall fun x => integral_bumpLaw_add m f x)

/-! ### Energy decay -/

/-- **Mollification changes the energy by `O(2^{-ms})`.** -/
theorem abs_energy_moll_sub_le [IsFiniteMeasure ρ] {Rρ : ℝ}
    (hRρ : ρ (closedBall (0 : ℂ) Rρ)ᶜ = 0) {ν : Measure ℂ} [IsFiniteMeasure ν] {C α Rν : ℝ}
    (hb : BallBound ν C α) (hα : 0 < α) (hRν : ν (closedBall (0 : ℂ) Rν)ᶜ = 0) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hsα : s < α) (m : ℕ) :
    |energy (moll m ρ) ν - energy ρ ν| ≤ ρ.real univ * holderK ν C α s * ((2 : ℝ)⁻¹ ^ m) ^ s := by
  have hGc : Continuous (potG ν) := continuous_potG hb hα hRν
  have hK := holderK_nonneg hb hs hsα
  have e1 : energy (moll m ρ) ν = ∫ x, ∫ y, potG ν (x + y) ∂bumpLaw m ∂ρ :=
    integral_moll hGc.measurable
      (integrable_of_continuous_of_compl_closedBall hGc (moll_compl_closedBall hRρ))
  have hρi : Integrable (potG ν) ρ := integrable_of_continuous_of_compl_closedBall hGc hRρ
  have hprod : Integrable (fun p : ℂ × ℂ => potG ν (p.1 + p.2)) (ρ.prod (bumpLaw m)) :=
    (integrable_map_measure hGc.measurable.aestronglyMeasurable
      measurable_add_pair.aemeasurable).mp
      (integrable_of_continuous_of_compl_closedBall hGc (moll_compl_closedBall hRρ))
  have hin : Integrable (fun x => ∫ y, potG ν (x + y) ∂bumpLaw m) ρ := hprod.integral_prod_left
  have hslice : ∀ x, Integrable (fun y => potG ν (x + y)) (bumpLaw m) := fun x =>
    integrable_of_continuous_of_compl_closedBall (hGc.comp (continuous_const.add continuous_id))
      (bumpLaw_compl_closedBall m)
  have e2 : energy (moll m ρ) ν - energy ρ ν =
      ∫ x, (∫ y, (potG ν (x + y) - potG ν x) ∂bumpLaw m) ∂ρ := by
    rw [e1, show energy ρ ν = ∫ x, potG ν x ∂ρ from rfl, ← integral_sub hin hρi]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_sub (hslice x) (integrable_const _), integral_const, probReal_univ,
      one_smul]
  have hm1 : (2 : ℝ)⁻¹ ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hbound : ∀ x, ‖∫ y, (potG ν (x + y) - potG ν x) ∂bumpLaw m‖ ≤
      holderK ν C α s * ((2 : ℝ)⁻¹ ^ m) ^ s := by
    intro x
    have h := norm_integral_le_of_norm_le_const (μ := bumpLaw m)
      (f := fun y => potG ν (x + y) - potG ν x) (C := holderK ν C α s * ((2 : ℝ)⁻¹ ^ m) ^ s) (by
        filter_upwards [ae_bumpLaw_norm_le m] with y hy
        have hxy : ‖(x + y) - x‖ ≤ 1 := by rw [add_sub_cancel_left]; linarith
        refine (Real.norm_eq_abs _ ▸ abs_potG_sub_le hb hα hRν hs hs1 hsα hxy).trans ?_
        rw [add_sub_cancel_left]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hy hs.le) hK)
    rwa [probReal_univ, mul_one] at h
  rw [e2]
  have h := norm_integral_le_of_norm_le_const (μ := ρ) (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at h
  calc _ ≤ holderK ν C α s * ((2 : ℝ)⁻¹ ^ m) ^ s * ρ.real univ := h
    _ = ρ.real univ * holderK ν C α s * ((2 : ℝ)⁻¹ ^ m) ^ s := by ring

/-! ### Consequences for a GFF frame -/

/-- Polarized frame identity for a difference of two regular measures. -/
theorem hasSum_sq_frame_sub {e : ℕ → ℂ → ℝ} (hframe : IsGFFFrame e) {μ ν : Measure ℂ}
    (hμ : IsRegular μ) (hν : IsRegular ν) :
    HasSum (fun k => (∫ z, e k z ∂μ - ∫ z, e k z ∂ν) ^ 2)
      (energy μ μ - energy μ ν - energy ν μ + energy ν ν) := by
  have h := (((hframe.2.2 μ μ hμ hμ).sub (hframe.2.2 μ ν hμ hν)).sub
    (hframe.2.2 ν μ hν hμ)).add (hframe.2.2 ν ν hν hν)
  refine h.congr_fun fun k => ?_
  ring

/-- **Geometric decay of the frame coefficients of `ρ * ψ_m - ρ`.** -/
theorem frame_moll_decay {e : ℕ → ℂ → ℝ} (hframe : IsGFFFrame e) {ρ : Measure ℂ}
    (hρ : IsRegular ρ) :
    ∃ K q : ℝ, 0 ≤ K ∧ 0 < q ∧ q < 1 ∧ ∀ m : ℕ,
      Summable (fun k => (∫ z, e k z ∂moll m ρ - ∫ z, e k z ∂ρ) ^ 2) ∧
        ∑' k, (∫ z, e k z ∂moll m ρ - ∫ z, e k z ∂ρ) ^ 2 ≤ K * q ^ m := by
  obtain ⟨hfin, ⟨R, hR⟩, C, α, hα, hb⟩ := hρ
  set s : ℝ := min α 1 / 2 with hsdef
  have hs : 0 < s := by positivity
  have hs1 : s ≤ 1 := by
    have : min α 1 ≤ 1 := min_le_right _ _
    linarith
  have hsα : s < α := by
    have : min α 1 ≤ α := min_le_left _ _
    have : 0 < min α 1 := lt_min hα one_pos
    linarith
  set K₀ := holderK ρ C α s with hK₀
  have hK₀0 : 0 ≤ K₀ := holderK_nonneg hb hs hsα
  set q : ℝ := (2 : ℝ)⁻¹ ^ s with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) s
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hs
  refine ⟨2 * ρ.real univ * K₀, q, by positivity, hq0, hq1, fun m => ?_⟩
  have hρm : IsRegular (moll m ρ) := isRegular_moll ⟨hfin, ⟨R, hR⟩, C, α, hα, hb⟩ m
  have h := hasSum_sq_frame_sub hframe hρm ⟨hfin, ⟨R, hR⟩, C, α, hα, hb⟩
  refine ⟨h.summable, ?_⟩
  rw [h.tsum_eq]
  have hpow : ((2 : ℝ)⁻¹ ^ m) ^ s = q ^ m := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  have hKm : holderK (moll m ρ) C α s = K₀ := by
    simp only [holderK, negMoment, moll_real_univ, hK₀]
  have h1 := abs_energy_moll_sub_le hR (ν := moll m ρ) (ballBound_moll hb) hα
    (moll_compl_closedBall hR) hs hs1 hsα m
  have h2 := abs_energy_moll_sub_le hR (ν := ρ) hb hα hR hs hs1 hsα m
  rw [hKm, hpow] at h1
  rw [hpow] at h2
  have e1 : energy (moll m ρ) (moll m ρ) - energy (moll m ρ) ρ - energy ρ (moll m ρ) +
      energy ρ ρ = (energy (moll m ρ) (moll m ρ) - energy ρ (moll m ρ)) -
        (energy (moll m ρ) ρ - energy ρ ρ) := by ring
  rw [e1]
  have h3 := le_abs_self (energy (moll m ρ) (moll m ρ) - energy ρ (moll m ρ))
  have h4 := neg_abs_le (energy (moll m ρ) ρ - energy ρ ρ)
  have h5 : ρ.real univ * K₀ * q ^ m + ρ.real univ * K₀ * q ^ m = 2 * ρ.real univ * K₀ * q ^ m := by
    ring
  linarith

end Realization
end GaussianLQG
