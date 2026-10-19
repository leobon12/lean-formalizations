import HigherDimLFPP.Field.Transport

/-!
# Basic variance bounds: Lemma 3.0 and the single-measure bound (3.12′) (packet P-F2, target T4)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1), Lemma 3.4(a) and its uses in Lemma 4.1
("`Var H_root ≤ C_d` by the calculation in Lemma 3.4(a)") and (5.19); planning audit HA2
(`planning/audits/HA2-section-3.md`), findings HA2-12 and HA2-15, Details D1.4 ((F1), (F2)) and
D8(a); HA3 D3(a) (root variance).

* Lemma 3.0 for point masses, at the level of `scaleCov` (`k_{a,b,z}` is `bandVecM` of `δ_z`):
  - (F1) `scaleCov_dirac_zero`: `Cov(H_{a,b}(z), H_{a,b}(w)) = ∫_a^b C((z - w)/t) dt/t`, and
    `scaleCov_dirac_self`: `Var H_{a,b}(z) = log(b/a)`;
  - (F2) `exists_scaleCov_dirac_sub_le`: `E(H_{a,b}(z) - H_{a,b}(w))² ≤ L |z - w|² / a²` (every `b`).
* (3.12′) `single_measure_bound` (HA2-12): for a probability measure with the growth bound (3.4)
  at scale `1` and every measurable `S ⊆ (0, ∞)` of finite length, `⟨H_S, μ⟩` is defined and
  `Var⟨H_S, μ⟩ ≤ C |S|`; and (3.12) for differences, `Var⟨H_S, μ - ν⟩ ≤ 4 C |S|`
  (`pair_measure_bound`).  This covers the root variance `Var⟨H_{ε,1}, ν_{[0,e₁]}⟩ ≤ C` of
  Lemma 4.1 (HA3 D3(a)) and Lemma 3.4(a) (`scaleCov_fine_scales_le`).

Proof of (3.12′) (HA2 D8(a)): `|C| ≤ 1` and `supp C ⊆ B̄(0, 2ρ_κ)` give
`∫∫ C((z - w)/t) dμ dμ / t ≤ t⁻¹ sup_z μ(B̄(z, 2ρ_κ t)) ≤ 2ρ_κ B` at every scale `t > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ}

/-! ### Lemma 3.0: point masses -/

theorem isPairable_dirac_zero (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ) (z : Rd d) :
    IsPairable κ (Ioo a b) (Measure.dirac z) 0 := by
  rw [IsPairable, bandFun_dirac, bandFun_zero_measure, sub_zero]
  exact memLp_bandKernel hκ ha b z

/-- **(F1)**: `Cov(H_{a,b}(z), H_{a,b}(w)) = ∫_{(a,b)} C(t⁻¹(z - w)) dt/t`. -/
theorem scaleCov_dirac_zero (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ) (z w : Rd d) :
    scaleCov κ (Ioo a b) (Measure.dirac z) 0 (Measure.dirac w) 0 =
      ∫ t in Ioo a b, autoCorr κ (t⁻¹ • (z - w)) / t := by
  rw [scaleCov, bandVecM_dirac_zero, bandVecM_dirac_zero, inner_bandVec hκ ha ha, max_self,
    min_self]

/-- **(F1)**: `Var H_{a,b}(z) = log(b/a)` for `0 < a ≤ b`. -/
theorem scaleCov_dirac_self (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (z : Rd d) :
    scaleCov κ (Ioo a b) (Measure.dirac z) 0 (Measure.dirac z) 0 = Real.log (b / a) := by
  rw [scaleCov, bandVecM_dirac_zero, real_inner_self_eq_norm_sq, norm_bandVec_sq hκ ha hab]

/-- The kernel vector of `δ_z - δ_w` is `k_{a,b,z} - k_{a,b,w}`. -/
theorem bandVecM_dirac_dirac (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ) (z w : Rd d) :
    bandVecM κ (Ioo a b) (Measure.dirac z) (Measure.dirac w) = bandVec κ a b z - bandVec κ a b w := by
  rw [bandVecM_sub (isPairable_dirac_zero hκ ha b z) (isPairable_dirac_zero hκ ha b w),
    bandVecM_dirac_zero, bandVecM_dirac_zero]

/-- **(F2), increment variance**: there is `L` with
`E(H_{a,b}(z) - H_{a,b}(w))² ≤ L |z - w|² / a²` for all `0 < a`, all `b` and all `z, w`. -/
theorem exists_scaleCov_dirac_sub_le (hκ : IsLFPPKernel κ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, 0 < a → ∀ (b : ℝ) (z w : Rd d),
      IsPairable κ (Ioo a b) (Measure.dirac z) (Measure.dirac w) ∧
        scaleCov κ (Ioo a b) (Measure.dirac z) (Measure.dirac w) (Measure.dirac z)
          (Measure.dirac w) ≤ L * ‖z - w‖ ^ 2 / a ^ 2 := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_bandVec_sub_sq_le hκ
  refine ⟨L, hL0, fun a ha b z w => ⟨?_, ?_⟩⟩
  · exact isPairable_of_subset_Icc hκ measurableSet_Ioo ha Ioo_subset_Icc_self _ _
  · rw [scaleCov, bandVecM_dirac_dirac hκ ha, real_inner_self_eq_norm_sq]
    exact hL a ha b z w

/-! ### The single-measure bound (3.12′) -/

/-- `scalePair κ t μ 0 μ 0 = ∫∫ C(t⁻¹(z - w))/t dμ dμ`. -/
theorem scalePair_zero (κ : Rd d → ℝ) (t : ℝ) (μ : Measure (Rd d)) :
    scalePair κ t μ 0 μ 0 = ∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(μ.prod μ) := by
  simp only [scalePair, mixInt, Measure.prod_zero, Measure.zero_prod, integral_zero_measure,
    sub_zero, add_zero]

/-- **HA2 D8(a)**: at every scale `t > 0`, `‖μ * K_t‖₂² ≤ 2ρ_κ B` for a probability measure with
the growth bound (3.4) at scale `1` (`ρ_κ` a support radius of `κ`). -/
theorem scalePair_zero_le (hκ : IsLFPPKernel κ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {t : ℝ} (ht : 0 < t) {μ : Measure (Rd d)}
    [IsProbabilityMeasure μ] {B : ℝ} (hB : 0 ≤ B) (hμ : GrowthBound μ B 1) :
    scalePair κ t μ 0 μ 0 ≤ 2 * ρ * B := by
  rw [scalePair_zero, integral_prod _ (integrable_autoCorr_div hκ t μ μ)]
  have hin : ∀ z : Rd d, ∫ w, autoCorr κ (t⁻¹ • (z - w)) / t ∂μ ≤ 2 * ρ * B := by
    intro z
    have hpt : ∀ w, autoCorr κ (t⁻¹ • (z - w)) / t ≤
        (closedBall z (2 * ρ * t)).indicator (fun _ => t⁻¹) w := by
      intro w
      by_cases hw : w ∈ closedBall z (2 * ρ * t)
      · rw [indicator_of_mem hw, div_eq_mul_inv]
        calc autoCorr κ (t⁻¹ • (z - w)) * t⁻¹ ≤ 1 * t⁻¹ :=
              mul_le_mul_of_nonneg_right (autoCorr_le_one hκ _) (inv_nonneg.2 ht.le)
          _ = t⁻¹ := one_mul _
      · rw [indicator_of_notMem hw]
        rw [mem_closedBall, dist_eq_norm, not_le] at hw
        have h2 : 2 * ρ ≤ ‖t⁻¹ • (z - w)‖ := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), norm_sub_rev, inv_mul_eq_div,
            le_div_iff₀ ht]
          exact hw.le
        rw [autoCorr_eq_zero_of_two_mul_le hρ h2, zero_div]
    have hi1 : Integrable (fun w => autoCorr κ (t⁻¹ • (z - w)) / t) μ := by
      refine Integrable.of_bound (((continuous_autoCorr hκ).comp
        ((continuous_const.sub continuous_id).const_smul t⁻¹)).div_const t).aestronglyMeasurable
        |t⁻¹| (Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_div, div_eq_mul_inv, abs_inv]
      calc |autoCorr κ (t⁻¹ • (z - w))| * |t|⁻¹ ≤ 1 * |t|⁻¹ :=
            mul_le_mul_of_nonneg_right (abs_autoCorr_le_one hκ _) (inv_nonneg.2 (abs_nonneg t))
        _ = |t|⁻¹ := one_mul _
    have hi2 : Integrable ((closedBall z (2 * ρ * t)).indicator fun _ => t⁻¹) μ :=
      (integrable_indicator_iff measurableSet_closedBall).2 (integrable_const _).integrableOn
    calc ∫ w, autoCorr κ (t⁻¹ • (z - w)) / t ∂μ
        ≤ ∫ w, (closedBall z (2 * ρ * t)).indicator (fun _ => t⁻¹) w ∂μ :=
          integral_mono hi1 hi2 hpt
      _ = t⁻¹ * μ.real (closedBall z (2 * ρ * t)) := by
          rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_comm]
      _ ≤ t⁻¹ * (B * (2 * ρ * t / 1)) :=
          mul_le_mul_of_nonneg_left (hμ.le_div hB z (by positivity)) (inv_nonneg.2 ht.le)
      _ = 2 * ρ * B := by field_simp
  calc ∫ z, ∫ w, autoCorr κ (t⁻¹ • ((z, w).1 - (z, w).2)) / t ∂μ ∂μ
      ≤ ∫ _z, 2 * ρ * B ∂μ :=
        integral_mono (integrable_autoCorr_div hκ t μ μ).integral_prod_left (integrable_const _)
          hin
    _ = 2 * ρ * B := by rw [integral_const, probReal_univ, one_smul]

/-- **(3.12′), the single-measure bound** (target T4; HA2-12, D8(a)): for every `B` there is
`C = C(d, κ, B)` such that for every probability measure `μ` with the growth bound (3.4) at scale
`1` and every measurable `S ⊆ (0, ∞)` of finite length, `⟨H_S, μ⟩` is defined and
`Var⟨H_S, μ⟩ ≤ C |S|`. -/
theorem single_measure_bound (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set ℝ), MeasurableSet S → S ⊆ Ioi 0 → volume S ≠ ⊤ →
      ∀ (μ : Measure (Rd d)) [IsProbabilityMeasure μ], GrowthBound μ B 1 →
        IsPairable κ S μ 0 ∧ scaleCov κ S μ 0 μ 0 ≤ C * volume.real S := by
  obtain ⟨ρ, hρ0, hρ⟩ := hκ.exists_radius
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  refine ⟨2 * ρ * B', by positivity, fun S hS hS0 hSf μ _ hμ => ?_⟩
  have hμ' := hμ.max_zero one_pos
  have hle : ∀ t ∈ S, scalePair κ t μ 0 μ 0 ≤ 2 * ρ * B' := fun t ht =>
    scalePair_zero_le hκ hρ0 hρ (hS0 ht) hB'0 hμ'
  have hgi : IntegrableOn (fun _ => 2 * ρ * B') S := integrableOn_const hSf
  have hp : IsPairable κ S μ 0 := isPairable_of_le hκ hS hS0 μ 0 hgi hle
  refine ⟨hp, ?_⟩
  rw [scaleCov_eq_integral hκ hS hS0 hp hp]
  calc ∫ t in S, scalePair κ t μ 0 μ 0 ≤ ∫ _t in S, 2 * ρ * B' :=
        setIntegral_mono_on (integrableOn_scalePair hκ hS hS0 hp hp) hgi hS hle
    _ = 2 * ρ * B' * volume.real S := by rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Pairability of `μ - ν` from that of `μ` and `ν` separately. -/
theorem IsPairable.of_zero {S : Set ℝ} {μ ν : Measure (Rd d)} (hμ : IsPairable κ S μ 0)
    (hν : IsPairable κ S ν 0) : IsPairable κ S μ ν := by
  have e : bandFun κ S μ - bandFun κ S ν =
      (bandFun κ S μ - bandFun κ S 0) - (bandFun κ S ν - bandFun κ S 0) := by
    rw [bandFun_zero_measure, sub_zero, sub_zero]
  rw [IsPairable, e]
  exact MemLp.sub hμ hν

/-- **(3.12) for differences** (HA2 D8(a)): `Var⟨H_S, μ - ν⟩ ≤ 4 C |S|` for probability measures
with the growth bound (3.4) at scale `1`. -/
theorem pair_measure_bound (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set ℝ), MeasurableSet S → S ⊆ Ioi 0 → volume S ≠ ⊤ →
      ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        GrowthBound μ B 1 → GrowthBound ν B 1 →
        IsPairable κ S μ ν ∧ scaleCov κ S μ ν μ ν ≤ C * volume.real S := by
  obtain ⟨C, hC0, hC⟩ := single_measure_bound hκ B
  refine ⟨4 * C, by positivity, fun S hS hS0 hSf μ ν _ _ hμ hν => ?_⟩
  obtain ⟨hpμ, hbμ⟩ := hC S hS hS0 hSf μ hμ
  obtain ⟨hpν, hbν⟩ := hC S hS hS0 hSf ν hν
  refine ⟨hpμ.of_zero hpν, ?_⟩
  rw [scaleCov_self, bandVecM_sub hpμ hpν]
  rw [scaleCov_self] at hbμ hbν
  have h1 := norm_sub_le (bandVecM κ S μ 0) (bandVecM κ S ν 0)
  have h2 : ‖bandVecM κ S μ 0 - bandVecM κ S ν 0‖ ^ 2 ≤
      2 * ‖bandVecM κ S μ 0‖ ^ 2 + 2 * ‖bandVecM κ S ν 0‖ ^ 2 := by
    nlinarith [sq_nonneg (‖bandVecM κ S μ 0‖ - ‖bandVecM κ S ν 0‖), norm_nonneg (bandVecM κ S μ 0 -
      bandVecM κ S ν 0)]
  linarith

/-- **Lemma 3.4(a)**, (3.12) and (3.12′) in the form of HA2's `Lemma34a` (scales below `a`):
`Var⟨H_{0,a}, μ⟩ ≤ C a` and `Var⟨H_{0,a}, μ - ν⟩ ≤ C a` for all `a > 0`. -/
theorem scaleCov_fine_scales_le (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, ∀ a : ℝ, 0 < a → ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ]
      [IsProbabilityMeasure ν], GrowthBound μ B 1 → GrowthBound ν B 1 →
      IsPairable κ (Ioo 0 a) μ 0 ∧ scaleCov κ (Ioo 0 a) μ 0 μ 0 ≤ C * a ∧
        IsPairable κ (Ioo 0 a) μ ν ∧ scaleCov κ (Ioo 0 a) μ ν μ ν ≤ C * a := by
  obtain ⟨C, hC0, hC⟩ := single_measure_bound hκ B
  obtain ⟨C', hC'0, hC'⟩ := pair_measure_bound hκ B
  refine ⟨max C C', fun a ha μ ν _ _ hμ hν => ?_⟩
  have hS0 : Ioo 0 a ⊆ Ioi 0 := Ioo_subset_Ioi_self
  have hSf : volume (Ioo (0 : ℝ) a) ≠ ⊤ := measure_Ioo_lt_top.ne
  have hvol : volume.real (Ioo (0 : ℝ) a) = a := by
    rw [measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal ha.le]
  obtain ⟨h1, h2⟩ := hC (Ioo 0 a) measurableSet_Ioo hS0 hSf μ hμ
  obtain ⟨h3, h4⟩ := hC' (Ioo 0 a) measurableSet_Ioo hS0 hSf μ ν hμ hν
  rw [hvol] at h2 h4
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha.le), h3,
    h4.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le)⟩

end HigherDimLFPP
