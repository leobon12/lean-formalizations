import HigherDimLQGMetric.Sphere.Proc
import LQGMetric.Field.CircleAvgIndep

/-!
# Covariances of sphere averages of the LGF and the `L²` identification

Packet F3 (Phase A, block A1), target 2. MA0 Details (a) D-F3 ("covariances of differences are
`∫∫ log|u−v|⁻¹` against differences of uniform sphere measures"); MA4 §4 note 4 ("for an LGF,
`sphereAvg h r z` is a.s. the `L²` sphere average"); MA5 §3.3 note 4.

Points of the sphere-average process are `p = (ε, r, z)` with `ε ≥ 0`, `r > 0` (`SphPt d`); the
value at `p` is `sphProc (h ω) ε r z` (`= h_r(z)` for `ε = 0`) and its "law" is
`sphLaw r z ε` (`= σ_{r,z}` for `ε = 0`). For an LGF `h` and `d ≥ 2`:

* `IsWholeSpaceLGF.isGaussianProcess_sphIncProc`: the increments `V(p) - V(p')` together with all
  mean-zero pairings `⟨h, φ⟩` form a centred Gaussian process (a.s. limits of mean-zero pairings,
  LQGMetric's `isGaussianProcess_of_ae_tendsto`);
* `IsWholeSpaceLGF.covariance_sphIncProc`:
  `Cov(V(p₁) - V(p₂), V(p₃) - V(p₄)) = logCov(sphLaw p₁, sphLaw p₂, sphLaw p₃, sphLaw p₄)`;
* `IsWholeSpaceLGF.covariance_sphIncProc_apply`:
  `Cov(V(p₁) - V(p₂), ⟨h, φ⟩) = logCov(sphLaw p₁, sphLaw p₂, φ⁺ dz, φ⁻ dz)`;
* `exists_integral_sq_sphIncProc_le`: `E[(V(p) - V(p'))²] ≤ C (‖z - z'‖ + |r - r'| + |ε - ε'|) /
  min(r, r')` with `C = C(d)`;
* for the sphere averages themselves (`ε = 0`, `sphLaw r z 0 = sphMeas r z = σ_{r,z}`):
  `IsWholeSpaceLGF.covariance_sphereAvg_sub`, `IsWholeSpaceLGF.covariance_sphereAvg_sub_apply`,
  `IsWholeSpaceLGF.isGaussianProcess_sphereAvg_sub`, and the `L²` identification
  `IsWholeSpaceLGF.tendsto_integral_sq_sphDiff_sub` (`h_r(z) - h_ρ(w)` is the a.s. and `L²` limit
  of the mean-zero pairings `⟨h, sphDiff n z r n w ρ⟩`).

The covariance limits use the continuity of `logCov` of sphere laws in the scales
(`Sphere/Proc.lean`) and, against a mean-zero test function, the transport bound with the
normalized measures `φ^± dz / ‖φ^±‖₁` as second pair (`tendsto_logCov_sphLaw_posM`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### Transport bound against a general second pair -/

theorem growthBound_mono_const {μ : Measure (Rd d)} {B B' R : ℝ}
    (h : HigherDimLFPP.GrowthBound μ B R) (hBB : B ≤ B') (hR : 0 < R) :
    HigherDimLFPP.GrowthBound μ B' R := by
  intro z t ht
  exact (h z t ht).trans (mul_le_mul_of_nonneg_right hBB
    (le_min zero_le_one (div_nonneg ht.le hR.le)))

/-- The transport bound for two sphere laws against a coupled pair of probability measures
with a growth bound at scale `1`. -/
theorem exists_abs_logCov_sphLaw_pair_le (hd : 2 ≤ d) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r₁ r₂ : ℝ), 0 < r₁ → 0 < r₂ → ∀ (z₁ z₂ : Rd d) (ε₁ ε₂ : ℝ)
      (α β : Measure (Rd d)) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (v D : ℝ),
      0 ≤ v → HigherDimLFPP.GrowthBound α B 1 → HigherDimLFPP.GrowthBound β B 1 →
      HigherDimLFPP.CoupledWithin α β v → (∀ᵐ x ∂α, ‖x‖ ≤ D) → (∀ᵐ x ∂β, ‖x‖ ≤ D) →
      |HigherDimLFPP.logCov (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) α β| ≤
        C * Real.sqrt ((‖z₁ - z₂‖ + |r₁ - r₂| + |ε₁ - ε₂|) * v) / min r₁ r₂ := by
  obtain ⟨C, hC0, hC⟩ := HigherDimLFPP.transport_logCov_bound d (max B (2 ^ d))
  refine ⟨C, hC0, fun r₁ r₂ h₁ h₂ z₁ z₂ ε₁ ε₂ α β _ _ v D hv gα gβ cαβ sα sβ => ?_⟩
  have := isProbabilityMeasure_sphLaw (show 1 ≤ d by omega) r₁ z₁ ε₁
  have := isProbabilityMeasure_sphLaw (show 1 ≤ d by omega) r₂ z₂ ε₂
  have hB : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hBm : (0 : ℝ) ≤ max B (2 ^ d) := le_max_of_le_right hB
  have hR := lt_min h₁ h₂
  have g₁ := growthBound_mono_const (growthBound_mono_scale (growthBound_sphLaw hd h₁ z₁ ε₁) hB
    hR (min_le_left _ _)) (le_max_right B _) hR
  have g₂ := growthBound_mono_const (growthBound_mono_scale (growthBound_sphLaw hd h₂ z₂ ε₂) hB
    hR (min_le_right _ _)) (le_max_right B _) hR
  have g₃ := growthBound_mono_const gα (le_max_left B (2 ^ d)) one_pos
  have g₄ := growthBound_mono_const gβ (le_max_left B (2 ^ d)) one_pos
  set D' := (‖z₁‖ + |r₁| + |ε₁|) + (‖z₂‖ + |r₂| + |ε₂|) + |D| with hD'
  have s₁ : ∀ᵐ x ∂(sphLaw r₁ z₁ ε₁), ‖x‖ ≤ D' := by
    filter_upwards [ae_sphLaw_norm_le r₁ z₁ ε₁] with x hx
    have : 0 ≤ ‖z₂‖ + |r₂| + |ε₂| := by positivity
    have := abs_nonneg D
    linarith
  have s₂ : ∀ᵐ x ∂(sphLaw r₂ z₂ ε₂), ‖x‖ ≤ D' := by
    filter_upwards [ae_sphLaw_norm_le r₂ z₂ ε₂] with x hx
    have : 0 ≤ ‖z₁‖ + |r₁| + |ε₁| := by positivity
    have := abs_nonneg D
    linarith
  have s₃ : ∀ᵐ x ∂α, ‖x‖ ≤ D' := by
    filter_upwards [sα] with x hx
    have : 0 ≤ ‖z₁‖ + |r₁| + |ε₁| := by positivity
    have : 0 ≤ ‖z₂‖ + |r₂| + |ε₂| := by positivity
    have := le_abs_self D
    linarith
  have s₄ : ∀ᵐ x ∂β, ‖x‖ ≤ D' := by
    filter_upwards [sβ] with x hx
    have : 0 ≤ ‖z₁‖ + |r₁| + |ε₁| := by positivity
    have : 0 ≤ ‖z₂‖ + |r₂| + |ε₂| := by positivity
    have := le_abs_self D
    linarith
  exact hC _ _ _ _ (min r₁ r₂) 1 _ _ hR one_pos (by positivity) hv g₁ g₂ g₃ g₄
    (coupledWithin_sphLaw _ _ _ _ _ _) cαβ
    (HigherDimLFPP.logPairable_of_growthBound hR one_pos g₁ g₂ g₃ g₄ s₁ s₂ s₃ s₄)

/-- `(φ dz)/‖φ⁺‖₁` and `((-φ) dz)/‖φ⁻‖₁` for a bounded, boundedly supported `φ` of mean zero and
positive mass: probability measures with a growth bound at scale `1`, coupled within `2D`. -/
theorem exists_posM_normalized [NeZero d] {f : Rd d → ℝ} {M D : ℝ} (hf : IsBddSupp f M D)
    (hf0 : ∫ x, f x = 0) (hm : 0 < (posM f).real univ) :
    ∃ (α β : Measure (Rd d)) (B : ℝ), IsProbabilityMeasure α ∧ IsProbabilityMeasure β ∧
      posM f = ENNReal.ofReal ((posM f).real univ) • α ∧
      posM (-f) = ENNReal.ofReal ((posM f).real univ) • β ∧
      HigherDimLFPP.GrowthBound α B 1 ∧ HigherDimLFPP.GrowthBound β B 1 ∧
      HigherDimLFPP.CoupledWithin α β (2 * D) ∧ (∀ᵐ x ∂α, ‖x‖ ≤ D) ∧ (∀ᵐ x ∂β, ‖x‖ ≤ D) := by
  set m := (posM f).real univ with hmdef
  have hm' : (posM (-f)).real univ = m := (posM_real_univ_eq hf hf0).symm
  have := isFiniteMeasure_posM hf
  have := isFiniteMeasure_posM hf.neg
  set c : ℝ≥0∞ := ENNReal.ofReal m with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 hm).ne'
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have huniv : posM f univ = c := by rw [hc, hmdef, ofReal_measureReal (measure_ne_top _ _)]
  have huniv' : posM (-f) univ = c := by
    rw [hc, ← hm', ofReal_measureReal (measure_ne_top _ _)]
  refine ⟨c⁻¹ • posM f, c⁻¹ • posM (-f), (M * volBall d + m) / m, ⟨?_⟩, ⟨?_⟩, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [Measure.smul_apply, huniv, smul_eq_mul, ENNReal.inv_mul_cancel hc0 hct]
  · rw [Measure.smul_apply, huniv', smul_eq_mul, ENNReal.inv_mul_cancel hc0 hct]
  · rw [smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul]
  · rw [smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul]
  · -- growth bound of `α`
    intro x s hs
    have h1 := posM_real_closedBall_le hf x hs
    have h2 : (posM f).real (closedBall x s) ≤ m := measureReal_mono (subset_univ _)
    rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      hc, ENNReal.toReal_ofReal hm.le, ← measureReal_def, div_one]
    have hB1 : 1 ≤ (M * volBall d + m) / m := by
      rw [le_div_iff₀ hm, one_mul]
      have := hf.nonneg; have := volBall_nonneg (d := d); nlinarith
    rcases le_total 1 s with hs1 | hs1
    · rw [min_eq_left hs1, mul_one]
      calc m⁻¹ * (posM f).real (closedBall x s) ≤ m⁻¹ * m :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hm.le)
        _ = 1 := inv_mul_cancel₀ hm.ne'
        _ ≤ _ := hB1
    · rw [min_eq_right hs1]
      calc m⁻¹ * (posM f).real (closedBall x s) ≤ m⁻¹ * ((M * volBall d + m) * s) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hm.le)
        _ = (M * volBall d + m) / m * s := by field_simp
  · -- growth bound of `β`
    intro x s hs
    have h1 := posM_real_closedBall_le hf.neg x hs
    have h2 : (posM (-f)).real (closedBall x s) ≤ m := hm' ▸ measureReal_mono (subset_univ _)
    rw [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      hc, ENNReal.toReal_ofReal hm.le, ← measureReal_def, div_one, hm'] at *
    have hB1 : 1 ≤ (M * volBall d + m) / m := by
      rw [le_div_iff₀ hm, one_mul]
      have := hf.nonneg; have := volBall_nonneg (d := d); nlinarith
    rcases le_total 1 s with hs1 | hs1
    · rw [min_eq_left hs1, mul_one]
      calc m⁻¹ * (posM (-f)).real (closedBall x s) ≤ m⁻¹ * m :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hm.le)
        _ = 1 := inv_mul_cancel₀ hm.ne'
        _ ≤ _ := hB1
    · rw [min_eq_right hs1]
      calc m⁻¹ * (posM (-f)).real (closedBall x s) ≤ m⁻¹ * ((M * volBall d + m) * s) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hm.le)
        _ = (M * volBall d + m) / m * s := by field_simp
  · -- the product coupling
    have hα : IsProbabilityMeasure (c⁻¹ • posM f) :=
      ⟨by rw [Measure.smul_apply, huniv, smul_eq_mul, ENNReal.inv_mul_cancel hc0 hct]⟩
    have hβ : IsProbabilityMeasure (c⁻¹ • posM (-f)) :=
      ⟨by rw [Measure.smul_apply, huniv', smul_eq_mul, ENNReal.inv_mul_cancel hc0 hct]⟩
    refine ⟨(c⁻¹ • posM f).prod (c⁻¹ • posM (-f)), ?_, ?_, ?_⟩
    · rw [Measure.map_fst_prod, measure_univ, one_smul]
    · rw [Measure.map_snd_prod, measure_univ, one_smul]
    · have a1 := (Measure.quasiMeasurePreserving_fst (μ := c⁻¹ • posM f)
        (ν := c⁻¹ • posM (-f))).ae (Measure.ae_smul_measure (ae_posM_norm_le hf) c⁻¹)
      have a2 := (Measure.quasiMeasurePreserving_snd (μ := c⁻¹ • posM f)
        (ν := c⁻¹ • posM (-f))).ae (Measure.ae_smul_measure (ae_posM_norm_le hf.neg) c⁻¹)
      filter_upwards [a1, a2] with q hq1 hq2
      calc ‖q.1 - q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := norm_sub_le _ _
        _ ≤ 2 * D := by linarith
  · exact Measure.ae_smul_measure (ae_posM_norm_le hf) c⁻¹
  · exact Measure.ae_smul_measure (ae_posM_norm_le hf.neg) c⁻¹

/-- **`logCov` of sphere laws against a mean-zero density is continuous in the scales.** -/
theorem tendsto_logCov_sphLaw_posM (hd : 2 ≤ d) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (z₁ z₂ : Rd d) {s₁ s₂ : ℕ → ℝ} {ε₁ ε₂ : ℝ} (t₁ : Tendsto s₁ atTop (𝓝 ε₁))
    (t₂ : Tendsto s₂ atTop (𝓝 ε₂)) {f : Rd d → ℝ} {M D : ℝ} (hf : IsBddSupp f M D)
    (hf0 : ∫ x, f x = 0) :
    Tendsto (fun n => HigherDimLFPP.logCov (sphLaw r₁ z₁ (s₁ n)) (sphLaw r₂ z₂ (s₂ n))
        (posM f) (posM (-f))) atTop
      (𝓝 (HigherDimLFPP.logCov (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) (posM f) (posM (-f)))) := by
  have : NeZero d := ⟨by omega⟩
  have := isFiniteMeasure_posM hf
  rcases (measureReal_nonneg (μ := posM f) (s := univ)).eq_or_lt with hm | hm
  · -- zero mass: both measures vanish
    have h0 : posM f = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hm.symm
    have h0' : posM (-f) = 0 := by
      have := isFiniteMeasure_posM hf.neg
      rw [← Measure.measure_univ_eq_zero]
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1
        ((posM_real_univ_eq hf hf0) ▸ hm.symm)
    simp only [h0, h0', logCov_zero_right]
    exact tendsto_const_nhds
  obtain ⟨α, β, B, hα, hβ, eα, eβ, gα, gβ, cαβ, sα, sβ⟩ := exists_posM_normalized hf hf0 hm
  obtain ⟨C, hC0, hC⟩ := exists_abs_logCov_sphLaw_pair_le hd B
  rw [eα, eβ]
  simp only [logCov_smul_right]
  refine Tendsto.const_mul _ ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set b : ℕ → ℝ := fun n =>
    C * Real.sqrt ((‖z₁ - z₁‖ + |r₁ - r₁| + |s₁ n - ε₁|) * (2 * D)) / min r₁ r₁ +
      C * Real.sqrt ((‖z₂ - z₂‖ + |r₂ - r₂| + |s₂ n - ε₂|) * (2 * D)) / min r₂ r₂ with hb
  have hD : 0 ≤ D := by
    have h1 := hf.eq_zero
    by_contra hneg
    push Not at hneg
    have : ∀ x : Rd d, f x = 0 := fun x => h1 x (hneg.trans_le (norm_nonneg x))
    have : posM f = 0 := by
      simp only [posM, this, ENNReal.ofReal_zero]
      exact withDensity_zero
    rw [this] at hm
    simp at hm
  have hb0 : Tendsto b atTop (𝓝 0) := by
    have e1 := tendsto_mul_sqrt_mul_div C (min r₁ r₁)
      (tendsto_dist_triple_zero (z := z₁) (r := r₁) t₁) (tendsto_const_nhds (x := 2 * D))
    have e2 := tendsto_mul_sqrt_mul_div C (min r₂ r₂)
      (tendsto_dist_triple_zero (z := z₂) (r := r₂) t₂) (tendsto_const_nhds (x := 2 * D))
    have := e1.add e2
    rwa [add_zero] at this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb0
  rw [Real.norm_eq_abs]
  have hsplit : HigherDimLFPP.logCov (sphLaw r₁ z₁ (s₁ n)) (sphLaw r₂ z₂ (s₂ n)) α β -
      HigherDimLFPP.logCov (sphLaw r₁ z₁ ε₁) (sphLaw r₂ z₂ ε₂) α β =
      HigherDimLFPP.logCov (sphLaw r₁ z₁ (s₁ n)) (sphLaw r₁ z₁ ε₁) α β -
        HigherDimLFPP.logCov (sphLaw r₂ z₂ (s₂ n)) (sphLaw r₂ z₂ ε₂) α β := by
    unfold HigherDimLFPP.logCov; ring
  rw [hsplit]
  have k1 := hC r₁ r₁ h₁ h₁ z₁ z₁ (s₁ n) ε₁ α β (2 * D) D (by positivity) gα gβ cαβ sα sβ
  have k2 := hC r₂ r₂ h₂ h₂ z₂ z₂ (s₂ n) ε₂ α β (2 * D) D (by positivity) gα gβ cαβ sα sβ
  calc _ ≤ |HigherDimLFPP.logCov (sphLaw r₁ z₁ (s₁ n)) (sphLaw r₁ z₁ ε₁) α β| +
        |HigherDimLFPP.logCov (sphLaw r₂ z₂ (s₂ n)) (sphLaw r₂ z₂ ε₂) α β| := abs_sub _ _
    _ ≤ b n := add_le_add k1 k2

/-! ### The mixed covariance identity -/

theorem posM_max_zero (f : Rd d → ℝ) : posM (fun x => max (f x) 0) = posM f := by
  unfold posM
  congr 1
  funext x
  simp only
  rcases le_total (f x) 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

theorem posM_max_neg_zero (f : Rd d → ℝ) : posM (fun x => max (-f x) 0) = posM (-f) :=
  posM_max_zero (-f)

/-- `logCovF (f₁ - f₂) g = logCov(f₁ dz, f₂ dz, g⁺ dz, g⁻ dz)` for nonnegative `f₁, f₂`. -/
theorem logCovF_sub_eq_logCov [NeZero d] {f₁ f₂ g : Rd d → ℝ} {M₁ D₁ M₂ D₂ M D : ℝ}
    (h₁ : IsBddSupp f₁ M₁ D₁) (h₂ : IsBddSupp f₂ M₂ D₂) (hg : IsBddSupp g M D)
    (p₁ : ∀ x, 0 ≤ f₁ x) (p₂ : ∀ x, 0 ≤ f₂ x) :
    logCovF (f₁ - f₂) g = HigherDimLFPP.logCov (posM f₁) (posM f₂) (posM g) (posM (-g)) := by
  have eg : g = (fun x => max (g x) 0) - fun x => max (-g x) 0 := by
    funext x; simp only [Pi.sub_apply]; exact (max_zero_sub_max_neg_zero_eq_self (g x)).symm
  have b₃ : IsBddSupp (fun x => max (g x) 0) M D := hg.posPart
  have b₄ : IsBddSupp (fun x => max (-g x) 0) M D := hg.neg.posPart
  rw [eg, logCovF_sub_sub_eq_logCov h₁ h₂ b₃ b₄ p₁ p₂ (fun x => le_max_right _ _)
    (fun x => le_max_right _ _), posM_max_zero, posM_max_neg_zero, ← eg]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-- **Covariance of a difference of nonnegative test functions with a mean-zero pairing**:
`Cov(⟨h, φ₁ - φ₂⟩, ⟨h, ψ⟩) = logCov(φ₁ dz, φ₂ dz, ψ⁺ dz, ψ⁻ dz)`. -/
theorem IsWholeSpaceLGF.covariance_sub_apply [NeZero d] (hh : IsWholeSpaceLGF h P)
    {φ₁ φ₂ : TestRd d} (hφ : ∫ x, φ₁ x = ∫ x, φ₂ x) (p₁ : ∀ x, 0 ≤ φ₁ x)
    (p₂ : ∀ x, 0 ≤ φ₂ x) (ψ : TestRd0 d) :
    cov[fun ω => h ω φ₁ - h ω φ₂, fun ω => h ω ψ.1; P] =
      HigherDimLFPP.logCov (posM φ₁) (posM φ₂) (posM ψ.1) (posM (-ψ.1)) := by
  have hc := hh.covariance_eq (testSub0 φ₁ φ₂ hφ) ψ
  simp only [testSub0_val, map_sub] at hc
  rw [hc]
  obtain ⟨M₁, D₁, b₁⟩ := exists_isBddSupp_testOn φ₁
  obtain ⟨M₂, D₂, b₂⟩ := exists_isBddSupp_testOn φ₂
  obtain ⟨M₃, D₃, b₃⟩ := exists_isBddSupp_testOn ψ.1
  have e1 : (⇑(φ₁ - φ₂) : Rd d → ℝ) = (fun x => φ₁ x) - fun x => φ₂ x := by
    funext x; rw [sub_apply]; rfl
  have hb1 : IsBddSupp (⇑(φ₁ - φ₂)) (M₁ + M₂) (max D₁ D₂) := by
    rw [e1]; exact (b₁.mono le_rfl (le_max_left _ _)).sub (b₂.mono le_rfl (le_max_right _ _))
  rw [logCovRd_eq_logCovF hb1 b₃, e1, logCovF_sub_eq_logCov b₁ b₂ b₃ p₁ p₂]

/-! ### Points of the sphere-average process and the increment process -/

/-- A point `(ε, r, z)` of the sphere-average process: scale `ε ≥ 0`, radius `r > 0`, centre `z`. -/
structure SphPt (d : ℕ) where
  /-- the mollification scale (`0` for the sphere average itself) -/
  ε : ℝ
  /-- the radius -/
  r : ℝ
  /-- the centre -/
  z : Rd d
  hε : 0 ≤ ε
  hr : 0 < r

/-- The law `sphLaw p.r p.z p.ε` of the point (`σ_{r,z}` for `ε = 0`). -/
abbrev SphPt.law (p : SphPt d) : Measure (Rd d) := sphLaw p.r p.z p.ε

/-- The coupling distance between two points. -/
abbrev SphPt.dist (p q : SphPt d) : ℝ := ‖p.z - q.z‖ + |p.r - q.r| + |p.ε - q.ε|

/-- The process of increments `V(p) - V(p')` of `V = sphProc h`, together with the mean-zero
pairings of `h`. -/
def sphIncProc (h : Ω → DistRd d) : (SphPt d × SphPt d) ⊕ TestRd0 d → Ω → ℝ
  | .inl q => fun ω => sphProc (h ω) q.1.ε q.1.r q.1.z - sphProc (h ω) q.2.ε q.2.r q.2.z
  | .inr φ => fun ω => h ω φ.1

/-- The approximating mean-zero test functions at step `n`. -/
def sphIncTest (hd : 1 ≤ d) (n : ℕ) : (SphPt d × SphPt d) ⊕ TestRd0 d → TestRd0 d
  | .inl q => testSub0 (sphMol (approxScale n q.1.ε) q.1.z q.1.r)
      (sphMol (approxScale n q.2.ε) q.2.z q.2.r)
      (by rw [integral_sphMol hd (approxScale_pos q.1.hε n),
        integral_sphMol hd (approxScale_pos q.2.hε n)])
  | .inr φ => φ

theorem measurable_sphIncProc (hm : Measurable h) (t : (SphPt d × SphPt d) ⊕ TestRd0 d) :
    Measurable (sphIncProc h t) := by
  rcases t with q | φ
  · exact ((measurable_sphProc _ _ _).comp hm).sub ((measurable_sphProc _ _ _).comp hm)
  · exact (measurable_distOn_apply _).comp hm

theorem IsWholeSpaceLGF.ae_tendsto_sphIncTest (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (t : (SphPt d × SphPt d) ⊕ TestRd0 d) :
    ∀ᵐ ω ∂P, Tendsto (fun n => h ω (sphIncTest (by omega) n t).1) atTop
      (𝓝 (sphIncProc h t ω)) := by
  rcases t with ⟨p, q⟩ | φ
  · filter_upwards [hh.ae_tendsto_sphProc hd p.hε p.hr p.z,
      hh.ae_tendsto_sphProc hd q.hε q.hr q.z] with ω h1 h2
    refine (h1.sub h2).congr fun n => ?_
    simp only [sphIncTest, testSub0_val, map_sub]
  · exact ae_of_all _ fun ω => tendsto_const_nhds

/-- **The increments of the sphere-average process and the mean-zero pairings form a centred
Gaussian process** (`d ≥ 2`). -/
theorem IsWholeSpaceLGF.isGaussianProcess_sphIncProc (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) :
    IsGaussianProcess (sphIncProc h) P := by
  have := hh.gaussian.isProbabilityMeasure
  refine LQGMetric.CircleAvgIndep.isGaussianProcess_of_ae_tendsto
    (Yn := fun n t ω => h ω (sphIncTest (by omega) n t).1) (fun n => ?_) (fun n t => ?_)
    (measurable_sphIncProc hh.measurable) (hh.ae_tendsto_sphIncTest hd)
  · exact hh.gaussian.comp_right (sphIncTest (by omega) n)
  · exact hh.centered _

theorem IsWholeSpaceLGF.integral_sphIncProc (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (t : (SphPt d × SphPt d) ⊕ TestRd0 d) : ∫ ω, sphIncProc h t ω ∂P = 0 := by
  have := hh.gaussian.isProbabilityMeasure
  exact (LQGMetric.CircleAvgIndep.gaussian_of_ae_tendsto
    (Y := fun n ω => h ω (sphIncTest (by omega) n t).1)
    (fun n => hh.gaussian.hasGaussianLaw_eval _) (fun n => hh.centered _)
    (measurable_sphIncProc hh.measurable t).aemeasurable (hh.ae_tendsto_sphIncTest hd t)).2.1

theorem IsWholeSpaceLGF.tendsto_covariance_sphIncTest (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (s t : (SphPt d × SphPt d) ⊕ TestRd0 d) :
    Tendsto (fun n => cov[fun ω => h ω (sphIncTest (by omega) n s).1,
      fun ω => h ω (sphIncTest (by omega) n t).1; P]) atTop
      (𝓝 cov[sphIncProc h s, sphIncProc h t; P]) := by
  have := hh.gaussian.isProbabilityMeasure
  exact LQGMetric.CircleAvgIndep.tendsto_covariance_of_ae_tendsto
    (Yn := fun n t ω => h ω (sphIncTest (by omega) n t).1)
    (fun n => hh.gaussian.comp_right (sphIncTest (by omega) n)) (fun n t => hh.centered _)
    (measurable_sphIncProc hh.measurable) (hh.ae_tendsto_sphIncTest hd) s t

/-- **Covariance of sphere-average increments**:
`Cov(V(p₁) - V(p₂), V(p₃) - V(p₄)) = logCov(sphLaw p₁, sphLaw p₂, sphLaw p₃, sphLaw p₄)`. -/
theorem IsWholeSpaceLGF.covariance_sphIncProc (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (p₁ p₂ p₃ p₄ : SphPt d) :
    cov[sphIncProc h (.inl (p₁, p₂)), sphIncProc h (.inl (p₃, p₄)); P] =
      HigherDimLFPP.logCov p₁.law p₂.law p₃.law p₄.law := by
  have : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  refine tendsto_nhds_unique (hh.tendsto_covariance_sphIncTest hd _ _) ?_
  have e : ∀ n : ℕ, cov[fun ω => h ω (sphIncTest hd1 n (.inl (p₁, p₂))).1,
      fun ω => h ω (sphIncTest hd1 n (.inl (p₃, p₄))).1; P] =
      HigherDimLFPP.logCov (sphLaw p₁.r p₁.z (approxScale n p₁.ε))
        (sphLaw p₂.r p₂.z (approxScale n p₂.ε)) (sphLaw p₃.r p₃.z (approxScale n p₃.ε))
        (sphLaw p₄.r p₄.z (approxScale n p₄.ε)) := by
    intro n
    simp only [sphIncTest, testSub0_val, map_sub]
    rw [hh.covariance_sub_sub
      (by rw [integral_sphMol hd1 (approxScale_pos p₁.hε n),
        integral_sphMol hd1 (approxScale_pos p₂.hε n)])
      (by rw [integral_sphMol hd1 (approxScale_pos p₃.hε n),
        integral_sphMol hd1 (approxScale_pos p₄.hε n)])
      (sphMol_nonneg (approxScale_pos p₁.hε n) _ _) (sphMol_nonneg (approxScale_pos p₂.hε n) _ _)
      (sphMol_nonneg (approxScale_pos p₃.hε n) _ _) (sphMol_nonneg (approxScale_pos p₄.hε n) _ _),
      posM_sphMol hd1 (approxScale_pos p₁.hε n), posM_sphMol hd1 (approxScale_pos p₂.hε n),
      posM_sphMol hd1 (approxScale_pos p₃.hε n), posM_sphMol hd1 (approxScale_pos p₄.hε n)]
  simp_rw [e]
  exact tendsto_logCov_sphLaw hd p₁.hr p₂.hr p₃.hr p₄.hr _ _ _ _ (tendsto_approxScale _)
    (tendsto_approxScale _) (tendsto_approxScale _) (tendsto_approxScale _)

/-- **Covariance of a sphere-average increment with a mean-zero pairing**:
`Cov(V(p₁) - V(p₂), ⟨h, φ⟩) = logCov(sphLaw p₁, sphLaw p₂, φ⁺ dz, φ⁻ dz)`. -/
theorem IsWholeSpaceLGF.covariance_sphIncProc_apply (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (p₁ p₂ : SphPt d) (φ : TestRd0 d) :
    cov[sphIncProc h (.inl (p₁, p₂)), fun ω => h ω φ.1; P] =
      HigherDimLFPP.logCov p₁.law p₂.law (posM φ.1) (posM (-φ.1)) := by
  have : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  refine tendsto_nhds_unique (hh.tendsto_covariance_sphIncTest hd (.inl (p₁, p₂)) (.inr φ)) ?_
  have e : ∀ n : ℕ, cov[fun ω => h ω (sphIncTest hd1 n (.inl (p₁, p₂))).1,
      fun ω => h ω (sphIncTest hd1 n (.inr φ)).1; P] =
      HigherDimLFPP.logCov (sphLaw p₁.r p₁.z (approxScale n p₁.ε))
        (sphLaw p₂.r p₂.z (approxScale n p₂.ε)) (posM φ.1) (posM (-φ.1)) := by
    intro n
    simp only [sphIncTest, testSub0_val, map_sub]
    rw [hh.covariance_sub_apply
      (by rw [integral_sphMol hd1 (approxScale_pos p₁.hε n),
        integral_sphMol hd1 (approxScale_pos p₂.hε n)])
      (sphMol_nonneg (approxScale_pos p₁.hε n) _ _) (sphMol_nonneg (approxScale_pos p₂.hε n) _ _),
      posM_sphMol hd1 (approxScale_pos p₁.hε n), posM_sphMol hd1 (approxScale_pos p₂.hε n)]
  simp_rw [e]
  obtain ⟨M, D, hMD⟩ := exists_isBddSupp_testOn φ.1
  exact tendsto_logCov_sphLaw_posM hd p₁.hr p₂.hr _ _ (tendsto_approxScale _)
    (tendsto_approxScale _) hMD φ.2

/-- **`L²` bound for increments** (`d ≥ 2`): `V(p) - V(p')` is centred Gaussian and
`E[(V(p) - V(p'))²] = logCov(sphLaw p, sphLaw p', sphLaw p, sphLaw p')
≤ C (‖z - z'‖ + |r - r'| + |ε - ε'|) / min(r, r')`, `C = C(d)`. -/
theorem exists_integral_sq_sphIncProc_le (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ p q : SphPt d,
        HasGaussianLaw (sphIncProc h (.inl (p, q))) P ∧
        ∫ ω, sphIncProc h (.inl (p, q)) ω ∂P = 0 ∧
        ∫ ω, sphIncProc h (.inl (p, q)) ω ^ 2 ∂P =
          HigherDimLFPP.logCov p.law q.law p.law q.law ∧
        HigherDimLFPP.logCov p.law q.law p.law q.law ≤ C * p.dist q / min p.r q.r := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_logCov_sphLaw_le hd
  refine ⟨C, hC0, fun {Ω} _ {P} {h} hh p q => ?_⟩
  have hG := (hh.isGaussianProcess_sphIncProc hd).hasGaussianLaw_eval (.inl (p, q))
  have h0 := hh.integral_sphIncProc hd (.inl (p, q))
  refine ⟨hG, h0, ?_, ?_⟩
  · rw [← hh.covariance_sphIncProc hd p q p q, covariance_self hG.aemeasurable,
      variance_eq_integral hG.aemeasurable, h0]
    simp
  · have hb := hC p.r q.r p.r q.r p.hr q.hr p.hr q.hr p.z q.z p.z q.z p.ε q.ε p.ε q.ε
    have hu0 : 0 ≤ p.dist q := by unfold SphPt.dist; positivity
    unfold SphPt.dist at hu0 ⊢
    rw [Real.sqrt_mul_self hu0] at hb
    exact (le_abs_self _).trans hb

end HigherDimLQGMetric
