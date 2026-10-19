import HigherDimLFPP.Field.VarBounds

/-!
# Lemma 3.4 (a), (c) and (3.16): scale-band estimates (packet P-F3b)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.3, Lemma 3.4 ((3.12), (3.14), (3.16));
planning audit HA2 (`planning/audits/HA2-section-3.md`), findings HA2-12, HA2-14 and Details D8
(a), (c), (d); HA4 (`planning/audits/HA4-section-5.md`), Details D4 ((K1)–(K3)) and D6 (the forms
consumed by §5).

* **(a)** `integral_scaleConv_sq_le`: `‖μ * K_t‖₂² ≤ B max(1, 2ρ_κ)` at every scale `t > 0` for a
  probability measure with the growth bound (3.4) at scale `1` (constant `B`); hence (3.12′)
  `bandLemma34a_single` (`Var⟨H_S, μ⟩ ≤ C |S| ≤ C a` for every measurable `S ⊆ (0, a)`) and
  (3.12) `bandLemma34a` (HA2's `Lemma34a`) and `bandLemma34a_subset` (differences, `S ⊆ (0, a)`).
  These are thin wrappers around P-F2's `scalePair_zero_le`, `single_measure_bound`,
  `pair_measure_bound` and `scaleCov_fine_scales_le` (`Field/VarBounds.lean`).
* **(c)** `bandLemma34c`, (3.14): if `ν` has the growth bound (3.4) at scale `1` and `μ` is coupled
  with `ν` within `u ≤ a`, then `Var⟨H_S, μ - ν⟩ ≤ C u² / a` for every measurable
  `S ⊆ (a, ∞)` (all bands `(a, b)`, `b ≤ ∞`).  No growth bound on `μ` is used (HA2 D8(c)).
* **(d)** `bandLemma34d_var`, (3.16): if `ν` is coupled within `a` with a measure `ν'` having the
  growth bound (3.4) at scale `1`, then `Var⟨H_{a,b}, η⟩ ≤ C b η(ℝ^d)` for **every** positive
  measure `η ≤ ν` and every `b ≥ a` (HA2-14: `b ≤ 1` is not needed); `bandLemma34d_prefix` is
  the case of the prefixes `η = ν|_{z₁ ≤ x}` (`Bands.prefixM`).  The expected maxima over `j`
  (the fixed-prefix form of (3.15) consumed by Lemma 5.3) are in `Field/BandsSup.lean`.

Proofs (HA2 D8):

* (c) at a scale `t ≥ a ≥ u`, P-F2's Lipschitz bound `abs_scaleConv_sub_le_lip` (applied to the
  swapped coupling, so that the growth bound of `ν` is the one used) gives
  `‖(μ - ν) * K_t‖_∞ ≤ K B (ρ + 1) u t^{-(d+1)/2}`, and `integral_abs_scaleConv_sub_le` gives
  `‖(μ - ν) * K_t‖₁ ≤ C₂ u t^{(d-3)/2}`; their product is `C₀ u² t⁻²`
  (`scalePair_le_of_coupled`), and `∫_a^∞ t⁻² dt = 1/a`.
* (d) the coupling gives `ν(B̄(z, r)) ≤ ν'(B̄(z, r + a)) ≤ B (r + a)`
  (`measureReal_closedBall_le_of_coupled`); since `C ≥ 0` (`κ ≥ 0`) and `C = 0` off
  `B̄(0, 2ρ_κ)`, `∫ C((z - w)/t)/t dη(w) ≤ ∫ C((z - w)/t)/t dν(w) ≤ t⁻¹ ν(B̄(z, 2ρ_κ t))
  ≤ B (2ρ_κ + 1)` for `t ≥ a` (`integral_autoCorr_div_le_of_coupled`), so
  `scalePair κ t η 0 η 0 ≤ B (2ρ_κ + 1) η(ℝ^d)` (`scalePair_zero_le_of_le`); integrate over
  `(a, b)`.

No 2D source file: the 2D library (`LQGDimension`) has no measure-level band estimates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ}

/-! ### Auxiliary facts on growth bounds, couplings and prefixes -/

namespace Bands

/-- A growth bound (3.4) at a positive scale forces a nonnegative constant. -/
theorem growthBound_const_nonneg {μ : Measure (Rd d)} {B R : ℝ} (h : GrowthBound μ B R)
    (hR : 0 < R) : 0 ≤ B := by
  have h1 := h 0 R hR
  rw [div_self hR.ne', min_self, mul_one] at h1
  exact measureReal_nonneg.trans h1

/-- Displacement couplings are symmetric. -/
theorem coupledWithin_symm {μ ν : Measure (Rd d)} {u : ℝ} (h : CoupledWithin μ ν u) :
    CoupledWithin ν μ u := by
  obtain ⟨cpl, h1, h2, hu⟩ := h
  refine ⟨cpl.map Prod.swap, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst measurable_swap]
    exact h2
  · rw [Measure.map_map measurable_snd measurable_swap]
    exact h1
  · have hm : MeasurableSet {q : Rd d × Rd d | ‖q.1 - q.2‖ ≤ u} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [ae_map_iff measurable_swap.aemeasurable hm]
    filter_upwards [hu] with q hq
    simpa only [Prod.fst_swap, Prod.snd_swap, norm_sub_rev] using hq

/-- **Small balls of a measure coupled with a growth-bounded one** (HA2 D8(d), HA4 (K4)):
if `ν` is coupled within `a ≥ 0` with `ν'`, and `ν'` has the growth bound (3.4) at scale `1` with
constant `B ≥ 0`, then `ν(B̄(z, r)) ≤ B (r + a)` for every `r > 0`. -/
theorem measureReal_closedBall_le_of_coupled {ν ν' : Measure (Rd d)} [IsFiniteMeasure ν]
    [IsFiniteMeasure ν'] {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hc : CoupledWithin ν ν' a)
    (hg : GrowthBound ν' B 1) (z : Rd d) {r : ℝ} (hr : 0 < r) :
    ν.real (closedBall z r) ≤ B * (r + a) := by
  obtain ⟨cpl, h1, h2, hu⟩ := hc
  have hle : ν (closedBall z r) ≤ ν' (closedBall z (r + a)) := by
    rw [← h1, ← h2, Measure.map_apply measurable_fst measurableSet_closedBall,
      Measure.map_apply measurable_snd measurableSet_closedBall]
    refine measure_mono_ae ?_
    filter_upwards [hu] with q hq hq1
    simp only [mem_preimage, mem_closedBall, dist_eq_norm] at hq1 ⊢
    calc ‖q.2 - z‖ ≤ ‖q.2 - q.1‖ + ‖q.1 - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖q.1 - q.2‖ + ‖q.1 - z‖ := by rw [norm_sub_rev q.2 q.1]
      _ ≤ a + r := add_le_add hq hq1
      _ = r + a := add_comm a r
  have h' : ν.real (closedBall z r) ≤ ν'.real (closedBall z (r + a)) := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hle
  calc ν.real (closedBall z r) ≤ ν'.real (closedBall z (r + a)) := h'
    _ ≤ B * min 1 ((r + a) / 1) := hg z (r + a) (by linarith)
    _ ≤ B * (r + a) := by
        rw [div_one]
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) hB

/-- The prefix `μ|_{z₁ ≤ x}` of a measure (HA2's `prefixM`, with the horizontal coordinate
`z₁ = ⟪e₁, z⟫`, which is `Lower.horiz z`). -/
def prefixM (μ : Measure (Rd d)) (x : ℝ) : Measure (Rd d) :=
  μ.restrict {z | ⟪e₁ d, z⟫ ≤ x}

theorem prefixM_le (μ : Measure (Rd d)) (x : ℝ) : prefixM μ x ≤ μ :=
  Measure.restrict_le_self

instance (μ : Measure (Rd d)) [IsFiniteMeasure μ] (x : ℝ) : IsFiniteMeasure (prefixM μ x) := by
  unfold prefixM
  infer_instance

theorem prefixM_real_univ_le (μ : Measure (Rd d)) [IsFiniteMeasure μ] (x : ℝ) :
    (prefixM μ x).real univ ≤ μ.real univ := by
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (prefixM_le μ x univ)

end Bands

/-! ### Lemma 3.4(a): fine scales -/

section PartA

/-- `∫ (μ * K_t)² = scalePair κ t μ 0 μ 0` for `t > 0`. -/
theorem integral_scaleConv_sq (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) (μ : Measure (Rd d))
    [IsFiniteMeasure μ] : ∫ y, scaleConv κ t μ y ^ 2 = scalePair κ t μ 0 μ 0 := by
  rw [← integral_scaleConv_sub_mul hκ ht μ 0 μ 0]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [scaleConv, integral_zero_measure, sub_zero, sq]

/-- **HA2 D8(a)**: `‖μ * K_t‖₂² ≤ B max(1, 2ρ_κ)` at every scale `t > 0`, for a probability
measure with the growth bound (3.4) at scale `1` (constant `B`) and a support radius `ρ` of `κ`. -/
theorem integral_scaleConv_sq_le (hκ : IsLFPPKernel κ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {t : ℝ} (ht : 0 < t) {μ : Measure (Rd d)}
    [IsProbabilityMeasure μ] {B : ℝ} (hμ : GrowthBound μ B 1) :
    ∫ y, scaleConv κ t μ y ^ 2 ≤ B * max 1 (2 * ρ) := by
  have hB := Bands.growthBound_const_nonneg hμ one_pos
  rw [integral_scaleConv_sq hκ ht]
  calc scalePair κ t μ 0 μ 0 ≤ 2 * ρ * B := scalePair_zero_le hκ hρ0 hρ ht hB hμ
    _ = B * (2 * ρ) := by ring
    _ ≤ B * max 1 (2 * ρ) := mul_le_mul_of_nonneg_left (le_max_right _ _) hB

/-- **(3.12′)** (HA2-12), for scale sets inside `(0, a)`: for every `B` there is `C = C(d, κ, B)`
such that for every probability measure `μ` with the growth bound (3.4) at scale `1`, every
`a > 0` and every measurable `S ⊆ (0, a)`, `⟨H_S, μ⟩` is defined and
`Var⟨H_S, μ⟩ ≤ C |S| ≤ C a`. -/
theorem bandLemma34a_single (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (S : Set ℝ), 0 < a → MeasurableSet S → S ⊆ Ioo 0 a →
      ∀ (μ : Measure (Rd d)) [IsProbabilityMeasure μ], GrowthBound μ B 1 →
        IsPairable κ S μ 0 ∧ scaleCov κ S μ 0 μ 0 ≤ C * volume.real S ∧
          scaleCov κ S μ 0 μ 0 ≤ C * a := by
  obtain ⟨C, hC0, hC⟩ := single_measure_bound hκ B
  refine ⟨C, hC0, fun a S ha hS hSa μ _ hμ => ?_⟩
  have hS0 : S ⊆ Ioi 0 := hSa.trans Ioo_subset_Ioi_self
  have hSf : volume S ≠ ⊤ := ((measure_mono hSa).trans_lt measure_Ioo_lt_top).ne
  have hvol : volume.real S ≤ a := by
    calc volume.real S ≤ volume.real (Ioo (0 : ℝ) a) :=
          measureReal_mono hSa measure_Ioo_lt_top.ne
      _ = a := by rw [measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal ha.le]
  obtain ⟨hp, hb⟩ := hC S hS hS0 hSf μ hμ
  exact ⟨hp, hb, hb.trans (mul_le_mul_of_nonneg_left hvol hC0)⟩

/-- **(3.12)** for differences, scale sets inside `(0, a)`:
`Var⟨H_S, μ - ν⟩ ≤ C |S| ≤ C a` for probability measures with the growth bound (3.4) at
scale `1`. -/
theorem bandLemma34a_subset (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (S : Set ℝ), 0 < a → MeasurableSet S → S ⊆ Ioo 0 a →
      ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        GrowthBound μ B 1 → GrowthBound ν B 1 →
        IsPairable κ S μ ν ∧ scaleCov κ S μ ν μ ν ≤ C * volume.real S ∧
          scaleCov κ S μ ν μ ν ≤ C * a := by
  obtain ⟨C, hC0, hC⟩ := pair_measure_bound hκ B
  refine ⟨C, hC0, fun a S ha hS hSa μ ν _ _ hμ hν => ?_⟩
  have hS0 : S ⊆ Ioi 0 := hSa.trans Ioo_subset_Ioi_self
  have hSf : volume S ≠ ⊤ := ((measure_mono hSa).trans_lt measure_Ioo_lt_top).ne
  have hvol : volume.real S ≤ a := by
    calc volume.real S ≤ volume.real (Ioo (0 : ℝ) a) :=
          measureReal_mono hSa measure_Ioo_lt_top.ne
      _ = a := by rw [measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal ha.le]
  obtain ⟨hp, hb⟩ := hC S hS hS0 hSf μ ν hμ hν
  exact ⟨hp, hb, hb.trans (mul_le_mul_of_nonneg_left hvol hC0)⟩

/-- **Lemma 3.4(a)**, (3.12) together with (3.12′), in the exact form of HA2's `Lemma34a`
(band `(0, a)`, all `a > 0`). -/
theorem bandLemma34a (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, ∀ a : ℝ, 0 < a → ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ]
      [IsProbabilityMeasure ν], GrowthBound μ B 1 → GrowthBound ν B 1 →
      IsPairable κ (Ioo 0 a) μ 0 ∧ scaleCov κ (Ioo 0 a) μ 0 μ 0 ≤ C * a ∧
        IsPairable κ (Ioo 0 a) μ ν ∧ scaleCov κ (Ioo 0 a) μ ν μ ν ≤ C * a :=
  scaleCov_fine_scales_le hκ B

end PartA

/-! ### Lemma 3.4(c): the coupling bound (3.14) -/

section PartC

/-- **HA2 D8(c), one scale**: there is `C₀ = C₀(d, κ, B)` such that for `0 ≤ u ≤ t`, every
probability measure `ν` with the growth bound (3.4) at scale `1` and every probability measure
`μ` coupled with `ν` within `u`, `‖(μ - ν) * K_t‖₂² ≤ C₀ u² t⁻²`.  No growth bound on `μ` is
used. -/
theorem exists_scalePair_le_of_coupled (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ t : ℝ, 0 < t → ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ]
      [IsProbabilityMeasure ν] (u : ℝ), 0 ≤ u → u ≤ t → GrowthBound ν B 1 →
      CoupledWithin μ ν u → scalePair κ t μ ν μ ν ≤ C₀ * u ^ 2 * t ^ (-2 : ℝ) := by
  obtain ⟨K, hK⟩ := hκ.exists_lipschitzWith
  obtain ⟨ρ, hρ0, hρ⟩ := hκ.exists_radius
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_integral_abs_scaleKernel_sub_le hκ
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  refine ⟨K * B' * (ρ + 1) * C₂, by positivity, fun t ht μ ν _ _ u hu hut hν hcpl => ?_⟩
  have hk := kpre_pos (d := d) ht
  -- the sup bound, from the growth of `ν` (swap the coupling)
  obtain ⟨cpl, h1, h2, hcu⟩ := Bands.coupledWithin_symm hcpl
  have hsup : ∀ y, |scaleConv κ t μ y - scaleConv κ t ν y| ≤
      kpre d t * K * (t⁻¹ * u) * (B' * ((ρ + 1) * t / 1)) := by
    intro y
    rw [abs_sub_comm]
    exact abs_scaleConv_sub_le_lip hκ hK hρ0 hρ ht h1 h2 hu hcu hut hB'0 (hν.max_zero one_pos) y
  obtain ⟨hGi, hGl⟩ := integral_abs_scaleConv_sub_le hκ hC₂0 hC₂ ht hcpl
  have hM0 : 0 ≤ kpre d t * K * (t⁻¹ * u) * (B' * ((ρ + 1) * t / 1)) := by positivity
  have hmin : min 1 (u / t) ≤ u / t := min_le_right _ _
  have hprod := abs_scalePair_le_mul hκ ht hsup hGi hGl hM0
  have h2t : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht.le, Real.rpow_natCast]
  have hkk := kpre_mul_kpre_mul (d := d) ht
  calc scalePair κ t μ ν μ ν ≤ |scalePair κ t μ ν μ ν| := le_abs_self _
    _ ≤ kpre d t * K * (t⁻¹ * u) * (B' * ((ρ + 1) * t / 1)) *
          (C₂ * kpre d t * t ^ d * min 1 (u / t)) := hprod
    _ ≤ kpre d t * K * (t⁻¹ * u) * (B' * ((ρ + 1) * t / 1)) *
          (C₂ * kpre d t * t ^ d * (u / t)) := by gcongr
    _ = K * B' * (ρ + 1) * C₂ * u ^ 2 * (t ^ 2)⁻¹ * (kpre d t * kpre d t * t ^ d * t) := by
        field_simp
    _ = K * B' * (ρ + 1) * C₂ * u ^ 2 * t ^ (-2 : ℝ) := by rw [hkk, mul_one, h2t]

/-- `∫_a^∞ t⁻² dt = a⁻¹`, with integrability, for `a > 0`. -/
theorem Bands.integral_Ioi_rpow_neg_two {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi a) ∧ ∫ t in Ioi a, t ^ (-2 : ℝ) = a⁻¹ := by
  refine ⟨integrableOn_Ioi_rpow_of_lt (by norm_num) ha, ?_⟩
  rw [integral_Ioi_rpow_of_lt (by norm_num) ha, show (-2 : ℝ) + 1 = -1 by norm_num,
    Real.rpow_neg_one]
  ring

/-- **Lemma 3.4(c), (3.14)** (HA2 D8(c); HA2's `Lemma34c`): for every `B` there is
`C = C(d, κ, B)` such that for `0 < a`, `0 ≤ u ≤ a`, every measurable scale set `S ⊆ (a, ∞)`
(in particular every band `(a, b)`, `b ≤ ∞`), every probability measure `ν` with the growth
bound (3.4) at scale `1` and every probability measure `μ` coupled with `ν` within `u`,
`⟨H_S, μ - ν⟩` is defined and `Var⟨H_S, μ - ν⟩ ≤ C u² / a`.  No growth bound on `μ` is
needed. -/
theorem bandLemma34c (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a u : ℝ) (S : Set ℝ), 0 < a → 0 ≤ u → u ≤ a →
      MeasurableSet S → S ⊆ Ioi a → ∀ (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ]
      [IsProbabilityMeasure ν], GrowthBound ν B 1 → CoupledWithin μ ν u →
      IsPairable κ S μ ν ∧ scaleCov κ S μ ν μ ν ≤ C * u ^ 2 / a := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_scalePair_le_of_coupled hκ B
  refine ⟨C₀, hC₀0, fun a u S ha hu hua hS hSa μ ν _ _ hν hcpl => ?_⟩
  have hS0 : S ⊆ Ioi 0 := fun t ht => lt_trans ha (hSa ht)
  obtain ⟨hint, hval⟩ := Bands.integral_Ioi_rpow_neg_two ha
  have hgi : IntegrableOn (fun t : ℝ => C₀ * u ^ 2 * t ^ (-2 : ℝ)) (Ioi a) :=
    hint.const_mul (C₀ * u ^ 2)
  have hle : ∀ t ∈ S, scalePair κ t μ ν μ ν ≤ C₀ * u ^ 2 * t ^ (-2 : ℝ) := fun t ht =>
    hC₀ t (hS0 ht) μ ν u hu (hua.trans (hSa ht).le) hν hcpl
  have hp : IsPairable κ S μ ν := isPairable_of_le hκ hS hS0 μ ν (hgi.mono_set hSa) hle
  refine ⟨hp, ?_⟩
  rw [scaleCov_eq_integral hκ hS hS0 hp hp]
  calc ∫ t in S, scalePair κ t μ ν μ ν ≤ ∫ t in S, C₀ * u ^ 2 * t ^ (-2 : ℝ) :=
        setIntegral_mono_on (integrableOn_scalePair hκ hS hS0 hp hp) (hgi.mono_set hSa) hS hle
    _ ≤ ∫ t in Ioi a, C₀ * u ^ 2 * t ^ (-2 : ℝ) := by
        refine setIntegral_mono_set hgi ?_ (Eventually.of_forall hSa)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (lt_trans ha ht).le _)
    _ = C₀ * u ^ 2 / a := by
        rw [integral_const_mul, hval, div_eq_mul_inv]

end PartC

/-! ### (3.16): positive measures below a coupled measure -/

section PartD

/-- **HA2 D8(d), kernel mass** (HA4 (K1)): for `t ≥ a`, every `z` and `ν` coupled within `a`
with a measure `ν'` having the growth bound (3.4) at scale `1` (constant `B ≥ 0`),
`∫ C((z - w)/t)/t dν(w) ≤ B (2ρ + 1)`, where `ρ` is a support radius of `κ`. -/
theorem integral_autoCorr_div_le_of_coupled (hκ : IsLFPPKernel κ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {ν ν' : Measure (Rd d)} [IsFiniteMeasure ν]
    [IsFiniteMeasure ν'] {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hc : CoupledWithin ν ν' a)
    (hg : GrowthBound ν' B 1) {t : ℝ} (ht : 0 < t) (hat : a ≤ t) (z : Rd d) :
    ∫ w, autoCorr κ (t⁻¹ • (z - w)) / t ∂ν ≤ B * (2 * ρ + 1) := by
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
  have hi1 : Integrable (fun w => autoCorr κ (t⁻¹ • (z - w)) / t) ν := by
    refine Integrable.of_bound (((continuous_autoCorr hκ).comp
      ((continuous_const.sub continuous_id).const_smul t⁻¹)).div_const t).aestronglyMeasurable
      |t⁻¹| (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_div, div_eq_mul_inv, abs_inv]
    calc |autoCorr κ (t⁻¹ • (z - w))| * |t|⁻¹ ≤ 1 * |t|⁻¹ :=
          mul_le_mul_of_nonneg_right (abs_autoCorr_le_one hκ _) (inv_nonneg.2 (abs_nonneg t))
      _ = |t|⁻¹ := one_mul _
  have hi2 : Integrable ((closedBall z (2 * ρ * t)).indicator fun _ => t⁻¹) ν :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrable_const _).integrableOn
  have hball := Bands.measureReal_closedBall_le_of_coupled ha hB hc hg z
    (r := 2 * ρ * t) (by positivity)
  calc ∫ w, autoCorr κ (t⁻¹ • (z - w)) / t ∂ν
      ≤ ∫ w, (closedBall z (2 * ρ * t)).indicator (fun _ => t⁻¹) w ∂ν :=
        integral_mono hi1 hi2 hpt
    _ = t⁻¹ * ν.real (closedBall z (2 * ρ * t)) := by
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_comm]
    _ ≤ t⁻¹ * (B * (2 * ρ * t + a)) := mul_le_mul_of_nonneg_left hball (inv_nonneg.2 ht.le)
    _ ≤ t⁻¹ * (B * (2 * ρ * t + t)) := by gcongr
    _ = B * (2 * ρ + 1) := by field_simp

/-- **HA2 D8(d) at one scale** (HA4 (K2)): for `t ≥ a` and every positive finite measure
`η ≤ ν`, `‖η * K_t‖₂² ≤ B (2ρ + 1) η(ℝ^d)`. -/
theorem scalePair_zero_le_of_le (hκ : IsLFPPKernel κ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {ν ν' : Measure (Rd d)} [IsFiniteMeasure ν]
    [IsFiniteMeasure ν'] {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hc : CoupledWithin ν ν' a)
    (hg : GrowthBound ν' B 1) {t : ℝ} (ht : 0 < t) (hat : a ≤ t) {η : Measure (Rd d)}
    [IsFiniteMeasure η] (hη : η ≤ ν) :
    scalePair κ t η 0 η 0 ≤ B * (2 * ρ + 1) * η.real univ := by
  rw [scalePair_zero, integral_prod _ (integrable_autoCorr_div hκ t η η)]
  have hin : ∀ z : Rd d, ∫ w, autoCorr κ (t⁻¹ • (z - w)) / t ∂η ≤ B * (2 * ρ + 1) := by
    intro z
    have hi1 : Integrable (fun w => autoCorr κ (t⁻¹ • (z - w)) / t) ν := by
      refine Integrable.of_bound (((continuous_autoCorr hκ).comp
        ((continuous_const.sub continuous_id).const_smul t⁻¹)).div_const t).aestronglyMeasurable
        |t⁻¹| (Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_div, div_eq_mul_inv, abs_inv]
      calc |autoCorr κ (t⁻¹ • (z - w))| * |t|⁻¹ ≤ 1 * |t|⁻¹ :=
            mul_le_mul_of_nonneg_right (abs_autoCorr_le_one hκ _) (inv_nonneg.2 (abs_nonneg t))
        _ = |t|⁻¹ := one_mul _
    have h0 : 0 ≤ᵐ[ν] fun w => autoCorr κ (t⁻¹ • (z - w)) / t :=
      Eventually.of_forall fun w => div_nonneg (autoCorr_nonneg hκ _) ht.le
    exact (integral_mono_measure hη h0 hi1).trans
      (integral_autoCorr_div_le_of_coupled hκ hρ0 hρ ha hB hc hg ht hat z)
  calc ∫ z, ∫ w, autoCorr κ (t⁻¹ • ((z, w).1 - (z, w).2)) / t ∂η ∂η
      ≤ ∫ _z, B * (2 * ρ + 1) ∂η :=
        integral_mono (integrable_autoCorr_div hκ t η η).integral_prod_left (integrable_const _)
          hin
    _ = B * (2 * ρ + 1) * η.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

/-- **(3.16)** (HA2 D8(d), HA4 (K2); the bound of Lemma 3.4(d) consumed by Lemma 5.3): for every
`B` there is `C = C(d, κ, B)` such that for `0 < a ≤ b`, every finite measure `ν` coupled within
`a` with a finite measure `ν'` having the growth bound (3.4) at scale `1`, and every positive
finite measure `η ≤ ν`, `⟨H_{a,b}, η⟩` is defined and `Var⟨H_{a,b}, η⟩ ≤ C b η(ℝ^d)`.
(The paper's `b ≤ 1` is not needed, HA2-14.) -/
theorem bandLemma34d_var (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∀ (ν ν' : Measure (Rd d)) [IsFiniteMeasure ν] [IsFiniteMeasure ν'],
        GrowthBound ν' B 1 → CoupledWithin ν ν' a →
        ∀ (η : Measure (Rd d)) [IsFiniteMeasure η], η ≤ ν →
          IsPairable κ (Ioo a b) η 0 ∧ scaleCov κ (Ioo a b) η 0 η 0 ≤ C * b * η.real univ := by
  obtain ⟨ρ, hρ0, hρ⟩ := hκ.exists_radius
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  refine ⟨B' * (2 * ρ + 1), by positivity, fun a b ha hab ν ν' _ _ hg hc η _ hη => ?_⟩
  have hg' := hg.max_zero one_pos
  have hS0 : Ioo a b ⊆ Ioi 0 := fun t ht => lt_trans ha ht.1
  have hp : IsPairable κ (Ioo a b) η 0 :=
    isPairable_of_subset_Icc hκ measurableSet_Ioo ha Ioo_subset_Icc_self η 0
  refine ⟨hp, ?_⟩
  have hle : ∀ t ∈ Ioo a b, scalePair κ t η 0 η 0 ≤ B' * (2 * ρ + 1) * η.real univ :=
    fun t ht => scalePair_zero_le_of_le hκ hρ0 hρ ha.le hB'0 hc hg' (hS0 ht) ht.1.le hη
  have hgi : IntegrableOn (fun _ : ℝ => B' * (2 * ρ + 1) * η.real univ) (Ioo a b) :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hη0 : 0 ≤ η.real univ := measureReal_nonneg
  rw [scaleCov_eq_integral hκ measurableSet_Ioo hS0 hp hp]
  calc ∫ t in Ioo a b, scalePair κ t η 0 η 0
      ≤ ∫ _t in Ioo a b, B' * (2 * ρ + 1) * η.real univ :=
        setIntegral_mono_on (integrableOn_scalePair hκ measurableSet_Ioo hS0 hp hp) hgi
          measurableSet_Ioo hle
    _ = B' * (2 * ρ + 1) * η.real univ * (b - a) := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
        ring
    _ ≤ B' * (2 * ρ + 1) * η.real univ * b := by
        have : b - a ≤ b := by linarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = B' * (2 * ρ + 1) * b * η.real univ := by ring

/-- **(3.16) for prefixes** (HA2 D8(d), HA4 (K5)): with the constant of `bandLemma34d_var`,
`Var⟨H_{a,b}, ν|_{z₁ ≤ x}⟩ ≤ C b` for every `x` and every probability measure `ν` coupled within
`a` with a probability measure `ν'` having the growth bound (3.4) at scale `1`. -/
theorem bandLemma34d_prefix (hκ : IsLFPPKernel κ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∀ (ν ν' : Measure (Rd d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'],
        GrowthBound ν' B 1 → CoupledWithin ν ν' a → ∀ x : ℝ,
          IsPairable κ (Ioo a b) (Bands.prefixM ν x) 0 ∧
            scaleCov κ (Ioo a b) (Bands.prefixM ν x) 0 (Bands.prefixM ν x) 0 ≤ C * b := by
  obtain ⟨C, hC0, hC⟩ := bandLemma34d_var hκ B
  refine ⟨C, hC0, fun a b ha hab ν ν' _ _ hg hc x => ?_⟩
  obtain ⟨hp, hb⟩ := hC a b ha hab ν ν' hg hc (Bands.prefixM ν x) (Bands.prefixM_le ν x)
  refine ⟨hp, hb.trans ?_⟩
  have h1 : (Bands.prefixM ν x).real univ ≤ 1 := by
    have := Bands.prefixM_real_univ_le ν x
    rwa [probReal_univ (μ := ν)] at this
  have hb0 : 0 ≤ b := ha.le.trans hab
  calc C * b * (Bands.prefixM ν x).real univ ≤ C * b * 1 :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hC0 hb0)
    _ = C * b := mul_one _

end PartD

end HigherDimLFPP
