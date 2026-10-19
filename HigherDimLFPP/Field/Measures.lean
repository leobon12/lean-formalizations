import HigherDimLFPP.Field.BandVec
import LQGDimension.Blueprint.Gaussian

/-!
# Measure-level band vectors and their covariance (packet P-F2, target T1)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1), (3.1) and §3.1; planning audit HA2
(`planning/audits/HA2-section-3.md`), notation paragraph, Details D1 ("Band integrands"), D2.1, D4
and the Lean block (c) (`bandFun`, `IsPairable`, `bandVec`, `scaleCov`).

For a finite measure `μ` on `ℝ^d` and a Borel scale set `S ⊆ (0, ∞)`, the band integrand is
`F^S_μ(t, y) = 1_S(t) (μ * K_t)(y)` with `(μ * K_t)(y) = ∫ K_t(z - y) dμ(z)` (`scaleConv`).
The white-noise vector of `⟨H_S, μ - ν⟩` is `bandVecM κ S μ ν ∈ L²(ℝ × ℝ^d)` (junk `0` unless
`IsPairable κ S μ ν`, i.e. `F^S_μ - F^S_ν ∈ L²`), and
`scaleCov κ S μ ν μ' ν' = ⟪bandVecM κ S μ ν, bandVecM κ S μ' ν'⟫` (Itô isometry: this is the
covariance of the pairings).  The point vectors of P-F1 are the case of Dirac masses
(`bandVecM_dirac_zero`).

Main results:

* fixed scale (HA2 D3, Step 1): for `t > 0` and finite measures,
  `∫ (μ * K_t)(y) (μ' * K_t)(y) dy = ∫∫ C(t⁻¹(z - w))/t dμ(z) dμ'(w)` (`integral_scaleConv_mul`),
  hence `∫ ((μ - ν) * K_t)((μ' - ν') * K_t) = scalePair κ t μ ν μ' ν'`
  (`integral_scaleConv_sub_mul`), where `scalePair` is the four-term expansion `mixInt` of
  `∫∫ C(t⁻¹(z - w))/t (μ - ν)(dz) (μ' - ν')(dw)`;
* `isPairable_iff_lintegral`: `IsPairable κ S μ ν ↔ ∫⁻_S scalePair κ t μ ν μ ν dt < ∞`;
* `scaleCov_eq_integral`: `scaleCov κ S μ ν μ' ν' = ∫_S scalePair κ t μ ν μ' ν' dt` for pairable
  pairs (the formula of target T1);
* `bandVecM_dirac_zero`: compatibility with the point vectors `bandVec κ a b z` of P-F1;
* bilinearity (`bandVecM_add`, `bandVecM_swap`, `bandVecM_smul`, `bandVecM_sub`, ...);
* the Gram property: `sum_mul_scaleCov_nonneg`, `psdOn_scaleCov`;
* scale sets: `IsPairable.mono_set`, `scaleCov_self_le_of_subset` (HA2 D4, (3.3) for nested scale
  sets), `bandVecM_union` (band additivity (F3)), `inner_bandVecM_eq_zero_of_disjoint`
  (orthogonality of disjoint bands, HA2 D2.1);
* pairability: `isPairable_of_subset_Icc` (bounded bands, any finite measures) and
  `isPairable_of_subset_Ici` (unbounded bands, equal masses and bounded supports).

Templates: `LQGMetric/Field/WhiteNoiseKernel.lean` (`memLp_phiKernel`, `inner_phiKernelL2`) and
P-F1's `HigherDimLFPP/Field/BandVec.lean` (point vectors); there is no 2D measure-level analogue
(the 2D library works with finite segment combinations, `LQGDimension.Blueprint.Draft.SegComb`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

variable {d : ℕ}

/-! ### Definitions -/

/-- `(μ * K_t)(y) = ∫ K_t(z - y) dμ(z)`. -/
def scaleConv (κ : Rd d → ℝ) (t : ℝ) (μ : Measure (Rd d)) (y : Rd d) : ℝ :=
  ∫ z, scaleKernel κ t (z - y) ∂μ

/-- Scale-band integrand of a finite measure: `(t, y) ↦ 1_S(t) ∫ K_t(z - y) dμ(z)`
(HA2's `bandFun`). -/
def bandFun (κ : Rd d → ℝ) (S : Set ℝ) (μ : Measure (Rd d)) : ℝ × Rd d → ℝ :=
  fun p => S.indicator (fun t => ∫ z, scaleKernel κ t (z - p.2) ∂μ) p.1

/-- Square-integrability of the band integrand of `μ - ν` (the domain of the pairing
`⟨H_S, μ - ν⟩`; HA2's `IsPairable`). -/
def IsPairable (κ : Rd d → ℝ) (S : Set ℝ) (μ ν : Measure (Rd d)) : Prop :=
  MemLp (bandFun κ S μ - bandFun κ S ν) 2 volume

/-- The white-noise kernel vector of `⟨H_S, μ - ν⟩` in `L²(ℝ × ℝ^d)` (junk `0` if not pairable;
HA2's `bandVec`, renamed because `bandVec` is the frozen point vector `k_{a,b,z}`). -/
def bandVecM (κ : Rd d → ℝ) (S : Set ℝ) (μ ν : Measure (Rd d)) : WN d := by
  classical
  exact if h : IsPairable κ S μ ν then h.toLp _ else 0

/-- `Cov(⟨H_S, μ - ν⟩, ⟨H_S, μ' - ν'⟩)`, defined as the `L²` inner product of the kernel vectors
(Itô isometry); a Gram kernel, hence positive semidefinite (HA2's `scaleCov`). -/
def scaleCov (κ : Rd d → ℝ) (S : Set ℝ) (μ ν μ' ν' : Measure (Rd d)) : ℝ :=
  ⟪bandVecM κ S μ ν, bandVecM κ S μ' ν'⟫

/-- `∫∫ g(z, w) (μ - ν)(dz) (μ' - ν')(dw)`, expanded into its four product-measure integrals. -/
def mixInt (g : Rd d → Rd d → ℝ) (μ ν μ' ν' : Measure (Rd d)) : ℝ :=
  (∫ p, g p.1 p.2 ∂(μ.prod μ')) - (∫ p, g p.1 p.2 ∂(μ.prod ν'))
    - (∫ p, g p.1 p.2 ∂(ν.prod μ')) + (∫ p, g p.1 p.2 ∂(ν.prod ν'))

/-- The scale-`t` covariance density
`∫∫ t⁻¹ C(t⁻¹(z - w)) (μ - ν)(dz) (μ' - ν')(dw)`, with `C = autoCorr κ`. -/
def scalePair (κ : Rd d → ℝ) (t : ℝ) (μ ν μ' ν' : Measure (Rd d)) : ℝ :=
  mixInt (fun z w => autoCorr κ (t⁻¹ • (z - w)) / t) μ ν μ' ν'

/-! ### The kernel `K_t` -/

section Kernel

variable {κ : Rd d → ℝ}

theorem continuous_scaleKernel (hκ : IsLFPPKernel κ) (t : ℝ) : Continuous (scaleKernel κ t) := by
  unfold scaleKernel
  exact continuous_const.mul (hκ.continuous.comp (continuous_const_smul _))

/-- Joint measurability of `((t, y), z) ↦ K_t(z - y)`. -/
theorem measurable_scaleKernel_prod (hκ : IsLFPPKernel κ) :
    Measurable fun q : (ℝ × Rd d) × Rd d => scaleKernel κ q.1.1 (q.2 - q.1.2) := by
  unfold scaleKernel
  refine (measurable_fst.fst.pow_const _).mul (hκ.continuous.measurable.comp ?_)
  exact measurable_fst.fst.inv.smul (measurable_snd.sub measurable_fst.snd)

/-- `|K_t(v)| ≤ |t^{-(d+1)/2}| A` for every `t` (no sign condition on `t`). -/
theorem abs_scaleKernel_le' {A : ℝ} (hA : ∀ x, |κ x| ≤ A) (t : ℝ) (v : Rd d) :
    |scaleKernel κ t v| ≤ |t ^ (-((d : ℝ) + 1) / 2)| * A := by
  unfold scaleKernel
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hA _) (abs_nonneg _)

/-- `z ↦ K_t(z - y)` is integrable for every finite measure (and every `t`). -/
theorem integrable_scaleKernel_sub (hκ : IsLFPPKernel κ) (t : ℝ) (y : Rd d)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] : Integrable (fun z => scaleKernel κ t (z - y)) μ := by
  obtain ⟨A, hA⟩ := hκ.exists_bound
  refine Integrable.of_bound ((continuous_scaleKernel hκ t).comp
    (continuous_id.sub continuous_const)).aestronglyMeasurable (|t ^ (-((d : ℝ) + 1) / 2)| * A)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_scaleKernel_le' hA t _

/-- `∫ |K_t(z - y) K_t(w - y)| dy ≤ 1/t` (from `2|ab| ≤ a² + b²` and `‖K_t‖₂² = 1/t`). -/
theorem integral_abs_scaleKernel_mul_le (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (z w : Rd d) :
    ∫ y, |scaleKernel κ t (z - y) * scaleKernel κ t (w - y)| ≤ t⁻¹ := by
  have hz := integrable_scaleKernel_mul hκ ht z z
  have hw := integrable_scaleKernel_mul hκ ht w w
  have hzw := integrable_scaleKernel_mul hκ ht z w
  calc ∫ y, |scaleKernel κ t (z - y) * scaleKernel κ t (w - y)|
      ≤ ∫ y, (scaleKernel κ t (z - y) * scaleKernel κ t (z - y) +
          scaleKernel κ t (w - y) * scaleKernel κ t (w - y)) / 2 := by
        refine integral_mono hzw.abs ((hz.add hw).div_const 2) fun y => ?_
        set a := scaleKernel κ t (z - y)
        set b := scaleKernel κ t (w - y)
        rw [abs_mul]
        nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
    _ = t⁻¹ := by
        rw [integral_div, integral_add hz hw, integral_scaleKernel_mul ht,
          integral_scaleKernel_mul ht]
        simp only [sub_self, smul_zero, autoCorr_zero hκ]
        ring

end Kernel

/-! ### Fixed scale: the Fubini identity -/

section FixedScale

variable {κ : Rd d → ℝ}

/-- `(μ * K_t)(y) (μ' * K_t)(y) = ∫ K_t(z - y) K_t(w - y) d(μ ⊗ μ')(z, w)`. -/
theorem scaleConv_mul_scaleConv (t : ℝ) (μ μ' : Measure (Rd d)) [SFinite μ] [SFinite μ']
    (y : Rd d) :
    scaleConv κ t μ y * scaleConv κ t μ' y =
      ∫ x, scaleKernel κ t (x.1 - y) * scaleKernel κ t (x.2 - y) ∂(μ.prod μ') :=
  (integral_prod_mul (fun z => scaleKernel κ t (z - y)) (fun w => scaleKernel κ t (w - y))).symm

theorem measurable_scaleKernel_mul_prod (hκ : IsLFPPKernel κ) (t : ℝ) :
    Measurable fun q : (Rd d × Rd d) × Rd d =>
      scaleKernel κ t (q.1.1 - q.2) * scaleKernel κ t (q.1.2 - q.2) := by
  have h := (continuous_scaleKernel hκ t).measurable
  exact (h.comp (measurable_fst.fst.sub measurable_snd)).mul
    (h.comp (measurable_fst.snd.sub measurable_snd))

/-- For `t > 0`, `((z, w), y) ↦ K_t(z - y) K_t(w - y)` is integrable for `(μ ⊗ μ') ⊗ dy`. -/
theorem integrable_scaleKernel_mul_prod (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ μ' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    Integrable (fun q : (Rd d × Rd d) × Rd d =>
      scaleKernel κ t (q.1.1 - q.2) * scaleKernel κ t (q.1.2 - q.2)) ((μ.prod μ').prod volume) := by
  have hm := measurable_scaleKernel_mul_prod hκ t
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun x => integrable_scaleKernel_mul hκ ht x.1 x.2, ?_⟩
  refine Integrable.of_bound hm.norm.aestronglyMeasurable.integral_prod_right' t⁻¹
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
  simp only [Real.norm_eq_abs]
  exact integral_abs_scaleKernel_mul_le hκ ht x.1 x.2

/-- For `t > 0`, `y ↦ (μ * K_t)(y) (μ' * K_t)(y)` is integrable. -/
theorem integrable_scaleConv_mul (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ μ' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    Integrable fun y => scaleConv κ t μ y * scaleConv κ t μ' y := by
  refine (integrable_scaleKernel_mul_prod hκ ht μ μ').integral_prod_right.congr
    (Eventually.of_forall fun y => ?_)
  exact (scaleConv_mul_scaleConv t μ μ' y).symm

/-- **(3.1) for measures at a fixed scale** (HA2 D3, Step 1): for `t > 0`,
`∫ (μ * K_t)(μ' * K_t) = ∫∫ C(t⁻¹(z - w))/t dμ(z) dμ'(w)`. -/
theorem integral_scaleConv_mul (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ μ' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    ∫ y, scaleConv κ t μ y * scaleConv κ t μ' y =
      ∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(μ.prod μ') := by
  simp_rw [scaleConv_mul_scaleConv t μ μ']
  rw [← integral_integral_swap (f := fun (x : Rd d × Rd d) (y : Rd d) =>
    scaleKernel κ t (x.1 - y) * scaleKernel κ t (x.2 - y)) (integrable_scaleKernel_mul_prod hκ ht μ μ')]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact integral_scaleKernel_mul ht x.1 x.2

/-- The four-term expansion at a fixed scale: for `t > 0`,
`((μ - ν) * K_t) ((μ' - ν') * K_t)` is integrable with integral `scalePair κ t μ ν μ' ν'`. -/
theorem integrable_scaleConv_sub_mul (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] :
    Integrable fun y => (scaleConv κ t μ y - scaleConv κ t ν y) *
      (scaleConv κ t μ' y - scaleConv κ t ν' y) := by
  have e : (fun y => (scaleConv κ t μ y - scaleConv κ t ν y) *
      (scaleConv κ t μ' y - scaleConv κ t ν' y)) = fun y =>
      scaleConv κ t μ y * scaleConv κ t μ' y - scaleConv κ t μ y * scaleConv κ t ν' y -
        scaleConv κ t ν y * scaleConv κ t μ' y + scaleConv κ t ν y * scaleConv κ t ν' y := by
    funext y; ring
  rw [e]
  exact (((integrable_scaleConv_mul hκ ht μ μ').sub (integrable_scaleConv_mul hκ ht μ ν')).sub
    (integrable_scaleConv_mul hκ ht ν μ')).add (integrable_scaleConv_mul hκ ht ν ν')

theorem integral_scaleConv_sub_mul (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] :
    ∫ y, (scaleConv κ t μ y - scaleConv κ t ν y) * (scaleConv κ t μ' y - scaleConv κ t ν' y) =
      scalePair κ t μ ν μ' ν' := by
  have e : (fun y => (scaleConv κ t μ y - scaleConv κ t ν y) *
      (scaleConv κ t μ' y - scaleConv κ t ν' y)) = fun y =>
      scaleConv κ t μ y * scaleConv κ t μ' y - scaleConv κ t μ y * scaleConv κ t ν' y -
        scaleConv κ t ν y * scaleConv κ t μ' y + scaleConv κ t ν y * scaleConv κ t ν' y := by
    funext y; ring
  rw [e, integral_add _ (integrable_scaleConv_mul hκ ht ν ν'),
    integral_sub _ (integrable_scaleConv_mul hκ ht ν μ'),
    integral_sub (integrable_scaleConv_mul hκ ht μ μ') (integrable_scaleConv_mul hκ ht μ ν'),
    integral_scaleConv_mul hκ ht, integral_scaleConv_mul hκ ht, integral_scaleConv_mul hκ ht,
    integral_scaleConv_mul hκ ht]
  · rfl
  · exact (integrable_scaleConv_mul hκ ht μ μ').sub (integrable_scaleConv_mul hκ ht μ ν')
  · exact ((integrable_scaleConv_mul hκ ht μ μ').sub (integrable_scaleConv_mul hκ ht μ ν')).sub
      (integrable_scaleConv_mul hκ ht ν μ')

/-- `scalePair κ t μ ν μ ν = ‖(μ - ν) * K_t‖₂² ≥ 0` for `t > 0`. -/
theorem scalePair_self_nonneg (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t)
    (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ scalePair κ t μ ν μ ν := by
  rw [← integral_scaleConv_sub_mul hκ ht]
  exact integral_nonneg fun y => mul_self_nonneg _

end FixedScale

/-! ### Band functions, pairability and the covariance formula -/

section Band

variable {κ : Rd d → ℝ}

theorem bandFun_apply (S : Set ℝ) (μ : Measure (Rd d)) (p : ℝ × Rd d) :
    bandFun κ S μ p = S.indicator (fun t => scaleConv κ t μ p.2) p.1 := rfl

theorem bandFun_eq_indicator (S : Set ℝ) (μ : Measure (Rd d)) :
    bandFun κ S μ = (S ×ˢ univ).indicator fun p => scaleConv κ p.1 μ p.2 := by
  funext p
  by_cases h : p.1 ∈ S
  · rw [bandFun_apply, indicator_of_mem h, indicator_of_mem (mk_mem_prod h (mem_univ p.2))]
  · rw [bandFun_apply, indicator_of_notMem h,
      indicator_of_notMem fun hp => h (mem_prod.1 hp).1]

theorem measurable_scaleConv_uncurry (hκ : IsLFPPKernel κ) (μ : Measure (Rd d)) [SFinite μ] :
    Measurable fun p : ℝ × Rd d => scaleConv κ p.1 μ p.2 :=
  ((measurable_scaleKernel_prod hκ).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem measurable_bandFun (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (μ : Measure (Rd d)) [SFinite μ] : Measurable (bandFun κ S μ) := by
  rw [bandFun_eq_indicator]
  exact (measurable_scaleConv_uncurry hκ μ).indicator (hS.prod MeasurableSet.univ)

/-- The difference of two band functions on a slice `t ∈ S`. -/
theorem bandFun_sub_apply_of_mem {S : Set ℝ} (μ ν : Measure (Rd d)) {t : ℝ} (ht : t ∈ S)
    (y : Rd d) :
    bandFun κ S μ (t, y) - bandFun κ S ν (t, y) = scaleConv κ t μ y - scaleConv κ t ν y := by
  rw [bandFun_apply, bandFun_apply, indicator_of_mem ht, indicator_of_mem ht]

theorem bandFun_apply_of_notMem {S : Set ℝ} (μ : Measure (Rd d)) {p : ℝ × Rd d}
    (hp : p.1 ∉ S) : bandFun κ S μ p = 0 := by
  rw [bandFun_apply, indicator_of_notMem hp]

/-- **Tonelli for band functions**: `∫ |F^S_μ - F^S_ν|² = ∫_S scalePair κ t μ ν μ ν dt` (in
`ℝ≥0∞`). -/
theorem lintegral_bandFun_sub_sq (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∫⁻ p, ENNReal.ofReal ((bandFun κ S μ p - bandFun κ S ν p) ^ 2) =
      ∫⁻ t in S, ENNReal.ofReal (scalePair κ t μ ν μ ν) := by
  have hm : Measurable fun p => ENNReal.ofReal ((bandFun κ S μ p - bandFun κ S ν p) ^ 2) :=
    (((measurable_bandFun hκ hS μ).sub (measurable_bandFun hκ hS ν)).pow_const 2).ennreal_ofReal
  rw [show (volume : Measure (ℝ × Rd d)) = volume.prod volume from rfl,
    lintegral_prod _ hm.aemeasurable, ← lintegral_indicator hS]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ S
  · rw [indicator_of_mem ht]
    have ht0 : 0 < t := hS0 ht
    simp_rw [bandFun_sub_apply_of_mem μ ν ht]
    rw [← ofReal_integral_eq_lintegral_ofReal, ← integral_scaleConv_sub_mul hκ ht0]
    · simp_rw [sq]
    · simp_rw [sq]
      exact integrable_scaleConv_sub_mul hκ ht0 μ ν μ ν
    · exact Eventually.of_forall fun y => sq_nonneg _
  · rw [indicator_of_notMem ht]
    simp only [bandFun_apply_of_notMem μ (p := (t, _)) ht, bandFun_apply_of_notMem ν (p := (t, _)) ht,
      sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero,
      lintegral_zero]

/-- **Pairability criterion**: for `S ⊆ (0, ∞)` and finite measures,
`IsPairable κ S μ ν ↔ ∫_S scalePair κ t μ ν μ ν dt < ∞`. -/
theorem isPairable_iff_lintegral (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsPairable κ S μ ν ↔ ∫⁻ t in S, ENNReal.ofReal (scalePair κ t μ ν μ ν) < ⊤ := by
  have hm : Measurable (bandFun κ S μ - bandFun κ S ν) :=
    (measurable_bandFun hκ hS μ).sub (measurable_bandFun hκ hS ν)
  rw [IsPairable, memLp_two_iff_integrable_sq hm.aestronglyMeasurable,
    ← lintegral_bandFun_sub_sq hκ hS hS0 μ ν]
  have h0 : 0 ≤ᵐ[volume] fun p => (bandFun κ S μ - bandFun κ S ν) p ^ 2 :=
    Eventually.of_forall fun p => sq_nonneg _
  constructor
  · intro h
    exact (hasFiniteIntegral_iff_ofReal h0).1 h.2
  · intro h
    exact ⟨(hm.pow_const 2).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal h0).2 h⟩

/-- Pairability from an integrable majorant of the scale density. -/
theorem isPairable_of_le (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) (μ ν : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : ℝ → ℝ} (hg : IntegrableOn g S) (hle : ∀ t ∈ S, scalePair κ t μ ν μ ν ≤ g t) :
    IsPairable κ S μ ν := by
  rw [isPairable_iff_lintegral hκ hS hS0]
  calc ∫⁻ t in S, ENNReal.ofReal (scalePair κ t μ ν μ ν)
      ≤ ∫⁻ t in S, ENNReal.ofReal (g t) :=
        setLIntegral_mono' hS fun t ht => ENNReal.ofReal_le_ofReal (hle t ht)
    _ < ⊤ := Integrable.lintegral_lt_top hg

theorem bandVecM_eq_toLp {S : Set ℝ} {μ ν : Measure (Rd d)} (h : IsPairable κ S μ ν) :
    bandVecM κ S μ ν = h.toLp _ := by
  rw [bandVecM, dite_eq_left h]

theorem bandVecM_of_not {S : Set ℝ} {μ ν : Measure (Rd d)} (h : ¬IsPairable κ S μ ν) :
    bandVecM κ S μ ν = 0 := by
  rw [bandVecM, dite_eq_right h]

theorem coeFn_bandVecM {S : Set ℝ} {μ ν : Measure (Rd d)} (h : IsPairable κ S μ ν) :
    (bandVecM κ S μ ν : ℝ × Rd d → ℝ) =ᵐ[volume] bandFun κ S μ - bandFun κ S ν := by
  rw [bandVecM_eq_toLp h]
  exact MemLp.coeFn_toLp _

/-- `⟪bandVecM κ S μ ν, bandVecM κ S' μ' ν'⟫ = ∫ (F^S_μ - F^S_ν)(F^{S'}_{μ'} - F^{S'}_{ν'})`. -/
theorem inner_bandVecM_eq_integral {S S' : Set ℝ} {μ ν μ' ν' : Measure (Rd d)}
    (h : IsPairable κ S μ ν) (h' : IsPairable κ S' μ' ν') :
    ⟪bandVecM κ S μ ν, bandVecM κ S' μ' ν'⟫ =
      ∫ p, (bandFun κ S μ p - bandFun κ S ν p) * (bandFun κ S' μ' p - bandFun κ S' ν' p) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_bandVecM h, coeFn_bandVecM h'] with p h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply]
  simp only [Pi.sub_apply, conj_trivial, mul_comm, RCLike.mul_re, RCLike.re_to_real,
    RCLike.im_to_real, mul_zero, sub_zero]

/-- **The covariance formula** (target T1):
`scaleCov κ S μ ν μ' ν' = ∫_S ∫∫ t⁻¹ C(t⁻¹(z - w)) (μ - ν)(dz) (μ' - ν')(dw) dt`
for pairable pairs and `S ⊆ (0, ∞)`. -/
theorem scaleCov_eq_integral (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] (h : IsPairable κ S μ ν)
    (h' : IsPairable κ S μ' ν') :
    scaleCov κ S μ ν μ' ν' = ∫ t in S, scalePair κ t μ ν μ' ν' := by
  have hint : Integrable fun p => (bandFun κ S μ p - bandFun κ S ν p) *
      (bandFun κ S μ' p - bandFun κ S ν' p) := h.integrable_mul h'
  rw [scaleCov, inner_bandVecM_eq_integral h h',
    show (volume : Measure (ℝ × Rd d)) = volume.prod volume from rfl, integral_prod _ hint,
    ← integral_indicator hS]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ S
  · simp only [indicator_of_mem ht, bandFun_sub_apply_of_mem _ _ ht]
    exact integral_scaleConv_sub_mul hκ (hS0 ht) μ ν μ' ν'
  · simp only [indicator_of_notMem ht, bandFun_apply_of_notMem _ (p := (t, _)) ht, sub_self,
      mul_zero, integral_zero]

/-- The scale density of pairable pairs is integrable on `S`. -/
theorem integrableOn_scalePair (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    (hS0 : S ⊆ Ioi 0) {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] (h : IsPairable κ S μ ν)
    (h' : IsPairable κ S μ' ν') :
    IntegrableOn (fun t => scalePair κ t μ ν μ' ν') S := by
  have hint : Integrable (fun p => (bandFun κ S μ p - bandFun κ S ν p) *
      (bandFun κ S μ' p - bandFun κ S ν' p)) (volume.prod volume) := h.integrable_mul h'
  rw [← integrable_indicator_iff hS]
  refine hint.integral_prod_left.congr (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ S
  · simp only [indicator_of_mem ht, bandFun_sub_apply_of_mem _ _ ht]
    exact integral_scaleConv_sub_mul hκ (hS0 ht) μ ν μ' ν'
  · simp only [indicator_of_notMem ht, bandFun_apply_of_notMem _ (p := (t, _)) ht, sub_self,
      mul_zero, integral_zero]

/-- `scaleCov κ S μ ν μ ν = ‖bandVecM κ S μ ν‖²`. -/
theorem scaleCov_self (S : Set ℝ) (μ ν : Measure (Rd d)) :
    scaleCov κ S μ ν μ ν = ‖bandVecM κ S μ ν‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

theorem scaleCov_self_nonneg (S : Set ℝ) (μ ν : Measure (Rd d)) : 0 ≤ scaleCov κ S μ ν μ ν := by
  rw [scaleCov_self]
  positivity

/-- `scaleCov` is symmetric. -/
theorem scaleCov_comm (S : Set ℝ) (μ ν μ' ν' : Measure (Rd d)) :
    scaleCov κ S μ ν μ' ν' = scaleCov κ S μ' ν' μ ν :=
  real_inner_comm _ _

end Band

/-! ### Point vectors, bilinearity and the Gram property -/

section Algebra

variable {κ : Rd d → ℝ}

theorem bandFun_zero_measure (S : Set ℝ) : bandFun κ S (0 : Measure (Rd d)) = 0 := by
  funext p
  simp only [bandFun, integral_zero_measure, indicator_zero, Pi.zero_apply]

/-- The band function of a Dirac mass is P-F1's point kernel `k_{a,b,z}`. -/
theorem bandFun_dirac (a b : ℝ) (z : Rd d) :
    bandFun κ (Ioo a b) (Measure.dirac z) = bandKernel κ a b z := by
  funext p
  simp only [bandFun, bandKernel, integral_dirac]

/-- **Compatibility with the point vectors** (target T1): `bandVecM κ (a, b) δ_z 0 = k_{a,b,z}`
(the frozen `bandVec`), for all `a, b, z`. -/
theorem bandVecM_dirac_zero (a b : ℝ) (z : Rd d) :
    bandVecM κ (Ioo a b) (Measure.dirac z) 0 = bandVec κ a b z := by
  have e : bandFun κ (Ioo a b) (Measure.dirac z) - bandFun κ (Ioo a b) 0 = bandKernel κ a b z := by
    rw [bandFun_dirac, bandFun_zero_measure, sub_zero]
  by_cases h : MemLp (bandKernel κ a b z) 2 volume
  · have h' : IsPairable κ (Ioo a b) (Measure.dirac z) 0 := by rw [IsPairable, e]; exact h
    rw [bandVecM_eq_toLp h', bandVec, dite_eq_left h]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall (congrFun e))
  · have h' : ¬IsPairable κ (Ioo a b) (Measure.dirac z) 0 := by rw [IsPairable, e]; exact h
    rw [bandVecM_of_not h', bandVec, dite_eq_right h]

theorem scaleConv_add (hκ : IsLFPPKernel κ) (t : ℝ) (μ₁ μ₂ : Measure (Rd d)) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (y : Rd d) :
    scaleConv κ t (μ₁ + μ₂) y = scaleConv κ t μ₁ y + scaleConv κ t μ₂ y :=
  integral_add_measure (integrable_scaleKernel_sub hκ t y μ₁) (integrable_scaleKernel_sub hκ t y μ₂)

theorem bandFun_add (hκ : IsLFPPKernel κ) (S : Set ℝ) (μ₁ μ₂ : Measure (Rd d))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    bandFun κ S (μ₁ + μ₂) = bandFun κ S μ₁ + bandFun κ S μ₂ := by
  funext p
  simp only [Pi.add_apply, bandFun_apply]
  have e : (fun t => scaleConv κ t (μ₁ + μ₂) p.2) =
      fun t => scaleConv κ t μ₁ p.2 + scaleConv κ t μ₂ p.2 :=
    funext fun t => scaleConv_add hκ t μ₁ μ₂ p.2
  rw [e, indicator_add]

theorem bandFun_smul (S : Set ℝ) (c : ℝ≥0∞) (μ : Measure (Rd d)) :
    bandFun κ S (c • μ) = c.toReal • bandFun κ S μ := by
  funext p
  simp only [Pi.smul_apply, bandFun, integral_smul_measure]
  exact indicator_const_smul_apply S c.toReal _ p.1

/-- Two pairable pairs with a.e. equal band integrands have the same kernel vector. -/
theorem bandVecM_congr {S S' : Set ℝ} {μ ν μ' ν' : Measure (Rd d)} (h : IsPairable κ S μ ν)
    (h' : IsPairable κ S' μ' ν')
    (e : bandFun κ S μ - bandFun κ S ν =ᵐ[volume] bandFun κ S' μ' - bandFun κ S' ν') :
    bandVecM κ S μ ν = bandVecM κ S' μ' ν' :=
  Lp.ext ((coeFn_bandVecM h).trans (e.trans (coeFn_bandVecM h').symm))

theorem IsPairable.add (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ₁ ν₁ μ₂ ν₂ : Measure (Rd d)}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (h₁ : IsPairable κ S μ₁ ν₁) (h₂ : IsPairable κ S μ₂ ν₂) :
    IsPairable κ S (μ₁ + μ₂) (ν₁ + ν₂) := by
  have e : bandFun κ S (μ₁ + μ₂) - bandFun κ S (ν₁ + ν₂) =
      (bandFun κ S μ₁ - bandFun κ S ν₁) + (bandFun κ S μ₂ - bandFun κ S ν₂) := by
    rw [bandFun_add hκ, bandFun_add hκ]; abel
  rw [IsPairable, e]
  exact MemLp.add h₁ h₂

/-- **Additivity** of the kernel vectors in the measure pair. -/
theorem bandVecM_add (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ₁ ν₁ μ₂ ν₂ : Measure (Rd d)}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (h₁ : IsPairable κ S μ₁ ν₁) (h₂ : IsPairable κ S μ₂ ν₂) :
    bandVecM κ S (μ₁ + μ₂) (ν₁ + ν₂) = bandVecM κ S μ₁ ν₁ + bandVecM κ S μ₂ ν₂ := by
  have e : bandFun κ S (μ₁ + μ₂) - bandFun κ S (ν₁ + ν₂) =
      (bandFun κ S μ₁ - bandFun κ S ν₁) + (bandFun κ S μ₂ - bandFun κ S ν₂) := by
    rw [bandFun_add hκ, bandFun_add hκ]; abel
  refine Lp.ext ?_
  filter_upwards [coeFn_bandVecM (IsPairable.add hκ h₁ h₂),
    Lp.coeFn_add (bandVecM κ S μ₁ ν₁) (bandVecM κ S μ₂ ν₂), coeFn_bandVecM h₁,
    coeFn_bandVecM h₂] with p hp1 hp2 hp3 hp4
  rw [hp1, hp2, Pi.add_apply, hp3, hp4]
  exact congrFun e p

theorem isPairable_comm {S : Set ℝ} {μ ν : Measure (Rd d)} :
    IsPairable κ S μ ν ↔ IsPairable κ S ν μ := by
  rw [IsPairable, IsPairable, ← neg_sub, memLp_neg_iff]

/-- Exchanging the two measures negates the kernel vector. -/
theorem bandVecM_swap (S : Set ℝ) (μ ν : Measure (Rd d)) :
    bandVecM κ S ν μ = -bandVecM κ S μ ν := by
  by_cases h : IsPairable κ S μ ν
  · refine Lp.ext ?_
    filter_upwards [coeFn_bandVecM (isPairable_comm.1 h), Lp.coeFn_neg (bandVecM κ S μ ν),
      coeFn_bandVecM h] with p hp1 hp2 hp3
    rw [hp1, hp2, Pi.neg_apply, hp3]
    simp only [Pi.sub_apply, neg_sub]
  · rw [bandVecM_of_not h, bandVecM_of_not (mt isPairable_comm.2 h), neg_zero]

theorem bandVecM_self (S : Set ℝ) (μ : Measure (Rd d)) : bandVecM κ S μ μ = 0 := by
  have h : IsPairable κ S μ μ := by rw [IsPairable, sub_self]; exact MemLp.zero
  refine Lp.ext ?_
  filter_upwards [coeFn_bandVecM h, Lp.coeFn_zero (E := ℝ) (p := 2)
    (μ := (volume : Measure (ℝ × Rd d)))] with p hp1 hp2
  rw [hp1, hp2]
  simp only [Pi.sub_apply, sub_self, Pi.zero_apply]

/-- Adding a common finite measure to both entries does not change the kernel vector. -/
theorem bandVecM_add_right (hκ : IsLFPPKernel κ) (S : Set ℝ) (μ ν ρ : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ] :
    bandVecM κ S (μ + ρ) (ν + ρ) = bandVecM κ S μ ν := by
  have e : bandFun κ S (μ + ρ) - bandFun κ S (ν + ρ) = bandFun κ S μ - bandFun κ S ν := by
    rw [bandFun_add hκ, bandFun_add hκ]; abel
  have hiff : IsPairable κ S (μ + ρ) (ν + ρ) ↔ IsPairable κ S μ ν := by
    rw [IsPairable, IsPairable, e]
  by_cases h : IsPairable κ S μ ν
  · exact bandVecM_congr (hiff.2 h) h (Eventually.of_forall (congrFun e))
  · rw [bandVecM_of_not h, bandVecM_of_not (mt hiff.1 h)]

/-- `bandVecM κ S μ ν = bandVecM κ S μ 0 - bandVecM κ S ν 0` when both single measures are
pairable. -/
theorem bandVecM_sub {S : Set ℝ} {μ ν : Measure (Rd d)} (hμ : IsPairable κ S μ 0)
    (hν : IsPairable κ S ν 0) : bandVecM κ S μ ν = bandVecM κ S μ 0 - bandVecM κ S ν 0 := by
  have e : bandFun κ S μ - bandFun κ S ν =
      (bandFun κ S μ - bandFun κ S 0) - (bandFun κ S ν - bandFun κ S 0) := by
    rw [bandFun_zero_measure, sub_zero, sub_zero]
  have h : IsPairable κ S μ ν := by rw [IsPairable, e]; exact MemLp.sub hμ hν
  refine Lp.ext ?_
  filter_upwards [coeFn_bandVecM h, Lp.coeFn_sub (bandVecM κ S μ 0) (bandVecM κ S ν 0),
    coeFn_bandVecM hμ, coeFn_bandVecM hν] with p hp1 hp2 hp3 hp4
  rw [hp1, hp2]
  simp only [Pi.sub_apply] at hp3 hp4 ⊢
  rw [hp3, hp4, bandFun_zero_measure]
  simp only [Pi.zero_apply, sub_zero]

/-- Differences of pairable pairs: `v(μ, ν) - v(μ', ν') = v(μ + ν', ν + μ')`. -/
theorem bandVecM_sub_bandVecM (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ ν μ' ν' : Measure (Rd d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (h : IsPairable κ S μ ν) (h' : IsPairable κ S μ' ν') :
    bandVecM κ S μ ν - bandVecM κ S μ' ν' = bandVecM κ S (μ + ν') (ν + μ') := by
  rw [bandVecM_add hκ h (isPairable_comm.1 h'), bandVecM_swap S μ' ν', sub_eq_add_neg]

theorem IsPairable.sub (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ ν μ' ν' : Measure (Rd d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (h : IsPairable κ S μ ν) (h' : IsPairable κ S μ' ν') :
    IsPairable κ S (μ + ν') (ν + μ') :=
  IsPairable.add hκ h (isPairable_comm.1 h')

/-- Scaling both measures by `c < ∞` scales the kernel vector by `c`. -/
theorem bandVecM_smul (S : Set ℝ) (μ ν : Measure (Rd d)) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    bandVecM κ S (c • μ) (c • ν) = c.toReal • bandVecM κ S μ ν := by
  have e : bandFun κ S (c • μ) - bandFun κ S (c • ν) =
      c.toReal • (bandFun κ S μ - bandFun κ S ν) := by
    rw [bandFun_smul, bandFun_smul, smul_sub]
  rcases eq_or_ne c 0 with rfl | hc0
  · simp only [zero_smul, ENNReal.toReal_zero, bandVecM_self]
  have hcr : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hc0, hc⟩
  have hiff : IsPairable κ S (c • μ) (c • ν) ↔ IsPairable κ S μ ν := by
    rw [IsPairable, IsPairable, e]
    constructor
    · intro h'
      have h'' := h'.const_smul c.toReal⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hcr, one_smul] at h''
    · intro h'
      exact h'.const_smul c.toReal
  by_cases h : IsPairable κ S μ ν
  · refine Lp.ext ?_
    filter_upwards [coeFn_bandVecM (hiff.2 h), Lp.coeFn_smul c.toReal (bandVecM κ S μ ν),
      coeFn_bandVecM h] with p hp1 hp2 hp3
    rw [hp1, hp2, Pi.smul_apply, hp3]
    exact congrFun e p
  · rw [bandVecM_of_not h, bandVecM_of_not (mt hiff.1 h), smul_zero]

/-- Additivity of `scaleCov` in the first pair. -/
theorem scaleCov_add_left (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ₁ ν₁ μ₂ ν₂ : Measure (Rd d)}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (h₁ : IsPairable κ S μ₁ ν₁) (h₂ : IsPairable κ S μ₂ ν₂) (μ' ν' : Measure (Rd d)) :
    scaleCov κ S (μ₁ + μ₂) (ν₁ + ν₂) μ' ν' =
      scaleCov κ S μ₁ ν₁ μ' ν' + scaleCov κ S μ₂ ν₂ μ' ν' := by
  rw [scaleCov, bandVecM_add hκ h₁ h₂, inner_add_left]
  rfl

/-- Additivity of `scaleCov` in the second pair. -/
theorem scaleCov_add_right (hκ : IsLFPPKernel κ) {S : Set ℝ} (μ ν : Measure (Rd d))
    {μ₁ ν₁ μ₂ ν₂ : Measure (Rd d)} [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν₂] (h₁ : IsPairable κ S μ₁ ν₁) (h₂ : IsPairable κ S μ₂ ν₂) :
    scaleCov κ S μ ν (μ₁ + μ₂) (ν₁ + ν₂) =
      scaleCov κ S μ ν μ₁ ν₁ + scaleCov κ S μ ν μ₂ ν₂ := by
  rw [scaleCov, bandVecM_add hκ h₁ h₂, inner_add_right]
  rfl

/-- Exchanging the measures of the first pair negates `scaleCov`. -/
theorem scaleCov_swap_left (S : Set ℝ) (μ ν μ' ν' : Measure (Rd d)) :
    scaleCov κ S ν μ μ' ν' = -scaleCov κ S μ ν μ' ν' := by
  rw [scaleCov, scaleCov, bandVecM_swap, inner_neg_left]

theorem scaleCov_swap_right (S : Set ℝ) (μ ν μ' ν' : Measure (Rd d)) :
    scaleCov κ S μ ν ν' μ' = -scaleCov κ S μ ν μ' ν' := by
  rw [scaleCov, scaleCov, bandVecM_swap S μ' ν', inner_neg_right]

theorem scaleCov_smul_left (S : Set ℝ) (μ ν μ' ν' : Measure (Rd d)) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    scaleCov κ S (c • μ) (c • ν) μ' ν' = c.toReal * scaleCov κ S μ ν μ' ν' := by
  rw [scaleCov, scaleCov, bandVecM_smul S μ ν hc, real_inner_smul_left]

/-- **Gram property** (target T1): `Σ_{i,j} c_i c_j scaleCov(μ_i, ν_i, μ_j, ν_j) ≥ 0`. -/
theorem sum_mul_scaleCov_nonneg {ι : Type*} (S : Set ℝ) (s : Finset ι)
    (μ ν : ι → Measure (Rd d)) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * scaleCov κ S (μ i) (ν i) (μ j) (ν j) := by
  have h : ∑ i ∈ s, ∑ j ∈ s, c i * c j * scaleCov κ S (μ i) (ν i) (μ j) (ν j) =
      ⟪∑ i ∈ s, c i • bandVecM κ S (μ i) (ν i), ∑ j ∈ s, c j • bandVecM κ S (μ j) (ν j)⟫ := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, scaleCov]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm]
    ring
  rw [h, real_inner_self_eq_norm_sq]
  positivity

/-- **Gram property**, matrix form: `scaleCov` is positive semidefinite on every finite family
(`LQGDimension.PSDOn`). -/
theorem psdOn_scaleCov {ι : Type*} (S : Set ℝ) (F : Finset ι) (μ ν : ι → Measure (Rd d)) :
    LQGDimension.PSDOn F fun i j => scaleCov κ S (μ i) (ν i) (μ j) (ν j) := by
  have h := Matrix.posSemidef_gram ℝ fun i : F => bandVecM κ S (μ i) (ν i)
  exact h

end Algebra

/-! ### Scale sets -/

section ScaleSets

variable {κ : Rd d → ℝ}

theorem bandFun_sub_eq_indicator_of_subset {S T : Set ℝ} (hST : S ⊆ T) (μ ν : Measure (Rd d)) :
    bandFun κ S μ - bandFun κ S ν = (S ×ˢ univ).indicator (bandFun κ T μ - bandFun κ T ν) := by
  funext p
  by_cases h : p.1 ∈ S
  · rw [indicator_of_mem (mk_mem_prod h (mem_univ p.2)), Pi.sub_apply, Pi.sub_apply,
      bandFun_apply, bandFun_apply, bandFun_apply, bandFun_apply, indicator_of_mem h,
      indicator_of_mem h, indicator_of_mem (hST h), indicator_of_mem (hST h)]
  · rw [indicator_of_notMem fun hp => h (mem_prod.1 hp).1, Pi.sub_apply,
      bandFun_apply_of_notMem μ h, bandFun_apply_of_notMem ν h, sub_self]

/-- Pairability passes to measurable scale subsets (HA2 D4). -/
theorem IsPairable.mono_set {S T : Set ℝ} (hS : MeasurableSet S) (hST : S ⊆ T)
    {μ ν : Measure (Rd d)} (h : IsPairable κ T μ ν) : IsPairable κ S μ ν := by
  rw [IsPairable, bandFun_sub_eq_indicator_of_subset hST]
  exact h.indicator (hS.prod MeasurableSet.univ)

/-- **Cutoff domination** for nested scale sets (HA2 D4; (3.3) is the case `T = (0, ∞)`):
`Var⟨H_S, μ - ν⟩ ≤ Var⟨H_T, μ - ν⟩`. -/
theorem scaleCov_self_le_of_subset {S T : Set ℝ} (hS : MeasurableSet S) (hST : S ⊆ T)
    {μ ν : Measure (Rd d)} (h : IsPairable κ T μ ν) :
    scaleCov κ S μ ν μ ν ≤ scaleCov κ T μ ν μ ν := by
  have hS' := h.mono_set hS hST
  rw [scaleCov, scaleCov, inner_bandVecM_eq_integral hS' hS', inner_bandVecM_eq_integral h h]
  refine integral_mono (hS'.integrable_mul hS') (h.integrable_mul h) fun p => ?_
  have e := congrFun (bandFun_sub_eq_indicator_of_subset (κ := κ) hST μ ν) p
  simp only [Pi.sub_apply] at e
  rw [e]
  by_cases hp : p ∈ S ×ˢ (univ : Set (Rd d))
  · rw [indicator_of_mem hp]
    simp only [Pi.sub_apply, le_refl]
  · rw [indicator_of_notMem hp, mul_zero]
    exact mul_self_nonneg _

/-- **Orthogonality of disjoint bands** (HA2 D2.1): the kernel vectors of disjoint scale sets are
orthogonal (so the pairings are independent). -/
theorem inner_bandVecM_eq_zero_of_disjoint {S₁ S₂ : Set ℝ} (hdisj : Disjoint S₁ S₂)
    (μ ν μ' ν' : Measure (Rd d)) : ⟪bandVecM κ S₁ μ ν, bandVecM κ S₂ μ' ν'⟫ = 0 := by
  by_cases h₁ : IsPairable κ S₁ μ ν
  · by_cases h₂ : IsPairable κ S₂ μ' ν'
    · rw [inner_bandVecM_eq_integral h₁ h₂]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun p => ?_)
      by_cases hp : p.1 ∈ S₁
      · have hp2 : p.1 ∉ S₂ := Set.disjoint_left.1 hdisj hp
        simp only [bandFun_apply_of_notMem μ' hp2, bandFun_apply_of_notMem ν' hp2, sub_self,
          mul_zero, Pi.zero_apply]
      · simp only [bandFun_apply_of_notMem μ hp, bandFun_apply_of_notMem ν hp, sub_self,
          zero_mul, Pi.zero_apply]
    · rw [bandVecM_of_not h₂, inner_zero_right]
  · rw [bandVecM_of_not h₁, inner_zero_left]

/-- **Band additivity** (HA2 (F3), measure level): for disjoint measurable scale sets,
`v_{S₁ ∪ S₂}(μ, ν) = v_{S₁}(μ, ν) + v_{S₂}(μ, ν)`. -/
theorem bandVecM_union {S₁ S₂ : Set ℝ} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hdisj : Disjoint S₁ S₂) {μ ν : Measure (Rd d)} (h : IsPairable κ (S₁ ∪ S₂) μ ν) :
    bandVecM κ (S₁ ∪ S₂) μ ν = bandVecM κ S₁ μ ν + bandVecM κ S₂ μ ν := by
  have h₁ := h.mono_set hS₁ subset_union_left
  have h₂ := h.mono_set hS₂ subset_union_right
  have e : bandFun κ (S₁ ∪ S₂) μ - bandFun κ (S₁ ∪ S₂) ν =
      (bandFun κ S₁ μ - bandFun κ S₁ ν) + (bandFun κ S₂ μ - bandFun κ S₂ ν) := by
    funext p
    simp only [Pi.add_apply, Pi.sub_apply]
    by_cases hp1 : p.1 ∈ S₁
    · have hp2 : p.1 ∉ S₂ := Set.disjoint_left.1 hdisj hp1
      rw [bandFun_apply_of_notMem μ hp2, bandFun_apply_of_notMem ν hp2, bandFun_apply,
        bandFun_apply, bandFun_apply, bandFun_apply, indicator_of_mem (mem_union_left _ hp1),
        indicator_of_mem (mem_union_left _ hp1), indicator_of_mem hp1, indicator_of_mem hp1]
      ring
    · by_cases hp2 : p.1 ∈ S₂
      · rw [bandFun_apply_of_notMem μ hp1, bandFun_apply_of_notMem ν hp1, bandFun_apply,
          bandFun_apply, bandFun_apply, bandFun_apply, indicator_of_mem (mem_union_right _ hp2),
          indicator_of_mem (mem_union_right _ hp2), indicator_of_mem hp2, indicator_of_mem hp2]
        ring
      · have hp : p.1 ∉ S₁ ∪ S₂ := fun hh => hh.elim hp1 hp2
        rw [bandFun_apply_of_notMem μ hp, bandFun_apply_of_notMem ν hp,
          bandFun_apply_of_notMem μ hp1, bandFun_apply_of_notMem ν hp1,
          bandFun_apply_of_notMem μ hp2, bandFun_apply_of_notMem ν hp2]
        ring
  refine Lp.ext ?_
  filter_upwards [coeFn_bandVecM h, Lp.coeFn_add (bandVecM κ S₁ μ ν) (bandVecM κ S₂ μ ν),
    coeFn_bandVecM h₁, coeFn_bandVecM h₂] with p hp1 hp2 hp3 hp4
  rw [hp1, hp2, Pi.add_apply, hp3, hp4]
  exact congrFun e p

end ScaleSets

/-! ### Bounds on `mixInt` and pairability -/

section Pairability

variable {κ : Rd d → ℝ}

/-- `|∫ g d(α ⊗ β)| ≤ M α(ℝ^d) β(ℝ^d)` for `|g| ≤ M` a.e. -/
theorem FieldAux.abs_integral_prod_le {g : Rd d → Rd d → ℝ} {M : ℝ} (α β : Measure (Rd d))
    [IsFiniteMeasure α] [IsFiniteMeasure β] (hg : ∀ᵐ p ∂(α.prod β), |g p.1 p.2| ≤ M) :
    |∫ p, g p.1 p.2 ∂(α.prod β)| ≤ M * (α.real univ * β.real univ) := by
  have h := norm_integral_le_of_norm_le_const (μ := α.prod β) (f := fun p => g p.1 p.2) (C := M)
    (by simpa only [Real.norm_eq_abs] using hg)
  rw [Real.norm_eq_abs] at h
  rwa [← univ_prod_univ, measureReal_prod_prod] at h

/-- `|mixInt g μ ν μ' ν'| ≤ M (μ(ℝ^d) + ν(ℝ^d)) (μ'(ℝ^d) + ν'(ℝ^d))` for `|g| ≤ M` a.e. on the
four product measures. -/
theorem abs_mixInt_le {g : Rd d → Rd d → ℝ} {M : ℝ} (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (h1 : ∀ᵐ p ∂(μ.prod μ'), |g p.1 p.2| ≤ M) (h2 : ∀ᵐ p ∂(μ.prod ν'), |g p.1 p.2| ≤ M)
    (h3 : ∀ᵐ p ∂(ν.prod μ'), |g p.1 p.2| ≤ M) (h4 : ∀ᵐ p ∂(ν.prod ν'), |g p.1 p.2| ≤ M) :
    |mixInt g μ ν μ' ν'| ≤
      M * ((μ.real univ + ν.real univ) * (μ'.real univ + ν'.real univ)) := by
  have e1 := abs_le.1 (FieldAux.abs_integral_prod_le μ μ' h1)
  have e2 := abs_le.1 (FieldAux.abs_integral_prod_le μ ν' h2)
  have e3 := abs_le.1 (FieldAux.abs_integral_prod_le ν μ' h3)
  have e4 := abs_le.1 (FieldAux.abs_integral_prod_le ν ν' h4)
  have hM : M * ((μ.real univ + ν.real univ) * (μ'.real univ + ν'.real univ)) =
      M * (μ.real univ * μ'.real univ) + M * (μ.real univ * ν'.real univ) +
        M * (ν.real univ * μ'.real univ) + M * (ν.real univ * ν'.real univ) := by ring
  rw [hM, mixInt, abs_le]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]

/-- `mixInt` of a constant: `c (μ(ℝ^d) - ν(ℝ^d)) (μ'(ℝ^d) - ν'(ℝ^d))`. -/
theorem mixInt_const (c : ℝ) (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] :
    mixInt (fun _ _ => c) μ ν μ' ν' =
      c * ((μ.real univ - ν.real univ) * (μ'.real univ - ν'.real univ)) := by
  simp only [mixInt, integral_const, smul_eq_mul, ← univ_prod_univ, measureReal_prod_prod]
  ring

/-- `mixInt` is additive in the integrand (given integrability on the four products). -/
theorem mixInt_sub {g₁ g₂ : Rd d → Rd d → ℝ} {μ ν μ' ν' : Measure (Rd d)}
    (h1 : ∀ α β : Measure (Rd d), (α = μ ∨ α = ν) → (β = μ' ∨ β = ν') →
      Integrable (fun p : Rd d × Rd d => g₁ p.1 p.2) (α.prod β))
    (h2 : ∀ α β : Measure (Rd d), (α = μ ∨ α = ν) → (β = μ' ∨ β = ν') →
      Integrable (fun p : Rd d × Rd d => g₂ p.1 p.2) (α.prod β)) :
    mixInt (fun z w => g₁ z w - g₂ z w) μ ν μ' ν' = mixInt g₁ μ ν μ' ν' - mixInt g₂ μ ν μ' ν' := by
  simp only [mixInt]
  rw [integral_sub (h1 μ μ' (Or.inl rfl) (Or.inl rfl)) (h2 μ μ' (Or.inl rfl) (Or.inl rfl)),
    integral_sub (h1 μ ν' (Or.inl rfl) (Or.inr rfl)) (h2 μ ν' (Or.inl rfl) (Or.inr rfl)),
    integral_sub (h1 ν μ' (Or.inr rfl) (Or.inl rfl)) (h2 ν μ' (Or.inr rfl) (Or.inl rfl)),
    integral_sub (h1 ν ν' (Or.inr rfl) (Or.inr rfl)) (h2 ν ν' (Or.inr rfl) (Or.inr rfl))]
  ring

/-- `mixInt` is additive in the integrand (given integrability on the four products). -/
theorem mixInt_add {g₁ g₂ : Rd d → Rd d → ℝ} {μ ν μ' ν' : Measure (Rd d)}
    (h1 : ∀ α β : Measure (Rd d), (α = μ ∨ α = ν) → (β = μ' ∨ β = ν') →
      Integrable (fun p : Rd d × Rd d => g₁ p.1 p.2) (α.prod β))
    (h2 : ∀ α β : Measure (Rd d), (α = μ ∨ α = ν) → (β = μ' ∨ β = ν') →
      Integrable (fun p : Rd d × Rd d => g₂ p.1 p.2) (α.prod β)) :
    mixInt (fun z w => g₁ z w + g₂ z w) μ ν μ' ν' = mixInt g₁ μ ν μ' ν' + mixInt g₂ μ ν μ' ν' := by
  simp only [mixInt]
  rw [integral_add (h1 μ μ' (Or.inl rfl) (Or.inl rfl)) (h2 μ μ' (Or.inl rfl) (Or.inl rfl)),
    integral_add (h1 μ ν' (Or.inl rfl) (Or.inr rfl)) (h2 μ ν' (Or.inl rfl) (Or.inr rfl)),
    integral_add (h1 ν μ' (Or.inr rfl) (Or.inl rfl)) (h2 ν μ' (Or.inr rfl) (Or.inl rfl)),
    integral_add (h1 ν ν' (Or.inr rfl) (Or.inr rfl)) (h2 ν ν' (Or.inr rfl) (Or.inr rfl))]
  ring

/-- `mixInt` commutes with constant factors. -/
theorem mixInt_const_mul (c : ℝ) (g : Rd d → Rd d → ℝ) (μ ν μ' ν' : Measure (Rd d)) :
    mixInt (fun z w => c * g z w) μ ν μ' ν' = c * mixInt g μ ν μ' ν' := by
  simp only [mixInt, integral_const_mul]
  ring

/-- `mixInt` only sees the integrand almost everywhere on the four product measures. -/
theorem mixInt_congr_ae {g₁ g₂ : Rd d → Rd d → ℝ} {μ ν μ' ν' : Measure (Rd d)}
    (h : ∀ α β : Measure (Rd d), (α = μ ∨ α = ν) → (β = μ' ∨ β = ν') →
      ∀ᵐ p ∂(α.prod β), g₁ p.1 p.2 = g₂ p.1 p.2) :
    mixInt g₁ μ ν μ' ν' = mixInt g₂ μ ν μ' ν' := by
  simp only [mixInt]
  rw [integral_congr_ae (h μ μ' (Or.inl rfl) (Or.inl rfl)),
    integral_congr_ae (h μ ν' (Or.inl rfl) (Or.inr rfl)),
    integral_congr_ae (h ν μ' (Or.inr rfl) (Or.inl rfl)),
    integral_congr_ae (h ν ν' (Or.inr rfl) (Or.inr rfl))]

/-- `mixInt` of pushforwards: `∫∫ g d(T_*·) = ∫∫ g(T z, T w) d(·)`. -/
theorem mixInt_map {T : Rd d → Rd d} (hT : Measurable T) {g : Rd d → Rd d → ℝ}
    (hg : Measurable fun p : Rd d × Rd d => g p.1 p.2) (μ ν μ' ν' : Measure (Rd d)) [SFinite μ]
    [SFinite ν] [SFinite μ'] [SFinite ν'] :
    mixInt g (μ.map T) (ν.map T) (μ'.map T) (ν'.map T) =
      mixInt (fun z w => g (T z) (T w)) μ ν μ' ν' := by
  have key : ∀ (α β : Measure (Rd d)) [SFinite α] [SFinite β],
      ∫ p, g p.1 p.2 ∂((α.map T).prod (β.map T)) = ∫ p, g (T p.1) (T p.2) ∂(α.prod β) := by
    intro α β _ _
    rw [Measure.map_prod_map α β hT hT,
      integral_map (hT.prodMap hT).aemeasurable hg.aestronglyMeasurable]
    rfl
  simp only [mixInt, key]

/-- `|scalePair κ t μ ν μ' ν'| ≤ t⁻¹ (μ(ℝ^d) + ν(ℝ^d)) (μ'(ℝ^d) + ν'(ℝ^d))` (`|C| ≤ 1`). -/
theorem abs_scalePair_le (hκ : IsLFPPKernel κ) {t : ℝ} (ht : 0 < t) (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] :
    |scalePair κ t μ ν μ' ν'| ≤
      t⁻¹ * ((μ.real univ + ν.real univ) * (μ'.real univ + ν'.real univ)) := by
  have hb : ∀ z w : Rd d, |autoCorr κ (t⁻¹ • (z - w)) / t| ≤ t⁻¹ := by
    intro z w
    rw [abs_div, abs_of_pos ht, div_eq_mul_inv]
    calc |autoCorr κ (t⁻¹ • (z - w))| * t⁻¹ ≤ 1 * t⁻¹ :=
          mul_le_mul_of_nonneg_right (abs_autoCorr_le_one hκ _) (inv_nonneg.2 ht.le)
      _ = t⁻¹ := one_mul _
  exact abs_mixInt_le μ ν μ' ν' (Eventually.of_forall fun p => hb p.1 p.2)
    (Eventually.of_forall fun p => hb p.1 p.2) (Eventually.of_forall fun p => hb p.1 p.2)
    (Eventually.of_forall fun p => hb p.1 p.2)

/-- **Pairability for bounded bands** (target T1): every pair of finite measures is pairable
for a measurable scale set `S ⊆ [a, b]` with `a > 0`. -/
theorem isPairable_of_subset_Icc (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    {a b : ℝ} (ha : 0 < a) (hSab : S ⊆ Icc a b) (μ ν : Measure (Rd d)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : IsPairable κ S μ ν := by
  have hS0 : S ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le ha (hSab ht).1
  set M := (μ.real univ + ν.real univ) * (μ.real univ + ν.real univ) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine isPairable_of_le hκ hS hS0 μ ν (g := fun _ => a⁻¹ * M) ?_ fun t ht => ?_
  · exact (integrableOn_const (measure_Icc_lt_top (a := a) (b := b)).ne).mono_set hSab
  · have ht0 : 0 < t := hS0 ht
    calc scalePair κ t μ ν μ ν ≤ |scalePair κ t μ ν μ ν| := le_abs_self _
      _ ≤ t⁻¹ * M := abs_scalePair_le hκ ht0 μ ν μ ν
      _ ≤ a⁻¹ * M := mul_le_mul_of_nonneg_right (inv_anti₀ ha (hSab ht).1) hM0

/-- Integrability of a continuous bounded kernel of `z - w` against finite product measures. -/
theorem integrable_autoCorr_div (hκ : IsLFPPKernel κ) (t : ℝ) (α β : Measure (Rd d))
    [IsFiniteMeasure α] [IsFiniteMeasure β] :
    Integrable (fun p : Rd d × Rd d => autoCorr κ (t⁻¹ • (p.1 - p.2)) / t) (α.prod β) := by
  refine Integrable.of_bound (((continuous_autoCorr hκ).comp
    ((continuous_fst.sub continuous_snd).const_smul t⁻¹)).div_const t).aestronglyMeasurable
    (|t⁻¹|) (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_div, div_eq_mul_inv, abs_inv]
  calc |autoCorr κ (t⁻¹ • (p.1 - p.2))| * |t|⁻¹ ≤ 1 * |t|⁻¹ :=
        mul_le_mul_of_nonneg_right (abs_autoCorr_le_one hκ _) (inv_nonneg.2 (abs_nonneg t))
    _ = |t|⁻¹ := one_mul _

/-- With equal masses of the first pair, any constant can be subtracted from the integrand:
`scalePair κ t μ ν μ' ν' = ∫∫ (C(t⁻¹(z - w))/t - c₀) (μ - ν)(dz) (μ' - ν')(dw)`. -/
theorem scalePair_eq_mixInt_sub_const (hκ : IsLFPPKernel κ) (t c₀ : ℝ)
    (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] (hmass : μ.real univ = ν.real univ) :
    scalePair κ t μ ν μ' ν' =
      mixInt (fun z w => autoCorr κ (t⁻¹ • (z - w)) / t - c₀) μ ν μ' ν' := by
  rw [mixInt_sub (g₁ := fun z w => autoCorr κ (t⁻¹ • (z - w)) / t) (g₂ := fun _ _ => c₀)]
  · rw [mixInt_const, hmass, sub_self, zero_mul, mul_zero, sub_zero]
    rfl
  · rintro α β (rfl | rfl) (rfl | rfl) <;> exact integrable_autoCorr_div hκ t _ _
  · rintro α β (rfl | rfl) (rfl | rfl) <;> exact integrable_const _

/-- The case `c₀ = 1/t`: `scalePair κ t μ ν μ' ν' = ∫∫ (C(t⁻¹(z - w)) - 1)/t (μ - ν)(μ' - ν')`. -/
theorem scalePair_eq_mixInt_sub_one (hκ : IsLFPPKernel κ) (t : ℝ) (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (hmass : μ.real univ = ν.real univ) :
    scalePair κ t μ ν μ' ν' =
      mixInt (fun z w => autoCorr κ (t⁻¹ • (z - w)) / t - 1 / t) μ ν μ' ν' :=
  scalePair_eq_mixInt_sub_const hκ t (1 / t) μ ν μ' ν' hmass

/-- A.e. bound on the coordinates of a product measure. -/
theorem FieldAux.ae_prod_norm_le {α β : Measure (Rd d)} [SFinite α] [SFinite β] {D : ℝ}
    (hα : ∀ᵐ z ∂α, ‖z‖ ≤ D) (hβ : ∀ᵐ z ∂β, ‖z‖ ≤ D) :
    ∀ᵐ p ∂(α.prod β), ‖p.1 - p.2‖ ≤ 2 * D := by
  have h1 : ∀ᵐ p ∂(α.prod β), ‖p.1‖ ≤ D := Measure.quasiMeasurePreserving_fst.ae hα
  have h2 : ∀ᵐ p ∂(α.prod β), ‖p.2‖ ≤ D := Measure.quasiMeasurePreserving_snd.ae hβ
  filter_upwards [h1, h2] with p hp1 hp2
  calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
    _ ≤ 2 * D := by linarith

/-- **Pairability for unbounded bands** `S ⊆ [a, ∞)`, `a > 0`, for finite measures of equal
mass with bounded supports.  (Equal masses are necessary: for `μ = δ₀`, `ν = 0` and `S = (1, ∞)`,
`∫_S scalePair = ∫_1^∞ dt/t = ∞`.) -/
theorem isPairable_of_subset_Ici (hκ : IsLFPPKernel κ) {S : Set ℝ} (hS : MeasurableSet S)
    {a : ℝ} (ha : 0 < a) (hSa : S ⊆ Ici a) (μ ν : Measure (Rd d)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hmass : μ.real univ = ν.real univ) {D : ℝ} (hμD : ∀ᵐ z ∂μ, ‖z‖ ≤ D)
    (hνD : ∀ᵐ z ∂ν, ‖z‖ ≤ D) : IsPairable κ S μ ν := by
  obtain ⟨L, hL0, hL⟩ := exists_one_sub_autoCorr_le hκ
  have hS0 : S ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le ha (hSa ht)
  set M := (μ.real univ + ν.real univ) * (μ.real univ + ν.real univ) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine isPairable_of_le hκ hS hS0 μ ν (g := fun t => L * (2 * D) ^ 2 * M * t ^ (-3 : ℝ)) ?_
    fun t ht => ?_
  · have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) ha).const_mul
      (L * (2 * D) ^ 2 * M)
    exact ((integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).2 h).mono_set hSa
  · have ht0 : 0 < t := hS0 ht
    have h3 : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    have hpt : ∀ p : Rd d × Rd d, ‖p.1 - p.2‖ ≤ 2 * D →
        |autoCorr κ (t⁻¹ • (p.1 - p.2)) / t - 1 / t| ≤ L * (2 * D) ^ 2 * (t ^ 3)⁻¹ := by
      intro p hp
      have h1 := hL (t⁻¹ • (p.1 - p.2))
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le)] at h1
      have e : autoCorr κ (t⁻¹ • (p.1 - p.2)) / t - 1 / t =
          -((1 - autoCorr κ (t⁻¹ • (p.1 - p.2))) / t) := by ring
      rw [e, abs_neg, abs_of_nonneg (div_nonneg h1.1 ht0.le)]
      have hD : 0 ≤ 2 * D := (norm_nonneg _).trans hp
      have hsq : ‖p.1 - p.2‖ ^ 2 ≤ (2 * D) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
      calc (1 - autoCorr κ (t⁻¹ • (p.1 - p.2))) / t ≤ L * (t⁻¹ * ‖p.1 - p.2‖) ^ 2 / t :=
            div_le_div_of_nonneg_right h1.2 ht0.le
        _ = L * ‖p.1 - p.2‖ ^ 2 * (t ^ 3)⁻¹ := by field_simp
        _ ≤ L * (2 * D) ^ 2 * (t ^ 3)⁻¹ := by gcongr
    have hb := abs_mixInt_le (g := fun z w => autoCorr κ (t⁻¹ • (z - w)) / t - 1 / t)
      (M := L * (2 * D) ^ 2 * (t ^ 3)⁻¹) μ ν μ ν
      ((FieldAux.ae_prod_norm_le hμD hμD).mono fun p hp => hpt p hp)
      ((FieldAux.ae_prod_norm_le hμD hνD).mono fun p hp => hpt p hp)
      ((FieldAux.ae_prod_norm_le hνD hμD).mono fun p hp => hpt p hp)
      ((FieldAux.ae_prod_norm_le hνD hνD).mono fun p hp => hpt p hp)
    rw [scalePair_eq_mixInt_sub_one hκ t μ ν μ ν hmass, h3]
    calc mixInt (fun z w => autoCorr κ (t⁻¹ • (z - w)) / t - 1 / t) μ ν μ ν
        ≤ |mixInt (fun z w => autoCorr κ (t⁻¹ • (z - w)) / t - 1 / t) μ ν μ ν| := le_abs_self _
      _ ≤ L * (2 * D) ^ 2 * (t ^ 3)⁻¹ * M := hb
      _ = L * (2 * D) ^ 2 * M * (t ^ 3)⁻¹ := by ring

end Pairability

end HigherDimLFPP
