import HigherDimLFPP.Field.VarBounds
import HigherDimLFPP.Field.BandFacts
import HigherDimLFPP.Field.SupBounds
import HigherDimLFPP.Upper.ChainRecords
import QuantumZipper.Proofs.Section5.Prop16DomCoupleFubini

/-!
# The law of the record variables (interface (I1) of HA3 §7)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1), (3.1) and §4.3 (the record variables
`Y = δ^{-1/2} ⟨H_{ε,1}, ν_{[x,y]} - ν_Q⟩`); planning audit HA3
(`planning/audits/HA3-section-4.md`), §7 interface (I1) ("for any finite family of segment
combinations, `(⟨H_{ε,1}, η_i⟩)_i` is centered Gaussian with covariance `Γ_{ε,1}(η_i, η_j)`") and
Details D6 (iii), D7 (which use (I1) for bilinearity and for the Chernoff bound).

The field is the frozen white-noise model (ruling H10): `W` is a white noise on `WN d` and `H` is
a continuous version of `z ↦ W(k_{a,b,z})`.  For a finite measure `μ` put
`pvec κ a b μ = ∫ k_{a,b,z} dμ(z) ∈ L²(ℝ × ℝ^d)` (Bochner integral).  Then:

* `integral_ae_eq_pvec` (**stochastic Fubini**): `∫ H dμ = W(pvec μ)` almost surely
  (QuantumZipper's `gaussFubini_core`, an `L²` computation);
* `inner_pvec_sub` (**Itô isometry for measures**): for finite measures,
  `⟪pvec μ - pvec ν, pvec μ' - pvec ν'⟫ = scaleCov κ (a, b) μ ν μ' ν'`, the covariance (3.1) of
  P-F2, so that Lemma 3.1 (`transport_cov_bound`) applies to the record variables;
* `cfgVec`, `cfgVal_ae_eq`, `inner_cfgVec`: the record variable `cfgVal δ H c` of a configuration
  `c = (P₁, P₂)` is `W(cfgVec c)` almost surely, with
  `⟪cfgVec c, cfgVec c'⟫ = δ⁻¹ scaleCov κ (a, b) ν_{P₁} ν_{P₂} ν_{P₁'} ν_{P₂'}`;
* sums along chains (`sum_cfgVal_ae_eq`, `variance_sum_cfgVal`), expected maxima
  (`integral_iSup_cfgVal`, `integrable_iSup_cfgVal`) and the **Chernoff bound for finite Gaussian
  maxima of white-noise vectors** (`whiteNoise_measure_lt_iSup_le`, the white-noise form of the
  2D `LQGDimension.ChainUnion.measure_lt_iSup_le`).

2D source: `LQGDimension/LFPP/SegCombLaw.lean` (finite segment combinations, by Riemann sums) and
`LQGDimension/LFPP/ChainUnionAux.lean` (`measure_lt_iSup_le`).  Here the stochastic Fubini
theorem replaces the Riemann sums, because the d-dimensional field is given by the white noise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

variable {d : ℕ} {κ : Rd d → ℝ}

/-! ## Point vectors: continuity and boundedness -/

section PointVectors

/-- The point vectors are Lipschitz in the point: `‖k_z - k_w‖ ≤ (√L / a) ‖z - w‖`. -/
theorem exists_norm_bandVec_sub_le (hκ : IsLFPPKernel κ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, 0 < a → ∀ (b : ℝ) (z w : Rd d),
      ‖bandVec κ a b z - bandVec κ a b w‖ ≤ L / a * ‖z - w‖ := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_bandVec_sub_sq_le hκ
  refine ⟨Real.sqrt L, Real.sqrt_nonneg _, fun a ha b z w => ?_⟩
  have h := hL a ha b z w
  have hrhs : L * ‖z - w‖ ^ 2 / a ^ 2 = (Real.sqrt L / a * ‖z - w‖) ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt hL0]
    ring
  rw [hrhs] at h
  have hR : 0 ≤ Real.sqrt L / a * ‖z - w‖ := by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 h

/-- The point vectors depend continuously on the point. -/
theorem continuous_bandVec (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Continuous (bandVec κ a b : Rd d → WN d) := by
  obtain ⟨L, hL0, hL⟩ := exists_norm_bandVec_sub_le (d := d) hκ
  have hlip : LipschitzWith (Real.toNNReal (L / a)) (bandVec κ a b : Rd d → WN d) := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    exact hL a ha b z w
  exact hlip.continuous

theorem norm_bandVec_le (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : Rd d) :
    ‖bandVec κ a b z‖ ≤ Real.sqrt (Real.log (b / a)) := by
  rw [← norm_bandVec_sq hκ ha hab z, Real.sqrt_sq (norm_nonneg _)]

theorem integrable_bandVec (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] : Integrable (bandVec κ a b) μ :=
  Integrable.of_bound (continuous_bandVec hκ ha b).aestronglyMeasurable _
    (Eventually.of_forall fun z => norm_bandVec_le hκ ha hab z)

end PointVectors

/-! ## Measure vectors and the stochastic Fubini theorem -/

section MeasureVectors

/-- The white-noise vector `∫ k_{a,b,z} dμ(z) ∈ L²(ℝ × ℝ^d)` of the pairing `⟨H_{a,b}, μ⟩`. -/
def pvec (κ : Rd d → ℝ) (a b : ℝ) (μ : Measure (Rd d)) : WN d := ∫ z, bandVec κ a b z ∂μ

theorem inner_pvec_right (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] (x : WN d) :
    ⟪x, pvec κ a b μ⟫ = ∫ z, ⟪x, bandVec κ a b z⟫ ∂μ :=
  (integral_inner (integrable_bandVec hκ ha hab μ) x).symm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

/-- **Stochastic Fubini** (HA2 F6, interface (I1)): for a continuous version `H` of the band field
`H_{a,b}` and a finite measure `μ`, `∫ H dμ = W(pvec μ)` almost surely. -/
theorem integral_ae_eq_pvec (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] :
    (fun ω => ∫ z, H z ω ∂μ) =ᵐ[P] W (pvec κ a b μ) := by
  have := hW.isProbabilityMeasure
  have hc := continuous_bandVec hκ ha b
  have hGm : Measurable (Function.uncurry fun (ω : Ω) (z : Rd d) => H z ω) :=
    hH.measurable_uncurry.comp measurable_swap
  have h := QuantumZipper.Prop16Asm.gaussFubini_core (W := W) hW.hasLaw μ (bandVec κ a b)
    (M := Real.sqrt (Real.log (b / a))) (fun z => norm_bandVec_le hκ ha hab z)
    ((hc.comp continuous_fst).inner (hc.comp continuous_snd)).measurable
    (fun x => (hc.inner continuous_const).measurable) (fun ω z => H z ω) hGm
    (fun z => hH.ae_eq z) hW.measurable (pvec κ a b μ) (fun x => by
      rw [real_inner_comm, inner_pvec_right hκ ha hab μ x]
      exact integral_congr_ae (Eventually.of_forall fun z => real_inner_comm _ _))
  filter_upwards [h] with ω hω
  exact hω

/-- The scale integrand `(p, t) ↦ C(t⁻¹(p.1 - p.2))/t` is integrable on
`(α ⊗ β) ⊗ (dt restricted to (a, b))`, `a > 0`. -/
theorem integrable_autoCorr_prod_Ioo (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (α β : Measure (Rd d)) [IsFiniteMeasure α] [IsFiniteMeasure β] :
    Integrable (fun q : (Rd d × Rd d) × ℝ => autoCorr κ (q.2⁻¹ • (q.1.1 - q.1.2)) / q.2)
      ((α.prod β).prod (volume.restrict (Ioo a b))) := by
  have hm : Measurable fun q : (Rd d × Rd d) × ℝ =>
      autoCorr κ (q.2⁻¹ • (q.1.1 - q.1.2)) / q.2 :=
    ((continuous_autoCorr hκ).measurable.comp
      (measurable_snd.inv.smul (measurable_fst.fst.sub measurable_fst.snd))).div measurable_snd
  have hae : ∀ᵐ q ∂((α.prod β).prod (volume.restrict (Ioo a b))), q.2 ∈ Ioo a b :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioo)
  refine Integrable.of_bound hm.aestronglyMeasurable a⁻¹ ?_
  filter_upwards [hae] with q hq
  have hq0 : 0 < q.2 := lt_trans ha hq.1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
  calc |autoCorr κ (q.2⁻¹ • (q.1.1 - q.1.2))| ≤ 1 := abs_autoCorr_le_one hκ _
    _ = a⁻¹ * a := (inv_mul_cancel₀ ha.ne').symm
    _ ≤ a⁻¹ * q.2 := mul_le_mul_of_nonneg_left hq.1.le (inv_nonneg.2 ha.le)

/-- `⟪pvec μ, pvec μ'⟫ = ∫_{(a,b)} ∫∫ C(t⁻¹(z - w))/t dμ(z) dμ'(w) dt`. -/
theorem inner_pvec (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (μ μ' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure μ'] :
    ⟪pvec κ a b μ, pvec κ a b μ'⟫ =
      ∫ t in Ioo a b, ∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(μ.prod μ') := by
  have hc := continuous_bandVec hκ ha b
  have hpt : Integrable (fun p : Rd d × Rd d => ⟪bandVec κ a b p.1, bandVec κ a b p.2⟫)
      (μ.prod μ') := by
    refine Integrable.of_bound ((hc.comp continuous_fst).inner
      (hc.comp continuous_snd)).aestronglyMeasurable (Real.log (b / a)) ?_
    refine Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h1 := norm_bandVec_le hκ ha hab p.1
    have h2 := norm_bandVec_le hκ ha hab p.2
    have hs : Real.sqrt (Real.log (b / a)) * Real.sqrt (Real.log (b / a)) = Real.log (b / a) :=
      Real.mul_self_sqrt (Real.log_nonneg ((one_le_div ha).2 hab))
    calc ‖bandVec κ a b p.1‖ * ‖bandVec κ a b p.2‖
        ≤ Real.sqrt (Real.log (b / a)) * Real.sqrt (Real.log (b / a)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.log (b / a) := hs
  have step1 : ⟪pvec κ a b μ, pvec κ a b μ'⟫ =
      ∫ p, ⟪bandVec κ a b p.1, bandVec κ a b p.2⟫ ∂(μ.prod μ') := by
    rw [integral_prod _ hpt, real_inner_comm, inner_pvec_right hκ ha hab μ]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show ⟪pvec κ a b μ', bandVec κ a b z⟫ = ∫ y, ⟪bandVec κ a b z, bandVec κ a b y⟫ ∂μ'
    rw [real_inner_comm, inner_pvec_right hκ ha hab μ']
  rw [step1]
  have step2 : ∀ p : Rd d × Rd d, ⟪bandVec κ a b p.1, bandVec κ a b p.2⟫ =
      ∫ t in Ioo a b, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t := by
    intro p
    rw [inner_bandVec hκ ha ha, max_self, min_self]
  simp_rw [step2]
  exact integral_integral_swap (f := fun (p : Rd d × Rd d) (t : ℝ) =>
    autoCorr κ (t⁻¹ • (p.1 - p.2)) / t) (integrable_autoCorr_prod_Ioo hκ ha b μ μ')

theorem integrableOn_autoCorr_prod (hκ : IsLFPPKernel κ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (α β : Measure (Rd d)) [IsFiniteMeasure α] [IsFiniteMeasure β] :
    IntegrableOn (fun t => ∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(α.prod β)) (Ioo a b) :=
  (integrable_autoCorr_prod_Ioo hκ ha b α β).integral_prod_right

/-- **Itô isometry for measures**: for finite measures,
`⟪pvec μ - pvec ν, pvec μ' - pvec ν'⟫ = scaleCov κ (a, b) μ ν μ' ν'` (the covariance (3.1)). -/
theorem inner_pvec_sub (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure μ']
    [IsFiniteMeasure ν'] :
    ⟪pvec κ a b μ - pvec κ a b ν, pvec κ a b μ' - pvec κ a b ν'⟫ =
      scaleCov κ (Ioo a b) μ ν μ' ν' := by
  have hS0 : Ioo a b ⊆ Ioi 0 := fun t ht => lt_trans ha ht.1
  rw [scaleCov_eq_integral hκ measurableSet_Ioo hS0
    (isPairable_of_subset_Icc hκ measurableSet_Ioo ha Ioo_subset_Icc_self μ ν)
    (isPairable_of_subset_Icc hκ measurableSet_Ioo ha Ioo_subset_Icc_self μ' ν')]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_pvec hκ ha hab,
    inner_pvec hκ ha hab, inner_pvec hκ ha hab, inner_pvec hκ ha hab]
  have i1 := integrableOn_autoCorr_prod hκ ha b μ μ'
  have i2 := integrableOn_autoCorr_prod hκ ha b μ ν'
  have i3 := integrableOn_autoCorr_prod hκ ha b ν μ'
  have i4 := integrableOn_autoCorr_prod hκ ha b ν ν'
  have e : (∫ t in Ioo a b, scalePair κ t μ ν μ' ν') = ∫ t in Ioo a b,
      (((∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(μ.prod μ')) -
          ∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(μ.prod ν')) -
        ((∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(ν.prod μ')) -
          ∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(ν.prod ν'))) :=
    integral_congr_ae (Eventually.of_forall fun t => by
      simp only [scalePair, mixInt]
      ring)
  have h12 : IntegrableOn (fun t => (∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(μ.prod μ')) -
      ∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(μ.prod ν')) (Ioo a b) := i1.sub i2
  have h34 : IntegrableOn (fun t => (∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(ν.prod μ')) -
      ∫ p, autoCorr κ (t⁻¹ • (p.1 - p.2)) / t ∂(ν.prod ν')) (Ioo a b) := i3.sub i4
  rw [e, integral_sub h12 h34, integral_sub i1 i2, integral_sub i3 i4]

end MeasureVectors

/-! ## Polygon measures are finite -/

section PolyFinite

theorem isFiniteMeasure_polyMeasure (z : List (Rd d)) : IsFiniteMeasure (polyMeasure z) := by
  unfold polyMeasure
  refine List.sum_induction (fun μ : Measure (Rd d) => IsFiniteMeasure μ) (fun μ ν hμ hν => ?_)
    (by infer_instance) (fun μ hμ => ?_)
  · exact @isFiniteMeasureAdd _ _ μ ν hμ hν
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hμ
    constructor
    rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_lt_top

attribute [local instance] isFiniteMeasure_polyMeasure

end PolyFinite

/-! ## Record variables as white-noise values -/

section RecordVectors

attribute [local instance] isFiniteMeasure_polyMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

/-- The white-noise vector of the record variable of a configuration `c = (P₁, P₂)`:
`δ^{-1/2} (pvec ν_{P₁} - pvec ν_{P₂})`. -/
def cfgVec (κ : Rd d → ℝ) (a b δ : ℝ) (c : Config d) : WN d :=
  δ ^ (-(1 / 2 : ℝ)) • (pvec κ a b (polyMeasure c.1) - pvec κ a b (polyMeasure c.2))

/-- The record variable `cfgVal δ H c` is `W(cfgVec c)` almost surely. -/
theorem cfgVal_ae_eq (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) (δ : ℝ) (c : Config d) :
    (fun ω => cfgVal δ (fun z => H z ω) c) =ᵐ[P] W (cfgVec κ a b δ c) := by
  have h1 := integral_ae_eq_pvec hκ hW ha hab hH (polyMeasure c.1)
  have h2 := integral_ae_eq_pvec hκ hW ha hab hH (polyMeasure c.2)
  have h3 := hW.smul_ae (δ ^ (-(1 / 2 : ℝ)))
    (pvec κ a b (polyMeasure c.1) - pvec κ a b (polyMeasure c.2))
  have h4 := hW.sub_ae (pvec κ a b (polyMeasure c.1)) (pvec κ a b (polyMeasure c.2))
  filter_upwards [h1, h2, h3, h4] with ω e1 e2 e3 e4
  rw [cfgVal, cfgVec, e3, e4, e1, e2]

theorem rpow_neg_half_sq' {δ : ℝ} (hδ : 0 < δ) : δ ^ (-(1 / 2 : ℝ)) * δ ^ (-(1 / 2 : ℝ)) = δ⁻¹ := by
  rw [← Real.rpow_add hδ]
  norm_num
  exact Real.rpow_neg_one δ

/-- `⟪cfgVec c, cfgVec c'⟫ = δ⁻¹ scaleCov κ (a, b) ν_{P₁} ν_{P₂} ν_{P₁'} ν_{P₂'}`. -/
theorem inner_cfgVec (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {δ : ℝ}
    (hδ : 0 < δ) (c c' : Config d) :
    ⟪cfgVec κ a b δ c, cfgVec κ a b δ c'⟫ =
      δ⁻¹ * scaleCov κ (Ioo a b) (polyMeasure c.1) (polyMeasure c.2) (polyMeasure c'.1)
        (polyMeasure c'.2) := by
  rw [cfgVec, cfgVec, real_inner_smul_left, real_inner_smul_right,
    inner_pvec_sub hκ ha hab, ← mul_assoc, rpow_neg_half_sq' hδ]

/-- Sums of record variables along a tuple of configurations are white-noise values. -/
theorem sum_cfgVal_ae_eq (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) (δ : ℝ) {ι : Type*}
    [Fintype ι] (c : ι → Config d) :
    (fun ω => ∑ i, cfgVal δ (fun z => H z ω) (c i)) =ᵐ[P] W (∑ i, cfgVec κ a b δ (c i)) := by
  have hall : ∀ᵐ ω ∂P, ∀ i, cfgVal δ (fun z => H z ω) (c i) = W (cfgVec κ a b δ (c i)) ω :=
    ae_all_iff.2 fun i => cfgVal_ae_eq hκ hW ha hab hH δ (c i)
  have hsum := hW.sum_smul_ae (fun i => cfgVec κ a b δ (c i)) (fun _ => 1)
  simp only [one_smul, one_mul] at hsum
  filter_upwards [hall, hsum] with ω h1 h2
  rw [h2]
  exact Finset.sum_congr rfl fun i _ => h1 i

/-- The variance of a sum of record variables is the squared norm of its white-noise vector. -/
theorem variance_sum_cfgVal (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) (δ : ℝ)
    {ι : Type*} [Fintype ι] (c : ι → Config d) :
    Var[fun ω => ∑ i, cfgVal δ (fun z => H z ω) (c i); P] = ‖∑ i, cfgVec κ a b δ (c i)‖ ^ 2 := by
  rw [variance_congr (sum_cfgVal_ae_eq hκ hW ha hab hH δ c), hW.variance_eq]

/-- Expected maxima of record variables over finite families. -/
theorem integral_iSup_cfgVal (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) (δ : ℝ)
    (F : Finset (Config d)) :
    ∫ ω, (⨆ c : F, cfgVal δ (fun z => H z ω) c) ∂P =
      LQGDimension.gaussianExpectedMax F
        (fun c c' => ⟪cfgVec κ a b δ c, cfgVec κ a b δ c'⟫) (fun _ => 0) := by
  rw [← hW.integral_iSup_eq_gaussianExpectedMax F (cfgVec κ a b δ) (fun _ => 0)]
  have hall : ∀ᵐ ω ∂P, ∀ c : F, cfgVal δ (fun z => H z ω) c = W (cfgVec κ a b δ c) ω :=
    ae_all_iff.2 fun c => cfgVal_ae_eq hκ hW ha hab hH δ c
  refine integral_congr_ae ?_
  filter_upwards [hall] with ω hω
  simp only [add_zero, hω]

/-- Maxima of record variables over finite nonempty families are integrable. -/
theorem integrable_iSup_cfgVal (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {H : Rd d → Ω → ℝ} (hH : IsBandVersion P W κ a b H) (δ : ℝ)
    {F : Finset (Config d)} (hF : F.Nonempty) :
    Integrable (fun ω => ⨆ c : F, cfgVal δ (fun z => H z ω) c) P := by
  have := hW.isProbabilityMeasure
  have : Nonempty F := hF.to_subtype
  refine SupB.integrable_iSup_of_finite fun c => ?_
  refine (hW.memLp (cfgVec κ a b δ c) 1 ENNReal.one_ne_top).integrable le_rfl |>.congr ?_
  exact (cfgVal_ae_eq hκ hW ha hab hH δ c).symm

end RecordVectors

/-! ## The Chernoff bound for finite Gaussian maxima of white-noise vectors -/

section Chernoff

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

/-- **Chernoff bound for a finite Gaussian maximum** (white-noise form of the 2D
`LQGDimension.ChainUnion.measure_lt_iSup_le`): if `‖v i‖² ≤ V` on a finite nonempty `F`, then
`P(β < max_F (W(v i) + b i)) ≤ exp(-tβ + t E max + (π²/8) t² V)` for `t ≥ 0`. -/
theorem whiteNoise_measure_lt_iSup_le (hW : IsWhiteNoise P W) {ι : Type*} {F : Finset ι}
    (hF : F.Nonempty) (v : ι → WN d) (b : ι → ℝ) (V : ℝ) (hV : ∀ i ∈ F, ‖v i‖ ^ 2 ≤ V)
    (β t : ℝ) (ht : 0 ≤ t) :
    P {ω | β < ⨆ i : F, W (v i) ω + b i} ≤
      ENNReal.ofReal (Real.exp (-t * β + t * ∫ ω, (⨆ i : F, W (v i) ω + b i) ∂P +
        Real.pi ^ 2 / 8 * t ^ 2 * V)) := by
  classical
  have := hW.isProbabilityMeasure
  set X : Ω → F → ℝ := fun ω i => W (v i) ω with hX
  have hXG : HasGaussianLaw X P := hW.hasGaussianLaw_fintype (fun i : F => v i)
  obtain ⟨u, hu, hmap⟩ := LQGMetric.Pitt.exists_gram_map_eq hXG
  have hmean : (fun i : F => ∫ ω, X ω i ∂P) = 0 := funext fun i => hW.integral_eq_zero _
  rw [hmean] at hmap
  set w : ι → EuclideanSpace ℝ F := fun i => if h : i ∈ F then u ⟨i, h⟩ else 0 with hwdef
  have hw : ∀ i : F, w i = u i := fun i => by
    simp only [hwdef, i.2, ↓reduceDIte, Subtype.coe_eta]
  have hV0 : 0 ≤ V := by
    obtain ⟨i, hi⟩ := hF
    exact (sq_nonneg _).trans (hV i hi)
  have hnorm : ∀ i ∈ F, ‖w i‖ ≤ Real.sqrt V := by
    intro i hi
    refine Real.le_sqrt_of_sq_le ?_
    rw [hw ⟨i, hi⟩, ← real_inner_self_eq_norm_sq, hu, hX, hW.cov_eq, real_inner_self_eq_norm_sq]
    exact hV i hi
  have hL : Measurable fun x : EuclideanSpace ℝ F => (0 : F → ℝ) + LQGMetric.Pitt.gramCLM u x :=
    (continuous_const.add (LQGMetric.Pitt.gramCLM u).continuous).measurable
  have hg : Measurable fun y : F → ℝ => ⨆ i : F, y i + b i :=
    Measurable.iSup fun i => (measurable_pi_apply i).add_const _
  have hgw : ∀ x : EuclideanSpace ℝ F,
      (fun y : F → ℝ => ⨆ i : F, y i + b i) ((0 : F → ℝ) + LQGMetric.Pitt.gramCLM u x) =
        ⨆ i : F, ⟪w i, x⟫ + b i := by
    intro x
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, LQGMetric.Pitt.gramCLM_apply, hw]
  have hint : ∫ ω, (⨆ i : F, W (v i) ω + b i) ∂P = LQGDimension.vecExpectedMax F w b := by
    have e1 : ∫ ω, (⨆ i : F, W (v i) ω + b i) ∂P =
        ∫ y, (⨆ i : F, y i + b i) ∂(P.map X) :=
      (integral_map hXG.aemeasurable hg.aestronglyMeasurable).symm
    rw [e1, hmap, integral_map hL.aemeasurable hg.aestronglyMeasurable]
    unfold LQGDimension.vecExpectedMax
    exact integral_congr_ae (Eventually.of_forall hgw)
  have hset : P {ω | β < ⨆ i : F, W (v i) ω + b i} =
      stdGaussian (EuclideanSpace ℝ F) {x | β < ⨆ i : F, ⟪w i, x⟫ + b i} := by
    have hU : MeasurableSet {y : F → ℝ | β < ⨆ i : F, y i + b i} :=
      measurableSet_lt measurable_const hg
    have e1 : {ω | β < ⨆ i : F, W (v i) ω + b i} = X ⁻¹' {y : F → ℝ | β < ⨆ i : F, y i + b i} :=
      rfl
    rw [e1, ← Measure.map_apply_of_aemeasurable hXG.aemeasurable hU, hmap,
      Measure.map_apply hL hU]
    congr 1
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hgw]
  rw [hset, hint]
  set EM := LQGDimension.vecExpectedMax F w b with hEM
  have hch := measure_ge_le_exp_mul_mgf (μ := stdGaussian (EuclideanSpace ℝ F))
    (X := fun x => (⨆ i : F, ⟪w i, x⟫ + b i) - EM) (β - EM) ht
    (LQGDimension.MaxConc.integrable_exp_max F w b hnorm t)
  have hmgf := LQGDimension.MaxConc.integral_exp_max_le F w b hnorm t
  rw [mgf] at hch
  calc stdGaussian (EuclideanSpace ℝ F) {x | β < ⨆ i : F, ⟪w i, x⟫ + b i}
      ≤ stdGaussian (EuclideanSpace ℝ F) {x | β - EM ≤ (⨆ i : F, ⟪w i, x⟫ + b i) - EM} := by
        refine measure_mono fun x hx => ?_
        simp only [mem_ofPred_eq] at hx ⊢
        linarith
    _ = ENNReal.ofReal ((stdGaussian (EuclideanSpace ℝ F)).real
          {x | β - EM ≤ (⨆ i : F, ⟪w i, x⟫ + b i) - EM}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (Real.exp (-t * (β - EM)) *
          Real.exp (Real.pi ^ 2 / 8 * t ^ 2 * Real.sqrt V ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal (hch.trans ?_)
        exact mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = ENNReal.ofReal (Real.exp (-t * β + t * EM + Real.pi ^ 2 / 8 * t ^ 2 * V)) := by
        rw [← Real.exp_add, Real.sq_sqrt hV0]
        congr 2
        ring

end Chernoff

end HigherDimLFPP.Upper
