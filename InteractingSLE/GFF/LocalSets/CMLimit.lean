import InteractingSLE.GFF.LocalSets.Basic

/-!
# Cameron–Martin for limits of covariance shifts

For a centred Gaussian process `X : I → Ω → ℝ` and finitely supported `σ : I →₀ ℝ`, QuantumZipper's
`CameronMartin.map_tiltMeasure_path` identifies the law of `X + K(·, σ)` with the law of `X` under
the tilt `exp(Xσ − K(σ, σ)/2) · P`. This file passes to limits: if `σₙ` is Cauchy for the
covariance norm (`K(σₙ − σₘ, σₙ − σₘ) → 0`, `K(σₙ, σₙ) → v`) and the shifts `K(j, σₙ)` converge
pointwise to `c j`, then the law of `X + c` is again a tilt of the law of `X` (the tilt densities
converge in `L²`); in particular the two laws are mutually absolutely continuous.

This is the Cameron–Martin theorem for shifts in the closure of the finite covariance shifts
(Bogachev, *Gaussian Measures*, Thm 2.4.5), used for Proposition 3.4 (ii) of the specification,
where the shift `χ (F₁ − F₂)` has finite Dirichlet energy but is not compactly supported.

## Main results

* `integral_tiltDensity_mul` : `E[D_σ D_τ] = exp((K(σ,σ) + K(τ,τ))/2 − K(σ−τ, σ−τ)/2)`;
* `exists_tendsto_integral_mul_tiltDensity` : the tilt densities converge weakly in `L²`;
* `map_add_eq_withDensity_of_tendsto` : `law(X + c) = law(X under D · P)`;
* `map_add_absolutelyContinuous_of_tendsto`, `map_absolutelyContinuous_add_of_tendsto` : the two
  absolute continuities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open QuantumZipper.CameronMartin
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace GFF

section CMLimit

variable {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : I → Ω → ℝ}

lemma comb_add (hX : IsGaussianProcess X P) (σ τ : I →₀ ℝ) (ω : Ω) :
    comb X (σ + τ) ω = comb X σ ω + comb X τ ω := by
  classical
  rw [comb_eq_sum_subset hX (σ + τ) Finsupp.support_add,
    comb_eq_sum_subset hX σ Finset.subset_union_left,
    comb_eq_sum_subset hX τ Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.add_apply, add_mul]

lemma comb_neg (hX : IsGaussianProcess X P) (σ : I →₀ ℝ) (ω : Ω) :
    comb X (-σ) ω = -comb X σ ω := by
  rw [comb_eq_sum_subset hX (-σ) (Finsupp.support_neg σ).subset, comb, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.neg_apply, neg_mul]

lemma comb_sub (hX : IsGaussianProcess X P) (σ τ : I →₀ ℝ) (ω : Ω) :
    comb X (σ - τ) ω = comb X σ ω - comb X τ ω := by
  rw [sub_eq_add_neg, comb_add hX, comb_neg hX, ← sub_eq_add_neg]

lemma hasGaussianLaw_comb (hX : IsGaussianProcess X P) (σ : I →₀ ℝ) :
    HasGaussianLaw (comb X σ) P :=
  hasGaussianLaw_finsetComb hX σ.support σ

lemma memLp_comb (hX : IsGaussianProcess X P) (σ : I →₀ ℝ) : MemLp (comb X σ) 2 P :=
  memLp_two_finsetComb hX σ.support σ

lemma integral_comb (hX : IsGaussianProcess X P) (hcent : ∀ i, P[X i] = 0) (σ : I →₀ ℝ) :
    ∫ ω, comb X σ ω ∂P = 0 :=
  integral_finsetComb hX hcent σ.support σ

/-- Parallelogram identity for the covariance norm. -/
lemma covNorm_add_add_covNorm_sub (hX : IsGaussianProcess X P) (σ τ : I →₀ ℝ) :
    covNorm X P (σ + τ) + covNorm X P (σ - τ) = 2 * covNorm X P σ + 2 * covNorm X P τ := by
  have := hX.isProbabilityMeasure
  rw [← variance_comb hX, ← variance_comb hX, ← variance_comb hX, ← variance_comb hX]
  have e1 : comb X (σ + τ) = comb X σ + comb X τ := funext (comb_add hX σ τ)
  have e2 : comb X (σ - τ) = comb X σ - comb X τ := funext (comb_sub hX σ τ)
  rw [e1, e2, variance_add (memLp_comb hX σ) (memLp_comb hX τ),
    variance_sub (memLp_comb hX σ) (memLp_comb hX τ)]
  ring

lemma covNorm_neg (hX : IsGaussianProcess X P) (σ : I →₀ ℝ) :
    covNorm X P (-σ) = covNorm X P σ := by
  have := hX.isProbabilityMeasure
  rw [← variance_comb hX, ← variance_comb hX]
  have e : comb X (-σ) = -comb X σ := funext (comb_neg hX σ)
  rw [e, variance_neg]

lemma covShift_neg (σ : I →₀ ℝ) (j : I) : covShift X P (-σ) j = -covShift X P σ j := by
  simp only [covShift, Finsupp.support_neg, Finsupp.neg_apply, neg_mul, Finset.sum_neg_distrib]

/-- `E[D_σ D_τ] = exp((K(σ,σ) + K(τ,τ))/2 − K(σ−τ,σ−τ)/2)` for the tilt densities. -/
lemma integral_tiltDensity_mul (hX : IsGaussianProcess X P) (hcent : ∀ i, P[X i] = 0)
    (σ τ : I →₀ ℝ) :
    Integrable (fun ω => tiltDensity X P σ ω * tiltDensity X P τ ω) P ∧
      ∫ ω, tiltDensity X P σ ω * tiltDensity X P τ ω ∂P =
        Real.exp ((covNorm X P σ + covNorm X P τ) / 2 - covNorm X P (σ - τ) / 2) := by
  obtain ⟨hi, he⟩ := gauss_exp hX hcent (hasGaussianLaw_comb hX (σ + τ))
    (integral_comb hX hcent _)
  have e : (fun ω => tiltDensity X P σ ω * tiltDensity X P τ ω) =
      fun ω => Real.exp (comb X (σ + τ) ω) *
        Real.exp (-((covNorm X P σ + covNorm X P τ) / 2)) := by
    funext ω
    rw [tiltDensity, tiltDensity, ← Real.exp_add, ← Real.exp_add, comb_add hX]
    ring_nf
  rw [e]
  refine ⟨hi.mul_const _, ?_⟩
  rw [integral_mul_const, he, variance_comb hX, ← Real.exp_add]
  congr 1
  have := covNorm_add_add_covNorm_sub hX σ τ
  linarith

lemma memLp_tiltDensity (hX : IsGaussianProcess X P) (hmeas : ∀ i, Measurable (X i))
    (hcent : ∀ i, P[X i] = 0) (σ : I →₀ ℝ) : MemLp (tiltDensity X P σ) 2 P := by
  refine (memLp_two_iff_integrable_sq
    (measurable_tiltDensity hX hmeas σ).aestronglyMeasurable).2 ?_
  simpa only [sq] using (integral_tiltDensity_mul hX hcent σ σ).1

/-- `‖f‖²_{L²} = ∫ f²`. -/
lemma norm_toLp_sq {f : Ω → ℝ} (hf : MemLp f 2 P) : ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp [hω, sq]

/-- `∫ g uₙ → ∫ g u` when `uₙ → u` in `L²` and `g ∈ L²`. -/
lemma tendsto_integral_mul_of_tendsto_L2 {u : ℕ → Lp ℝ 2 P} {ul : Lp ℝ 2 P}
    (hu : Tendsto u atTop (𝓝 ul)) {g : Ω → ℝ} (hg : MemLp g 2 P) :
    Tendsto (fun n => ∫ ω, g ω * u n ω ∂P) atTop (𝓝 (∫ ω, g ω * ul ω ∂P)) := by
  have key : ∀ v : Lp ℝ 2 P, ⟪hg.toLp g, v⟫ = ∫ ω, g ω * v ω ∂P := fun v => by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with ω hω
    simp [hω, mul_comm]
  simp only [← key]
  exact tendsto_const_nhds.inner hu

lemma covNorm_zero : covNorm X P 0 = 0 := by simp [covNorm]

variable (hX : IsGaussianProcess X P) (hmeas : ∀ i, Measurable (X i)) (hcent : ∀ i, P[X i] = 0)
  {σ : ℕ → I →₀ ℝ} {v : ℝ}

include hX hmeas hcent in
/-- **The tilt densities converge weakly in `L²`.** If `K(σₙ, σₙ) → v` and
`K(σₙ − σₘ, σₙ − σₘ) → 0`, the densities `D_{σₙ}` form a Cauchy sequence in `L²`; their limit `D`
(chosen measurable) satisfies `∫ g D_{σₙ} → ∫ g D` for every `g ∈ L²`. -/
lemma exists_tendsto_integral_mul_tiltDensity
    (hv : Tendsto (fun n => covNorm X P (σ n)) atTop (𝓝 v))
    (hw : Tendsto (fun p : ℕ × ℕ => covNorm X P (σ p.1 - σ p.2)) atTop (𝓝 0)) :
    ∃ D : Ω → ℝ, Measurable D ∧ MemLp D 2 P ∧ ∀ g : Ω → ℝ, MemLp g 2 P →
      Tendsto (fun n => ∫ ω, g ω * tiltDensity X P (σ n) ω ∂P) atTop
        (𝓝 (∫ ω, g ω * D ω ∂P)) := by
  have := hX.isProbabilityMeasure
  set u : ℕ → Lp ℝ 2 P := fun n => (memLp_tiltDensity hX hmeas hcent (σ n)).toLp _ with hu_def
  have hdist : ∀ n m, dist (u n) (u m) ^ 2 =
      Real.exp (covNorm X P (σ n)) -
        2 * Real.exp ((covNorm X P (σ n) + covNorm X P (σ m)) / 2 - covNorm X P (σ n - σ m) / 2) +
        Real.exp (covNorm X P (σ m)) := by
    intro n m
    rw [dist_eq_norm, hu_def, ← MemLp.toLp_sub, norm_toLp_sq]
    have h1 := integral_tiltDensity_mul hX hcent (σ n) (σ n)
    have h2 := integral_tiltDensity_mul hX hcent (σ n) (σ m)
    have h3 := integral_tiltDensity_mul hX hcent (σ m) (σ m)
    have e : (fun ω => (tiltDensity X P (σ n) - tiltDensity X P (σ m)) ω ^ 2) =
        fun ω => (tiltDensity X P (σ n) ω * tiltDensity X P (σ n) ω -
          2 * (tiltDensity X P (σ n) ω * tiltDensity X P (σ m) ω)) +
          tiltDensity X P (σ m) ω * tiltDensity X P (σ m) ω := by
      funext ω
      simp only [Pi.sub_apply]
      ring
    rw [e, integral_add (f := fun ω => tiltDensity X P (σ n) ω * tiltDensity X P (σ n) ω -
        2 * (tiltDensity X P (σ n) ω * tiltDensity X P (σ m) ω))
        (by exact h1.1.sub (h2.1.const_mul 2)) h3.1,
      integral_sub h1.1 (h2.1.const_mul 2), integral_const_mul, h1.2, h2.2, h3.2]
    simp only [sub_self, covNorm_zero, zero_div, sub_zero, add_self_div_two]
  have hlim : Tendsto (fun p : ℕ × ℕ => dist (u p.1) (u p.2) ^ 2) atTop (𝓝 0) := by
    simp only [hdist]
    have hv1 : Tendsto (fun p : ℕ × ℕ => covNorm X P (σ p.1)) atTop (𝓝 v) := by
      rw [← prod_atTop_atTop_eq]; exact hv.comp tendsto_fst
    have hv2 : Tendsto (fun p : ℕ × ℕ => covNorm X P (σ p.2)) atTop (𝓝 v) := by
      rw [← prod_atTop_atTop_eq]; exact hv.comp tendsto_snd
    have := ((Real.continuous_exp.tendsto v).comp hv1).sub
      (((Real.continuous_exp.tendsto _).comp (((hv1.add hv2).div_const 2).sub
        (hw.div_const 2))).const_mul 2) |>.add ((Real.continuous_exp.tendsto v).comp hv2)
    have e0 : Real.exp v - 2 * Real.exp ((v + v) / 2 - 0 / 2) + Real.exp v = 0 := by
      rw [zero_div, sub_zero, add_self_div_two]
      ring
    rw [e0] at this
    exact this
  have hcau : CauchySeq u := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    simp only [Real.sqrt_zero] at this
    refine this.congr fun p => ?_
    simp [Real.sqrt_sq dist_nonneg]
  obtain ⟨ul, hul⟩ := cauchySeq_tendsto_of_complete hcau
  have hm := (Lp.memLp ul).1
  refine ⟨hm.mk _, hm.stronglyMeasurable_mk.measurable, (Lp.memLp ul).ae_eq hm.ae_eq_mk,
    fun g hg => ?_⟩
  have h := tendsto_integral_mul_of_tendsto_L2 hul hg
  have e1 : ∀ n, ∫ ω, g ω * u n ω ∂P = ∫ ω, g ω * tiltDensity X P (σ n) ω ∂P := fun n =>
    integral_congr_ae (by
      filter_upwards [(memLp_tiltDensity hX hmeas hcent (σ n)).coeFn_toLp] with ω hω
      rw [hω])
  have e2 : ∫ ω, g ω * ul ω ∂P = ∫ ω, g ω * hm.mk _ ω ∂P :=
    integral_congr_ae (by filter_upwards [hm.ae_eq_mk] with ω hω; rw [hω])
  simp only [e1, e2] at h
  exact h

include hX hmeas hcent in
/-- **Cameron–Martin for a limit of covariance shifts.** If `K(σₙ, σₙ) → v`,
`K(σₙ − σₘ, σₙ − σₘ) → 0` and `K(j, σₙ) → c j` for every `j`, then the law of `X + c` is the law of
`X` under `D · P` for some integrable `D ≥ 0` (the `L²` limit of the tilt densities). -/
theorem map_add_eq_withDensity_of_tendsto
    (hv : Tendsto (fun n => covNorm X P (σ n)) atTop (𝓝 v))
    (hw : Tendsto (fun p : ℕ × ℕ => covNorm X P (σ p.1 - σ p.2)) atTop (𝓝 0)) {c : I → ℝ}
    (hc : ∀ j, Tendsto (fun n => covShift X P (σ n) j) atTop (𝓝 (c j))) :
    ∃ D : Ω → ℝ, Measurable D ∧ Integrable D P ∧ 0 ≤ᵐ[P] D ∧
      P.map (fun ω j => X j ω + c j) =
        (P.withDensity fun ω => ENNReal.ofReal (D ω)).map (fun ω j => X j ω) := by
  have := hX.isProbabilityMeasure
  obtain ⟨D, hDm, hD2, hlim⟩ := exists_tendsto_integral_mul_tiltDensity hX hmeas hcent hv hw
  have hD1 : Integrable D P := hD2.integrable one_le_two
  have hDnn : 0 ≤ᵐ[P] D := by
    refine ae_nonneg_of_forall_setIntegral_nonneg hD1 fun s hs _ => ?_
    have h := hlim (s.indicator fun _ => (1 : ℝ))
      (memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top P s)))
    have e : ∀ f : Ω → ℝ, ∫ ω, s.indicator (fun _ => (1 : ℝ)) ω * f ω ∂P = ∫ ω in s, f ω ∂P :=
      fun f => by
        rw [← integral_indicator hs]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        by_cases hω : ω ∈ s <;> simp [hω]
    simp only [e] at h
    exact ge_of_tendsto' h fun n => setIntegral_nonneg hs fun ω _ => (Real.exp_pos _).le
  set Q := P.withDensity fun ω => ENNReal.ofReal (D ω) with hQdef
  have hQ : ∀ g : Ω → ℝ, ∫ ω, g ω ∂Q = ∫ ω, D ω * g ω ∂P := fun g => by
    rw [hQdef, integral_withDensity_eq_integral_toReal_smul
      (f := fun ω => ENNReal.ofReal (D ω)) (by exact ENNReal.measurable_ofReal.comp hDm)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [hDnn] with ω hω
    simp [ENNReal.toReal_ofReal hω, smul_eq_mul]
  have hQfin : IsFiniteMeasure Q := isFiniteMeasure_withDensity_ofReal hD1.2
  have hXm : Measurable fun ω j => X j ω := measurable_pi_iff.mpr hmeas
  have hXc : Measurable fun ω j => X j ω + c j :=
    measurable_pi_iff.mpr fun j => (hmeas j).add_const _
  have hfd : ∀ J : Finset I, P.map (fun ω => J.restrict (fun j => X j ω + c j)) =
      Q.map (fun ω => J.restrict (fun j => X j ω)) := by
    intro J
    have hV : Measurable fun ω => J.restrict (fun j => X j ω) :=
      measurable_pi_iff.mpr fun j => hmeas j
    have hVc : Measurable fun ω => J.restrict (fun j => X j ω + c j) :=
      measurable_pi_iff.mpr fun j => (hmeas j).add_const _
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map hVc.aemeasurable f.continuous.aestronglyMeasurable,
      integral_map hV.aemeasurable f.continuous.aestronglyMeasurable, hQ]
    have hVn : ∀ n, Measurable fun ω => J.restrict (fun j => X j ω + covShift X P (σ n) j) :=
      fun n => measurable_pi_iff.mpr fun j => (hmeas j).add_const _
    have h1 : Tendsto (fun n => ∫ ω, f (J.restrict fun j => X j ω + covShift X P (σ n) j) ∂P)
        atTop (𝓝 (∫ ω, f (J.restrict fun j => X j ω + c j) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.measurable.comp (hVn n)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _)
        (ae_of_all _ fun ω => ?_)
      exact (f.continuous.tendsto _).comp
        (tendsto_pi_nhds.2 fun j => tendsto_const_nhds.add (hc j))
    have h2 : ∀ n, ∫ ω, f (J.restrict fun j => X j ω + covShift X P (σ n) j) ∂P =
        ∫ ω, f (J.restrict fun j => X j ω) * tiltDensity X P (σ n) ω ∂P := by
      intro n
      have key := map_tiltMeasure_restrict hX hmeas hcent (σ n) J
      rw [← integral_map (hVn n).aemeasurable f.continuous.aestronglyMeasurable, ← key,
        integral_map hV.aemeasurable f.continuous.aestronglyMeasurable,
        integral_tiltMeasure hX hmeas]
      simp only [mul_comm]
    have hfm : MemLp (fun ω => f (J.restrict fun j => X j ω)) 2 P :=
      MemLp.of_bound (f.continuous.measurable.comp hV).aestronglyMeasurable ‖f‖
        (ae_of_all _ fun ω => f.norm_coe_le_norm _)
    have h3 := hlim _ hfm
    simp only [h2] at h1
    rw [tendsto_nhds_unique h1 h3]
    simp only [mul_comm]
  refine ⟨D, hDm, hD1, hDnn, ?_⟩
  refine ext_of_generate_finite (measurableCylinders fun _ : I => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun s hs => ?_) ?_
  · obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
    rw [Measure.map_apply hXc hS.cylinder, Measure.map_apply hXm hS.cylinder]
    have hV : Measurable fun ω => J.restrict (fun j => X j ω) :=
      measurable_pi_iff.mpr fun j => hmeas j
    have hVc : Measurable fun ω => J.restrict (fun j => X j ω + c j) :=
      measurable_pi_iff.mpr fun j => (hmeas j).add_const _
    have := congrArg (fun μ : Measure (J → ℝ) => μ S) (hfd J)
    rwa [Measure.map_apply hVc hS, Measure.map_apply hV hS] at this
  · have := congrArg (fun μ : Measure ((∅ : Finset I) → ℝ) => μ univ) (hfd ∅)
    have hV0 : Measurable fun ω => (∅ : Finset I).restrict (fun j => X j ω) :=
      measurable_pi_iff.mpr fun j => hmeas j
    have hVc0 : Measurable fun ω => (∅ : Finset I).restrict (fun j => X j ω + c j) :=
      measurable_pi_iff.mpr fun j => (hmeas j).add_const _
    rw [Measure.map_apply hVc0 MeasurableSet.univ, Measure.map_apply hV0 MeasurableSet.univ] at this
    rw [Measure.map_apply hXc MeasurableSet.univ, Measure.map_apply hXm MeasurableSet.univ]
    simpa only [preimage_univ] using this

include hX hmeas hcent in
/-- `law(X + c) ≪ law(X)` for a limit `c` of covariance shifts (see
`map_add_eq_withDensity_of_tendsto`). -/
theorem map_add_absolutelyContinuous_of_tendsto
    (hv : Tendsto (fun n => covNorm X P (σ n)) atTop (𝓝 v))
    (hw : Tendsto (fun p : ℕ × ℕ => covNorm X P (σ p.1 - σ p.2)) atTop (𝓝 0)) {c : I → ℝ}
    (hc : ∀ j, Tendsto (fun n => covShift X P (σ n) j) atTop (𝓝 (c j))) :
    P.map (fun ω j => X j ω + c j) ≪ P.map (fun ω j => X j ω) := by
  obtain ⟨D, -, -, -, h⟩ := map_add_eq_withDensity_of_tendsto hX hmeas hcent hv hw hc
  rw [h]
  exact (withDensity_absolutelyContinuous _ _).map (measurable_pi_iff.mpr hmeas)

include hX hmeas hcent in
/-- `law(X) ≪ law(X + c)` for a limit `c` of covariance shifts (apply the other direction to
`−σₙ`, `−c` and translate by `c`). -/
theorem map_absolutelyContinuous_add_of_tendsto
    (hv : Tendsto (fun n => covNorm X P (σ n)) atTop (𝓝 v))
    (hw : Tendsto (fun p : ℕ × ℕ => covNorm X P (σ p.1 - σ p.2)) atTop (𝓝 0)) {c : I → ℝ}
    (hc : ∀ j, Tendsto (fun n => covShift X P (σ n) j) atTop (𝓝 (c j))) :
    P.map (fun ω j => X j ω) ≪ P.map (fun ω j => X j ω + c j) := by
  have hv' : Tendsto (fun n => covNorm X P (-σ n)) atTop (𝓝 v) := by
    simpa only [covNorm_neg hX] using hv
  have hw' : Tendsto (fun p : ℕ × ℕ => covNorm X P (-σ p.1 - -σ p.2)) atTop (𝓝 0) := by
    have e : ∀ p : ℕ × ℕ, -σ p.1 - -σ p.2 = -(σ p.1 - σ p.2) := fun p => by abel
    simp only [e, covNorm_neg hX]
    exact hw
  have hc' : ∀ j, Tendsto (fun n => covShift X P (-σ n) j) atTop (𝓝 (-c j)) := fun j => by
    simpa only [covShift_neg] using (hc j).neg
  have h := map_add_absolutelyContinuous_of_tendsto (σ := fun n => -σ n) hX hmeas hcent hv' hw'
    hc'
  have hT : Measurable fun x : I → ℝ => x + c :=
    measurable_pi_iff.mpr fun j => (measurable_pi_apply j).add_const _
  have hm1 : Measurable fun ω j => X j ω + -c j :=
    measurable_pi_iff.mpr fun j => (hmeas j).add_const _
  have hm2 : Measurable fun ω j => X j ω := measurable_pi_iff.mpr hmeas
  have := h.map hT
  rw [Measure.map_map hT hm1, Measure.map_map hT hm2] at this
  have e1 : (fun x : I → ℝ => x + c) ∘ (fun ω j => X j ω + -c j) = fun ω j => X j ω := by
    funext ω j
    simp
  have e2 : (fun x : I → ℝ => x + c) ∘ (fun ω j => X j ω) = fun ω j => X j ω + c j := by
    funext ω j
    simp
  rwa [e1, e2] at this

end CMLimit

end GFF
end InteractingSLE
