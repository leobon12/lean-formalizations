import QuantumZipper.Proofs.Probability.CameronMartin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Blueprint M4-P1: the Cameron–Martin 0-1 law

Let `X : I → Ω → ℝ` be a centered Gaussian process with covariance `K = covK X P`. If a
measurable set `A ⊆ ℝ^I` of paths is invariant, up to `law X`-null sets, under every translation
`x ↦ x + q • K(·,i)` (`i ∈ I`, `q ∈ ℚ`), then `P(X ∈ A) ∈ {0,1}`.

The index type `I` is arbitrary (countability is not needed).

Proof (one strategy, via the Gaussian tilt of `CameronMartin`):
1. Rational invariance propagates to shifts `K(·,σ)` for rational finitely supported `σ`
   (the shifts are quasi-invariant by Cameron–Martin), then to real `σ` using the
   total-variation bound `abs_measureReal_shift_sub_le` and `covNorm (σ - σₙ) → 0`.
2. With `E = {X ∈ A}`, real invariance says `∫_E exp(Xσ − K(σ,σ)/2) dP = P(E)` for all `σ`.
   Hence every finite combination `Y = ∑ c_j X_j` has the same mgf under `P|_E` and under
   `P(E) • P`, so the same law; by `charFunDual` the finite-dimensional marginals agree, and by
   cylinders `law(X; P|_E) = P(E) • law(X; P)`. Evaluating at `A` gives `P(E) = P(E)²`.
-/

open MeasureTheory ProbabilityTheory Complex Filter
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

namespace QuantumZipper.ZeroOneCM

open QuantumZipper.CameronMartin

variable {Ω I : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : I → Ω → ℝ}

lemma zo_measurable_add (h : I → ℝ) : Measurable fun x : I → ℝ ↦ x + h :=
  measurable_pi_iff.mpr fun j ↦ (measurable_pi_apply j).add_const _

lemma zo_covShift_add (σ τ : I →₀ ℝ) (j : I) :
    covShift X P (σ + τ) j = covShift X P σ j + covShift X P τ j := by
  show (σ + τ).sum (fun i q ↦ q * covK X P j i) =
    σ.sum (fun i q ↦ q * covK X P j i) + τ.sum (fun i q ↦ q * covK X P j i)
  exact Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)

lemma zo_covShift_single (i : I) (q : ℝ) (j : I) :
    covShift X P (Finsupp.single i q) j = q * covK X P j i := by
  show (Finsupp.single i q).sum (fun i q ↦ q * covK X P j i) = _
  rw [Finsupp.sum_single_index (zero_mul _)]

lemma zo_covShift_zero (j : I) : covShift X P 0 j = 0 := by
  simp [covShift]

section Core

variable (hX : IsGaussianProcess X P) (hmeas : ∀ i, Measurable (X i))
  (hcent : ∀ i, P[X i] = 0)
include hX hmeas hcent

/-- Step 2a: one-dimensional laws of finite combinations agree under `P|_E` and `P(E) • P`. -/
lemma zo_map_comb {E : Set Ω} (hE0 : P E ≠ 0)
    (hshift : ∀ σ : I →₀ ℝ, ∫ ω in E, tiltDensity X P σ ω ∂P = P.real E)
    (J : Finset I) (c : I → ℝ) :
    (P.restrict E).map (fun ω ↦ ∑ j ∈ J, c j * X j ω) =
      ((P E).toNNReal • P).map (fun ω ↦ ∑ j ∈ J, c j * X j ω) := by
  haveI := hX.isProbabilityMeasure
  set Y : Ω → ℝ := fun ω ↦ ∑ j ∈ J, c j * X j ω with hYdef
  have hYm : Measurable Y := by rw [hYdef]; fun_prop
  have key : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * Y ω)) P ∧
      ∫ ω in E, Real.exp (t * Y ω) ∂P = P.real E * ∫ ω, Real.exp (t * Y ω) ∂P := by
    intro t
    classical
    let σ : I →₀ ℝ := Finsupp.onFinset J (fun i ↦ if i ∈ J then t * c i else 0) (by
      intro i hi; by_contra h; exact hi (if_neg h))
    have hσ : σ.support ⊆ J := Finsupp.support_onFinset_subset
    have hcomb : ∀ ω, comb X σ ω = t * Y ω := by
      intro ω
      rw [comb_eq_sum_subset hX σ hσ, hYdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      simp only [σ, Finsupp.onFinset_apply, if_pos hj]; ring
    have hexp : ∀ ω, Real.exp (t * Y ω) =
        tiltDensity X P σ ω * Real.exp (covNorm X P σ / 2) := by
      intro ω
      rw [tiltDensity, ← Real.exp_add, hcomb]; ring_nf
    obtain ⟨hi, h1⟩ := tiltDensity_integral hX hmeas hcent σ
    simp_rw [hexp]
    refine ⟨hi.mul_const _, ?_⟩
    rw [integral_mul_const, integral_mul_const, hshift σ, h1, one_mul]
  have hmgf : mgf Y (P.restrict E) = mgf Y ((P E).toNNReal • P) := by
    funext t
    rw [mgf, mgf, integral_smul_nnreal_measure, (key t).2, NNReal.smul_def, smul_eq_mul,
      ENNReal.coe_toNNReal_eq_toReal, measureReal_def]
  have hne : P.restrict E = 0 ↔ (P E).toNNReal • P = 0 := by
    constructor <;> intro h
    · exact absurd (Measure.restrict_eq_zero.mp h) hE0
    · exfalso
      have h2 : ((P E).toNNReal • P) Set.univ = 0 := by rw [h]; rfl
      rw [Measure.coe_nnreal_smul_apply, measure_univ, mul_one, ENNReal.coe_eq_zero,
        ENNReal.toNNReal_eq_zero_iff] at h2
      exact h2.elim hE0 (measure_ne_top P E)
  have hint : integrableExpSet Y (P.restrict E) = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    exact (key t).1.restrict
  have hc := eqOn_complexMGF_of_mgf' hmgf hne
  rw [hint, interior_univ] at hc
  exact Measure.ext_of_complexMGF_eq hYm.aemeasurable hYm.aemeasurable
    (funext fun z ↦ hc (by simp))

open Classical in
/-- Step 2b: finite-dimensional marginals agree. -/
lemma zo_map_restrict {E : Set Ω} (hE0 : P E ≠ 0)
    (hshift : ∀ σ : I →₀ ℝ, ∫ ω in E, tiltDensity X P σ ω ∂P = P.real E) (J : Finset I) :
    (P.restrict E).map (fun ω ↦ J.restrict (fun j ↦ X j ω)) =
      ((P E).toNNReal • P).map (fun ω ↦ J.restrict (fun j ↦ X j ω)) := by
  haveI := hX.isProbabilityMeasure
  have hV : Measurable fun ω ↦ J.restrict (fun j ↦ X j ω) :=
    measurable_pi_iff.mpr fun j ↦ hmeas j
  refine Measure.ext_of_charFunDual (funext fun L ↦ ?_)
  set c : I → ℝ := fun j ↦
    if h : j ∈ J then L (fun k ↦ if (⟨j, h⟩ : J) = k then 1 else 0) else 0 with hc
  have key := zo_map_comb hX hmeas hcent hE0 hshift J c
  have hcont : Continuous fun y : ℝ ↦ cexp (y * Complex.I) := by fun_prop
  rw [charFunDual_apply, charFunDual_apply, integral_map hV.aemeasurable (by fun_prop),
    integral_map hV.aemeasurable (by fun_prop)]
  have h1 : ∀ ω, L (J.restrict (fun j ↦ X j ω)) = ∑ j ∈ J, c j * X j ω := fun ω ↦
    strongDual_restrict_eq_sum hX J J subset_rfl L _
  simp_rw [h1]
  have hYm : Measurable fun ω ↦ ∑ j ∈ J, c j * X j ω := by fun_prop
  rw [← integral_map (f := fun y : ℝ ↦ cexp (y * Complex.I)) hYm.aemeasurable
      hcont.aestronglyMeasurable, key,
    integral_map hYm.aemeasurable hcont.aestronglyMeasurable]

/-- Step 2c: `law(X; P|_E) = P(E) • law(X; P)`. -/
lemma zo_map_path {E : Set Ω} (hE0 : P E ≠ 0)
    (hshift : ∀ σ : I →₀ ℝ, ∫ ω in E, tiltDensity X P σ ω ∂P = P.real E) :
    (P.restrict E).map (fun ω j ↦ X j ω) = ((P E).toNNReal • P).map (fun ω j ↦ X j ω) := by
  haveI := hX.isProbabilityMeasure
  have hp : Measurable fun ω j ↦ X j ω := measurable_pi_iff.mpr hmeas
  refine ext_of_generate_finite (measurableCylinders fun _ : I ↦ ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun s hs ↦ ?_) ?_
  · obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
    rw [Measure.map_apply hp hS.cylinder, Measure.map_apply hp hS.cylinder]
    have := congrArg (fun μ : Measure (J → ℝ) ↦ μ S)
      (zo_map_restrict hX hmeas hcent hE0 hshift J)
    have hV : Measurable fun ω ↦ J.restrict (fun j ↦ X j ω) :=
      measurable_pi_iff.mpr fun j ↦ hmeas j
    beta_reduce at this
    rwa [Measure.map_apply hV hS, Measure.map_apply hV hS] at this
  · rw [Measure.map_apply hp MeasurableSet.univ, Measure.map_apply hp MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply_univ, Measure.coe_nnreal_smul_apply,
      measure_univ, mul_one, ENNReal.coe_toNNReal (measure_ne_top P E)]

/-- Step 1a: the shifted law is absolutely continuous w.r.t. the law. -/
lemma zo_map_shift_ac (σ : I →₀ ℝ) :
    P.map (fun ω j ↦ X j ω + covShift X P σ j) ≪ P.map (fun ω j ↦ X j ω) := by
  have hp : Measurable fun ω j ↦ X j ω := measurable_pi_iff.mpr hmeas
  rw [← map_tiltMeasure_path hX hmeas hcent σ]
  exact Measure.AbsolutelyContinuous.map (by unfold tiltMeasure; exact withDensity_absolutelyContinuous _ _)
    hp

lemma zo_map_map_shift (σ : I →₀ ℝ) (h : I → ℝ) :
    (P.map (fun ω j ↦ X j ω + covShift X P σ j)).map (fun x : I → ℝ ↦ x + h) =
      P.map (fun ω j ↦ X j ω + covShift X P σ j + h j) := by
  rw [Measure.map_map (zo_measurable_add h)
    (measurable_pi_iff.mpr fun j ↦ (hmeas j).add_const _)]
  rfl

/-- Step 1b: the shift by `K(·,σ)` is quasi-measure-preserving for `law X`. -/
lemma zo_qmp (σ : I →₀ ℝ) :
    Measure.QuasiMeasurePreserving (fun x : I → ℝ ↦ x + covShift X P σ)
      (P.map fun ω j ↦ X j ω) (P.map fun ω j ↦ X j ω) := by
  refine ⟨zo_measurable_add _, ?_⟩
  have := zo_map_map_shift hX hmeas hcent 0 (covShift X P σ)
  simp only [zo_covShift_zero, add_zero] at this
  rw [this]
  exact zo_map_shift_ac hX hmeas hcent σ

variable {A : Set (I → ℝ)}

/-- Step 1c: invariance under rational finitely supported shifts. -/
lemma zo_rat_inv
    (hinv : ∀ (i : I) (q : ℚ), (fun x : I → ℝ ↦ x + (q : ℝ) • fun j ↦ covK X P j i) ⁻¹' A
      =ᵐ[P.map fun ω j ↦ X j ω] A) (σ : I →₀ ℚ) :
    (fun x : I → ℝ ↦ x + covShift X P (σ.mapRange (fun q : ℚ ↦ (q : ℝ)) Rat.cast_zero)) ⁻¹' A
      =ᵐ[P.map fun ω j ↦ X j ω] A := by
  induction σ using Finsupp.induction with
  | zero =>
    have : (fun x : I → ℝ ↦ x + covShift X P ((0 : I →₀ ℚ).mapRange (fun q : ℚ ↦ (q : ℝ))
        Rat.cast_zero)) = id := by
      funext x j; simp [covShift]
    rw [this]; rfl
  | single_add i q τ _ _ ih =>
    have heq : ∀ x : I → ℝ, x + covShift X P ((Finsupp.single i q + τ).mapRange
        (fun q : ℚ ↦ (q : ℝ)) Rat.cast_zero) =
        (x + covShift X P (τ.mapRange (fun q : ℚ ↦ (q : ℝ)) Rat.cast_zero)) +
          (q : ℝ) • fun j ↦ covK X P j i := by
      intro x; funext j
      rw [Finsupp.mapRange_add (fun a b ↦ Rat.cast_add a b), Finsupp.mapRange_single]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zo_covShift_add, zo_covShift_single]
      ring
    have hset : (fun x : I → ℝ ↦ x + covShift X P ((Finsupp.single i q + τ).mapRange
        (fun q : ℚ ↦ (q : ℝ)) Rat.cast_zero)) ⁻¹' A =
        (fun x : I → ℝ ↦ x + covShift X P (τ.mapRange (fun q : ℚ ↦ (q : ℝ)) Rat.cast_zero)) ⁻¹'
          ((fun x : I → ℝ ↦ x + (q : ℝ) • fun j ↦ covK X P j i) ⁻¹' A) := by
      ext x; simp only [Set.mem_preimage, heq]
    rw [hset]
    exact ((zo_qmp hX hmeas hcent _).preimage_ae_eq (hinv i q)).trans ih

/-- Step 1d: invariance under all real finitely supported shifts. -/
lemma zo_real_inv (hA : MeasurableSet A)
    (hinv : ∀ (i : I) (q : ℚ), (fun x : I → ℝ ↦ x + (q : ℝ) • fun j ↦ covK X P j i) ⁻¹' A
      =ᵐ[P.map fun ω j ↦ X j ω] A) (σ : I →₀ ℝ) :
    (P.map fun ω j ↦ X j ω + covShift X P σ j).real A = (P.map fun ω j ↦ X j ω).real A := by
  haveI := hX.isProbabilityMeasure
  have hstep : ∀ τ : I →₀ ℚ,
      |(P.map fun ω j ↦ X j ω + covShift X P σ j).real A - (P.map fun ω j ↦ X j ω).real A| ≤
        Real.sqrt (Real.exp (covNorm X P
          (σ - τ.mapRange (fun q : ℚ ↦ (q : ℝ)) Rat.cast_zero)) - 1) := by
    intro τ
    set τR := τ.mapRange (fun q : ℚ ↦ (q : ℝ)) Rat.cast_zero
    set δ := σ - τR
    have hcs : ∀ j, covShift X P σ j = covShift X P δ j + covShift X P τR j := fun j ↦ by
      rw [← zo_covShift_add, sub_add_cancel]
    have hmap : P.map (fun ω j ↦ X j ω + covShift X P σ j) =
        (P.map fun ω j ↦ X j ω + covShift X P δ j).map (fun x ↦ x + covShift X P τR) := by
      rw [zo_map_map_shift hX hmeas hcent]
      congr 1; funext ω j; rw [hcs]; ring
    have h1 : (P.map fun ω j ↦ X j ω + covShift X P σ j).real A =
        (P.map fun ω j ↦ X j ω + covShift X P δ j).real A := by
      rw [hmap, measureReal_def, measureReal_def, Measure.map_apply (zo_measurable_add _) hA]
      congr 1
      exact measure_congr ((zo_map_shift_ac hX hmeas hcent δ).ae_eq (zo_rat_inv hX hmeas hcent hinv τ))
    rw [h1]
    exact abs_measureReal_shift_sub_le hX hmeas hcent δ A hA
  -- rational approximations
  let τ : ℕ → I →₀ ℚ := fun n ↦
    σ.mapRange (fun x : ℝ ↦ ((⌊x * ((n : ℝ) + 1)⌋ : ℚ) / ((n : ℚ) + 1))) (by simp)
  set δ : ℕ → I →₀ ℝ := fun n ↦ σ - (τ n).mapRange (fun q : ℚ ↦ (q : ℝ)) Rat.cast_zero with hδdef
  have hδ : ∀ n i, δ n i = σ i - (⌊σ i * ((n : ℝ) + 1)⌋ : ℝ) / ((n : ℝ) + 1) := by
    intro n i
    simp [hδdef, τ]
  have hsupp : ∀ n, (δ n).support ⊆ σ.support := by
    intro n i hi
    rw [Finsupp.mem_support_iff] at hi ⊢
    intro h0; apply hi; rw [hδ, h0]; simp
  have hlim_i : ∀ i, Tendsto (fun n : ℕ ↦ δ n i) atTop (𝓝 0) := by
    intro i
    simp_rw [hδ]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n ↦ ?_) (fun n ↦ ?_)
    · have hm : (0 : ℝ) < n + 1 := by positivity
      rw [sub_nonneg, div_le_iff₀ hm]
      exact Int.floor_le _
    · have hm : (0 : ℝ) < n + 1 := by positivity
      have := Int.lt_floor_add_one (σ i * (n + 1))
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hm]
      linarith
  have hcn : ∀ n, covNorm X P (δ n) =
      ∑ j ∈ σ.support, δ n j * ∑ i ∈ σ.support, δ n i * covK X P j i := by
    intro n
    unfold covNorm covShift
    rw [Finset.sum_subset (hsupp n) ?_]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      congr 1
      exact Finset.sum_subset (hsupp n) fun i _ hi ↦ by
        rw [Finsupp.notMem_support_iff.mp hi, zero_mul]
    · intro j _ hj
      rw [Finsupp.notMem_support_iff.mp hj, zero_mul]
  have hlimN : Tendsto (fun n ↦ covNorm X P (δ n)) atTop (𝓝 0) := by
    simp_rw [hcn]
    have h0 : (0 : ℝ) = ∑ j ∈ σ.support, (0 : ℝ) * ∑ i ∈ σ.support, (0 : ℝ) * covK X P j i := by
      simp
    rw [h0]
    exact tendsto_finsetSum _ fun j _ ↦ (hlim_i j).mul
      (tendsto_finsetSum _ fun i _ ↦ (hlim_i i).mul tendsto_const_nhds)
  have hlimF : Tendsto (fun n ↦ Real.sqrt (Real.exp (covNorm X P (δ n)) - 1)) atTop (𝓝 0) := by
    have hc : Continuous fun x : ℝ ↦ Real.sqrt (Real.exp x - 1) := by fun_prop
    have := (hc.tendsto 0).comp hlimN
    simpa [Function.comp_def] using this
  have habs := ge_of_tendsto hlimF (Eventually.of_forall fun n ↦ hstep (τ n))
  have := abs_nonpos_iff.mp habs
  linarith

/-- **Blueprint M4-P1 (Cameron–Martin 0-1 law).** Let `X` be a centered Gaussian process with
covariance `K = covK X P`, and let `A` be a measurable set of paths which is invariant up to
`law X`-null sets under every translation `x ↦ x + q • K(·,i)`, `i ∈ I`, `q ∈ ℚ`. Then
`P(X ∈ A) ∈ {0,1}`. -/
theorem measure_preimage_eq_zero_or_one_of_ratShift (hA : MeasurableSet A)
    (hinv : ∀ (i : I) (q : ℚ), (fun x : I → ℝ ↦ x + (q : ℝ) • fun j ↦ covK X P j i) ⁻¹' A
      =ᵐ[P.map fun ω j ↦ X j ω] A) :
    P ((fun ω j ↦ X j ω) ⁻¹' A) = 0 ∨ P ((fun ω j ↦ X j ω) ⁻¹' A) = 1 := by
  haveI := hX.isProbabilityMeasure
  have hp : Measurable (fun ω j ↦ X j ω) := measurable_pi_iff.mpr hmeas
  have hΦ : Measurable (A.indicator (1 : (I → ℝ) → ℝ)) := measurable_const.indicator hA
  have hshift : ∀ σ : I →₀ ℝ, ∫ ω in (fun ω j ↦ X j ω) ⁻¹' A, tiltDensity X P σ ω ∂P =
      P.real ((fun ω j ↦ X j ω) ⁻¹' A) := by
    intro σ
    have hpσ : Measurable fun ω j ↦ X j ω + covShift X P σ j :=
      measurable_pi_iff.mpr fun j ↦ (hmeas j).add_const _
    have hmain := integral_mul_tiltDensity hX hmeas hcent σ _ hΦ
    have e1 : (P.map fun ω j ↦ X j ω + covShift X P σ j).real A =
        ∫ ω, A.indicator 1 (fun j ↦ X j ω + covShift X P σ j) ∂P := by
      rw [← integral_indicator_one hA, integral_map hpσ.aemeasurable hΦ.aestronglyMeasurable]
    have e2 : ∫ ω, A.indicator 1 (fun j ↦ X j ω) * tiltDensity X P σ ω ∂P =
        ∫ ω in (fun ω j ↦ X j ω) ⁻¹' A, tiltDensity X P σ ω ∂P := by
      rw [← integral_indicator (hp hA)]
      congr 1; funext ω
      by_cases h : (fun j ↦ X j ω) ∈ A <;> simp [Set.indicator, h]
    have e3 : (P.map fun ω j ↦ X j ω).real A = P.real ((fun ω j ↦ X j ω) ⁻¹' A) := by
      rw [measureReal_def, measureReal_def, Measure.map_apply hp hA]
    rw [← e2, hmain, ← e1, zo_real_inv hX hmeas hcent hA hinv σ, e3]
  by_cases hE0 : P ((fun ω j ↦ X j ω) ⁻¹' A) = 0
  · exact Or.inl hE0
  right
  have hlaw := zo_map_path hX hmeas hcent hE0 hshift
  have h := congrArg (fun μ : Measure (I → ℝ) ↦ μ A) hlaw
  rw [Measure.map_apply hp hA, Measure.map_apply hp hA, Measure.restrict_apply (hp hA),
    Set.inter_self, Measure.coe_nnreal_smul_apply, ENNReal.coe_toNNReal (measure_ne_top _ _)] at h
  set x := P ((fun ω j ↦ X j ω) ⁻¹' A)
  have ht : x.toReal = x.toReal * x.toReal := by rw [← ENNReal.toReal_mul, ← h]
  have hne : x.toReal ≠ 0 := (ENNReal.toReal_pos hE0 (measure_ne_top _ _)).ne'
  have h1 : x.toReal = 1 := mul_left_cancel₀ hne (by rw [mul_one]; exact ht.symm)
  exact (ENNReal.toReal_eq_one_iff x).mp h1

end Core

end QuantumZipper.ZeroOneCM
