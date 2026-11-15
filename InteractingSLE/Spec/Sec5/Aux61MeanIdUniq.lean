/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ChLocRestart

/-!
# (K-b): the harmonic part of a chart decomposition is unique

Packet PROVE-AUX61-MEAN. `Aux61ChLoc.IsChartMeanAt μ Z B Y q 𝒢 M` (PROVE-AUX61-CHARTLOC) asks that the harmonic part of
EVERY conditional Gaussian decomposition `Aux61ChLoc.IsChartGaussAt μ Z B Y q 𝒢 h₁` of the chart field given `𝒢` pairs
like `M` off the chart hull. Given `𝒢`, the harmonic part is the conditional mean, so it is unique; this file proves
that uniqueness from the conditional characteristic functionals alone (no integrability of the chart field is
needed), and hence that (K-b) holds as soon as ONE decomposition has the mean `M`:

* `gauss_condExp_cexp_field_eq`: on the live event, `E[e^{i Y(φ)} | 𝒢] = e^{i h₁(φ)} e^{−½ ‖φ‖²}`;
* `eq_of_forall_cexp_div`: two reals with `e^{i a/(n+1)} = e^{i b/(n+1)}` for every `n` are equal;
* **`gauss_ae_apply_eq`**: two decompositions given the same `𝒢` have, for each test, a.s. the same harmonic
  part on the live event (apply the first item to the tests `φ/(n+1)`; the Gaussian factor is nonzero);
* **`gauss_ae_forall_apply_eq`**: the same, a.s. simultaneously for every test off the chart hull (both parts
  are harmonic there; bump tests at rational centres and radii, `LocalSets.ae_forall_apply_eq_of_bump`);
* **`isChartMeanAt_of_isChartGaussAt`**: (K-b) for `𝒢` and `M` follows from one decomposition with mean `M`.

Conditional helpers with distinct names; they replace no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function Metric
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61MeanId

open Aux61Fib (FibCode)
open Aux61ChLoc (IsChartGaussAt IsChartMeanAt liveEv measurableSet_live)
open Aux61UnionK (chartHull norm_cexp_I_mul_ofReal_le measurable_field_apply isOpen_H_diff_chartHull)

universe u

/-! ### An elementary fact about `e^{i·}` -/

/-- **Two reals whose phases agree at every scale `1/(n+1)` are equal.** -/
theorem eq_of_forall_cexp_div {a b : ℝ}
    (h : ∀ n : ℕ, Complex.exp (Complex.I * ((a / ((n : ℝ) + 1) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((b / ((n : ℝ) + 1) : ℝ) : ℂ))) : a = b := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|a - b| / (2 * Real.pi))
  have hpi : 0 < 2 * Real.pi := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h n)
  -- `(a − b)/(n+1) = 2πk`
  have hk' : (a - b) / ((n : ℝ) + 1) = k * (2 * Real.pi) := by
    have := congrArg Complex.im hk
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      one_mul, zero_add, Complex.add_im, Complex.intCast_re, Complex.intCast_im, mul_zero, sub_zero,
      Complex.re_ofNat, Complex.im_ofNat, Complex.mul_re, Complex.ofReal_re] at this
    rw [sub_div]
    linarith
  have hsmall : |(a - b) / ((n : ℝ) + 1)| < 2 * Real.pi := by
    rw [abs_div, abs_of_pos hn1, div_lt_iff₀ hn1]
    have := (div_lt_iff₀ hpi).1 hn
    nlinarith
  rw [hk', abs_mul, abs_of_pos hpi] at hsmall
  have hk0 : k = 0 := by
    have h1 : |(k : ℝ)| < 1 := by
      by_contra hc
      push Not at hc
      nlinarith
    have h2 : |k| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.1 h2
  rw [hk0, Int.cast_zero, zero_mul, div_eq_zero_iff] at hk'
  rcases hk' with h0 | h0
  · linarith
  · linarith

/-! ### Uniqueness of the harmonic part -/

section Uniq

variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]
  {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
  {h₁ h₁' : X → DistOn upperHalfPlaneOpens}

/-- **The conditional characteristic functional of the chart field** given `𝒢`, on the live event:
`E[e^{i Y(φ)} | 𝒢] = e^{i h₁(φ)} e^{−½ ‖φ‖²_{H⁻¹(ℍ∖K_q)}}` (pull the `𝒢`-measurable phase `e^{i h₁(φ)}` out). -/
theorem gauss_condExp_cexp_field_eq [IsFiniteMeasure μ] (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁)
    (hY : Measurable Y) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      μ[fun x' => Complex.exp (Complex.I * ((Y x').field φ : ℂ)) | 𝒢] x =
        Complex.exp (Complex.I * (h₁ x φ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ chartHull Y q x) φ φ) : ℝ) : ℂ) := by
  have hh₁𝒢 : Measurable[𝒢] fun x => h₁ x φ :=
    (measurable_pi_apply φ).comp ((LQGMetric.measurable_distEval _).comp hG.measurable)
  have hh₁ : Measurable fun x => h₁ x φ := hh₁𝒢.mono hG.le le_rfl
  have hP : StronglyMeasurable[𝒢] fun x => Complex.exp (Complex.I * (h₁ x φ : ℂ)) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hh₁𝒢))).stronglyMeasurable
  have hgm : Measurable fun x => Complex.exp (Complex.I * (((Y x).field φ - h₁ x φ : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_field_apply hY φ).sub hh₁)))
  have hg : Integrable (fun x => Complex.exp (Complex.I * (((Y x).field φ - h₁ x φ : ℝ) : ℂ))) μ :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _)
  have h1 := condExp_stronglyMeasurable_bilin_of_bound (ContinuousLinearMap.mul ℝ ℂ) hG.le hP hg 1
    (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _)
  have e : (fun x' => Complex.exp (Complex.I * ((Y x').field φ : ℂ))) = fun x =>
      (ContinuousLinearMap.mul ℝ ℂ) (Complex.exp (Complex.I * (h₁ x φ : ℂ)))
        (Complex.exp (Complex.I * (((Y x).field φ - h₁ x φ : ℝ) : ℂ))) := by
    funext x
    rw [ContinuousLinearMap.mul_apply', ← Complex.exp_add]
    congr 1
    push_cast
    ring
  filter_upwards [h1, hG.gff φ] with x hx hgff hxB hlt
  rw [e, hx, ContinuousLinearMap.mul_apply', hgff hxB hlt]

/-- **The harmonic part of a decomposition is unique** (for each test): two conditional Gaussian decompositions of the
chart field given the same `𝒢` have almost surely the same harmonic part on the live event. -/
theorem gauss_ae_apply_eq [IsFiniteMeasure μ] (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁)
    (hG' : IsChartGaussAt μ Z B Y q 𝒢 h₁') (hY : Measurable Y) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → h₁ x φ = h₁' x φ := by
  set φn : ℕ → TestOn upperHalfPlaneOpens := fun n => (1 / ((n : ℝ) + 1)) • φ with hφn
  have hall : ∀ n : ℕ, ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      Complex.exp (Complex.I * (h₁ x (φn n) : ℂ)) = Complex.exp (Complex.I * (h₁' x (φn n) : ℂ)) := by
    intro n
    filter_upwards [gauss_condExp_cexp_field_eq hG hY (φn n), gauss_condExp_cexp_field_eq hG' hY (φn n)]
      with x h1 h2 hxB hlt
    have e := (h1 hxB hlt).symm.trans (h2 hxB hlt)
    have hne : ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ chartHull Y q x) (φn n) (φn n)) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    exact mul_right_cancel₀ hne e
  filter_upwards [ae_all_iff.2 hall] with x hx hxB hlt
  refine eq_of_forall_cexp_div fun n => ?_
  have e := hx n hxB hlt
  have h1 : h₁ x (φn n) = 1 / ((n : ℝ) + 1) * h₁ x φ := by
    simp only [hφn, map_smul, smul_eq_mul]
  have h2 : h₁' x (φn n) = 1 / ((n : ℝ) + 1) * h₁' x φ := by
    simp only [hφn, map_smul, smul_eq_mul]
  rw [h1, h2] at e
  convert e using 4 <;> ring

/-- The empty set is harmonic territory for every distribution. -/
theorem isHarmonicDistOn_empty (T : DistOn upperHalfPlaneOpens) : IsHarmonicDistOn T ∅ := by
  refine ⟨0, fun z hz => hz.elim, fun φ hφ => ?_⟩
  have h0 : ∀ z, φ z = 0 := fun z => by
    by_contra hz
    exact hφ (subset_tsupport _ hz)
  have hφ0 : φ = 0 := by ext z; exact h0 z
  simp only [hφ0, map_zero, Pi.zero_apply, zero_mul, integral_zero]

/-- **The harmonic part is unique, simultaneously for every test off the chart hull.** -/
theorem gauss_ae_forall_apply_eq [IsFiniteMeasure μ] (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁)
    (hG' : IsChartGaussAt μ Z B Y q 𝒢 h₁') (hY : Measurable Y) (hB : MeasurableSet B) :
    ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ ψ : TestOn upperHalfPlaneOpens,
      Disjoint (tsupport ψ) (chartHull Y q x) → h₁ x ψ = h₁' x ψ := by
  classical
  set S := liveEv Z B Y q with hSdef
  have hS : MeasurableSet S := hG.le _ (measurableSet_live hG.marksZ hG.marksY hB)
  set O : X → Set ℂ := fun x => if x ∈ S then H \ chartHull Y q x else ∅ with hOdef
  have hO : ∀ x, IsOpen (O x) ∧ O x ⊆ H := fun x => by
    by_cases hx : x ∈ S
    · simp only [hOdef, hx, ↓reduceIte]
      exact ⟨isOpen_H_diff_chartHull Y hx.2, sdiff_subset⟩
    · simp only [hOdef, hx, ↓reduceIte]
      exact ⟨isOpen_empty, empty_subset _⟩
  have hharm : ∀ {g : X → DistOn upperHalfPlaneOpens}, IsChartGaussAt μ Z B Y q 𝒢 g →
      ∀ᵐ x ∂μ, IsHarmonicDistOn (g x) (O x) := fun {g} hg => by
    filter_upwards [hg.harmonic] with x hx
    by_cases hxS : x ∈ S
    · simp only [hOdef, hxS, ↓reduceIte]
      exact hx hxS.1 hxS.2
    · simp only [hOdef, hxS, ↓reduceIte]
      exact isHarmonicDistOn_empty _
  have key := LocalSets.ae_forall_apply_eq_of_bump (P := μ) (O := O) (ae_of_all _ hO) (hharm hG) (hharm hG')
    fun z δ hδ hBδ => by
      filter_upwards [gauss_ae_apply_eq hG hG' hY (GFF.bumpTest z hδ hBδ)] with x hx hsub
      by_cases hxS : x ∈ S
      · exact hx hxS.1 hxS.2
      · simp only [hOdef, hxS, ↓reduceIte, subset_empty_iff] at hsub
        exact absurd hsub (nonempty_closedBall.2 hδ.le).ne_empty
  filter_upwards [key] with x hx hxB hlt ψ hψ
  have hxS : x ∈ S := ⟨hxB, hlt⟩
  refine hx ψ ?_
  simp only [hOdef, hxS, ↓reduceIte]
  exact fun z hz => ⟨ψ.tsupport_subset hz, Set.disjoint_left.1 hψ hz⟩

/-- **(K-b) from one decomposition**: if one conditional Gaussian decomposition of the chart field given `𝒢` has the
mean `M` off the chart hull, then every one does (`IsChartMeanAt`). -/
theorem isChartMeanAt_of_isChartGaussAt [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    {M : X → ℂ → ℝ} (hG₀ : IsChartGaussAt μ Z B Y q 𝒢 h₁)
    (hmean : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ ψ : TestOn upperHalfPlaneOpens,
      Disjoint (tsupport ψ) (chartHull Y q x) → h₁ x ψ = ∫ z, M x z * ψ z) :
    @IsChartMeanAt X mX β mβ μ Z B Y q 𝒢 M := by
  intro h₁' hG'
  filter_upwards [gauss_ae_forall_apply_eq hG' hG₀ hY hB, hmean] with x hx hm hxB hlt ψ hψ
  rw [hx hxB hlt ψ hψ, hm hxB hlt ψ hψ]

end Uniq

end InteractingSLE.Sec5.Aux61MeanId
