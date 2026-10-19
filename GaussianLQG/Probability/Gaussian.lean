import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian facts (blueprint Lemma `lem:gauss`)

Let `Z` be a real random variable with law `N(0, v)` (`HasLaw Z (gaussianReal 0 v) P`), so
`s = √v` is its standard deviation.

* Moments: `integral_of_hasLaw_gaussianReal` (`E Z = 0`), `integral_sq_of_hasLaw_gaussianReal`
  (`E Z² = v`), and the absolute moments `integral_abs_rpow_of_hasLaw_gaussianReal`:
  `E|Z|^p = v^{p/2} E|N|^p` with `N ∼ N(0,1)`, i.e. `‖Z‖_p = s ‖N‖_p`
  (`integral_abs_rpow_rpow_inv_of_hasLaw_gaussianReal`).
* Exponential moments: `integral_exp_mul_of_hasLaw_gaussianReal`: `E e^{tZ} = e^{v t²/2}`.
* Two-sided tail: `measureReal_le_abs_le_of_hasLaw_gaussianReal`:
  `P[|Z| ≥ x] ≤ 2 e^{-x²/(2v)}` for `x ≥ 0` (so also `P[|Z| > x]`).
* Expected maximum: `integral_iSup_abs_le` — if `Z_1, …, Z_n` are centered Gaussians with
  variances at most `s²` (no independence is assumed), then `E max_i |Z_i| ≤ s √(2 log(2n))`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

section OneDim

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}

/-- A centered Gaussian has mean zero. -/
theorem integral_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ∂P = 0 := by
  rw [hX.integral_eq, integral_id_gaussianReal]

/-- `E Z² = v` for `Z ∼ N(0, v)`. -/
theorem integral_sq_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P) :
    ∫ ω, X ω ^ 2 ∂P = v := by
  have hvar := hX.variance_eq
  rwa [variance_id_gaussianReal,
    variance_of_integral_eq_zero hX.aemeasurable (integral_of_hasLaw_gaussianReal hX)] at hvar

theorem variance_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P) :
    Var[X; P] = v := by
  rw [hX.variance_eq, variance_id_gaussianReal]

theorem memLp_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P) {p : ℝ≥0∞}
    (hp : p ≠ ∞) : MemLp X p P :=
  hX.memLp (memLp_id_gaussianReal' p hp)

theorem integrable_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P) :
    Integrable X P :=
  memLp_one_iff_integrable.1 (memLp_of_hasLaw_gaussianReal hX ENNReal.one_ne_top)

/-- `N(0, v)` is the image of `N(0, 1)` under `x ↦ √v x`. -/
theorem gaussianReal_eq_map_sqrt_mul (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map fun x => Real.sqrt v * x := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.eq
    push_cast
    rw [Real.sq_sqrt v.coe_nonneg]
    ring

/-- **Absolute moments** (Lemma `lem:gauss`): `E|Z|^p = v^{p/2} E|N|^p` for `Z ∼ N(0, v)`. -/
theorem integral_abs_rpow_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P)
    (p : ℝ) :
    ∫ ω, |X ω| ^ p ∂P = (v : ℝ) ^ (p / 2) * ∫ x, |x| ^ p ∂gaussianReal 0 1 := by
  have hm : Measurable fun x : ℝ => |x| ^ p := by fun_prop
  have h := hX.integral_comp (f := fun x : ℝ => |x| ^ p) hm.aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, gaussianReal_eq_map_sqrt_mul, integral_map (by fun_prop) hm.aestronglyMeasurable,
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hs : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  dsimp only
  rw [abs_mul, abs_of_nonneg hs, Real.mul_rpow hs (abs_nonneg x), Real.sqrt_eq_rpow,
    ← Real.rpow_mul v.coe_nonneg]
  ring_nf

/-- Absolute moments of integer order as lower integrals:
`∫⁻ |Z|^n = v^{n/2} E|N|^n` for `Z ∼ N(0, v)`. -/
theorem lintegral_abs_pow_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ n) ∂P =
      ENNReal.ofReal ((v : ℝ) ^ ((n : ℝ) / 2) * ∫ x, |x| ^ (n : ℝ) ∂gaussianReal 0 1) := by
  have := hX.isProbabilityMeasure
  have hmem := memLp_of_hasLaw_gaussianReal hX (p := (n : ℝ≥0∞)) (ENNReal.natCast_ne_top n)
  have hint : Integrable (fun ω => |X ω| ^ n) P := by
    simpa only [Real.norm_eq_abs] using hmem.integrable_norm_pow'
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by positivity),
    ← integral_abs_rpow_of_hasLaw_gaussianReal hX]
  simp_rw [Real.rpow_natCast]

/-- **`‖Z‖_p = s ‖N‖_p`** (Lemma `lem:gauss`), for `Z ∼ N(0, s²)` and `p > 0`. -/
theorem integral_abs_rpow_rpow_inv_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P)
    {p : ℝ} (hp : 0 < p) :
    (∫ ω, |X ω| ^ p ∂P) ^ p⁻¹ =
      Real.sqrt v * (∫ x, |x| ^ p ∂gaussianReal 0 1) ^ p⁻¹ := by
  rw [integral_abs_rpow_of_hasLaw_gaussianReal hX p,
    Real.mul_rpow (Real.rpow_nonneg v.coe_nonneg _)
      (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _),
    ← Real.rpow_mul v.coe_nonneg, Real.sqrt_eq_rpow]
  congr 2
  field_simp

/-- **Exponential moments** (Lemma `lem:gauss`): `E e^{tZ} = e^{v t²/2}` for `Z ∼ N(0, v)`. -/
theorem integral_exp_mul_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P) (t : ℝ) :
    ∫ ω, Real.exp (t * X ω) ∂P = Real.exp (v * t ^ 2 / 2) := by
  have h := mgf_gaussianReal hX t
  rw [zero_mul, zero_add] at h
  exact h

theorem integrable_exp_mul_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P)
    (t : ℝ) : Integrable (fun ω => Real.exp (t * X ω)) P := by
  have h := hX.integrable_comp (f := fun x : ℝ => Real.exp (t * x))
    (integrable_exp_mul_gaussianReal t)
  simpa only [Function.comp_def] using h

theorem hasLaw_neg_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P) :
    HasLaw (fun ω => -X ω) (gaussianReal 0 v) P := by
  have h := gaussianReal_neg hX
  rwa [neg_zero] at h

/-- One-sided Gaussian tail: `P[Z ≥ x] ≤ e^{-x²/(2v)}` for `x ≥ 0`. -/
theorem measureReal_le_le_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P)
    {x : ℝ} (hx : 0 ≤ x) : P.real {ω | x ≤ X ω} ≤ Real.exp (-x ^ 2 / (2 * v)) := by
  have := hX.isProbabilityMeasure
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    simp only [NNReal.coe_zero, mul_zero, div_zero, Real.exp_zero]
    exact measureReal_le_one
  have hv' : (0 : ℝ) < v := lt_of_le_of_ne v.coe_nonneg (by exact_mod_cast hv.symm)
  have h := measure_ge_le_exp_mul_mgf (X := X) (μ := P) x (t := x / v) (by positivity)
    (integrable_exp_mul_of_hasLaw_gaussianReal hX _)
  rw [mgf_gaussianReal hX, ← Real.exp_add] at h
  refine h.trans (le_of_eq (congrArg Real.exp ?_))
  field_simp
  ring

/-- **Two-sided Gaussian tail** (Lemma `lem:gauss`): `P[|Z| ≥ x] ≤ 2 e^{-x²/(2v)}` for `x ≥ 0`. -/
theorem measureReal_le_abs_le_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P)
    {x : ℝ} (hx : 0 ≤ x) : P.real {ω | x ≤ |X ω|} ≤ 2 * Real.exp (-x ^ 2 / (2 * v)) := by
  have := hX.isProbabilityMeasure
  have hsub : {ω | x ≤ |X ω|} ⊆ {ω | x ≤ X ω} ∪ {ω | x ≤ -X ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    rcases le_abs'.1 hω with h | h
    · exact Or.inr (by simp only [mem_ofPred_eq]; linarith)
    · exact Or.inl h
  calc P.real {ω | x ≤ |X ω|} ≤ P.real ({ω | x ≤ X ω} ∪ {ω | x ≤ -X ω}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | x ≤ X ω} + P.real {ω | x ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-x ^ 2 / (2 * v)) + Real.exp (-x ^ 2 / (2 * v)) :=
        add_le_add (measureReal_le_le_of_hasLaw_gaussianReal hX hx)
          (measureReal_le_le_of_hasLaw_gaussianReal (hasLaw_neg_of_hasLaw_gaussianReal hX) hx)
    _ = 2 * Real.exp (-x ^ 2 / (2 * v)) := by ring

/-- The strict two-sided tail `P[|Z| > x] ≤ 2 e^{-x²/(2v)}`, as stated in Lemma `lem:gauss`. -/
theorem measureReal_lt_abs_le_of_hasLaw_gaussianReal (hX : HasLaw X (gaussianReal 0 v) P)
    {x : ℝ} (hx : 0 ≤ x) : P.real {ω | x < |X ω|} ≤ 2 * Real.exp (-x ^ 2 / (2 * v)) := by
  have := hX.isProbabilityMeasure
  exact (measureReal_mono fun ω (hω : x < |X ω|) => (le_of_lt hω : x ≤ |X ω|)).trans
    (measureReal_le_abs_le_of_hasLaw_gaussianReal hX hx)

/-- `HasGaussianLaw` with mean zero gives the law `N(0, Var)`. -/
theorem hasLaw_of_hasGaussianLaw (hX : HasGaussianLaw X P) (h0 : ∫ ω, X ω ∂P = 0) :
    HasLaw X (gaussianReal 0 (Var[X; P]).toNNReal) P := by
  refine ⟨hX.aemeasurable, ?_⟩
  rw [hX.map_eq_gaussianReal, h0]

end OneDim

/-! ## The expected maximum of finitely many Gaussians -/

section Max

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {ι : Type*} [Fintype ι] {Z : ι → Ω → ℝ} {v : ι → ℝ≥0}

theorem aemeasurable_iSup_abs (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (v i)) P) :
    AEMeasurable (fun ω => ⨆ i, |Z i ω|) P :=
  AEMeasurable.iSup fun i => continuous_abs.measurable.comp_aemeasurable (hZ i).aemeasurable

theorem iSup_abs_le_sum (ω : Ω) : ⨆ i, |Z i ω| ≤ ∑ i, |Z i ω| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · exact ciSup_le fun i =>
      Finset.single_le_sum (f := fun i => |Z i ω|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

theorem iSup_abs_nonneg (ω : Ω) : 0 ≤ ⨆ i, |Z i ω| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · obtain ⟨i⟩ := hι
    exact (abs_nonneg _).trans (le_ciSup (Finite.bddAbove_range fun i => |Z i ω|) i)

theorem integrable_iSup_abs (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (v i)) P) :
    Integrable (fun ω => ⨆ i, |Z i ω|) P := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun i _ =>
    (integrable_of_hasLaw_gaussianReal (hZ i)).abs) (aemeasurable_iSup_abs hZ).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (iSup_abs_nonneg ω)]
  exact iSup_abs_le_sum ω

/-- The exponential-moment bound: for every `l > 0`,
`E max_i |Z_i| ≤ (log (2n) + l² s² / 2) / l`. -/
theorem integral_iSup_abs_le_of_pos [Nonempty ι]
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (v i)) P) {s : ℝ} (hv : ∀ i, (v i : ℝ) ≤ s ^ 2)
    {l : ℝ} (hl : 0 < l) :
    ∫ ω, (⨆ i, |Z i ω|) ∂P ≤ (Real.log (2 * Fintype.card ι) + l ^ 2 * s ^ 2 / 2) / l := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have := (hZ i₀).isProbabilityMeasure
  set N : ℝ := 2 * (Fintype.card ι : ℝ) with hN
  have hN0 : 0 < N := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    positivity
  set a : ℝ := Real.log N + l ^ 2 * s ^ 2 / 2 with ha
  set F : Ω → ℝ := fun ω => ∑ i, (Real.exp (l * Z i ω) + Real.exp (-l * Z i ω)) with hF
  have hint : ∀ i, Integrable (fun ω => Real.exp (l * Z i ω) + Real.exp (-l * Z i ω)) P :=
    fun i => (integrable_exp_mul_of_hasLaw_gaussianReal (hZ i) l).add
      (integrable_exp_mul_of_hasLaw_gaussianReal (hZ i) (-l))
  have hFint : Integrable F P := integrable_finsetSum _ fun i _ => hint i
  -- the pointwise bound `l M ≤ a - 1 + e^{-a} F`
  have hpt : ∀ ω, l * (⨆ i, |Z i ω|) ≤ (a - 1) + Real.exp (-a) * F ω := by
    intro ω
    obtain ⟨i₁, hi₁⟩ := exists_eq_ciSup_of_finite (f := fun i => |Z i ω|)
    rw [← hi₁]
    have h1 : Real.exp (l * |Z i₁ ω|) ≤ F ω := by
      have h2 : Real.exp (l * |Z i₁ ω|) ≤ Real.exp (l * Z i₁ ω) + Real.exp (-l * Z i₁ ω) := by
        rcases abs_cases (Z i₁ ω) with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; linarith [Real.exp_pos (-l * Z i₁ ω)]
        · rw [h, mul_neg, ← neg_mul]; linarith [Real.exp_pos (l * Z i₁ ω)]
      exact h2.trans (Finset.single_le_sum
        (f := fun i => Real.exp (l * Z i ω) + Real.exp (-l * Z i ω))
        (fun i _ => by positivity) (Finset.mem_univ i₁))
    have h3 : l * |Z i₁ ω| - a + 1 ≤ Real.exp (-a) * Real.exp (l * |Z i₁ ω|) := by
      have h := Real.add_one_le_exp (l * |Z i₁ ω| - a)
      have e : Real.exp (l * |Z i₁ ω| - a) = Real.exp (-a) * Real.exp (l * |Z i₁ ω|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rwa [e] at h
    have h4 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-a)).le
    linarith
  have hR : Integrable (fun ω => (a - 1) + Real.exp (-a) * F ω) P :=
    (integrable_const (a - 1)).add (hFint.const_mul _)
  have hmono := integral_mono ((integrable_iSup_abs hZ).const_mul l) hR hpt
  rw [integral_const_mul, integral_add (integrable_const _) (hFint.const_mul _), integral_const,
    integral_const_mul, probReal_univ, one_smul] at hmono
  have hFbound : ∫ ω, F ω ∂P ≤ N * Real.exp (l ^ 2 * s ^ 2 / 2) := by
    rw [hF, integral_finsetSum _ fun i _ => hint i]
    calc ∑ i, ∫ ω, (Real.exp (l * Z i ω) + Real.exp (-l * Z i ω)) ∂P
        ≤ ∑ _i : ι, 2 * Real.exp (l ^ 2 * s ^ 2 / 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [integral_add (integrable_exp_mul_of_hasLaw_gaussianReal (hZ i) l)
            (integrable_exp_mul_of_hasLaw_gaussianReal (hZ i) (-l)),
            integral_exp_mul_of_hasLaw_gaussianReal (hZ i),
            integral_exp_mul_of_hasLaw_gaussianReal (hZ i)]
          have hle : Real.exp ((v i : ℝ) * l ^ 2 / 2) ≤ Real.exp (l ^ 2 * s ^ 2 / 2) := by
            refine Real.exp_le_exp.2 ?_
            have := mul_le_mul_of_nonneg_left (hv i) (sq_nonneg l)
            linarith
          rw [neg_sq]
          linarith
      _ = N * Real.exp (l ^ 2 * s ^ 2 / 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
          ring
  have hexp : Real.exp (-a) * (N * Real.exp (l ^ 2 * s ^ 2 / 2)) = 1 := by
    rw [ha, neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hN0, Real.exp_neg]
    field_simp
  have hea := Real.exp_pos (-a)
  have h5 := mul_le_mul_of_nonneg_left hFbound hea.le
  rw [le_div_iff₀ hl]
  linarith

/-- **Expected maximum** (Lemma `lem:gauss`): if `Z_1, …, Z_n` are centered Gaussians with
variances at most `s²`, then `E max_i |Z_i| ≤ s √(2 log (2n))`. No independence is assumed. -/
theorem integral_iSup_abs_le (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (v i)) P) {s : ℝ}
    (hs : 0 ≤ s) (hv : ∀ i, (v i : ℝ) ≤ s ^ 2) :
    ∫ ω, (⨆ i, |Z i ω|) ∂P ≤ s * Real.sqrt (2 * Real.log (2 * Fintype.card ι)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlog : 0 < Real.log (2 * Fintype.card ι) := Real.log_pos (by linarith)
  rcases hs.lt_or_eq with hs' | hs'
  · set r : ℝ := Real.sqrt (2 * Real.log (2 * Fintype.card ι)) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hr2 : r ^ 2 = 2 * Real.log (2 * Fintype.card ι) := Real.sq_sqrt (by positivity)
    refine (integral_iSup_abs_le_of_pos hZ hv (l := r / s) (by positivity)).trans
      (le_of_eq ?_)
    field_simp
    nlinarith [hr2]
  · subst hs'
    by_contra hcon
    rw [not_le] at hcon
    rw [zero_mul] at hcon
    set m := ∫ ω, (⨆ i, |Z i ω|) ∂P with hm
    have h := integral_iSup_abs_le_of_pos hZ hv (l := 2 * Real.log (2 * Fintype.card ι) / m)
      (by positivity)
    rw [← hm] at h
    have e : (Real.log (2 * Fintype.card ι) +
        (2 * Real.log (2 * Fintype.card ι) / m) ^ 2 * 0 ^ 2 / 2) /
          (2 * Real.log (2 * Fintype.card ι) / m) = m / 2 := by
      field_simp
      ring
    rw [e] at h
    linarith

/-- The expected-maximum bound for centered Gaussians given through `HasGaussianLaw`. -/
theorem integral_iSup_abs_le_of_hasGaussianLaw (hZ : ∀ i, HasGaussianLaw (Z i) P)
    (h0 : ∀ i, ∫ ω, Z i ω ∂P = 0) {s : ℝ} (hs : 0 ≤ s) (hv : ∀ i, Var[Z i; P] ≤ s ^ 2) :
    ∫ ω, (⨆ i, |Z i ω|) ∂P ≤ s * Real.sqrt (2 * Real.log (2 * Fintype.card ι)) :=
  integral_iSup_abs_le (fun i => hasLaw_of_hasGaussianLaw (hZ i) (h0 i)) hs fun i => by
    rw [Real.coe_toNNReal _ (variance_nonneg _ _)]
    exact hv i

end Max

end GaussianLQG
