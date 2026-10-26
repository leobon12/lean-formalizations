import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Second moments of integrals of square-integrable processes (packet F2b)

Let `Y : Ω → α → ℝ` be jointly measurable with square-integrable sections `Y · u`, and let `f` be a
weight with `∫ |f(u)| ‖Y_u‖_{L²(P)} dμ(u) < ∞`. Then `X(ω) = ∫ f(u) Y(ω, u) dμ(u)` satisfies

* `E[X X'] = ∫∫ f(u) g(v) E[Y_u Z_v] dμ(u) dμ(v)` (`integral_mul_integral_eq_F2b`), and
* `E[X²] ≤ (∫ |f(u)| ‖Y_u‖_{L²(P)} dμ(u))²` (`integral_sq_integral_le_F2b`, Minkowski's integral
  inequality in `L²`), and
* `E[X] = ∫ f(u) E[Y_u] dμ(u)` (`integral_integral_eq_F2b`).

These are the Fubini steps of the planning audit MA3, Details P3 (proof 2: the variance of the
convolution field from the sphere-average covariance) and P4.1′ (increments by Minkowski).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPPAS.Gauss

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω}

/-- The `L²(P)` norm of the section `ω ↦ Y ω u`. -/
def l2SecF2b (P : Measure Ω) (Y : Ω → α → ℝ) (u : α) : ℝ :=
  √(∫ ω, Y ω u ^ 2 ∂P)

omit [MeasurableSpace α] in
lemma l2SecF2b_nonneg (P : Measure Ω) (Y : Ω → α → ℝ) (u : α) : 0 ≤ l2SecF2b P Y u :=
  Real.sqrt_nonneg _

/-- Cauchy–Schwarz in `L²(P)`. -/
lemma integral_abs_mul_le_sqrt_F2b {Y Z : Ω → ℝ} (hY : MemLp Y 2 P) (hZ : MemLp Z 2 P) :
    ∫ ω, |Y ω * Z ω| ∂P ≤ √(∫ ω, Y ω ^ 2 ∂P) * √(∫ ω, Z ω ^ 2 ∂P) := by
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hY' : MemLp (fun ω => |Y ω|) (ENNReal.ofReal 2) P := by rw [h2]; exact hY.abs
  have hZ' : MemLp (fun ω => |Z ω|) (ENNReal.ofReal 2) P := by rw [h2]; exact hZ.abs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun ω => abs_nonneg (Y ω))
    (Filter.Eventually.of_forall fun ω => abs_nonneg (Z ω)) hY' hZ'
  have hsq : ∀ x : ℝ, |x| ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [Real.rpow_two, sq_abs]
  simp only [hsq, one_div] at h
  have hs : ∀ a : ℝ, a ^ (2 : ℝ)⁻¹ = √a := fun a => by
    rw [Real.sqrt_eq_rpow, one_div]
  simp only [hs] at h
  simpa only [abs_mul] using h

/-- `E|Y| ≤ ‖Y‖_{L²}` on a probability space. -/
lemma integral_abs_le_sqrt_F2b [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    ∫ ω, |Y ω| ∂P ≤ √(∫ ω, Y ω ^ 2 ∂P) := by
  have h := integral_abs_mul_le_sqrt_F2b hY (memLp_const (1 : ℝ))
  simpa only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul, Real.sqrt_one]
    using h

variable {μ : Measure α} [SFinite μ]

omit [SFinite μ] in
/-- The section norm is measurable for a jointly measurable process. -/
lemma measurable_l2SecF2b [SFinite P] {Y : Ω → α → ℝ}
    (hY : Measurable fun q : Ω × α => Y q.1 q.2) : Measurable (l2SecF2b P Y) := by
  have hm : Measurable fun q : Ω × α => Y q.1 q.2 ^ 2 := hY.pow_const 2
  exact (hm.stronglyMeasurable.integral_prod_left' (μ := P)).measurable.sqrt

/-- The integrand `(ω, u) ↦ f(u) Y(ω, u)` is integrable on the product. -/
theorem integrable_prod_mul_F2b [IsProbabilityMeasure P] {f : α → ℝ} {Y : Ω → α → ℝ}
    (hf : Measurable f) (hY : Measurable fun q : Ω × α => Y q.1 q.2)
    (hY2 : ∀ᵐ u ∂μ, MemLp (fun ω => Y ω u) 2 P)
    (hfY : Integrable (fun u => |f u| * l2SecF2b P Y u) μ) :
    Integrable (fun q : Ω × α => f q.2 * Y q.1 q.2) (P.prod μ) := by
  have hm : Measurable fun q : Ω × α => f q.2 * Y q.1 q.2 := (hf.comp measurable_snd).mul hY
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [hY2] with u hu
    exact (hu.integrable one_le_two).const_mul _
  · refine Integrable.mono' hfY ?_ ?_
    · exact ((hm.norm.stronglyMeasurable.integral_prod_left' (μ := P))).aestronglyMeasurable
    · filter_upwards [hY2] with u hu
      have hnn : 0 ≤ ∫ ω, ‖f u * Y ω u‖ ∂P := integral_nonneg fun ω => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have he : (fun ω => ‖f u * Y ω u‖) = fun ω => |f u| * |Y ω u| := by
        funext ω
        rw [Real.norm_eq_abs, abs_mul]
      rw [he, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_F2b hu) (abs_nonneg _)

/-- Almost every section `u ↦ f(u) Y(ω, u)` is integrable. -/
theorem ae_integrable_mul_F2b [IsProbabilityMeasure P] {f : α → ℝ} {Y : Ω → α → ℝ}
    (hf : Measurable f) (hY : Measurable fun q : Ω × α => Y q.1 q.2)
    (hY2 : ∀ᵐ u ∂μ, MemLp (fun ω => Y ω u) 2 P)
    (hfY : Integrable (fun u => |f u| * l2SecF2b P Y u) μ) :
    ∀ᵐ ω ∂P, Integrable (fun u => f u * Y ω u) μ :=
  (integrable_prod_mul_F2b hf hY hY2 hfY).prod_right_ae

/-- **Fubini for means of integrals.** -/
theorem integral_integral_eq_F2b [IsProbabilityMeasure P] {f : α → ℝ} {Y : Ω → α → ℝ}
    (hf : Measurable f) (hY : Measurable fun q : Ω × α => Y q.1 q.2)
    (hY2 : ∀ᵐ u ∂μ, MemLp (fun ω => Y ω u) 2 P)
    (hfY : Integrable (fun u => |f u| * l2SecF2b P Y u) μ) :
    ∫ ω, ∫ u, f u * Y ω u ∂μ ∂P = ∫ u, f u * ∫ ω, Y ω u ∂P ∂μ := by
  have hint := integrable_prod_mul_F2b hf hY hY2 hfY
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact integral_const_mul _ _

/-- **Fubini for covariances of integrals.** -/
theorem integral_mul_integral_eq_F2b [IsProbabilityMeasure P] {f g : α → ℝ}
    {Y Z : Ω → α → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hY : Measurable fun q : Ω × α => Y q.1 q.2) (hZ : Measurable fun q : Ω × α => Z q.1 q.2)
    (hY2 : ∀ᵐ u ∂μ, MemLp (fun ω => Y ω u) 2 P) (hZ2 : ∀ᵐ u ∂μ, MemLp (fun ω => Z ω u) 2 P)
    (hfY : Integrable (fun u => |f u| * l2SecF2b P Y u) μ)
    (hgZ : Integrable (fun u => |g u| * l2SecF2b P Z u) μ) :
    ∫ ω, (∫ u, f u * Y ω u ∂μ) * (∫ v, g v * Z ω v ∂μ) ∂P =
      ∫ q, f q.1 * g q.2 * ∫ ω, Y ω q.1 * Z ω q.2 ∂P ∂(μ.prod μ) := by
  let F : Ω → α × α → ℝ := fun ω q => (f q.1 * Y ω q.1) * (g q.2 * Z ω q.2)
  have hpt : ∀ ω, (∫ u, f u * Y ω u ∂μ) * (∫ v, g v * Z ω v ∂μ) =
      ∫ q, F ω q ∂(μ.prod μ) := fun ω =>
    (integral_prod_mul (fun u => f u * Y ω u) (fun v => g v * Z ω v)).symm
  have hYc : Measurable fun x : Ω × (α × α) => Y x.1 x.2.1 :=
    hY.comp (measurable_fst.prodMk (measurable_snd.fst))
  have hZc : Measurable fun x : Ω × (α × α) => Z x.1 x.2.2 :=
    hZ.comp (measurable_fst.prodMk (measurable_snd.snd))
  have hFm : Measurable (Function.uncurry F) := by
    have hf' : Measurable fun x : Ω × (α × α) => f x.2.1 := hf.comp measurable_snd.fst
    have hg' : Measurable fun x : Ω × (α × α) => g x.2.2 := hg.comp measurable_snd.snd
    exact (hf'.mul hYc).mul (hg'.mul hZc)
  have h1 : ∀ᵐ q ∂(μ.prod μ), MemLp (fun ω => Y ω q.1) 2 P :=
    Measure.quasiMeasurePreserving_fst.ae hY2
  have h2 : ∀ᵐ q ∂(μ.prod μ), MemLp (fun ω => Z ω q.2) 2 P :=
    Measure.quasiMeasurePreserving_snd.ae hZ2
  have hbound : ∀ᵐ q ∂(μ.prod μ), ∫ ω, ‖F ω q‖ ∂P ≤
      (|f q.1| * l2SecF2b P Y q.1) * (|g q.2| * l2SecF2b P Z q.2) := by
    filter_upwards [h1, h2] with q hq1 hq2
    have hcs := integral_abs_mul_le_sqrt_F2b hq1 hq2
    have he : (fun ω => ‖F ω q‖) = fun ω => (|f q.1| * |g q.2|) * |Y ω q.1 * Z ω q.2| := by
      funext ω
      simp only [F, Real.norm_eq_abs, abs_mul]
      ring
    rw [he, integral_const_mul]
    calc |f q.1| * |g q.2| * ∫ ω, |Y ω q.1 * Z ω q.2| ∂P
        ≤ |f q.1| * |g q.2| * (l2SecF2b P Y q.1 * l2SecF2b P Z q.2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = _ := by ring
  have hFint : Integrable (Function.uncurry F) (P.prod (μ.prod μ)) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [h1, h2] with q hq1 hq2
      have hint := hq1.integrable_mul hq2
      have he : (fun ω => Function.uncurry F (ω, q)) =
          fun ω => (f q.1 * g q.2) * ((fun ω => Y ω q.1) * fun ω => Z ω q.2) ω := by
        funext ω
        simp only [Function.uncurry_apply_pair, F, Pi.mul_apply]
        ring
      rw [he]
      exact hint.const_mul _
    · refine Integrable.mono' (hfY.mul_prod hgZ) ?_ ?_
      · exact (hFm.norm.stronglyMeasurable.integral_prod_left' (μ := P)).aestronglyMeasurable
      · filter_upwards [hbound] with q hq
        have hnn : 0 ≤ ∫ ω, ‖F ω q‖ ∂P := integral_nonneg fun ω => norm_nonneg _
        show ‖∫ ω, ‖F ω q‖ ∂P‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        exact hq
  calc ∫ ω, (∫ u, f u * Y ω u ∂μ) * (∫ v, g v * Z ω v ∂μ) ∂P
      = ∫ ω, ∫ q, F ω q ∂(μ.prod μ) ∂P := by simp only [hpt]
    _ = ∫ q, ∫ ω, F ω q ∂P ∂(μ.prod μ) := integral_integral_swap hFint
    _ = ∫ q, f q.1 * g q.2 * ∫ ω, Y ω q.1 * Z ω q.2 ∂P ∂(μ.prod μ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        simp only
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only [F]
        ring

/-- **Minkowski's integral inequality in `L²`**, in the form needed for the increment bounds. -/
theorem integral_sq_integral_le_F2b [IsProbabilityMeasure P] {f : α → ℝ} {Y : Ω → α → ℝ}
    (hf : Measurable f) (hY : Measurable fun q : Ω × α => Y q.1 q.2)
    (hY2 : ∀ᵐ u ∂μ, MemLp (fun ω => Y ω u) 2 P)
    (hfY : Integrable (fun u => |f u| * l2SecF2b P Y u) μ) :
    ∫ ω, (∫ u, f u * Y ω u ∂μ) ^ 2 ∂P ≤ (∫ u, |f u| * l2SecF2b P Y u ∂μ) ^ 2 := by
  have hcov := integral_mul_integral_eq_F2b hf hf hY hY hY2 hY2 hfY hfY
  simp only [← sq] at hcov
  rw [hcov, sq, ← integral_prod_mul (μ := μ) (ν := μ)]
  have h1 : ∀ᵐ q ∂(μ.prod μ), MemLp (fun ω => Y ω q.1) 2 P :=
    Measure.quasiMeasurePreserving_fst.ae hY2
  have h2 : ∀ᵐ q ∂(μ.prod μ), MemLp (fun ω => Y ω q.2) 2 P :=
    Measure.quasiMeasurePreserving_snd.ae hY2
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hfY.mul_prod hfY) ?_
  filter_upwards [h1, h2] with q hq1 hq2
  have hcs := integral_abs_mul_le_sqrt_F2b hq1 hq2
  have habs : |∫ ω, Y ω q.1 * Y ω q.2 ∂P| ≤ l2SecF2b P Y q.1 * l2SecF2b P Y q.2 :=
    (abs_integral_le_integral_abs).trans hcs
  calc ‖f q.1 * f q.2 * ∫ ω, Y ω q.1 * Y ω q.2 ∂P‖
      = |f q.1| * |f q.2| * |∫ ω, Y ω q.1 * Y ω q.2 ∂P| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
    _ ≤ |f q.1| * |f q.2| * (l2SecF2b P Y q.1 * l2SecF2b P Y q.2) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ = |f q.1| * l2SecF2b P Y q.1 * (|f q.2| * l2SecF2b P Y q.2) := by ring

end HigherDimLFPPAS.Gauss
