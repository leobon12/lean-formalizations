import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# IL-6: the exponential (discrete Lévy) lemma

Blueprint node IL-6 of `blueprint/THM11_BLUEPRINT.md`.  Let `X` and `X² + V` be martingales,
with `X₀ = x₀`, `V₀ = v₀` deterministic, `|V| ≤ K`, `|V_{t+s} − V_t| ≤ K s`, and third-moment
control `E|X_{t+s} − X_t|³ ≤ C s^{3/2}` (`s ≤ 1`) of the increments of `X`.  Then
`E exp(i X_T − V_T/2) = exp(i x₀ − v₀/2)`.

The pathwise hypothesis `|X_{t'} − X_t| ≤ K(osc_{[t,t']}B + t' − t)` of the blueprint enters only
through the third-moment bound, which follows from it and IL-1 (`E osc³ ≤ C s^{3/2}`); we take
the moment bound as the hypothesis, which makes the lemma strictly more general.
-/

namespace QuantumZipper.ItoLite

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ≥0 m0}

/-- A martingale increment is orthogonal to `ℱ_t`-measurable multipliers. -/
theorem il6_integral_mul_increment_eq_zero {f : ℝ≥0 → Ω → ℝ} (hf : Martingale f ℱ P)
    {t t' : ℝ≥0} (htt : t ≤ t') {η : Ω → ℝ} (hη : StronglyMeasurable[ℱ t] η)
    (h1 : Integrable (η * f t') P) (h2 : Integrable (η * f t) P) :
    ∫ ω, η ω * (f t' ω - f t ω) ∂P = 0 := by
  have h3 := condExp_mul_of_stronglyMeasurable_left hη h1 (hf.integrable t')
  have h4 : P[η * f t' | ℱ t] =ᵐ[P] η * f t :=
    h3.trans ((hf.condExp_ae_eq htt).mono fun ω hω => by simp [Pi.mul_apply, hω])
  have key : ∫ ω, (η * f t') ω ∂P = ∫ ω, (η * f t) ω ∂P := by
    rw [← integral_condExp (ℱ.le t) (f := η * f t')]
    exact integral_congr_ae h4
  simp_rw [mul_sub]
  have hs := integral_sub h1 h2
  simp only [Pi.mul_apply] at hs key
  rw [hs, key, sub_self]

/-- Complex bounded multipliers, from real ones. -/
theorem il6_integral_cmul_eq_zero_of_real {t : ℝ≥0} {c : ℝ} {g : Ω → ℝ} (hg : Integrable g P)
    (H : ∀ η : Ω → ℝ, StronglyMeasurable[ℱ t] η → (∀ ω, |η ω| ≤ c) →
      ∫ ω, η ω * g ω ∂P = 0)
    {ξ : Ω → ℂ} (hξ : StronglyMeasurable[ℱ t] ξ) (hb : ∀ ω, ‖ξ ω‖ ≤ c) :
    ∫ ω, ξ ω * (g ω : ℂ) ∂P = 0 := by
  have hre_m : StronglyMeasurable[ℱ t] (fun ω => (ξ ω).re) :=
    Complex.continuous_re.comp_stronglyMeasurable hξ
  have him_m : StronglyMeasurable[ℱ t] (fun ω => (ξ ω).im) :=
    Complex.continuous_im.comp_stronglyMeasurable hξ
  have hre := H _ hre_m (fun ω => (Complex.abs_re_le_norm _).trans (hb ω))
  have him := H _ him_m (fun ω => (Complex.abs_im_le_norm _).trans (hb ω))
  have hI1 : Integrable (fun ω => (ξ ω).re * g ω) P :=
    hg.bdd_mul (c := c) (hre_m.mono (ℱ.le t)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hb ω))
  have hI2 : Integrable (fun ω => (ξ ω).im * g ω) P :=
    hg.bdd_mul (c := c) (him_m.mono (ℱ.le t)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact (Complex.abs_im_le_norm _).trans (hb ω))
  have e : (fun ω => ξ ω * (g ω : ℂ)) = fun ω =>
      (((ξ ω).re * g ω : ℝ) : ℂ) + Complex.I * (((ξ ω).im * g ω : ℝ) : ℂ) := by
    funext ω; apply Complex.ext <;> simp
  rw [e, integral_add hI1.ofReal (hI2.ofReal.const_mul _), integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, hre, him]
  simp

/-- Second-order Taylor remainder of `exp` with a bound depending only on `|Re w|`. -/
theorem il6_norm_exp_sub_taylor2_le {w : ℂ} {K : ℝ} (hw : |w.re| ≤ K) :
    ‖Complex.exp w - 1 - w - w ^ 2 / 2‖ ≤ (Real.exp K + 3) * ‖w‖ ^ 3 := by
  have hexp : 0 < Real.exp K := Real.exp_pos K
  by_cases h : ‖w‖ ≤ 1
  · have hb := Complex.exp_bound h (n := 3) (by norm_num)
    have e : ∑ m ∈ Finset.range 3, w ^ m / (m.factorial : ℂ) = 1 + w + w ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [e] at hb
    have e2 : Complex.exp w - 1 - w - w ^ 2 / 2 = Complex.exp w - (1 + w + w ^ 2 / 2) := by ring
    rw [e2]
    refine hb.trans ?_
    have : ((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℝ) * (3 : ℕ))⁻¹ ≤ Real.exp K + 3 := by
      norm_num [Nat.factorial]; linarith
    exact mul_le_mul_of_nonneg_left this (by positivity) |>.trans_eq (mul_comm _ _)
  · push Not at h
    have hn : ‖Complex.exp w‖ ≤ Real.exp K := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.2 ((le_abs_self _).trans hw)
    have h1 : 1 ≤ ‖w‖ ^ 3 := one_le_pow₀ h.le
    have h2 : ‖w‖ ≤ ‖w‖ ^ 3 := le_self_pow₀ h.le (by norm_num)
    have h3 : ‖w‖ ^ 2 ≤ ‖w‖ ^ 3 := pow_le_pow_right₀ h.le (by norm_num)
    have h4 : Real.exp K * 1 ≤ Real.exp K * ‖w‖ ^ 3 := mul_le_mul_of_nonneg_left h1 hexp.le
    have hw2 : ‖w ^ 2 / 2‖ = ‖w‖ ^ 2 / 2 := by simp [norm_pow]
    calc ‖Complex.exp w - 1 - w - w ^ 2 / 2‖
        ≤ ‖Complex.exp w‖ + ‖(1 : ℂ)‖ + ‖w‖ + ‖w ^ 2 / 2‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ (Real.exp K + 3) * ‖w‖ ^ 3 := by rw [hw2, norm_one]; nlinarith

/-- Elementary: `a s ≤ a³ + s √s` for `a ≥ 0`, `s ≥ 0`. -/
theorem il6_mul_le_cube_add (a s : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    a * s ≤ a ^ 3 + s * Real.sqrt s := by
  have hq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs
  rcases le_total a (Real.sqrt s) with h | h
  · have : a * s ≤ Real.sqrt s * s := mul_le_mul_of_nonneg_right h hs
    nlinarith [pow_nonneg ha 3]
  · have : s ≤ a * a := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this ha]

/-- The pointwise one-step error bound. -/
theorem il6_pointwise_bound {K s : ℝ} (hK : 0 ≤ K) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {d e : ℝ} (he : |e| ≤ K * s) (he2 : |e| ≤ 2 * K) {ξ : ℂ} (hξ : ‖ξ‖ ≤ Real.exp (K / 2)) :
    ‖ξ * (Complex.exp (Complex.I * d - e / 2) - 1 - (Complex.I * d - (d ^ 2 + e) / 2))‖ ≤
      Real.exp (K / 2) * ((Real.exp K + 3) * 4 * (1 + K ^ 3) + K + K ^ 2) *
        (|d| ^ 3 + s * Real.sqrt s) := by
  set w : ℂ := Complex.I * d - e / 2 with hwdef
  set a := |d|
  set q := s * Real.sqrt s
  set E := Real.exp K + 3
  have hE : 0 ≤ E := by positivity
  have ha : 0 ≤ a := abs_nonneg d
  have hq0 : 0 ≤ q := mul_nonneg hs0 (Real.sqrt_nonneg s)
  have hsq : s ≤ Real.sqrt s := by
    have := Real.sqrt_le_sqrt hs1
    rw [Real.sqrt_one] at this
    nlinarith [Real.mul_self_sqrt hs0, Real.sqrt_nonneg s]
  have F3 : s ^ 3 ≤ q := by
    have : s ^ 3 ≤ s * s := by nlinarith [mul_nonneg hs0 hs0]
    nlinarith [mul_le_mul_of_nonneg_left hsq hs0]
  have F4 : s ^ 2 ≤ q := by nlinarith [mul_le_mul_of_nonneg_left hsq hs0]
  have F5 : a * s ≤ a ^ 3 + q := il6_mul_le_cube_add a s ha hs0
  have hre : |w.re| ≤ K := by
    have : w.re = -e / 2 := by simp [hwdef]; ring
    rw [this, abs_div, abs_neg]; norm_num; linarith
  have hwn : ‖w‖ ≤ a + K * s := by
    calc ‖w‖ ≤ ‖Complex.I * (d : ℂ)‖ + ‖(e : ℂ) / 2‖ := norm_sub_le _ _
      _ = a + |e| / 2 := by simp [a]
      _ ≤ a + K * s := by nlinarith [abs_nonneg e]
  have hw3 : ‖w‖ ^ 3 ≤ 4 * (a ^ 3 + K ^ 3 * s ^ 3) := by
    have hb : 0 ≤ K * s := mul_nonneg hK hs0
    have := pow_le_pow_left₀ (norm_nonneg w) hwn 3
    refine this.trans ?_
    have : K ^ 3 * s ^ 3 = (K * s) ^ 3 := by ring
    rw [this]
    nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - K * s)), mul_nonneg ha hb]
  have hR := il6_norm_exp_sub_taylor2_le hre
  have hsplit : Complex.exp w - 1 - (Complex.I * d - (d ^ 2 + e) / 2) =
      (Complex.exp w - 1 - w - w ^ 2 / 2) + (-(Complex.I * d * e) / 2 + e ^ 2 / 8) := by
    rw [hwdef]; ring_nf; simp [Complex.I_sq]; ring
  have hcorr : ‖-(Complex.I * d * e) / 2 + (e : ℂ) ^ 2 / 8‖ ≤ a * (K * s) / 2 + K ^ 2 * s ^ 2 / 8 := by
    have he' : e ^ 2 ≤ (K * s) ^ 2 := by
      rw [← sq_abs e]; exact pow_le_pow_left₀ (abs_nonneg e) he 2
    calc ‖-(Complex.I * d * e) / 2 + (e : ℂ) ^ 2 / 8‖
        ≤ ‖-(Complex.I * d * e) / 2‖ + ‖(e : ℂ) ^ 2 / 8‖ := norm_add_le _ _
      _ = a * |e| / 2 + e ^ 2 / 8 := by
          simp [a, norm_pow, sq_abs]
      _ ≤ a * (K * s) / 2 + K ^ 2 * s ^ 2 / 8 := by
          have := mul_le_mul_of_nonneg_left he ha
          nlinarith
  have htot : ‖Complex.exp w - 1 - (Complex.I * d - (d ^ 2 + e) / 2)‖ ≤
      (E * 4 * (1 + K ^ 3) + K + K ^ 2) * (a ^ 3 + q) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have t1 : E * ‖w‖ ^ 3 ≤ E * (4 * (a ^ 3 + K ^ 3 * s ^ 3)) :=
      mul_le_mul_of_nonneg_left hw3 hE
    have t2 : E * 4 * K ^ 3 * s ^ 3 ≤ E * 4 * K ^ 3 * q :=
      mul_le_mul_of_nonneg_left F3 (by positivity)
    have t3 : K * (a * s) ≤ K * (a ^ 3 + q) := mul_le_mul_of_nonneg_left F5 hK
    have t4 : K ^ 2 * s ^ 2 ≤ K ^ 2 * q := mul_le_mul_of_nonneg_left F4 (by positivity)
    have t5 : 0 ≤ E * 4 * a ^ 3 := by positivity
    have t6 : 0 ≤ E * 4 * K ^ 3 * a ^ 3 := by positivity
    have t7 : 0 ≤ K ^ 2 * a ^ 3 := by positivity
    have t8 : 0 ≤ E * 4 * q := by positivity
    have t9 : 0 ≤ K * a ^ 3 := by positivity
    have t10 : 0 ≤ K * q := by positivity
    nlinarith
  rw [norm_mul]
  calc ‖ξ‖ * ‖Complex.exp w - 1 - (Complex.I * d - (d ^ 2 + e) / 2)‖
      ≤ Real.exp (K / 2) * ((E * 4 * (1 + K ^ 3) + K + K ^ 2) * (a ^ 3 + q)) :=
        mul_le_mul hξ htot (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- The exponential martingale candidate `exp(i X_t − V_t / 2)`. -/
noncomputable def il6ExpProc (X V : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * (X t ω : ℂ) - (V t ω : ℂ) / 2)

/-- **IL-6 (exponential / discrete Lévy lemma).** -/
theorem il6_integral_exp_eq {X V : ℝ≥0 → Ω → ℝ} {K C x₀ v₀ : ℝ} (T : ℝ≥0)
    (hX : Martingale X ℱ P) (hQ : Martingale (fun t ω => X t ω ^ 2 + V t ω) ℱ P)
    (hX0 : ∀ ω, X 0 ω = x₀) (hV0 : ∀ ω, V 0 ω = v₀)
    (hVb : ∀ t ω, |V t ω| ≤ K)
    (hVinc : ∀ (t s : ℝ≥0) ω, |V (t + s) ω - V t ω| ≤ K * s)
    (hXint : ∀ t s : ℝ≥0, Integrable (fun ω => |X (t + s) ω - X t ω| ^ 3) P)
    (hX3 : ∀ t s : ℝ≥0, s ≤ 1 →
      ∫ ω, |X (t + s) ω - X t ω| ^ 3 ∂P ≤ C * ((s : ℝ) * Real.sqrt s)) :
    ∫ ω, Complex.exp (Complex.I * (X T ω : ℂ) - (V T ω : ℂ) / 2) ∂P =
      Complex.exp (Complex.I * (x₀ : ℂ) - (v₀ : ℂ) / 2) := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  have hK : 0 ≤ K := (abs_nonneg _).trans (hVb 0 ω₀)
  -- measurability and integrability
  have hXm : ∀ t, StronglyMeasurable[ℱ t] (X t) := fun t => hX.1 t
  have hVm : ∀ t, StronglyMeasurable[ℱ t] (V t) := by
    intro t
    have := (hQ.1 t).sub ((hX.1 t).pow 2)
    convert this using 1
    funext ω; simp
  have hVi : ∀ t, Integrable (V t) P := fun t =>
    Integrable.of_bound ((hVm t).mono (ℱ.le t)).aestronglyMeasurable K
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hVb t ω)
  have hX2 : ∀ t, Integrable (fun ω => X t ω ^ 2) P := fun t =>
    ((hQ.integrable t).sub (hVi t)).congr (ae_of_all _ fun ω => by simp)
  have hXX : ∀ t t', Integrable (fun ω => X t ω * X t' ω) P := fun t t' =>
    Integrable.mono' ((hX2 t).add (hX2 t'))
      ((((hXm t).mono (ℱ.le t)).mul ((hXm t').mono (ℱ.le t'))).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        show |X t ω * X t' ω| ≤ X t ω ^ 2 + X t' ω ^ 2
        rw [abs_mul]
        nlinarith [sq_abs (X t ω), sq_abs (X t' ω), sq_nonneg (|X t ω| - |X t' ω|)])
  set M := il6ExpProc X V with hMdef
  have hMm : ∀ t, StronglyMeasurable[ℱ t] (M t) := by
    intro t
    have h1 := (hXm t).measurable
    have h2 := (hVm t).measurable
    exact (Complex.measurable_exp.comp ((measurable_const.mul
      (Complex.measurable_ofReal.comp h1)).sub
      ((Complex.measurable_ofReal.comp h2).div_const 2))).stronglyMeasurable
  have hMb : ∀ t ω, ‖M t ω‖ ≤ Real.exp (K / 2) := by
    intro t ω
    simp only [hMdef, il6ExpProc, Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 (hVb t ω)).1
    simp; linarith
  have hMi : ∀ t, Integrable (M t) P := fun t =>
    Integrable.of_bound ((hMm t).mono (ℱ.le t)).aestronglyMeasurable _
      (ae_of_all _ (hMb t))
  -- orthogonality relations for real bounded multipliers
  have hO1 : ∀ t s : ℝ≥0, ∀ η : Ω → ℝ, StronglyMeasurable[ℱ t] η →
      (∀ ω, |η ω| ≤ Real.exp (K / 2)) →
      ∫ ω, η ω * (X (t + s) ω - X t ω) ∂P = 0 := by
    intro t s η hη hb
    have hbd : ∀ᵐ ω ∂P, ‖η ω‖ ≤ Real.exp (K / 2) := ae_of_all _ fun ω => hb ω
    have hae : AEStronglyMeasurable η P := (hη.mono (ℱ.le t)).aestronglyMeasurable
    exact il6_integral_mul_increment_eq_zero hX le_self_add hη
      ((hX.integrable _).bdd_mul hae hbd) ((hX.integrable _).bdd_mul hae hbd)
  have hO2 : ∀ t s : ℝ≥0, ∀ η : Ω → ℝ, StronglyMeasurable[ℱ t] η →
      (∀ ω, |η ω| ≤ Real.exp (K / 2)) →
      ∫ ω, η ω * ((X (t + s) ω - X t ω) ^ 2 + (V (t + s) ω - V t ω)) ∂P = 0 := by
    intro t s η hη hb
    have hbd : ∀ᵐ ω ∂P, ‖η ω‖ ≤ Real.exp (K / 2) := ae_of_all _ fun ω => hb ω
    have hae : AEStronglyMeasurable η P := (hη.mono (ℱ.le t)).aestronglyMeasurable
    have hA := il6_integral_mul_increment_eq_zero hQ (le_self_add (b := s)) hη
      ((hQ.integrable _).bdd_mul hae hbd) ((hQ.integrable _).bdd_mul hae hbd)
    have hηX : StronglyMeasurable[ℱ t] (η * X t) := hη.mul (hXm t)
    have hB := il6_integral_mul_increment_eq_zero hX (le_self_add (b := s)) hηX
      (((hXX t (t + s)).bdd_mul hae hbd).congr (ae_of_all _ fun ω => by
        simp [Pi.mul_apply]; ring))
      (((hXX t t).bdd_mul hae hbd).congr (ae_of_all _ fun ω => by
        simp [Pi.mul_apply]; ring))
    have iA : Integrable (fun ω => η ω * ((X (t + s) ω ^ 2 + V (t + s) ω) -
        (X t ω ^ 2 + V t ω))) P :=
      ((hQ.integrable _).sub (hQ.integrable _)).bdd_mul hae hbd
    have iB : Integrable (fun ω => (η * X t) ω * (X (t + s) ω - X t ω)) P :=
      (((hXX t (t + s)).sub (hXX t t)).bdd_mul hae hbd).congr (ae_of_all _ fun ω => by
        simp [Pi.mul_apply]; ring)
    have e : (fun ω => η ω * ((X (t + s) ω - X t ω) ^ 2 + (V (t + s) ω - V t ω))) =
        fun ω => η ω * ((X (t + s) ω ^ 2 + V (t + s) ω) - (X t ω ^ 2 + V t ω)) -
          2 * ((η * X t) ω * (X (t + s) ω - X t ω)) := by
      funext ω; simp [Pi.mul_apply]; ring
    rw [e, integral_sub iA (iB.const_mul 2), integral_const_mul]
    beta_reduce at hA ⊢
    rw [hA, hB]; simp
  -- one step
  set B := (Real.exp K + 3) * 4 * (1 + K ^ 3) + K + K ^ 2 with hB
  have hBn : 0 ≤ B := by positivity
  have hstep : ∀ t s : ℝ≥0, s ≤ 1 →
      ‖∫ ω, M (t + s) ω ∂P - ∫ ω, M t ω ∂P‖ ≤
        Real.exp (K / 2) * B * (C + 1) * ((s : ℝ) * Real.sqrt s) := by
    intro t s hs
    have hs1 : (s : ℝ) ≤ 1 := by exact_mod_cast hs
    set d : Ω → ℝ := fun ω => X (t + s) ω - X t ω with hd
    set e : Ω → ℝ := fun ω => V (t + s) ω - V t ω with he
    have hdi : Integrable d P := (hX.integrable _).sub (hX.integrable _)
    have hd2 : Integrable (fun ω => d ω ^ 2) P := by
      have : (fun ω => d ω ^ 2) = fun ω =>
          X (t + s) ω * X (t + s) ω - 2 * (X t ω * X (t + s) ω) + X t ω * X t ω := by
        funext ω; simp [hd]; ring
      rw [this]
      exact ((hXX _ _).sub ((hXX _ _).const_mul 2)).add (hXX _ _)
    have hei : Integrable e P := (hVi _).sub (hVi _)
    have hg2 : Integrable (fun ω => d ω ^ 2 + e ω) P := hd2.add hei
    have hZ1 : ∫ ω, M t ω * (d ω : ℂ) ∂P = 0 :=
      il6_integral_cmul_eq_zero_of_real hdi (hO1 t s) (hMm t) (hMb t)
    have hZ2 : ∫ ω, M t ω * ((d ω ^ 2 + e ω : ℝ) : ℂ) ∂P = 0 :=
      il6_integral_cmul_eq_zero_of_real hg2 (hO2 t s) (hMm t) (hMb t)
    have hMae : AEStronglyMeasurable (M t) P := ((hMm t).mono (ℱ.le t)).aestronglyMeasurable
    have hMbd : ∀ᵐ ω ∂P, ‖M t ω‖ ≤ Real.exp (K / 2) := ae_of_all _ (hMb t)
    have i1 : Integrable (fun ω => M t ω * (d ω : ℂ)) P := hdi.ofReal.bdd_mul hMae hMbd
    have i2 : Integrable (fun ω => M t ω * ((d ω ^ 2 + e ω : ℝ) : ℂ)) P :=
      hg2.ofReal.bdd_mul hMae hMbd
    set R : Ω → ℂ := fun ω => M t ω * (Complex.exp (Complex.I * d ω - e ω / 2) - 1 -
      (Complex.I * d ω - (d ω ^ 2 + e ω) / 2)) with hR
    have hpt : ∀ ω, M (t + s) ω - M t ω =
        Complex.I * (M t ω * (d ω : ℂ)) - (1 / 2) * (M t ω * ((d ω ^ 2 + e ω : ℝ) : ℂ)) +
          R ω := by
      intro ω
      have hexp : M (t + s) ω = M t ω * Complex.exp (Complex.I * d ω - e ω / 2) := by
        simp only [hMdef, il6ExpProc, hd, he, ← Complex.exp_add]
        congr 1; push_cast; ring
      rw [hexp, hR]; push_cast; ring
    have iR : Integrable R P := by
      have : R = fun ω => (M (t + s) ω - M t ω) -
          (Complex.I * (M t ω * (d ω : ℂ)) - (1 / 2) * (M t ω * ((d ω ^ 2 + e ω : ℝ) : ℂ))) := by
        funext ω; rw [hpt ω]; ring
      rw [this]
      exact ((hMi _).sub (hMi _)).sub ((i1.const_mul _).sub (i2.const_mul _))
    have hdiff : ∫ ω, M (t + s) ω ∂P - ∫ ω, M t ω ∂P = ∫ ω, R ω ∂P := by
      rw [← integral_sub (hMi _) (hMi _)]
      simp_rw [hpt]
      rw [integral_add (f := fun ω => Complex.I * (M t ω * (d ω : ℂ)) -
          (1 / 2) * (M t ω * ((d ω ^ 2 + e ω : ℝ) : ℂ))) ((i1.const_mul _).sub (i2.const_mul _)) iR,
        integral_sub (f := fun ω => Complex.I * (M t ω * (d ω : ℂ)))
          (g := fun ω => (1 / 2) * (M t ω * ((d ω ^ 2 + e ω : ℝ) : ℂ)))
          (i1.const_mul _) (i2.const_mul _), integral_const_mul,
        integral_const_mul, hZ1, hZ2]
      simp
    rw [hdiff]
    have hbound : ∀ ω, ‖R ω‖ ≤ Real.exp (K / 2) * B * (|d ω| ^ 3 + s * Real.sqrt s) := by
      intro ω
      have he1 : |e ω| ≤ K * s := hVinc t s ω
      have he2 : |e ω| ≤ 2 * K := by
        have := abs_sub (V (t + s) ω) (V t ω)
        have h1 := hVb (t + s) ω; have h2 := hVb t ω
        simp only [he]; linarith
      exact il6_pointwise_bound hK s.2 hs1 he1 he2 (hMb t ω)
    have iG : Integrable (fun ω => Real.exp (K / 2) * B * (|d ω| ^ 3 + s * Real.sqrt s)) P :=
      ((hXint t s).add (integrable_const _)).const_mul _
    refine (norm_integral_le_of_norm_le iG (ae_of_all _ hbound)).trans ?_
    rw [integral_const_mul, integral_add (hXint t s) (integrable_const _), integral_const]
    have h3 := hX3 t s hs
    have hc : 0 ≤ Real.exp (K / 2) * B := by positivity
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have : ∫ ω, |d ω| ^ 3 ∂P + s * Real.sqrt s ≤ (C + 1) * (s * Real.sqrt s) := by
      simp only [hd]; linarith
    calc Real.exp (K / 2) * B * (∫ ω, |d ω| ^ 3 ∂P + s * Real.sqrt s)
        ≤ Real.exp (K / 2) * B * ((C + 1) * (s * Real.sqrt s)) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  -- telescoping and the limit
  set L := Real.exp (K / 2) * B * (C + 1)
  have hM0 : ∫ ω, M 0 ω ∂P = Complex.exp (Complex.I * (x₀ : ℂ) - (v₀ : ℂ) / 2) := by
    have : M 0 = fun _ => Complex.exp (Complex.I * (x₀ : ℂ) - (v₀ : ℂ) / 2) := by
      funext ω; simp [hMdef, il6ExpProc, hX0, hV0]
    rw [this, integral_const]; simp
  have hbnd : ∀ n : ℕ, (T : ℝ) ≤ n → 0 < n →
      ‖∫ ω, M T ω ∂P - ∫ ω, M 0 ω ∂P‖ ≤ L * T * Real.sqrt (T / n) := by
    intro n hTn hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    set s : ℝ≥0 := T / n with hs
    have hsr : (s : ℝ) = T / n := by simp [hs]
    have hs1 : s ≤ 1 := by
      rw [← NNReal.coe_le_coe, hsr, NNReal.coe_one, div_le_one (by exact_mod_cast hn)]
      exact hTn
    set tt : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) * s
    have htt : ∀ j, tt (j + 1) = tt j + s := fun j => by simp [tt]; ring
    have htn : tt n = T := by
      simp only [tt, hs]
      rw [mul_div_cancel₀]
      exact_mod_cast hn.ne'
    have htel := Finset.sum_range_sub (fun j => ∫ ω, M (tt j) ω ∂P) n
    simp only [htn, tt, Nat.cast_zero, zero_mul] at htel
    rw [← htel]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ Finset.range n, ‖∫ ω, M (((j + 1 : ℕ) : ℝ≥0) * s) ω ∂P -
          ∫ ω, M ((j : ℝ≥0) * s) ω ∂P‖
        ≤ ∑ _j ∈ Finset.range n, L * ((s : ℝ) * Real.sqrt s) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := hstep ((j : ℝ≥0) * s) s hs1
          have e : ((j + 1 : ℕ) : ℝ≥0) * s = (j : ℝ≥0) * s + s := htt j
          rw [e]; exact this
      _ = L * T * Real.sqrt (T / n) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsr]
          field_simp
  have hlim : Tendsto (fun n : ℕ => L * T * Real.sqrt (T / n)) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ))).const_mul (L * T)
    simpa using this
  have hle : ‖∫ ω, M T ω ∂P - ∫ ω, M 0 ω ∂P‖ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (max 1 ⌈(T : ℝ)⌉₊)] with n hn
    exact hbnd n ((Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn))
      (lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hn))
  have := norm_le_zero_iff.1 hle
  rw [sub_eq_zero, hM0] at this
  simpa [hMdef, il6ExpProc] using this

end QuantumZipper.ItoLite
