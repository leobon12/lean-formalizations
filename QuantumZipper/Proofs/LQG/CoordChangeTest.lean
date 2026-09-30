import QuantumZipper.Proofs.LQG.CoordChangeCompare
import QuantumZipper.Proofs.LQG.BoundaryExistenceAS

/-!
# M4-T4: convergence against one test function

For a test function `f` supported in the inner interval `S = [a, b]` and `g` with
`f = g ∘ Re ψ` on `S` (`g` continuous, compactly supported, vanishing off `Re ψ(S)`):

  a.s. `∫ f d(bdryApprox γ (coordChange (X ω) ψ Q) k) → ∫ g dν_{X ω}`
  (`ae_tendsto_integral_bdryApprox_coordChange`).

Chain of comparisons (all in `L¹(P)`, with a geometric rate in `k`), for the normalized field:
`FA` (the transformed field) → `FB` (semicircles `fc(ψ t, ψ'(t) 2^{-k})`, step 3,
`integral_abs_dA_sub_dB_le`) → `FU` (dyadic semicircles of radius `2^{j-k}` around `ψ t`, step 4,
`trl_coordChange_bound`) `= ∫ g dν_{2^{j-k}}(Z)` (substitution `u = ψ(t)`, using
`γQ/2 − γ²/4 = 1`) → `∫ g dν_Z` (M4-B3). Borel–Cantelli concludes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate Real
open scoped ENNReal NNReal

namespace QuantumZipper
namespace CoordChange

open GaussTK BdryExist TwoRadius

variable {Ω : Type*} [MeasurableSpace Ω]

theorem ae_tendsto_zero_of_summable_abs {P : Measure Ω} {D : ℕ → Ω → ℝ}
    (hD : ∀ k, Integrable (D k) P) (hs : Summable fun k => ∫ ω, |D k ω| ∂P) :
    ∀ᵐ ω ∂P, Tendsto (fun k => D k ω) atTop (𝓝 0) := by
  set f : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal |D k ω|
  have hfm : ∀ k, AEMeasurable (f k) P := fun k =>
    (continuous_abs.measurable.comp_aemeasurable (hD k).1.aemeasurable).ennreal_ofReal
  have hsum : ∫⁻ ω, ∑' k, f k ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum hfm]
    have e : ∀ k, ∫⁻ ω, f k ω ∂P = ENNReal.ofReal (∫ ω, |D k ω| ∂P) := fun k =>
      (ofReal_integral_eq_lintegral_ofReal (hD k).abs (ae_of_all _ fun ω => abs_nonneg _)).symm
    simp_rw [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun ω => abs_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hfm) hsum
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun k => f k ω) atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun k => |D k ω|) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [f, Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _)] using this
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h2

/-- Product integrability from uniform first moments on a set of finite measure. -/
theorem integrable_prod_of_bound {P : Measure Ω} [IsProbabilityMeasure P] {F : Ω × ℝ → ℝ}
    (hF : Measurable F) {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S < ∞) {B : ℝ}
    (hint : ∀ t ∈ S, Integrable (fun ω => F (ω, t)) P)
    (hb : ∀ t ∈ S, ∫ ω, |F (ω, t)| ∂P ≤ B) : Integrable F (P.prod (volume.restrict S)) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf.ne
  rw [integrable_prod_iff' hF.aestronglyMeasurable]
  refine ⟨(ae_restrict_iff' hS).2 (ae_of_all _ hint), ?_⟩
  have hm : AEStronglyMeasurable (fun t => ∫ ω, ‖F (ω, t)‖ ∂P) (volume.restrict S) :=
    (hF.norm.stronglyMeasurable.integral_prod_left' (μ := P)).aestronglyMeasurable
  refine Integrable.of_bound hm B ((ae_restrict_iff' hS).2 (ae_of_all _ fun t ht => ?_))
  rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
  simpa [Real.norm_eq_abs] using hb t ht

/-! ### The three densities -/

/-- Density of `bdryApprox` of the transformed field, normalized by `X(fc(0,R))`. -/
def dAf (X : Ω → FieldSample) (ψ : ℂ → ℂ) (γ R : ℝ) (k : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  radius k ^ (γ ^ 2 / 4) *
    exp (γ / 2 * (avgReg (coordChange (X ω) ψ (Qc γ)) k (t : ℂ) - X ω (foldedCircle 0 R)))

/-- Jacobian times the density at `fc(ψ t, ψ'(t) 2^{-k})`. -/
def dBf (X : Ω → FieldSample) (ψ : ℂ → ℂ) (γ R : ℝ) (k : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (deriv ψ t).re * ((deriv ψ t).re * radius k) ^ (γ ^ 2 / 4) *
    exp (γ / 2 * wProc X ψ R (radius k) t ω)

/-- The dyadic density at radius `2^{j-k}` around `ψ t`. -/
def dUf (X : Ω → FieldSample) (ψ : ℂ → ℂ) (a b γ R : ℝ) (j k : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  radius (k - j) ^ (γ ^ 2 / 4) * exp (γ / 2 * bU X R (k - j) (psiRe ψ a b t) ω)

theorem measurable_dAf {P : Measure Ω} {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (ψ : ℂ → ℂ) (γ R : ℝ) (k : ℕ) : Measurable (fun p : Ω × ℝ => dAf X ψ γ R k p.2 p.1) := by
  have h1 : Measurable fun p : Ω × ℝ => avgReg (coordChange (X p.1) ψ (Qc γ)) k (p.2 : ℂ) :=
    Measurable.comp (g := fun q : ℝ × Ω => avgReg (coordChange (X q.2) ψ (Qc γ)) k (q.1 : ℂ))
      (f := Prod.swap) (measurable_avgReg_coordChange hX ψ (Qc γ) k) measurable_swap
  have h2 : Measurable fun p : Ω × ℝ => X p.1 (foldedCircle 0 R) :=
    (hX.measurable_coord _).comp measurable_fst
  exact measurable_const.mul ((h1.sub h2).const_mul _).exp

theorem measurable_dBf {P : Measure Ω} {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (ψ : ℂ → ℂ) (γ R : ℝ) (k : ℕ) : Measurable (fun p : Ω × ℝ => dBf X ψ γ R k p.2 p.1) := by
  have hd : Measurable fun p : Ω × ℝ => (deriv ψ (p.2 : ℂ)).re :=
    Complex.continuous_re.measurable.comp
      ((measurable_deriv ψ).comp (Complex.continuous_ofReal.measurable.comp measurable_snd))
  have hw : Measurable fun p : Ω × ℝ => wProc X ψ R (radius k) p.2 p.1 :=
    Measurable.comp (g := fun q : ℝ × Ω => wProc X ψ R (radius k) q.1 q.2) (f := Prod.swap)
      (measurable_wProc hX ψ R (radius k)) measurable_swap
  unfold dBf
  exact Measurable.mul (Measurable.mul hd (Measurable.pow_const (Measurable.mul_const hd _) _))
    (Measurable.exp (Measurable.const_mul hw _))

namespace Data

variable {ψ : ℂ → ℂ} {a b δ m C : ℝ}

theorem measurable_dUf (h : Data ψ a b δ m C) {P : Measure Ω} {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (γ R : ℝ) (j k : ℕ) :
    Measurable (fun p : Ω × ℝ => dUf X ψ a b γ R j k p.2 p.1) := by
  have hU : Measurable (fun p : Ω × ℝ => bU X R (k - j) (psiRe ψ a b p.2) p.1) :=
    (measurable_avgReg (k - j)).comp (((measurable_zField hX R).comp measurable_fst).prodMk
      (Complex.continuous_ofReal.measurable.comp (h.measurable_psiRe.comp measurable_snd)))
  exact measurable_const.mul (hU.const_mul _).exp

theorem integral_dBf {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {γ : ℝ}
    {R : ℝ} (hR : |(ψ t).re| + 1 ≤ R) {k : ℕ} (hk : (deriv ψ t).re * radius k ≤ 1 / 4) :
    Integrable (fun ω => dBf X ψ γ R k t ω) P ∧
      ∫ ω, dBf X ψ γ R k t ω ∂P = (deriv ψ t).re * exp (γ ^ 2 / 4 * log R) := by
  have hd := h.deriv_re_pos ht
  have hr := radius_pos k
  set ρ := (deriv ψ t).re * radius k
  have hρ : 0 < ρ := mul_pos hd hr
  have hR0 : 0 < R := by linarith [abs_nonneg (ψ t).re]
  have hlaw := (hasLaw_fcPairVal hX (good_Z (ofReal_mem_Hbar (ψ t).re) hρ hR0)).congr
    (h.ae_wProc_eq hX ht R hr hk)
  rw [fcPairCov_Zself hρ (by linarith)] at hlaw
  have hv0 : 0 ≤ 2 * log R - 2 * log ρ := by
    have : log ρ ≤ 0 := log_nonpos hρ.le (by linarith)
    have : 0 ≤ log R := log_nonneg (by linarith [abs_nonneg (ψ t).re])
    linarith
  have hi := hlaw.integrable_comp (f := fun x : ℝ => exp (γ / 2 * x))
    (integrable_exp_mul_gaussianReal _)
  have hE := hlaw.integral_comp (f := fun x : ℝ => exp (γ / 2 * x)) (by fun_prop)
  rw [Function.comp_def] at hE
  have hmgf := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := (2 * log R - 2 * log ρ).toNNReal))
    (γ / 2)
  simp only [mgf] at hmgf
  refine ⟨(hi.const_mul _).congr (ae_of_all _ fun ω => rfl), ?_⟩
  unfold dBf
  rw [integral_const_mul, hE, hmgf, Real.coe_toNNReal _ hv0, rpow_def_of_pos hρ, mul_assoc,
    ← exp_add]
  congr 2; ring

theorem integral_dUf {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {γ : ℝ}
    {R : ℝ} (hR : |(ψ t).re| + 1 ≤ R) (j k : ℕ) :
    Integrable (fun ω => dUf X ψ a b γ R j k t ω) P ∧
      ∫ ω, dUf X ψ a b γ R j k t ω ∂P = exp (γ ^ 2 / 4 * log R) := by
  have hr1 := radius_pos (k - j)
  have hr1le := radius_le_one (k - j)
  have hSR : ∀ u ∈ ({(ψ t).re} : Set ℝ), |u| + 1 ≤ R := by
    intro u hu; rw [mem_singleton_iff.1 hu]; exact hR
  have hlaw := (trlHyp_field hX hSR (k - j)).lawU (ψ t).re (mem_singleton _)
  have hE := integral_exp_bU hX hSR (k - j) (mem_singleton _) (γ / 2)
  have hi := hlaw.integrable_comp (f := fun x : ℝ => exp (γ / 2 * x))
    (integrable_exp_mul_gaussianReal _)
  have hv0 : 0 ≤ 2 * log R - 2 * log (radius (k - j)) := by
    have : log (radius (k - j)) ≤ 0 := log_nonpos hr1.le hr1le
    have : 0 ≤ log R := log_nonneg (by linarith [abs_nonneg (ψ t).re])
    linarith
  unfold dUf
  rw [psiRe_eq ht]
  refine ⟨(hi.const_mul _).congr (ae_of_all _ fun ω => rfl), ?_⟩
  rw [integral_const_mul, hE, bV, Real.coe_toNNReal _ hv0, rpow_def_of_pos hr1, ← exp_add]
  congr 1; ring

/-- Step 3 in `L¹`: `E|FA − FB| ≤ M |S| Kc (2^{-k})^{1/2 − γ²/12}`. -/
theorem bound_FA_FB {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {R : ℝ} (hR : ∀ t ∈ Icc a b, |(ψ t).re| + 1 ≤ R) {j k : ℕ}
    (hj : ∀ t ∈ Icc a b, (deriv ψ t).re ≤ 2 ^ j) (hk0 : 2 * radius k ≤ r0 δ m C)
    (hk1 : 2 ^ j * radius k ≤ 1 / 4) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ t, |f t| ≤ M) :
    Integrable (fun p : Ω × ℝ => f p.2 * dAf X ψ γ R k p.2 p.1)
        (P.prod (volume.restrict (Icc a b))) ∧
      Integrable (fun p : Ω × ℝ => f p.2 * dBf X ψ γ R k p.2 p.1)
        (P.prod (volume.restrict (Icc a b))) ∧
      ∫ ω, |(∫ t in Icc a b, f t * dAf X ψ γ R k t ω) - ∫ t in Icc a b, f t * dBf X ψ γ R k t ω| ∂P
        ≤ M * volume.real (Icc a b) *
          (Kc γ R m C j * exp ((1 / 2 - γ ^ 2 / 12) * log (radius k))) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set β := Kc γ R m C j * exp ((1 / 2 - γ ^ 2 / 12) * log (radius k)) with hβ
  have hSf : volume (Icc a b) < ∞ := measure_Icc_lt_top
  have hkt : ∀ t ∈ Icc a b, (deriv ψ t).re * radius k ≤ 1 / 4 := fun t ht =>
    (mul_le_mul_of_nonneg_right (hj t ht) (radius_pos k).le).trans hk1
  have hmA := measurable_dAf hX ψ γ R k
  have hmB := measurable_dBf hX ψ γ R k
  have hcmp := fun t (ht : t ∈ Icc a b) =>
    h.integral_abs_dA_sub_dB_le hX ht hγ hγ2 (hR t ht) (hj t ht) hk0 hk1
  have hBt := fun t (ht : t ∈ Icc a b) => h.integral_dBf hX ht (γ := γ) (hR t ht) (hkt t ht)
  have hsub : ∀ t ∈ Icc a b, Integrable (fun ω => dAf X ψ γ R k t ω - dBf X ψ γ R k t ω) P := by
    intro t ht
    have hm : AEStronglyMeasurable (fun ω => dAf X ψ γ R k t ω - dBf X ψ γ R k t ω) P :=
      ((hmA.comp (measurable_prodMk_right (y := t))).sub
        (hmB.comp (measurable_prodMk_right (y := t)))).aestronglyMeasurable
    rw [← integrable_norm_iff hm]
    simpa only [Real.norm_eq_abs, dAf, dBf] using (hcmp t ht).1
  have i1 : Integrable (fun p : Ω × ℝ => f p.2 * (dAf X ψ γ R k p.2 p.1 - dBf X ψ γ R k p.2 p.1))
      (P.prod (volume.restrict (Icc a b))) := by
    refine integrable_prod_of_bound
      (F := fun p : Ω × ℝ => f p.2 * (dAf X ψ γ R k p.2 p.1 - dBf X ψ γ R k p.2 p.1))
      ((hf.comp measurable_snd).mul (hmA.sub hmB)) measurableSet_Icc
      hSf (B := M * β) (fun t ht => by exact (hsub t ht).const_mul (f t)) (fun t ht => ?_)
    simp only [abs_mul]
    rw [integral_const_mul]
    refine mul_le_mul (hM t) ?_ (integral_nonneg fun _ => abs_nonneg _) hM0
    simpa only [dAf, dBf] using (hcmp t ht).2
  have i2 : Integrable (fun p : Ω × ℝ => f p.2 * dBf X ψ γ R k p.2 p.1)
      (P.prod (volume.restrict (Icc a b))) := by
    refine integrable_prod_of_bound (F := fun p : Ω × ℝ => f p.2 * dBf X ψ γ R k p.2 p.1)
      ((hf.comp measurable_snd).mul hmB) measurableSet_Icc hSf
      (B := M * (2 ^ j * exp (γ ^ 2 / 4 * log R))) (fun t ht => by exact (hBt t ht).1.const_mul (f t))
      (fun t ht => ?_)
    have hnn : ∀ ω, 0 ≤ dBf X ψ γ R k t ω := fun ω => by
      unfold dBf
      have := h.deriv_re_pos ht
      have := radius_pos k
      positivity
    simp only [abs_mul, abs_of_nonneg (hnn _)]
    rw [integral_const_mul, (hBt t ht).2]
    refine mul_le_mul (hM t) (mul_le_mul_of_nonneg_right (hj t ht) (exp_pos _).le)
      (mul_nonneg (h.deriv_re_pos ht).le (exp_pos _).le) hM0
  have i3 : Integrable (fun p : Ω × ℝ => f p.2 * dAf X ψ γ R k p.2 p.1)
      (P.prod (volume.restrict (Icc a b))) :=
    (i1.add i2).congr (ae_of_all _ fun p => by simp only [Pi.add_apply]; ring)
  refine ⟨i3, i2, ?_⟩
  have hpath : ∀ᵐ ω ∂P, (∫ t in Icc a b, f t * dAf X ψ γ R k t ω) -
      ∫ t in Icc a b, f t * dBf X ψ γ R k t ω =
      ∫ t in Icc a b, f t * (dAf X ψ γ R k t ω - dBf X ψ γ R k t ω) := by
    filter_upwards [i3.prod_right_ae, i2.prod_right_ae] with ω h3 h2
    refine (integral_sub h3 h2).symm.trans ?_
    congr 1; funext t; ring
  have hFi : Integrable (fun ω => (∫ t in Icc a b, f t * dAf X ψ γ R k t ω) -
      ∫ t in Icc a b, f t * dBf X ψ γ R k t ω) P := by
    have := i3.integral_prod_left.sub i2.integral_prod_left
    exact this
  calc ∫ ω, |(∫ t in Icc a b, f t * dAf X ψ γ R k t ω) - ∫ t in Icc a b, f t * dBf X ψ γ R k t ω| ∂P
      ≤ ∫ ω, (∫ t in Icc a b, |f t * (dAf X ψ γ R k t ω - dBf X ψ γ R k t ω)|) ∂P := by
        refine integral_mono_ae hFi.abs i1.abs.integral_prod_left ?_
        filter_upwards [hpath] with ω hω
        rw [hω]
        exact abs_integral_le_integral_abs
    _ = ∫ t in Icc a b, ∫ ω, |f t * (dAf X ψ γ R k t ω - dBf X ψ γ R k t ω)| ∂P := by
        have := integral_integral_swap (μ := P) (ν := volume.restrict (Icc a b))
          (f := fun ω t => |f t * (dAf X ψ γ R k t ω - dBf X ψ γ R k t ω)|) i1.abs
        exact this
    _ ≤ ∫ _t in Icc a b, M * β := by
        refine setIntegral_mono_on ?_ (integrable_const _) measurableSet_Icc (fun t ht => ?_)
        · exact i1.abs.integral_prod_right
        · simp only [abs_mul]
          rw [integral_const_mul]
          refine mul_le_mul (hM t) ?_ (integral_nonneg fun _ => abs_nonneg _) hM0
          simpa only [dAf, dBf] using (hcmp t ht).2
    _ = M * volume.real (Icc a b) * β := by
        rw [setIntegral_const, smul_eq_mul]; ring

/-- Step 4 in `L¹`: `E|FB − FU| ≤` the two-radius bound. -/
theorem bound_FB_FU {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {R : ℝ} (hR : ∀ t ∈ Icc a b, |(ψ t).re| + 1 ≤ R) {j k : ℕ} (hjk : j ≤ k)
    (hj : ∀ t ∈ Icc a b, (deriv ψ t).re ≤ 2 ^ j) (hk1 : 2 ^ j * radius k ≤ 1 / 4)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ t, |f t| ≤ M)
    (hfS : ∀ t ∉ Icc a b, f t = 0)
    (i2 : Integrable (fun p : Ω × ℝ => f p.2 * dBf X ψ γ R k p.2 p.1)
      (P.prod (volume.restrict (Icc a b)))) :
    Integrable (fun p : Ω × ℝ => f p.2 * (deriv ψ p.2).re * dUf X ψ a b γ R j k p.2 p.1)
        (P.prod (volume.restrict (Icc a b))) ∧
      ∫ ω, |(∫ t in Icc a b, f t * dBf X ψ γ R k t ω) -
          ∫ t in Icc a b, f t * (deriv ψ t).re * dUf X ψ a b γ R j k t ω| ∂P
        ≤ √((M * 2 ^ j) ^ 2 * ((1 + exp (γ ^ 2 / 4 * (2 * log (2 ^ j / m)))) *
            (exp ((γ - max 0 ((3 * γ - 2) / 4)) ^ 2 * (2 * log R) / 2) *
            exp ((γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2) * log (1 / radius (k - j))))) *
            (2 * (2 * radius (k - j) / m) * volume.real (Icc a b)))
        + M * 2 ^ j * (2 * (exp ((γ / 2 + (2 - γ) / 4) ^ 2 * (2 * log R) / 2) *
            exp (-((2 - γ) ^ 2 / 16) * log (1 / radius (k - j))))) * volume.real (Icc a b) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hSf : volume (Icc a b) < ∞ := measure_Icc_lt_top
  have hd : Measurable fun t : ℝ => (deriv ψ t).re :=
    Complex.continuous_re.measurable.comp ((measurable_deriv ψ).comp
      Complex.continuous_ofReal.measurable)
  have hf' : Measurable fun t => f t * (deriv ψ t).re := hf.mul hd
  have hM' : ∀ t, |f t * (deriv ψ t).re| ≤ M * 2 ^ j := by
    intro t
    by_cases ht : t ∈ Icc a b
    · rw [abs_mul, abs_of_pos (h.deriv_re_pos ht)]
      exact mul_le_mul (hM t) (hj t ht) (h.deriv_re_pos ht).le hM0
    · rw [hfS t ht, zero_mul, abs_zero]; positivity
  have hmU := h.measurable_dUf hX γ R j k
  have i4 : Integrable (fun p : Ω × ℝ => f p.2 * (deriv ψ p.2).re * dUf X ψ a b γ R j k p.2 p.1)
      (P.prod (volume.restrict (Icc a b))) := by
    refine integrable_prod_of_bound
      (F := fun p : Ω × ℝ => f p.2 * (deriv ψ p.2).re * dUf X ψ a b γ R j k p.2 p.1)
      (((hf.comp measurable_snd).mul (hd.comp measurable_snd)).mul
      hmU) measurableSet_Icc hSf (B := M * 2 ^ j * exp (γ ^ 2 / 4 * log R))
      (fun t ht => by exact ((h.integral_dUf hX ht (γ := γ) (hR t ht) j k).1.const_mul
        (f t * (deriv ψ t).re))) (fun t ht => ?_)
    have hnn : ∀ ω, 0 ≤ dUf X ψ a b γ R j k t ω := fun ω => by
      unfold dUf; have := radius_pos (k - j); positivity
    simp only [abs_mul, abs_of_nonneg (hnn _)]
    rw [integral_const_mul, (h.integral_dUf hX ht (γ := γ) (hR t ht) j k).2, ← abs_mul]
    exact mul_le_mul_of_nonneg_right (hM' t) (exp_pos _).le
  refine ⟨i4, ?_⟩
  have htrl := h.trl_coordChange_bound hX hγ hγ2 hR hjk hj hk1 hf' hM'
  refine le_trans (le_of_eq ?_) htrl
  refine integral_congr_ae ?_
  filter_upwards [i2.prod_right_ae, i4.prod_right_ae] with ω h2 h4
  rw [← integral_sub h2 h4, ← abs_neg, ← integral_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  simp only [dBf, dUf]
  ring

theorem log_radius (k : ℕ) : log (radius k) = -(k * log 2) := by
  have := log_one_div_radius k
  rw [one_div, log_inv] at this; linarith

theorem radius_eq_exp (k : ℕ) : radius k = exp (-(k * log 2)) := by
  rw [← log_radius, exp_log (radius_pos k)]

/-- Massaging the two-radius bound into `K · e^{-β L}`. -/
theorem trl_rate_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {c₁ c₂ L : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hL : 0 ≤ L) :
    √(c₁ * exp ((γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2) * L) * exp (-L)) +
        c₂ * exp (-((2 - γ) ^ 2 / 16) * L)
      ≤ (√c₁ + c₂) * exp (-(bdryRate γ * L)) := by
  have he1 := bdryRate_e1_pos hγ hγ2
  have hb1 : bdryRate γ ≤ (1 - γ ^ 2 / 2 + (max 0 ((3 * γ - 2) / 4)) ^ 2) / 2 := min_le_left _ _
  have hb2 : bdryRate γ ≤ (2 - γ) ^ 2 / 16 := min_le_right _ _
  have e : c₁ * exp ((γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2) * L) * exp (-L) =
      c₁ * exp (-(1 - γ ^ 2 / 2 + (max 0 ((3 * γ - 2) / 4)) ^ 2) / 2 * L) ^ 2 := by
    rw [mul_assoc, ← exp_add, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  rw [e, Real.sqrt_mul hc₁, Real.sqrt_sq (exp_pos _).le]
  have t1 : √c₁ * exp (-(1 - γ ^ 2 / 2 + (max 0 ((3 * γ - 2) / 4)) ^ 2) / 2 * L) ≤
      √c₁ * exp (-(bdryRate γ * L)) :=
    mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) (Real.sqrt_nonneg _)
  have t2 : c₂ * exp (-((2 - γ) ^ 2 / 16) * L) ≤ c₂ * exp (-(bdryRate γ * L)) :=
    mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) hc₂
  linarith

/-- The scales used in M4-T4: a normalization radius `R`, a dyadic bound `2^j ≥ ψ'` and a
starting level `k₀`. -/
theorem exists_scales (h : Data ψ a b δ m C) (hab : a ≤ b) :
    ∃ (R : ℝ) (j k₀ : ℕ), (∀ t ∈ Icc a b, |(ψ t).re| + 1 ≤ R) ∧
      (∀ u ∈ (fun t : ℝ => (ψ t).re) '' Icc a b, |u| + 1 ≤ R) ∧
      (∀ t ∈ Icc a b, (deriv ψ t).re ≤ 2 ^ j) ∧
      ∀ k, k₀ ≤ k → 2 * radius k ≤ r0 δ m C ∧ 2 ^ j * radius k ≤ 1 / 4 ∧ j ≤ k := by
  have hS'c : IsCompact ((fun t : ℝ => (ψ t).re) '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn h.continuousOn_re_psi
  obtain ⟨B, hB⟩ := hS'c.isBounded.exists_norm_le
  have hSR' : ∀ u ∈ (fun t : ℝ => (ψ t).re) '' Icc a b, |u| + 1 ≤ max B 0 + 1 := fun u hu => by
    have := hB u hu; rw [Real.norm_eq_abs] at this; linarith [le_max_left B 0]
  have hdc : ContinuousOn (fun t : ℝ => (deriv ψ t).re) (Icc a b) := fun t ht =>
    (h.continuousAt_re_deriv ht).continuousWithinAt
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc
  obtain ⟨j, hjD⟩ := pow_unbounded_of_one_lt D (by norm_num : (1 : ℝ) < 2)
  have hpos : 0 < min (r0 δ m C / 2) (1 / (4 * 2 ^ j)) :=
    lt_min (by linarith [h.r0_pos (t := a) ⟨le_rfl, hab⟩]) (by positivity)
  have hrad : Tendsto radius atTop (𝓝 0) := by
    have e : radius = fun k : ℕ => (2 : ℝ)⁻¹ ^ k := rfl
    rw [e]; exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 (hrad.eventually (gt_mem_nhds hpos))
  refine ⟨max B 0 + 1, j, max k₁ j, fun t ht => hSR' _ (mem_image_of_mem _ ht), hSR',
    fun t ht => (le_abs_self _).trans ((show |(deriv ψ t).re| ≤ D by
      simpa [Real.norm_eq_abs] using hD t ht).trans hjD.le),
    fun k hk => ⟨?_, ?_, le_trans (le_max_right _ _) hk⟩⟩
  · have := (hk₁ k (le_trans (le_max_left _ _) hk)).le.trans (min_le_left _ _); linarith
  · have h1 := (hk₁ k (le_trans (le_max_left _ _) hk)).le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith

/-- **Convergence against one test function** (M4-T4). -/
theorem ae_tendsto_integral_bdryApprox_coordChange {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) (hab : a ≤ b)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {f g : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ t, |f t| ≤ M) (hfS : ∀ t ∉ Icc a b, f t = 0) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgS : ∀ u ∉ (fun t : ℝ => (ψ t).re) '' Icc a b, g u = 0)
    (hfg : ∀ t ∈ Icc a b, f t = g (ψ t).re) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ t, f t ∂(bdryApprox γ (coordChange (X ω) ψ (Qc γ)) k)) atTop
      (𝓝 (∫ u, g u ∂(qBoundaryMeasure γ (X ω)))) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hm := h.mpos
  have hC := h.C_nonneg (t := a) ⟨le_rfl, hab⟩
  have hSpc : IsCompact ((fun t : ℝ => (ψ t).re) '' Icc a b) := isCompact_Icc.image_of_continuousOn h.continuousOn_re_psi
  have hSpm : MeasurableSet ((fun t : ℝ => (ψ t).re) '' Icc a b) := hSpc.isClosed.measurableSet
  obtain ⟨R, j, k₀, hR, hSR', hj, hscale⟩ := h.exists_scales hab
  have hk0 : ∀ k, k₀ ≤ k → 2 * radius k ≤ r0 δ m C := fun k hk => (hscale k hk).1
  have hk1 : ∀ k, k₀ ≤ k → 2 ^ j * radius k ≤ 1 / 4 := fun k hk => (hscale k hk).2.1
  have hjk : ∀ k, k₀ ≤ k → j ≤ k := fun k hk => (hscale k hk).2.2
  -- M4-B3 for the normalized field
  obtain ⟨CB, hCB0, hCB⟩ := integral_abs_bdryApprox_sub_qBoundaryMeasure_le hX hγ hγ2 hSpm
    hSpc.measure_lt_top hSR' hg hgc hgS
  -- the substitution `u = ψ t`
  have hinj : InjOn (fun t : ℝ => (ψ t).re) (Icc a b) := by
    intro t ht u hu htu
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := h.psi_re_sub_ge ht hu hlt.le; simp only at htu; nlinarith
    · have := h.psi_re_sub_ge hu ht hlt.le; simp only at htu; nlinarith
  have hsubst : ∀ k ω, ∫ t in (Icc a b), f t * (deriv ψ t).re * dUf X ψ a b γ R j k t ω =
      ∫ u, g u ∂(bdryApprox γ (zField X R ω) (k - j)) := by
    intro k ω
    rw [integral_bdryApprox_zField γ R (k - j) hSpm hgS ω,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
        (fun t ht => (h.hasDerivAt_re_psi ht).hasDerivWithinAt) hinj]
    refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    simp only [dUf, bDens, smul_eq_mul]
    rw [abs_of_pos (h.deriv_re_pos ht), psiRe_eq ht, hfg t ht]
    ring
  -- the additive constant
  have hI2 : ∀ k ω, ∫ t, f t ∂(bdryApprox γ (coordChange (X ω) ψ (Qc γ)) k) =
      exp (γ / 2 * X ω (foldedCircle 0 R)) * ∫ t in (Icc a b), f t * dAf X ψ γ R k t ω := by
    intro k ω
    rw [integral_bdryApprox_eq γ _ k measurableSet_Icc hfS, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc (fun t _ => ?_)
    simp only [dAf]
    rw [mul_sub, exp_sub]
    field_simp
    try ring
  have hI3 : ∀ᵐ ω ∂P, ∫ u, g u ∂(qBoundaryMeasure γ (X ω)) =
      exp (γ / 2 * X ω (foldedCircle 0 R)) *
        ∫ u, g u ∂(qBoundaryMeasure γ (zField X R ω)) := by
    filter_upwards [ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2,
      ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R, ae_bdryApprox_eq_smul hX γ R]
      with ω h1 h2 h3
    have t1 := h1.2 g hg hgc
    have t2 := (h2.2 g hg hgc).const_mul (exp (γ / 2 * X ω (foldedCircle 0 R)))
    have e : ∀ k, ∫ u, g u ∂(bdryApprox γ (X ω) k) = exp (γ / 2 * X ω (foldedCircle 0 R)) *
        ∫ u, g u ∂(bdryApprox γ (zField X R ω) k) := by
      intro k
      rw [h3 k, integral_smul_measure, ENNReal.toReal_ofReal (exp_pos _).le, smul_eq_mul]
    simp_rw [e] at t1
    exact tendsto_nhds_unique t1 t2
  -- the `L¹` bound at each scale
  set FA : ℕ → Ω → ℝ := fun k ω => ∫ t in (Icc a b), f t * dAf X ψ γ R k t ω with hFA
  set FC : Ω → ℝ := fun ω => ∫ u, g u ∂(qBoundaryMeasure γ (zField X R ω)) with hFC
  have hFCi : Integrable FC P :=
    (tendsto_integral_bdryApprox hX hγ hγ2 hSpm hSpc.measure_lt_top hSR' hg hgc hgS).1
  have hvol0 : 0 ≤ volume.real (Icc a b) := measureReal_nonneg
  have hKc : 0 ≤ Kc γ R m C j := by
    have := M4_nonneg
    have := rpow_nonneg M4_nonneg (1 / 4 : ℝ)
    unfold Kc; positivity
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = (M * 2 ^ j) ^ 2 * ((1 + exp (γ ^ 2 / 4 * (2 * log (2 ^ j / m)))) *
      exp ((γ - max 0 ((3 * γ - 2) / 4)) ^ 2 * (2 * log R) / 2)) * (2 * (2 / m) * volume.real (Icc a b)) :=
    ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ, c = M * 2 ^ j *
      (2 * exp ((γ / 2 + (2 - γ) / 4) ^ 2 * (2 * log R) / 2)) * volume.real (Icc a b) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  have hβ0 : 0 < bdryRate γ := bdryRate_pos hγ hγ2
  have hβ₁0 : 0 < 1 / 2 - γ ^ 2 / 12 := by nlinarith
  have key : ∀ k, k₀ ≤ k → Integrable (fun ω => FA k ω - FC ω) P ∧
      ∫ ω, |FA k ω - FC ω| ∂P ≤
        M * volume.real (Icc a b) * Kc γ R m C j * exp (-((1 / 2 - γ ^ 2 / 12) * (k * log 2))) +
        ((√c₁ + c₂) + CB) * exp (-(bdryRate γ * ((k - j : ℕ) * log 2))) := by
    intro k hk
    obtain ⟨i3, i2, b1⟩ := h.bound_FA_FB hX hγ hγ2 hR hj (hk0 k hk) (hk1 k hk) hf hM
    obtain ⟨i4, b2⟩ := h.bound_FB_FU hX hγ hγ2 hR (hjk k hk) hj (hk1 k hk) hf hM hfS i2
    obtain ⟨i5, b3⟩ := hCB (k - j)
    have iA := i3.integral_prod_left
    have iB := i2.integral_prod_left
    have iU := i4.integral_prod_left
    have hFAi : Integrable (FA k) P := iA
    refine ⟨hFAi.sub hFCi, ?_⟩
    have hpt : ∀ ω, |FA k ω - FC ω| ≤
        |(∫ t in (Icc a b), f t * dAf X ψ γ R k t ω) - ∫ t in (Icc a b), f t * dBf X ψ γ R k t ω| +
        |(∫ t in (Icc a b), f t * dBf X ψ γ R k t ω) -
          ∫ t in (Icc a b), f t * (deriv ψ t).re * dUf X ψ a b γ R j k t ω| +
        |∫ u, g u ∂(bdryApprox γ (zField X R ω) (k - j)) -
          ∫ u, g u ∂(qBoundaryMeasure γ (zField X R ω))| := by
      intro ω
      rw [← hsubst k ω]
      simp only [hFA, hFC]
      have e : (∫ t in (Icc a b), f t * dAf X ψ γ R k t ω) - ∫ u, g u ∂(qBoundaryMeasure γ (zField X R ω)) =
          ((∫ t in (Icc a b), f t * dAf X ψ γ R k t ω) - ∫ t in (Icc a b), f t * dBf X ψ γ R k t ω) +
          ((∫ t in (Icc a b), f t * dBf X ψ γ R k t ω) -
            ∫ t in (Icc a b), f t * (deriv ψ t).re * dUf X ψ a b γ R j k t ω) +
          ((∫ t in (Icc a b), f t * (deriv ψ t).re * dUf X ψ a b γ R j k t ω) -
            ∫ u, g u ∂(qBoundaryMeasure γ (zField X R ω))) := by ring
      rw [e]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hint1 : Integrable (fun ω => |(∫ t in (Icc a b), f t * dAf X ψ γ R k t ω) -
        ∫ t in (Icc a b), f t * dBf X ψ γ R k t ω|) P := (iA.sub iB).abs
    have hint2 : Integrable (fun ω => |(∫ t in (Icc a b), f t * dBf X ψ γ R k t ω) -
        ∫ t in (Icc a b), f t * (deriv ψ t).re * dUf X ψ a b γ R j k t ω|) P := (iB.sub iU).abs
    have hint3 := i5.abs
    have hL0 : 0 ≤ log (1 / radius (k - j)) := by rw [log_one_div_radius]; positivity
    have hr1 : exp (-log (1 / radius (k - j))) = radius (k - j) := by
      rw [log_one_div_radius, radius_eq_exp]
    have hT := trl_rate_le hγ hγ2 hc₁0 hc₂0 hL0
    have b2' : ∫ ω, |(∫ t in (Icc a b), f t * dBf X ψ γ R k t ω) -
        ∫ t in (Icc a b), f t * (deriv ψ t).re * dUf X ψ a b γ R j k t ω| ∂P ≤
        (√c₁ + c₂) * exp (-(bdryRate γ * log (1 / radius (k - j)))) := by
      refine b2.trans (le_trans (le_of_eq ?_) hT)
      congr 1
      · congr 1
        rw [hc₁, hr1]; ring
      · rw [hc₂]; ring
    calc ∫ ω, |FA k ω - FC ω| ∂P ≤ ∫ ω, (|(∫ t in (Icc a b), f t * dAf X ψ γ R k t ω) -
          ∫ t in (Icc a b), f t * dBf X ψ γ R k t ω| +
          |(∫ t in (Icc a b), f t * dBf X ψ γ R k t ω) -
            ∫ t in (Icc a b), f t * (deriv ψ t).re * dUf X ψ a b γ R j k t ω| +
          |∫ u, g u ∂(bdryApprox γ (zField X R ω) (k - j)) -
            ∫ u, g u ∂(qBoundaryMeasure γ (zField X R ω))|) ∂P :=
          integral_mono (hFAi.sub hFCi).abs ((hint1.add hint2).add hint3) hpt
      _ = (∫ ω, |(∫ t in (Icc a b), f t * dAf X ψ γ R k t ω) - ∫ t in (Icc a b), f t * dBf X ψ γ R k t ω| ∂P) +
          (∫ ω, |(∫ t in (Icc a b), f t * dBf X ψ γ R k t ω) -
            ∫ t in (Icc a b), f t * (deriv ψ t).re * dUf X ψ a b γ R j k t ω| ∂P) +
          ∫ ω, |∫ u, g u ∂(bdryApprox γ (zField X R ω) (k - j)) -
            ∫ u, g u ∂(qBoundaryMeasure γ (zField X R ω))| ∂P := by
          have e1 := integral_add (hint1.add hint2) hint3
          have e2 := integral_add hint1 hint2
          simp only [Pi.add_apply] at e1 e2
          rw [e1, e2]
      _ ≤ M * volume.real (Icc a b) * (Kc γ R m C j * exp ((1 / 2 - γ ^ 2 / 12) * log (radius k))) +
          (√c₁ + c₂) * exp (-(bdryRate γ * log (1 / radius (k - j)))) +
          CB * exp (-bdryRate γ * ((k - j : ℕ) * log 2)) :=
          add_le_add (add_le_add b1 b2') b3
      _ = M * volume.real (Icc a b) * Kc γ R m C j * exp (-((1 / 2 - γ ^ 2 / 12) * (k * log 2))) +
          ((√c₁ + c₂) + CB) * exp (-(bdryRate γ * ((k - j : ℕ) * log 2))) := by
          rw [log_radius, log_one_div_radius]
          simp only [neg_mul, mul_neg]
          ring
  -- summability and Borel–Cantelli
  have hjk0 : j ≤ k₀ := hjk k₀ le_rfl
  have hsum : Summable fun n => ∫ ω, |FA (n + k₀) ω - FC ω| ∂P := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun ω => abs_nonneg _)
      (fun n => (key (n + k₀) (by omega)).2) ?_
    have g1 : Summable fun n : ℕ =>
        exp (-((1 / 2 - γ ^ 2 / 12) * (((n + k₀ : ℕ) : ℝ) * log 2))) := by
      have e : ∀ n : ℕ, exp (-((1 / 2 - γ ^ 2 / 12) * (((n + k₀ : ℕ) : ℝ) * log 2))) =
          exp (-((1 / 2 - γ ^ 2 / 12) * (k₀ * log 2))) *
            exp (-((1 / 2 - γ ^ 2 / 12) * log 2)) ^ n := by
        intro n; rw [← exp_nat_mul, ← exp_add]; push_cast; ring_nf
      simp_rw [e]
      exact (summable_geometric_of_lt_one (exp_pos _).le
        (Real.exp_lt_one_iff.2 (by have := log_pos one_lt_two; nlinarith))).mul_left _
    have g2 : Summable fun n : ℕ =>
        exp (-(bdryRate γ * (((n + k₀ - j : ℕ) : ℝ) * log 2))) := by
      have e : ∀ n : ℕ, exp (-(bdryRate γ * (((n + k₀ - j : ℕ) : ℝ) * log 2))) =
          exp (-(bdryRate γ * ((k₀ - j : ℕ) * log 2))) * exp (-(bdryRate γ * log 2)) ^ n := by
        intro n
        rw [show n + k₀ - j = n + (k₀ - j) by omega, ← exp_nat_mul, ← exp_add]
        push_cast; ring_nf
      simp_rw [e]
      exact (summable_geometric_of_lt_one (exp_pos _).le
        (Real.exp_lt_one_iff.2 (by have := log_pos one_lt_two; nlinarith))).mul_left _
    exact (g1.mul_left _).add (g2.mul_left _)
  have hBC := ae_tendsto_zero_of_summable_abs (fun n => (key (n + k₀) (by omega)).1) hsum
  filter_upwards [hBC, hI3] with ω h1 h3
  rw [h3]
  have h4 : Tendsto (fun k => FA k ω) atTop (𝓝 (FC ω)) := by
    rw [← tendsto_add_atTop_iff_nat k₀]
    have := h1.add_const (FC ω)
    simp only [sub_add_cancel, zero_add] at this
    exact this
  simp_rw [hI2]
  exact h4.const_mul _

end Data

end CoordChange
end QuantumZipper
