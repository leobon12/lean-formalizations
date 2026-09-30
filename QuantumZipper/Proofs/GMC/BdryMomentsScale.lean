import QuantumZipper.Proofs.LQG.FractionalMoments
import QuantumZipper.Proofs.GMC.BdryMomentsSup

/-!
# GMC-MOMENTS (2): boundary GMC moments of order `p > 1` with the supremum over levels, and the
# multifractal scaling bound, from a unit-scale uniform `q`-th moment (`q > p`)

Field and normalization (decision D37). Everything is stated for the **gauge-pinned** field
`Z = zField X R = X − X(fc(0,R))` (value `0` at `foldedCircle 0 R`), exactly as in
`FracMom` (M4-P3). The only analytic input, `InnerMomentBound`, concerns the rescaled *inner*
masses `innerMass γ X t δ k`, which are functions of the differences `X(fc(·,·)) − X(fc(t,δ))`
only, so no additive-constant issue arises there.

Main results (for `0 < γ < 2`, `1 ≤ p < q`, `S = bI t δ = [t − δ/2, t + δ/2]`, `|t| + δ ≤ R`,
`2·2^{-k} < δ`), assuming the unit-scale uniform `q`-th moment
`InnerMomentBound γ q X P A`: `E[W_k^q] ≤ A δ^q` for all `t, δ, k` (`W_k` the rescaled inner
mass of `S`, which has `E W_k = δ`):
* `lintegral_iSup_bdryApprox_rpow_le_of_moment`:
  `E (sup_m ν_{2^{-(k+m)}}(S))^p ≤ δ^{pγ²/4} e^{(2 log R − 2 log δ)(pγ/2)²/2} · δ^p · K`,
  with `K = supMomConst p q A (cInc γ) 2^{-β}` finite;
* `lintegral_qBoundaryMeasure_rpow_le_of_moment`: the same for the limit measure of `(t−δ/2,t+δ/2)`;
* `momentDyadic_of_innerMoment`: for `δ = 4·2^{-n}`,
  `E (sup_{k ≥ n} ν_{2^{-k}}(S_n))^p ≤ C 2^{-n(p(1+γ²/4) − p²γ²/4)}` (and for the limit measure):
  the boundary multifractal spectrum `ζ(p) = p(1+γ²/4) − p²γ²/4` (Kahane 1985; Rhodes–Vargas,
  *Gaussian multiplicative chaos and applications: a review*, arXiv:1305.6221, §2–3, moments and
  multifractality of GMC; here in its boundary form with `γ/2` in the exponent);
* `momentDyadic_of_innerMomentStmt`: the same from the law-level statement `InnerMomentStmt γ q`.

Proof: exactly the route of `FracMom.lintegral_iSup_bdryApprox_rpow_le` (M4-P3(b)), i.e. the exact
scaling decomposition `ν_{2^{-k}}(S) = e^{(γ/2)Ω} δ^{γ²/4} W_k` with `Ω` Gaussian of variance
`2 log(R/δ)` independent of the inner field (`ae_bdryApprox_eq_omega_mul`,
`indepFun_omega_innerSample`), but with the Jensen step (valid only for `p ≤ 1`) replaced by
`BdryMomentsSup.lintegral_iSup_rpow_le_supMomConst` applied to the normalized masses `W_{k+m}/δ`:
uniform `q`-th moments from `InnerMomentBound`, geometric `L¹` increments from the two-radius
lemma `FracMom.integral_abs_innerMass_step_le`. Own adaptation of the repository's p ≤ 1 argument.

**Open input** `InnerMomentBound` / `InnerMomentStmt γ q` (true for `q < 4/γ²`, by the standard
GMC moment theory: Kahane 1985; Rhodes–Vargas review, Thm 2.11 for the bulk analogue). Planned
proof (not done here): Palm/Cameron–Martin at level `k` (`PalmFormula.palm_levelK`) turns
`E[W^q] = E[W · W^{q−1}]` into `∫_S E[(W^{(x)})^{q−1}] dx`, where the field is shifted by
`(γ/2) Cov(·, Z(fc(x,2^{-k})))`, so `W^{(x)} ≲ ∫ max(|x−y|, 2^{-k})^{−γ²/2} W(dy)`; for
`q − 1 ≤ 1`, subadditivity over dyadic annuli around `x` and the fractional bound of
`FracMom.fracMoment_dyadic` (exponent `ζ(q−1)`) give a series `Σ_j 2^{j(q−1)(γ²/2) − jζ(q−1)}`,
convergent iff `q < 4/γ²`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace GMCMoments

open FracMom BdryExist

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The normalized inner masses `W_{k+m}/δ`. -/
def nMass (γ : ℝ) (X : Ω → FieldSample) (t δ : ℝ) (k m : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal δ⁻¹ * innerMass γ X t δ (k + m) ω

/-- **Open analytic input (unit-scale uniform `q`-th moment).** For every centre `t`, scale
`δ > 0` and level `k` with `2·2^{-k} < δ`, the rescaled inner mass of `[t − δ/2, t + δ/2]`
(`E W_k = δ`) satisfies `E[W_k^q] ≤ A δ^q`. -/
def InnerMomentBound (γ q : ℝ) (X : Ω → FieldSample) (P : Measure Ω) (A : ℝ≥0∞) : Prop :=
  ∀ (t δ : ℝ) (k : ℕ), 0 < δ → 2 * radius k < δ →
    ∫⁻ ω, innerMass γ X t δ k ω ^ q ∂P ≤ A * ENNReal.ofReal δ ^ q

/-- The law-level form of `InnerMomentBound`: one finite constant for every free field. -/
def InnerMomentStmt (γ q : ℝ) : Prop :=
  ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P → InnerMomentBound γ q X P A

theorem lintegral_nMass_rpow_le {γ q : ℝ} {A : ℝ≥0∞} (hq : 0 ≤ q)
    (hmom : InnerMomentBound γ q X P A) {t δ : ℝ} (hδ : 0 < δ) {k : ℕ}
    (hk : 2 * radius k < δ) (m : ℕ) :
    ∫⁻ ω, nMass γ X t δ k m ω ^ q ∂P ≤ A := by
  have hkm : 2 * radius (k + m) < δ := lt_of_le_of_lt (by linarith [radius_add_le k m]) hk
  simp only [nMass]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq ENNReal.ofReal_ne_top)]
  calc ENNReal.ofReal δ⁻¹ ^ q * ∫⁻ ω, innerMass γ X t δ (k + m) ω ^ q ∂P
      ≤ ENNReal.ofReal δ⁻¹ ^ q * (A * ENNReal.ofReal δ ^ q) := by
        gcongr; exact hmom t δ (k + m) hδ hkm
    _ = A := by
        rw [mul_left_comm, ← ENNReal.mul_rpow_of_nonneg _ _ hq,
          ← ENNReal.ofReal_mul (inv_nonneg.2 hδ.le), inv_mul_cancel₀ hδ.ne', ENNReal.ofReal_one,
          ENNReal.one_rpow, mul_one]

theorem lintegral_incr_nMass_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {t δ : ℝ} (hδ : 0 < δ) {k : ℕ}
    (hk : 2 * radius k < δ) (m : ℕ) :
    ∫⁻ ω, incr (nMass γ X t δ k) m ω ∂P ≤
      ENNReal.ofReal (cInc γ) * ENNReal.ofReal (exp (-bdryRate γ * log 2)) ^ m := by
  have hkm : ∀ m, 2 * radius (k + m) < δ := fun m =>
    lt_of_le_of_lt (by linarith [radius_add_le k m]) hk
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
  have hpt : ∀ ω, incr (nMass γ X t δ k) m ω = ENNReal.ofReal δ⁻¹ *
      ENNReal.ofReal |(innerMass γ X t δ (k + m) ω).toReal -
        (innerMass γ X t δ (k + m + 1) ω).toReal| := by
    intro ω
    simp only [incr, nMass, ENNReal.toReal_mul, ENNReal.toReal_ofReal hδi]
    rw [← ENNReal.ofReal_mul hδi]
    congr 1
    rw [← mul_sub, abs_mul, abs_of_nonneg hδi, abs_sub_comm]
    rfl
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hint : Integrable (fun ω => |(innerMass γ X t δ (k + m) ω).toReal -
      (innerMass γ X t δ (k + m + 1) ω).toReal|) P :=
    ((integrable_innerMass_toReal hX γ hδ (hkm m)).sub
      (integrable_innerMass_toReal hX γ hδ (hkm (m + 1)))).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => abs_nonneg _),
    ← ENNReal.ofReal_mul hδi, ← ENNReal.ofReal_pow (exp_pos _).le,
    ← ENNReal.ofReal_mul (cInc_nonneg γ)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hb := integral_abs_innerMass_step_le hX (P := P) (t := t) hγ hγ2 hδ (hkm m)
  have hLi : (m : ℝ) * log 2 ≤ log (δ / radius (k + m)) := by
    have h1 : radius (k + m) = radius k * (2 : ℝ)⁻¹ ^ m := by
      simp only [radius, pow_add]
    have hr := radius_pos k
    rw [h1, ← div_div, log_div (div_pos hδ hr).ne' (by positivity), log_pow, log_inv]
    have : 0 ≤ log (δ / radius k) := log_nonneg (by rw [le_div_iff₀ hr]; linarith)
    linarith
  have hE : exp (-bdryRate γ * log (δ / radius (k + m))) ≤ exp (-bdryRate γ * log 2) ^ m := by
    rw [← exp_nat_mul]
    apply exp_le_exp.2
    have := (bdryRate_pos hγ hγ2).le
    nlinarith
  calc δ⁻¹ * ∫ ω, |(innerMass γ X t δ (k + m) ω).toReal -
        (innerMass γ X t δ (k + m + 1) ω).toReal| ∂P
      ≤ δ⁻¹ * (cInc γ * δ * exp (-bdryRate γ * log (δ / radius (k + m)))) :=
        mul_le_mul_of_nonneg_left hb hδi
    _ = cInc γ * exp (-bdryRate γ * log (δ / radius (k + m))) := by
        field_simp
    _ ≤ cInc γ * exp (-bdryRate γ * log 2) ^ m :=
        mul_le_mul_of_nonneg_left hE (cInc_nonneg γ)

theorem ofReal_exp_bdryRate_lt_one {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ENNReal.ofReal (exp (-bdryRate γ * log 2)) < 1 := by
  rw [ENNReal.ofReal_lt_one, exp_lt_one_iff]
  have := bdryRate_pos hγ hγ2
  have := log_pos one_lt_two
  nlinarith

/-- **Inner masses, `p > 1`, sup over levels.** -/
theorem lintegral_iSup_innerMass_rpow_le_of_moment [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {t δ p q : ℝ}
    (hδ : 0 < δ) (hp : 1 ≤ p) (hpq : p < q) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hmom : InnerMomentBound γ q X P A) {k : ℕ} (hk : 2 * radius k < δ) :
    ∫⁻ ω, (⨆ m, innerMass γ X t δ (k + m) ω) ^ p ∂P ≤
      ENNReal.ofReal δ ^ p * supMomConst p q A (ENNReal.ofReal (cInc γ))
        (ENNReal.ofReal (exp (-bdryRate γ * log 2))) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hpt : ∀ ω, (⨆ m, innerMass γ X t δ (k + m) ω) ^ p =
      ENNReal.ofReal δ ^ p * (⨆ m, nMass γ X t δ k m ω) ^ p := by
    intro ω
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_iSup]
    congr 1
    refine iSup_congr fun m => ?_
    simp only [nMass]
    rw [← mul_assoc, ← ENNReal.ofReal_mul hδ.le, mul_inv_cancel₀ hδ.ne', ENNReal.ofReal_one,
      one_mul]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
  gcongr
  exact lintegral_iSup_rpow_le_supMomConst
    (fun m => ((measurable_innerMass hX γ t δ (k + m)).const_mul _).aemeasurable) hp hpq hA
    (fun m => lintegral_nMass_rpow_le hq0 hmom hδ hk m)
    (fun m => lintegral_incr_nMass_le hX hγ hγ2 hδ hk m)

/-- **Approximate boundary masses, `p > 1`, sup over levels** (normalized field `zField X R`). -/
theorem lintegral_iSup_bdryApprox_rpow_le_of_moment [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R t δ p q : ℝ}
    (hδ : 0 < δ) (hR : |t| + δ ≤ R) (hp : 1 ≤ p) (hpq : p < q) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hmom : InnerMomentBound γ q X P A) {k : ℕ} (hk : 2 * radius k < δ) :
    ∫⁻ ω, (⨆ m, bdryApprox γ (zField X R ω) (k + m) (bI t δ)) ^ p ∂P ≤
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 4)) *
        exp ((2 * log R - 2 * log δ).toNNReal * (p * γ / 2) ^ 2 / 2)) *
      (ENNReal.ofReal δ ^ p * supMomConst p q A (ENNReal.ofReal (cInc γ))
        (ENNReal.ofReal (exp (-bdryRate γ * log 2)))) := by
  have hp0 : 0 < p := by linarith
  have hkm : ∀ m, 2 * radius (k + m) < δ := fun m =>
    lt_of_le_of_lt (by linarith [radius_add_le k m]) hk
  set A' : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (exp (γ / 2 * omegaAvg X R t δ ω) * δ ^ (γ ^ 2 / 4)) ^ p with hA'
  set W : Ω → ℝ≥0∞ := fun ω => (⨆ m, innerMass γ X t δ (k + m) ω) ^ p with hW
  have hφ : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (γ / 2 * x) * δ ^ (γ ^ 2 / 4)) ^ p) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).pow_const p
  have hψ : Measurable (fun x : FieldSample => (⨆ m, massFun γ t δ (k + m) x) ^ p) :=
    (Measurable.iSup fun m => measurable_massFun γ t δ (k + m)).pow_const p
  have hind : IndepFun A' W P := (indepFun_omega_innerSample hX hδ hR).comp hφ hψ
  have hAm : Measurable A' := hφ.comp (measurable_omegaAvg hX R t δ)
  have hWm : Measurable W := hψ.comp (measurable_innerSample hX t δ)
  calc ∫⁻ ω, (⨆ m, bdryApprox γ (zField X R ω) (k + m) (bI t δ)) ^ p ∂P
      = ∫⁻ ω, (A' * W) ω ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_bdryApprox_eq_omega_mul hX γ R (P := P) (t := t) hδ] with ω hω
        simp_rw [hω _ (hkm _)]
        rw [← ENNReal.mul_iSup, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        rfl
    _ = (∫⁻ ω, A' ω ∂P) * ∫⁻ ω, W ω ∂P :=
        lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hAm hWm hind
    _ ≤ _ := by
        rw [hA', lintegral_omega_factor_rpow hX γ hδ hR hp0.le]
        gcongr
        exact lintegral_iSup_innerMass_rpow_le_of_moment hX hγ hγ2 hδ hp hpq hA hmom hk

/-- **The limit boundary measure, `p > 1`.** -/
theorem lintegral_qBoundaryMeasure_rpow_le_of_moment [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R t δ p q : ℝ}
    (hδ : 0 < δ) (hR : |t| + δ ≤ R) (hp : 1 ≤ p) (hpq : p < q) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hmom : InnerMomentBound γ q X P A) {k : ℕ} (hk : 2 * radius k < δ) :
    ∫⁻ ω, qBoundaryMeasure γ (zField X R ω) (Set.Ioo (t - δ / 2) (t + δ / 2)) ^ p ∂P ≤
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 4)) *
        exp ((2 * log R - 2 * log δ).toNNReal * (p * γ / 2) ^ 2 / 2)) *
      (ENNReal.ofReal δ ^ p * supMomConst p q A (ENNReal.ofReal (cInc γ))
        (ENNReal.ofReal (exp (-bdryRate γ * log 2)))) := by
  have hp0 : 0 < p := by linarith
  refine le_trans (lintegral_mono_ae ?_)
    (lintegral_iSup_bdryApprox_rpow_le_of_moment hX hγ hγ2 hδ hR hp hpq hA hmom hk)
  filter_upwards [ae_isVagueLimitR_qBoundaryMeasure_zField hX (P := P) hγ hγ2 R] with ω hω
  exact ENNReal.rpow_le_rpow (measure_Ioo_le_of_isVagueLimitR hω (k := k)
    fun m => le_iSup (fun m => bdryApprox γ (zField X R ω) (k + m) (bI t δ)) m) hp0.le

/-- **Dyadic form (multifractal scaling bound), `p > 1`.** For `0 < γ < 2`, `1 ≤ p < q`, `R > 0`
and the unit-scale input `InnerMomentBound γ q X P A` (`A < ∞`), there is `C` with, for every `n`
and every `t` with `|t| + 4·2^{-n} ≤ R`, `S_n = [t − 2·2^{-n}, t + 2·2^{-n}]`, `Z = zField X R`:
`E (sup_{k ≥ n} ν^Z_{2^{-k}}(S_n))^p ≤ C 2^{-n(p(1+γ²/4) − p²γ²/4)}`, and the same for the limit
measure of the open interval. -/
theorem momentDyadic_of_innerMoment [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R p q : ℝ} (hR : 0 < R) (hp : 1 ≤ p) (hpq : p < q)
    {A : ℝ≥0∞} (hA : A ≠ ⊤) (hmom : InnerMomentBound γ q X P A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (t : ℝ), |t| + 4 * radius n ≤ R →
      ∫⁻ ω, (⨆ m, bdryApprox γ (zField X R ω) (n + m) (bI t (4 * radius n))) ^ p ∂P ≤
          ENNReal.ofReal (C * 2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))) ∧
      ∫⁻ ω, qBoundaryMeasure γ (zField X R ω)
          (Set.Ioo (t - 4 * radius n / 2) (t + 4 * radius n / 2)) ^ p ∂P ≤
          ENNReal.ofReal (C * 2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))) := by
  have hp0 : 0 < p := by linarith
  set S := supMomConst p q A (ENNReal.ofReal (cInc γ)) (ENNReal.ofReal (exp (-bdryRate γ * log 2)))
    with hS
  have hSt : S ≠ ⊤ := supMomConst_ne_top hp hpq hA ENNReal.ofReal_ne_top
    (ofReal_exp_bdryRate_lt_one hγ hγ2)
  have hS1 : 1 ≤ S := one_le_supMomConst hp _ _ _
  set K := S.toReal - 1 with hK
  have hK0 : 0 ≤ K := by
    have := ENNReal.toReal_mono hSt hS1
    simp only [ENNReal.toReal_one] at this
    linarith
  have hSK : S = ENNReal.ofReal (1 + K) := by
    rw [hK, add_sub_cancel, ENNReal.ofReal_toReal hSt]
  refine ⟨4 ^ (p * (1 + γ ^ 2 / 4)) * R ^ (p ^ 2 * γ ^ 2 / 4) * (1 + K), ?_, fun n t ht => ?_⟩
  · have hRpos : 0 ≤ R ^ (p ^ 2 * γ ^ 2 / 4) := rpow_nonneg hR.le _
    positivity
  have hr := radius_pos n
  have hδ : 0 < 4 * radius n := by positivity
  have hk : 2 * radius n < 4 * radius n := by linarith
  have hδR : 4 * radius n ≤ R := by linarith [abs_nonneg t]
  have hG : ENNReal.ofReal ((4 * radius n) ^ (p * (γ ^ 2 / 4)) *
        exp ((2 * log R - 2 * log (4 * radius n)).toNNReal * (p * γ / 2) ^ 2 / 2)) *
      (ENNReal.ofReal (4 * radius n) ^ p * S) ≤
      ENNReal.ofReal ((4 ^ (p * (1 + γ ^ 2 / 4)) * R ^ (p ^ 2 * γ ^ 2 / 4) * (1 + K)) *
        2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))) := by
    have hA0 : 0 ≤ (4 * radius n) ^ (p * (γ ^ 2 / 4)) *
        exp ((2 * log R - 2 * log (4 * radius n)).toNNReal * (p * γ / 2) ^ 2 / 2) :=
      mul_nonneg (rpow_nonneg hδ.le _) (exp_pos _).le
    rw [hSK, ENNReal.ofReal_rpow_of_nonneg hδ.le hp0.le,
      ← ENNReal.ofReal_mul (rpow_nonneg hδ.le _), ← ENNReal.ofReal_mul hA0]
    exact ENNReal.ofReal_le_ofReal (dyadic_real_le hp0 hK0 hδR)
  exact ⟨(lintegral_iSup_bdryApprox_rpow_le_of_moment hX hγ hγ2 hδ ht hp hpq hA hmom hk).trans hG,
    (lintegral_qBoundaryMeasure_rpow_le_of_moment hX hγ hγ2 hδ ht hp hpq hA hmom hk).trans hG⟩

/-- The dyadic bound from the law-level input `InnerMomentStmt γ q`. -/
theorem momentDyadic_of_innerMomentStmt {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R p q : ℝ}
    (hR : 0 < R) (hp : 1 ≤ p) (hpq : p < q) (hI : InnerMomentStmt γ q)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (t : ℝ), |t| + 4 * radius n ≤ R →
      ∫⁻ ω, (⨆ m, bdryApprox γ (zField X R ω) (n + m) (bI t (4 * radius n))) ^ p ∂P ≤
          ENNReal.ofReal (C * 2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))) ∧
      ∫⁻ ω, qBoundaryMeasure γ (zField X R ω)
          (Set.Ioo (t - 4 * radius n / 2) (t + 4 * radius n / 2)) ^ p ∂P ≤
          ENNReal.ofReal (C * 2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))) := by
  obtain ⟨A, hA, hAll⟩ := hI
  exact momentDyadic_of_innerMoment hX hγ hγ2 hR hp hpq hA (hAll P X hX)

end GMCMoments
end QuantumZipper
