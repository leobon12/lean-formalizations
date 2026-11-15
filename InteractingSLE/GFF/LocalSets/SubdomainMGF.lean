import InteractingSLE.GFF.LocalSets.SubdomainLaw
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic

/-!
# Conditional exponential moments from conditional characteristic functions

Infrastructure for Proposition 3.8 (specification §3.2, p. 59), packet PROVE-LS-C.

If `E[e^{it Y} | 𝒢] = e^{−t² V/2}` for every real `t`, with `V ≥ 0`, then conditionally on `𝒢` the
variable `Y` is centred Gaussian with variance `V`; in particular, for every `𝒢`-measurable
`W ≥ 0` and real `λ`,
`E[W e^{λ Y}] = E[W e^{λ² V/2}]` (`lintegral_mul_exp_of_condCharFun`).

Proof: for `B ∈ 𝒢` the law of `Y` under `P|_B` and the law of `√V · Z` under `P|_B ⊗ N(0,1)` have the
same characteristic function `t ↦ ∫_B e^{−t² V/2}`, hence are equal (`Measure.ext_of_charFun`);
integrating `e^{λ x}` against the second gives `∫_B e^{λ² V/2}` (the Gaussian moment generating
function, Fubini). The general `W` follows by the induction principle for measurable
`ℝ≥0∞`-valued functions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped ENNReal NNReal

namespace InteractingSLE
namespace LocalSets

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- The law of `√V · Z` under `P|_B ⊗ N(0, 1)`. -/
def mixLaw (P : Measure Ω) (B : Set Ω) (V : Ω → ℝ) : Measure ℝ :=
  ((P.restrict B).prod (gaussianReal 0 1)).map fun p => Real.sqrt (V p.1) * p.2

lemma measurable_mixMap {V : Ω → ℝ} (hV : Measurable V) :
    Measurable fun p : Ω × ℝ => Real.sqrt (V p.1) * p.2 :=
  (hV.comp measurable_fst).sqrt.mul measurable_snd

instance (B : Set Ω) (V : Ω → ℝ) : IsFiniteMeasure (mixLaw P B V) := by
  unfold mixLaw; infer_instance

lemma charFun_mixLaw {B : Set Ω} {V : Ω → ℝ} (hV : Measurable V) (hV0 : ∀ᵐ ω ∂P, 0 ≤ V ω)
    (t : ℝ) :
    charFun (mixLaw P B V) t = ∫ ω in B, ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ) ∂P := by
  rw [charFun_apply_real, mixLaw, integral_map (measurable_mixMap hV).aemeasurable
    (by fun_prop)]
  have hint : Integrable (fun p : Ω × ℝ => cexp (↑t * ↑(Real.sqrt (V p.1) * p.2) * I))
      ((P.restrict B).prod (gaussianReal 0 1)) := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun p => ?_)
    rw [show (↑t * ↑(Real.sqrt (V p.1) * p.2) * I : ℂ) = ↑(t * (Real.sqrt (V p.1) * p.2)) * I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [integral_prod _ hint]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hV0] with ω hω
  have := charFun_gaussianReal (μ := 0) (v := 1) (t * Real.sqrt (V ω))
  rw [charFun_apply_real] at this
  have e : ∀ z : ℝ, (↑t * ↑(Real.sqrt (V ω) * z) * I : ℂ) = ↑(t * Real.sqrt (V ω)) * ↑z * I :=
    fun z => by push_cast; ring
  simp_rw [e]
  rw [this]
  have hs : (t * Real.sqrt (V ω)) ^ 2 = t ^ 2 * V ω := by
    rw [mul_pow, Real.sq_sqrt hω]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  rw [show ((t : ℂ) * (Real.sqrt (V ω) : ℂ)) ^ 2 = ((t * Real.sqrt (V ω)) ^ 2 : ℝ) by push_cast; ring,
    hs]
  push_cast
  ring

/-- Conditionally Gaussian: `(P|_B).map Y = mixLaw P B V` for `B ∈ 𝒢`. -/
theorem map_restrict_eq_mixLaw (h𝒢 : 𝒢 ≤ mΩ) {Y V : Ω → ℝ} (hY : Measurable Y)
    (hV : Measurable V) (hV0 : ∀ᵐ ω ∂P, 0 ≤ V ω)
    (hc : ∀ t : ℝ, P[fun ω => Complex.exp (Complex.I * ((t * Y ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ))
    {B : Set Ω} (hB : MeasurableSet[𝒢] B) :
    (P.restrict B).map Y = mixLaw P B V := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_mixLaw hV hV0, charFun_apply_real, integral_map hY.aemeasurable (by fun_prop)]
  have hFi : Integrable (fun ω => Complex.exp (Complex.I * ((t * Y ω : ℝ) : ℂ))) P :=
    GFF.integrable_exp_I_mul (measurable_const.mul hY)
  have e1 : ∫ ω in B, cexp (↑t * ↑(Y ω) * I) ∂P =
      ∫ ω in B, Complex.exp (Complex.I * ((t * Y ω : ℝ) : ℂ)) ∂P := by
    congr 1; funext ω; push_cast; ring_nf
  rw [e1, ← setIntegral_condExp h𝒢 hFi hB]
  exact setIntegral_congr_ae (h𝒢 _ hB) (by filter_upwards [hc t] with ω hω _ using hω)

/-- The Gaussian moment generating function under `P|_B`: `∫_B e^{λY} = ∫_B e^{λ² V/2}`. -/
theorem setLIntegral_exp_of_condCharFun (h𝒢 : 𝒢 ≤ mΩ) {Y V : Ω → ℝ} (hY : Measurable Y)
    (hV : Measurable V) (hV0 : ∀ᵐ ω ∂P, 0 ≤ V ω)
    (hc : ∀ t : ℝ, P[fun ω => Complex.exp (Complex.I * ((t * Y ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ))
    {B : Set Ω} (hB : MeasurableSet[𝒢] B) (lam : ℝ) :
    ∫⁻ ω in B, ENNReal.ofReal (Real.exp (lam * Y ω)) ∂P =
      ∫⁻ ω in B, ENNReal.ofReal (Real.exp (lam ^ 2 * V ω / 2)) ∂P := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (lam * x)) := by fun_prop
  have h1 : ∫⁻ ω in B, ENNReal.ofReal (Real.exp (lam * Y ω)) ∂P =
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x)) ∂((P.restrict B).map Y) := by
    rw [lintegral_map hm hY]
  rw [h1, map_restrict_eq_mixLaw h𝒢 hY hV hV0 hc hB, mixLaw, lintegral_map hm (measurable_mixMap hV),
    lintegral_prod (fun p : Ω × ℝ => ENNReal.ofReal (Real.exp (lam * (Real.sqrt (V p.1) * p.2))))
      (hm.comp (measurable_mixMap hV)).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hV0] with ω hω
  have hi : Integrable (fun z : ℝ => Real.exp (lam * Real.sqrt (V ω) * z)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal _
  have e : ∀ z : ℝ, Real.exp (lam * (Real.sqrt (V ω) * z)) = Real.exp (lam * Real.sqrt (V ω) * z) :=
    fun z => by ring_nf
  simp only [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun z => (Real.exp_pos _).le)]
  have hmgf := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (lam * Real.sqrt (V ω))
  rw [mgf] at hmgf
  rw [hmgf]
  congr 2
  rw [mul_pow, Real.sq_sqrt hω]
  push_cast
  ring

/-- **Conditional exponential moments** from conditional characteristic functions: if
`E[e^{itY} | 𝒢] = e^{−t² V/2}` for all `t`, with `V ≥ 0`, then `E[W e^{λY}] = E[W e^{λ²V/2}]` for
every `𝒢`-measurable `W ≥ 0`. -/
theorem lintegral_mul_exp_of_condCharFun (h𝒢 : 𝒢 ≤ mΩ) {Y V : Ω → ℝ} (hY : Measurable Y)
    (hV : Measurable V) (hV0 : ∀ᵐ ω ∂P, 0 ≤ V ω)
    (hc : ∀ t : ℝ, P[fun ω => Complex.exp (Complex.I * ((t * Y ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * V ω)) : ℝ) : ℂ))
    {W : Ω → ℝ≥0∞} (hW : Measurable[𝒢] W) (lam : ℝ) :
    ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam * Y ω)) ∂P =
      ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V ω / 2)) ∂P := by
  have hf₁ : Measurable fun ω => ENNReal.ofReal (Real.exp (lam * Y ω)) := by fun_prop
  have hf₂ : Measurable fun ω => ENNReal.ofReal (Real.exp (lam ^ 2 * V ω / 2)) := by fun_prop
  refine @Measurable.ennreal_induction Ω 𝒢 (fun W => ∫⁻ ω, W ω * ENNReal.ofReal
      (Real.exp (lam * Y ω)) ∂P = ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V ω / 2)) ∂P)
    ?_ ?_ ?_ W hW
  · intro c s hs
    have e : ∀ f : Ω → ℝ≥0∞, (fun ω => s.indicator (fun _ => c) ω * f ω) =
        s.indicator fun ω => c * f ω := fun f => by
      funext ω; by_cases hω : ω ∈ s <;> simp [hω]
    rw [e, e, lintegral_indicator (h𝒢 _ hs), lintegral_indicator (h𝒢 _ hs),
      lintegral_const_mul c hf₁, lintegral_const_mul c hf₂,
      setLIntegral_exp_of_condCharFun h𝒢 hY hV hV0 hc hs]
  · intro f g _ hf hg hf' hg'
    simp only [Pi.add_apply, add_mul]
    rw [lintegral_add_left (f := fun ω => f ω * ENNReal.ofReal (Real.exp (lam * Y ω)))
        ((hf.mono h𝒢 le_rfl).mul hf₁),
      lintegral_add_left (f := fun ω => f ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V ω / 2)))
        ((hf.mono h𝒢 le_rfl).mul hf₂), hf', hg']
  · intro f hf hmono hf'
    simp only [ENNReal.iSup_mul]
    rw [lintegral_iSup (f := fun n ω => f n ω * ENNReal.ofReal (Real.exp (lam * Y ω)))
        (fun n => ((hf n).mono h𝒢 le_rfl).mul hf₁)
        (fun n m hnm ω => mul_le_mul_left (hmono hnm ω) _),
      lintegral_iSup (f := fun n ω => f n ω * ENNReal.ofReal (Real.exp (lam ^ 2 * V ω / 2)))
        (fun n => ((hf n).mono h𝒢 le_rfl).mul hf₂)
        (fun n m hnm ω => mul_le_mul_left (hmono hnm ω) _)]
    simp only [hf']

end LocalSets
end InteractingSLE
