import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-LIPDET (b): the radius increment of a circle-smoothed pairing is a first-mode integral

Deterministic core of `n2ZPairLip_of_firstMode`. For a continuous `g : ℂ → ℝ`, a `C¹` function
`f` vanishing off a compact `K`, and radii `0 ≤ t' ≤ t`,

`∫ f(u) ∫_{[0,2π]} g(u + t e^{iθ}) dθ du − (same at t')
   = ∫_{[t',t]} ∫_{u ∈ K} ∫_{[0,2π]} Df(u)(−e^{iθ}) g(u + τ e^{iθ}) dθ du dτ`

(`n2Lip_core`). Proof: translate `u ↦ u − τ e^{iθ}` so that `τ` sits in the argument of `f`, use
the one-dimensional fundamental theorem of calculus along the segment, swap the integrals
(continuous integrands on compact sets), and translate back. This is the classical
"derivative of the spherical mean falls on the test function" computation (e.g. Evans, *PDE*,
§2.2.2, proof of Thm. 2 (mean-value formulas), where `d/dr` of a spherical mean is computed by
the same change of variables); the Lean argument is an own elementary proof.
-/

noncomputable section

open MeasureTheory Set Function
open scoped Real

namespace QuantumZipper
namespace D3Plus

/-- Unit vector `e^{iθ}`. -/
def n2LipE (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem continuous_n2LipE : Continuous n2LipE := by
  unfold n2LipE; fun_prop

theorem norm_n2LipE (θ : ℝ) : ‖n2LipE θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

/-- Fubini for a continuous integrand over two compact sets. -/
theorem n2Lip_swap {X Y E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    [SFinite μ] [SFinite ν] {A : Set X} {B : Set Y} (hA : IsCompact A) (hB : IsCompact B)
    {F : X → Y → E} (hF : Continuous (uncurry F)) :
    ∫ x in A, ∫ y in B, F x y ∂ν ∂μ = ∫ y in B, ∫ x in A, F x y ∂μ ∂ν := by
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hF.continuousOn.integrableOn_compact (hA.prod hB)

/-- Fubini between a full integral over `ℂ` (integrand vanishing off a compact `B`) and a set
integral over a compact `A ⊆ ℝ`. -/
theorem n2Lip_swapC {k : ℂ → ℝ → ℝ} (hk : Continuous (uncurry k)) {A : Set ℝ}
    (hA : IsCompact A) {B : Set ℂ} (hB : IsCompact B) (h0 : ∀ v ∉ B, ∀ τ ∈ A, k v τ = 0) :
    ∫ v, ∫ τ in A, k v τ = ∫ τ in A, ∫ v, k v τ := by
  have h1 : ∫ v, ∫ τ in A, k v τ = ∫ v in B, ∫ τ in A, k v τ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    exact setIntegral_eq_zero_of_forall_eq_zero fun τ hτ => h0 v hv τ hτ
  have h2 : ∫ τ in A, ∫ v, k v τ = ∫ τ in A, ∫ v in B, k v τ := by
    refine setIntegral_congr_fun hA.measurableSet fun τ hτ => ?_
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => h0 v hv τ hτ).symm
  rw [h1, h2]
  exact n2Lip_swap hB hA hk

/-- Translation: `∫ h(u) g(u + a) du = ∫ h(v − a) g(v) dv`. -/
theorem n2Lip_translate (h g : ℂ → ℝ) (a : ℂ) :
    ∫ u, h u * g (u + a) = ∫ v, h (v - a) * g v := by
  have := integral_sub_right_eq_self (μ := (volume : Measure ℂ)) (E := ℝ)
    (fun u => h u * g (u + a)) a
  simp only [sub_add_cancel] at this
  exact this.symm

/-- One-dimensional FTC along the segment `τ ↦ v − τ e`. -/
theorem n2Lip_ftc {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (v e : ℂ) {t' t : ℝ} (htt : t' ≤ t) :
    ∫ τ in Icc t' t, fderiv ℝ f (v - (τ : ℂ) * e) (-e) = f (v - (t : ℂ) * e) - f (v - (t' : ℂ) * e) := by
  have hdiff := hf.differentiable one_ne_zero
  have hD := hf.continuous_fderiv one_ne_zero
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le htt]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun τ : ℝ => f (v - (τ : ℂ) * e)) (fun τ _ => ?_) ?_
  · have hin : HasDerivAt (fun x : ℝ => v - (x : ℂ) * e) (-e) τ := by
      have := HasDerivAt.const_sub v (HasDerivAt.mul_const (HasDerivAt.ofReal_comp (hasDerivAt_id τ)) e)
      simpa using this
    exact HasFDerivAt.comp_hasDerivAt τ (hdiff _).hasFDerivAt hin
  · refine Continuous.intervalIntegrable ?_ _ _
    fun_prop

/-- `HasCompactSupport` from vanishing off a compact set. -/
theorem n2Lip_hcs {f : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K) (hfK : ∀ z ∉ K, f z = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro hK hfK

/-- The derivative of `f` vanishes off `K` (compact, hence closed). -/
theorem n2Lip_fderiv_zero {f : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hfK : ∀ z ∉ K, f z = 0) {z : ℂ} (hz : z ∉ K) : fderiv ℝ f z = 0 := by
  refine fderiv_of_notMem_tsupport ℝ fun hz' => hz ?_
  have : tsupport f ⊆ K := closure_minimal (fun y hy => by_contra fun h => hy (hfK y h))
    hK.isClosed
  exact this hz'

/-- **Per direction**: the radius increment of `τ ↦ ∫ f(u) g(u + τ e) du`. -/
theorem n2Lip_perDir {g : ℂ → ℝ} (hg : Continuous g) {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    {K : Set ℂ} (hK : IsCompact K) (hfK : ∀ z ∉ K, f z = 0) {e : ℂ} (he : ‖e‖ ≤ 1)
    {t' t : ℝ} (ht' : 0 ≤ t') (htt : t' ≤ t) :
    (∫ u, f u * g (u + (t : ℂ) * e)) - ∫ u, f u * g (u + (t' : ℂ) * e) =
      ∫ τ in Icc t' t, ∫ u, fderiv ℝ f u (-e) * g (u + (τ : ℂ) * e) := by
  have hD := hf.continuous_fderiv one_ne_zero
  have hfc := n2Lip_hcs hK hfK
  have hint : ∀ a : ℂ, Integrable fun v => f (v - a) * g v := fun a =>
    ((hf.continuous.comp (continuous_id.sub continuous_const)).mul hg).integrable_of_hasCompactSupport
      ((hfc.comp_homeomorph (Homeomorph.subRight a)).mul_right)
  refine Eq.trans (congrArg₂ (· - ·) (n2Lip_translate f g _) (n2Lip_translate f g _)) ?_
  rw [← integral_sub (hint _) (hint _)]
  have h1 : (fun v => f (v - (t : ℂ) * e) * g v - f (v - (t' : ℂ) * e) * g v) =
      fun v => ∫ τ in Icc t' t, fderiv ℝ f (v - (τ : ℂ) * e) (-e) * g v := by
    funext v
    rw [integral_mul_const, n2Lip_ftc hf v e htt, sub_mul]
  rw [h1]
  -- the compact set containing all the relevant `v`
  set K₁ : Set ℂ := (fun p : ℂ × ℂ => p.1 + p.2) '' (K ×ˢ Metric.closedBall 0 t) with hK₁
  have hK₁c : IsCompact K₁ :=
    (hK.prod (isCompact_closedBall 0 t)).image (by fun_prop)
  rw [n2Lip_swapC (k := fun v τ => fderiv ℝ f (v - (τ : ℂ) * e) (-e) * g v) (by fun_prop)
    isCompact_Icc hK₁c ?_]
  · refine setIntegral_congr_fun measurableSet_Icc fun τ _ => ?_
    exact (n2Lip_translate (fun u => fderiv ℝ f u (-e)) g _).symm
  · intro v hv τ hτ
    have hnot : v - (τ : ℂ) * e ∉ K := by
      intro hmem
      refine hv ⟨(v - (τ : ℂ) * e, (τ : ℂ) * e), ⟨hmem, ?_⟩, by simp⟩
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (ht'.trans hτ.1)]
      calc τ * ‖e‖ ≤ τ * 1 := mul_le_mul_of_nonneg_left he (ht'.trans hτ.1)
        _ = τ := mul_one τ
        _ ≤ t := hτ.2
    simp [n2Lip_fderiv_zero hK hfK hnot]

end D3Plus
end QuantumZipper
