import QuantumZipper.Proofs.Zipper.D3PlusN2LipSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-LIPDET (b), continued: the first-mode bound for a smooth test function

For a continuous `g`, a `C¹` function `f` vanishing off a compact `K` with `‖Df‖ ≤ L`, and radii
`0 < t' ≤ t`, if the first circle Fourier mode of `g` on `∂B(u, τ)` is at most `M/√τ` for
`u ∈ K`, `τ ∈ [t', t]`, then the circle-smoothed pairings satisfy

`|∫ f(u) ∫_{[0,2π]} g(u + t e^{iθ}) dθ du − (same at t')| ≤ |K| · L · M · 2√t`

(`n2Lip_core_bound`). The identity `n2Lip_core` writes the increment as
`∫_{[t',t]} ∫_u ∫_θ Df(u)(−e^{iθ}) g(u + τ e^{iθ})`, and the inner `θ`-integral is
`Df(u)` applied to minus the first mode. Own elementary argument (see `D3PlusN2LipSmooth`).
-/

noncomputable section

open MeasureTheory Set Function
open scoped Real

namespace QuantumZipper
namespace D3Plus

/-- Continuity of a parametric integral whose integrand vanishes off a compact set. -/
theorem n2Lip_contParam {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {k : X → ℂ → ℝ} (hk : Continuous (uncurry k)) {K : Set ℂ}
    (hK : IsCompact K) (h0 : ∀ x, ∀ u ∉ K, k x u = 0) : Continuous fun x => ∫ u, k x u := by
  have : (fun x => ∫ u, k x u) = fun x => ∫ u in K, k x u :=
    funext fun x => (setIntegral_eq_integral_of_forall_compl_eq_zero (h0 x)).symm
  rw [this]
  exact continuous_parametric_integral_of_continuous hk hK

/-- **Core identity**: the radius increment of the circle-smoothed pairing. -/
theorem n2Lip_core {g : ℂ → ℝ} (hg : Continuous g) {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    {K : Set ℂ} (hK : IsCompact K) (hfK : ∀ z ∉ K, f z = 0) {t' t : ℝ} (ht' : 0 ≤ t')
    (htt : t' ≤ t) :
    (∫ u, f u * ∫ θ in Icc 0 (2 * π), g (u + (t : ℂ) * n2LipE θ)) -
        ∫ u, f u * ∫ θ in Icc 0 (2 * π), g (u + (t' : ℂ) * n2LipE θ) =
      ∫ τ in Icc t' t, ∫ u, ∫ θ in Icc 0 (2 * π),
        fderiv ℝ f u (-n2LipE θ) * g (u + (τ : ℂ) * n2LipE θ) := by
  have hD := hf.continuous_fderiv one_ne_zero
  have hE := continuous_n2LipE
  have hfc := hf.continuous
  have hA : ∀ s : ℝ, ∫ u, f u * ∫ θ in Icc 0 (2 * π), g (u + (s : ℂ) * n2LipE θ) =
      ∫ θ in Icc 0 (2 * π), ∫ u, f u * g (u + (s : ℂ) * n2LipE θ) := by
    intro s
    simp_rw [← integral_const_mul]
    exact n2Lip_swapC (k := fun u θ => f u * g (u + (s : ℂ) * n2LipE θ)) (by fun_prop)
      isCompact_Icc hK (fun v hv θ _ => by simp [hfK v hv])
  have hcont : ∀ s : ℝ, Continuous fun θ => ∫ u, f u * g (u + (s : ℂ) * n2LipE θ) := fun s =>
    n2Lip_contParam (k := fun θ u => f u * g (u + (s : ℂ) * n2LipE θ)) (by fun_prop) hK
      (fun θ v hv => by simp [hfK v hv])
  rw [hA, hA, ← integral_sub ((hcont t).integrableOn_Icc) ((hcont t').integrableOn_Icc)]
  have h1 : ∫ θ in Icc 0 (2 * π), ((∫ u, f u * g (u + (t : ℂ) * n2LipE θ)) -
        ∫ u, f u * g (u + (t' : ℂ) * n2LipE θ)) =
      ∫ θ in Icc 0 (2 * π), ∫ τ in Icc t' t, ∫ u,
        fderiv ℝ f u (-n2LipE θ) * g (u + (τ : ℂ) * n2LipE θ) :=
    setIntegral_congr_fun measurableSet_Icc fun θ _ =>
      n2Lip_perDir hg hf hK hfK (norm_n2LipE θ).le ht' htt
  rw [h1]
  have hF : Continuous fun p : ℝ × ℝ => ∫ u,
      fderiv ℝ f u (-n2LipE p.1) * g (u + (p.2 : ℂ) * n2LipE p.1) :=
    n2Lip_contParam (k := fun (p : ℝ × ℝ) (u : ℂ) => fderiv ℝ f u (-n2LipE p.1) * g (u + (p.2 : ℂ) * n2LipE p.1))
      (by fun_prop) hK (fun p v hv => by simp [n2Lip_fderiv_zero hK hfK hv])
  refine (n2Lip_swap (F := fun (θ τ : ℝ) => ∫ u, fderiv ℝ f u (-n2LipE θ) * g (u + (τ : ℂ) * n2LipE θ))
    isCompact_Icc isCompact_Icc hF).trans ?_
  refine setIntegral_congr_fun measurableSet_Icc fun τ _ => ?_
  exact (n2Lip_swapC (k := fun u θ => fderiv ℝ f u (-n2LipE θ) * g (u + (τ : ℂ) * n2LipE θ))
    (by fun_prop) isCompact_Icc hK
    (fun v hv θ _ => by simp [n2Lip_fderiv_zero hK hfK hv])).symm

/-- `∫_{[t',t]} τ^{-1/2} dτ = 2√t − 2√t'`. -/
theorem n2Lip_int_invSqrt {t' t : ℝ} (ht' : 0 < t') (htt : t' ≤ t) :
    ∫ τ in Icc t' t, (Real.sqrt τ)⁻¹ = 2 * Real.sqrt t - 2 * Real.sqrt t' := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le htt]
  have hpos : ∀ x ∈ uIcc t' t, 0 < x := fun x hx => by
    rw [uIcc_of_le htt] at hx; exact ht'.trans_le hx.1
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun τ : ℝ => 2 * Real.sqrt τ) (fun x hx => ?_) ?_
  · have hx := hpos x hx
    have := HasDerivAt.const_mul 2 (Real.hasDerivAt_sqrt hx.ne')
    have h2 : 2 * (1 / (2 * Real.sqrt x)) = (Real.sqrt x)⁻¹ := by
      rw [one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
    rw [h2] at this
    exact this
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun x hx => ?_
    exact (Real.sqrt_pos.2 (hpos x hx)).ne'

/-- The inner `θ`-integral is `Df(u)` applied to minus the first mode. -/
theorem n2Lip_inner_le {g : ℂ → ℝ} (hg : Continuous g) (ℓ : ℂ →L[ℝ] ℝ) (u : ℂ) (τ : ℝ) :
    ‖∫ θ in Icc 0 (2 * π), ℓ (-n2LipE θ) * g (u + (τ : ℂ) * n2LipE θ)‖ ≤
      ‖ℓ‖ * ‖∫ θ in (0 : ℝ)..(2 * π), ((g (u + (τ : ℂ) * n2LipE θ) : ℝ) : ℂ) * n2LipE θ‖ := by
  have hE := continuous_n2LipE
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
  have hpt : ∀ θ : ℝ, ℓ (-n2LipE θ) * g (u + (τ : ℂ) * n2LipE θ) =
      ℓ (-(((g (u + (τ : ℂ) * n2LipE θ) : ℝ) : ℂ) * n2LipE θ)) := by
    intro θ
    have : ((g (u + (τ : ℂ) * n2LipE θ) : ℝ) : ℂ) * n2LipE θ =
        (g (u + (τ : ℂ) * n2LipE θ)) • n2LipE θ := Complex.real_smul.symm
    rw [this, map_neg, map_neg, map_smul, smul_eq_mul]
    ring
  simp_rw [hpt]
  rw [ContinuousLinearMap.intervalIntegral_comp_comm ℓ
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_neg]
  refine (ℓ.le_opNorm _).trans ?_
  rw [norm_neg]

/-- **Smooth-function bound.** -/
theorem n2Lip_core_bound {g : ℂ → ℝ} (hg : Continuous g) {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    {K : Set ℂ} (hK : IsCompact K) (hfK : ∀ z ∉ K, f z = 0) {L M : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ u, ‖fderiv ℝ f u‖ ≤ L) (hM : 0 ≤ M) {t' t : ℝ} (ht' : 0 < t') (htt : t' ≤ t)
    (hmode : ∀ u ∈ K, ∀ τ ∈ Icc t' t,
      ‖∫ θ in (0 : ℝ)..(2 * π), ((g (u + (τ : ℂ) * n2LipE θ) : ℝ) : ℂ) * n2LipE θ‖ ≤
        M / Real.sqrt τ) :
    |(∫ u, f u * ∫ θ in Icc 0 (2 * π), g (u + (t : ℂ) * n2LipE θ)) -
        ∫ u, f u * ∫ θ in Icc 0 (2 * π), g (u + (t' : ℂ) * n2LipE θ)| ≤
      volume.real K * L * M * (2 * Real.sqrt t) := by
  rw [n2Lip_core hg hf hK hfK ht'.le htt, ← Real.norm_eq_abs]
  have hbd : ∀ τ ∈ Icc t' t, ‖∫ u, ∫ θ in Icc 0 (2 * π),
      fderiv ℝ f u (-n2LipE θ) * g (u + (τ : ℂ) * n2LipE θ)‖ ≤
        volume.real K * L * M * (Real.sqrt τ)⁻¹ := by
    intro τ hτ
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (fun v hv => by simp [n2Lip_fderiv_zero hK hfK hv])]
    refine (norm_setIntegral_le_of_norm_le_const (C := L * (M / Real.sqrt τ))
      hK.measure_lt_top fun u hu => ?_).trans_eq ?_
    · exact (n2Lip_inner_le hg _ u τ).trans
        (mul_le_mul (hL u) (hmode u hu τ hτ) (norm_nonneg _) hL0)
    · ring
  have hint : IntegrableOn (fun τ => volume.real K * L * M * (Real.sqrt τ)⁻¹) (Icc t' t) := by
    refine ContinuousOn.integrableOn_Icc (ContinuousOn.mul continuousOn_const ?_)
    refine ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun x hx => ?_
    exact (Real.sqrt_pos.2 (ht'.trans_le hx.1)).ne'
  refine (norm_integral_le_of_norm_le hint
    ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hbd))).trans ?_
  rw [integral_const_mul, n2Lip_int_invSqrt ht' htt]
  have h1 : 0 ≤ volume.real K * L * M := by positivity
  have h2 : 0 ≤ Real.sqrt t' := Real.sqrt_nonneg _
  nlinarith

end D3Plus
end QuantumZipper
