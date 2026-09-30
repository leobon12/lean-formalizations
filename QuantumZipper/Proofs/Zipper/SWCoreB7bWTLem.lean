import QuantumZipper.Proofs.Zipper.SWCoreB7bWTH

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b-WT (3): bookkeeping lemmas for the weighted transport

Task SWC-B7b-WT (decision D64).

* `integral_bdryApprox_eq_weighted` — change of field in `bdryApprox`: the density of
  `bdryApprox γ y k` is that of `bdryApprox γ x k` times `e^{(γ/2)(h_k(y) − h_k(x))}`
  (the `e^{γφ/2}` rule, Duplantier–Sheffield, Invent. Math. 185 (2011), (5.1)/Prop. 2.1);
* `abs_integral_sub_le_dom`, `abs_le_mul_of_vanish`, `abs_sub_le_of_limits` — domination
  estimates; the last one gives the sup-norm Lipschitz bound of limit functionals from the
  convergence itself;
* `h0cut_abs_le_bound`, `setIntegral_h0cut_conv` — the `𝔥₀` weight in the target.

Own elementary proofs (cost rule of AGENT_GUIDE).
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

theorem measurable_avgReg_real (x : FieldSample) (k : ℕ) :
    Measurable fun t : ℝ => avgReg x k (t : ℂ) :=
  (measurable_avgReg k).comp (measurable_const.prodMk Complex.measurable_ofReal)

/-- **Change of field in `bdryApprox`** (density factor `e^{(γ/2)(h_k(y) − h_k(x))}`). -/
theorem integral_bdryApprox_eq_weighted (γ : ℝ) (x y : FieldSample) (k : ℕ) (f : ℝ → ℝ) :
    ∫ t, f t ∂bdryApprox γ y k =
      ∫ t, f t * Real.exp (γ / 2 * (avgReg y k (t : ℂ) - avgReg x k (t : ℂ))) ∂bdryApprox γ x k := by
  have hD : ∀ z : FieldSample, Measurable fun t : ℝ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg z k (t : ℂ))) :=
    fun z => ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_avgReg_real z k))))
  unfold bdryApprox
  rw [integral_withDensity_eq_integral_toReal_smul₀ (hD y).aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul₀ (hD x).aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have hr : 0 ≤ radius k ^ (γ ^ 2 / 4) := Real.rpow_nonneg (radius_pos k).le _
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg hr (Real.exp_pos _).le),
    ENNReal.toReal_ofReal (mul_nonneg hr (Real.exp_pos _).le)]
  have e : Real.exp (γ / 2 * avgReg y k (t : ℂ)) = Real.exp (γ / 2 * avgReg x k (t : ℂ)) *
      Real.exp (γ / 2 * (avgReg y k (t : ℂ) - avgReg x k (t : ℂ))) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]; ring

/-- A function vanishing off `Ks` and bounded by `C` is bounded by `C φ` if `φ ≥ 1` on `Ks`. -/
theorem abs_le_mul_of_vanish {Ks : Set ℝ} {φ h : ℝ → ℝ} {C : ℝ} (hK : ∀ x ∉ Ks, h x = 0)
    (hC : ∀ x, |h x| ≤ C) (hφ0 : ∀ x, 0 ≤ φ x) (hφK : ∀ x ∈ Ks, 1 ≤ φ x) :
    ∀ x, |h x| ≤ C * φ x := by
  intro x
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
  by_cases hx : x ∈ Ks
  · calc |h x| ≤ C := hC x
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * φ x := mul_le_mul_of_nonneg_left (hφK x hx) hC0
  · rw [hK x hx, abs_zero]; exact mul_nonneg hC0 (hφ0 x)

/-- `|∫ f₁ − ∫ f₂| ≤ δ ∫ φ` under domination by an integrable `φ`. -/
theorem abs_integral_sub_le_dom {μ : Measure ℝ} {φ f₁ f₂ : ℝ → ℝ} {δ C₁ C₂ : ℝ}
    (hφi : Integrable φ μ) (h₁m : AEStronglyMeasurable f₁ μ) (h₂m : AEStronglyMeasurable f₂ μ)
    (hb₁ : ∀ x, |f₁ x| ≤ C₁ * φ x) (hb₂ : ∀ x, |f₂ x| ≤ C₂ * φ x)
    (hd : ∀ x, |f₁ x - f₂ x| ≤ δ * φ x) :
    |∫ x, f₁ x ∂μ - ∫ x, f₂ x ∂μ| ≤ δ * ∫ x, φ x ∂μ := by
  have i₁ : Integrable f₁ μ := Integrable.mono' (hφi.const_mul C₁) h₁m
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb₁ x)
  have i₂ : Integrable f₂ μ := Integrable.mono' (hφi.const_mul C₂) h₂m
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb₂ x)
  rw [← integral_sub i₁ i₂, ← integral_const_mul]
  have := norm_integral_le_of_norm_le (hφi.const_mul δ)
    (ae_of_all μ fun x => show ‖f₁ x - f₂ x‖ ≤ δ * φ x by rw [Real.norm_eq_abs]; exact hd x)
  rwa [Real.norm_eq_abs] at this

/-- **Sup-norm Lipschitz bound for limit functionals**, read off from the convergence. -/
theorem abs_sub_le_of_limits {μ : ℕ → Measure ℝ} {Ks : Set ℝ} {φ f₁ f₂ : ℝ → ℝ}
    {L₁ L₂ Lφ ε C₁ C₂ : ℝ} (hε : 0 ≤ ε) (hφ0 : ∀ x, 0 ≤ φ x) (hφK : ∀ x ∈ Ks, 1 ≤ φ x)
    (h₁ : ∀ x ∉ Ks, f₁ x = 0) (h₂ : ∀ x ∉ Ks, f₂ x = 0)
    (hm₁ : StronglyMeasurable f₁) (hm₂ : StronglyMeasurable f₂)
    (hb₁ : ∀ x, |f₁ x| ≤ C₁) (hb₂ : ∀ x, |f₂ x| ≤ C₂) (hsup : ∀ x, |f₁ x - f₂ x| ≤ ε)
    (hφint : ∀ᶠ k in atTop, Integrable φ (μ k))
    (hc₁ : ∀ η > 0, ∀ᶠ k in atTop, |∫ x, f₁ x ∂μ k - L₁| ≤ η)
    (hc₂ : ∀ η > 0, ∀ᶠ k in atTop, |∫ x, f₂ x ∂μ k - L₂| ≤ η)
    (hcφ : ∀ η > 0, ∀ᶠ k in atTop, |∫ x, φ x ∂μ k - Lφ| ≤ η) :
    |L₁ - L₂| ≤ ε * Lφ := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set d : ℝ := δ / (2 + ε) with hd
  have hd0 : 0 < d := div_pos hδ (by linarith)
  obtain ⟨k, hk₁, hk₂, hkφ, hki⟩ :=
    ((hc₁ d hd0).and ((hc₂ d hd0).and ((hcφ d hd0).and hφint))).exists
  have hdom : ∀ x, |f₁ x - f₂ x| ≤ ε * φ x :=
    abs_le_mul_of_vanish (fun x hx => by rw [h₁ x hx, h₂ x hx, sub_zero]) hsup hφ0 hφK
  have key := abs_integral_sub_le_dom hki hm₁.aestronglyMeasurable hm₂.aestronglyMeasurable
    (abs_le_mul_of_vanish h₁ hb₁ hφ0 hφK) (abs_le_mul_of_vanish h₂ hb₂ hφ0 hφK) hdom
  have hφle : ∫ x, φ x ∂μ k ≤ Lφ + d := by linarith [(abs_le.1 hkφ).2]
  have h1 : ε * ∫ x, φ x ∂μ k ≤ ε * Lφ + ε * d := by
    have := mul_le_mul_of_nonneg_left hφle hε; linarith [mul_add ε Lφ d]
  have hdd : 2 * d + ε * d = δ := by
    rw [hd]; field_simp
  rw [abs_le] at hk₁ hk₂ key ⊢
  constructor <;> linarith [hk₁.1, hk₁.2, hk₂.1, hk₂.2, key.1, key.2]

/-- Bound on the cut-off `𝔥₀` on the `M`-ball. -/
theorem h0cut_abs_le_bound (κ : ℝ) {c M : ℝ} (hc : 0 < c) {z : ℂ} (hz : ‖z‖ ≤ M) :
    |h0cut κ c z| ≤ |2 / Real.sqrt κ| * (|Real.log c| + |Real.log (max M c)|) := by
  have h1 : c ≤ max ‖z‖ c := le_max_right _ _
  have h2 : max ‖z‖ c ≤ max M c := max_le_max hz le_rfl
  have l1 := Real.log_le_log hc h1
  have l2 := Real.log_le_log (hc.trans_le h1) h2
  simp only [h0cut, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log (max M c))]
  · linarith [le_abs_self (Real.log (max M c)), abs_nonneg (Real.log c)]

/-- **The `𝔥₀` weight in the target**: on `[ψ(a), ψ(b)]`, `ψ (ψ⁻¹ u) = u`, so the clamped
cut-off weight at `ψ⁻¹ u` is `𝔥₀(u)`. -/
theorem setIntegral_h0cut_conv {a b ρ M m c κ γ : ℝ} {ψ : ℂ → ℂ}
    (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) (hab : a ≤ b)
    (hsep : ∀ z ∈ thickening ρ (segC a b), c ≤ ‖ψ z‖) (f : ℝ → ℝ) (ν : Measure ℝ) :
    ∫ u in Icc (ψ a).re (ψ b).re,
        f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u) *
          Real.exp (γ / 2 * h0cut κ c (ψ ((projIcc a b hab
            (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u) : ℝ) : ℂ))) ∂ν =
      ∫ u in Icc (ψ a).re (ψ b).re,
        f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u) *
          Real.exp (γ / 2 * h0rev κ u) ∂ν := by
  refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
  have hcont : ContinuousOn (fun t : ℝ => (ψ t).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn (hψ.1.continuousOn.comp
      Complex.continuous_ofReal.continuousOn fun t ht =>
        self_subset_thickening hρ _ (ofReal_mem_segC ht))
  obtain ⟨hmem, heq⟩ := Function.invFunOn_pos (intermediate_value_Icc hab hcont hu)
  set s := Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u with hs
  have hps : ((projIcc a b hab s : ℝ)) = s := by rw [projIcc_of_mem hab hmem]
  have hz : ψ (s : ℂ) = (u : ℂ) :=
    Complex.ext (by simpa using heq) (by simpa using hψ.2.2.1 s hmem)
  have hcz : c ≤ ‖((u : ℝ) : ℂ)‖ := by
    rw [← hz]; exact hsep _ (self_subset_thickening hρ _ (ofReal_mem_segC hmem))
  rw [hps, hz, h0cut_eq hcz]

end SWCore
end QuantumZipper
