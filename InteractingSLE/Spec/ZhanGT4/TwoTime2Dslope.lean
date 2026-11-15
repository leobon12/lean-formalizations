/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Divided differences of holomorphic functions at the base point

Packet PROVE-ZHAN-GT4-A4, a tool for (D2) of Astra's follow-up note, Part A.1.1
(`source/external/AstraIG1/ig1_followup_proofs.txt` L263–L266): "The apparent singularity at `W_j` is removable. Taylor
expansion gives `∂h(W) = −3A₂`, `∂h'(W)/A₁ = A₂²/(2A₁²) − (4/3)A₃/A₁`."

For `f` holomorphic on an open `U ∋ a` and `q = dslope f a` (so `f z = f a + (z − a) q z`), the Taylor coefficients of
`f` at `a` are those of `q` shifted: `q a = f'(a)`, `q'(a) = f''(a)/2`, `q''(a) = f'''(a)/3`. These identities
(`deriv_deriv_eq_two_mul`, `deriv_deriv_deriv_eq_three_mul`) are all the "Taylor expansion" (D2) needs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE.ZhanGT4

variable {f : ℂ → ℂ} {U : Set ℂ} {a : ℂ}

theorem eq_add_mul_dslope (f : ℂ → ℂ) (a z : ℂ) : f z = f a + (z - a) * dslope f a z := by
  have h := sub_smul_dslope f a z
  rw [smul_eq_mul] at h
  rw [h]; ring

theorem differentiableOn_dslope_of_isOpen (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (dslope f a) U :=
  (Complex.differentiableOn_dslope (hU.mem_nhds ha)).2 hf

/-- `f' = q + (z − a) q'` on `U`, `q = dslope f a`. -/
theorem hasDerivAt_eq_dslope (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U) {z : ℂ}
    (hz : z ∈ U) : HasDerivAt f (dslope f a z + (z - a) * deriv (dslope f a) z) z := by
  have hq := ((differentiableOn_dslope_of_isOpen hU ha hf).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have h := ((hasDerivAt_id z).sub_const a).mul hq |>.const_add (f a)
  have h' : HasDerivAt f (1 * dslope f a z + (id z - a) * deriv (dslope f a) z) z :=
    h.congr_of_eventuallyEq (Eventually.of_forall fun w => by
      simp only [Pi.mul_apply, id]; exact eq_add_mul_dslope f a w)
  refine h'.congr_deriv ?_
  simp only [id]; ring

theorem deriv_eq_dslope (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    deriv f z = dslope f a z + (z - a) * deriv (dslope f a) z :=
  (hasDerivAt_eq_dslope hU ha hf hz).deriv

/-- `f'' = 2q' + (z − a) q''` on `U`. -/
theorem hasDerivAt_deriv_eq_dslope (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U) {z : ℂ}
    (hz : z ∈ U) :
    HasDerivAt (deriv f) (2 * deriv (dslope f a) z + (z - a) * deriv (deriv (dslope f a)) z) z := by
  have hq := differentiableOn_dslope_of_isOpen hU ha hf
  have hq' := hq.deriv hU
  have h1 := (hq.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have h2 := (hq'.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have h := h1.add (((hasDerivAt_id z).sub_const a).mul h2)
  have heq : (fun w => dslope f a w + (id w - a) * deriv (dslope f a) w) =ᶠ[𝓝 z] deriv f := by
    filter_upwards [hU.mem_nhds hz] with w hw using (deriv_eq_dslope hU ha hf hw).symm
  refine (h.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  simp only [id]; ring

/-- **`f''(a) = 2 q'(a)`.** -/
theorem deriv_deriv_eq_two_mul (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U) :
    deriv (deriv f) a = 2 * deriv (dslope f a) a := by
  rw [(hasDerivAt_deriv_eq_dslope hU ha hf ha).deriv, sub_self, zero_mul, add_zero]

/-- **`f'''(a) = 3 q''(a)`.** -/
theorem deriv_deriv_deriv_eq_three_mul (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U) :
    deriv (deriv (deriv f)) a = 3 * deriv (deriv (dslope f a)) a := by
  have hq := differentiableOn_dslope_of_isOpen hU ha hf
  have hq' := hq.deriv hU
  have hq'' := hq'.deriv hU
  have h1 := (hq'.differentiableAt (hU.mem_nhds ha)).hasDerivAt
  have h2 := (hq''.differentiableAt (hU.mem_nhds ha)).hasDerivAt
  have h := (h1.const_mul 2).add (((hasDerivAt_id a).sub_const a).mul h2)
  have h3 : HasDerivAt (deriv (deriv f)) (2 * deriv (deriv (dslope f a)) a +
      (1 * deriv (deriv (dslope f a)) a + (id a - a) * deriv (deriv (deriv (dslope f a))) a)) a := by
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds ha] with w hw
    simp only [Pi.add_apply, Pi.mul_apply, id]
    exact (hasDerivAt_deriv_eq_dslope hU ha hf hw).deriv
  rw [h3.deriv]
  simp only [id, sub_self, zero_mul, add_zero]; ring

/-- `q(a) = f'(a)`. -/
theorem dslope_self_eq_deriv (f : ℂ → ℂ) (a : ℂ) : dslope f a a = deriv f a := dslope_same f a

/-- **Integral form of the divided difference**: `dslope f a z = ∫₀¹ f'(a + θ(z − a)) dθ` for `f` holomorphic on a
convex open set containing `a` and `z`. -/
theorem dslope_eq_integral (hU : IsOpen U) (hconv : Convex ℝ U) (hf : DifferentiableOn ℂ f U) (ha : a ∈ U)
    {z : ℂ} (hz : z ∈ U) : dslope f a z = ∫ θ in (0 : ℝ)..1, deriv f (a + (θ : ℂ) * (z - a)) := by
  have hseg : ∀ θ ∈ Icc (0 : ℝ) 1, a + (θ : ℂ) * (z - a) ∈ U := fun θ hθ => by
    have := hconv ha hz (sub_nonneg.2 hθ.2) hθ.1 (by ring)
    convert this using 1
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]; ring
  have hdc : ContinuousOn (deriv f) U := (hf.deriv hU).continuousOn
  have hγ : Continuous fun θ : ℝ => a + (θ : ℂ) * (z - a) := by fun_prop
  have hcont : ContinuousOn (fun θ : ℝ => deriv f (a + (θ : ℂ) * (z - a))) (Icc 0 1) :=
    hdc.comp hγ.continuousOn fun θ hθ => hseg θ hθ
  rcases eq_or_ne z a with rfl | hza
  · simp
  rw [dslope_of_ne f hza, slope_def_field]
  have hFTC : ∫ θ in (0 : ℝ)..1, deriv f (a + (θ : ℂ) * (z - a)) * (z - a) = f z - f a := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (zero_le_one)
      (f := fun θ : ℝ => f (a + (θ : ℂ) * (z - a)))
      (f' := fun θ : ℝ => deriv f (a + (θ : ℂ) * (z - a)) * (z - a))
      ((hf.continuousOn).comp hγ.continuousOn fun θ hθ => hseg θ hθ) (fun θ hθ => ?_)
      ((hcont.mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one)
    · simpa using h
    · have hd := (hf.differentiableAt (hU.mem_nhds (hseg θ (Ioo_subset_Icc_self hθ)))).hasDerivAt
      have hl : HasDerivAt (fun θ : ℝ => a + (θ : ℂ) * (z - a)) (z - a) θ := by
        simpa using ((hasDerivAt_id θ).ofReal_comp.mul_const (z - a)).const_add a
      exact hd.comp θ hl
  rw [intervalIntegral.integral_mul_const] at hFTC
  have hza' : z - a ≠ 0 := sub_ne_zero.2 hza
  rw [← hFTC, mul_div_assoc, div_self hza', mul_one]

/-! ### The removable form of the (D1) right-hand side -/

/-- The removable form `D̂` of `D(z) = 2f'(a)²/(f(z) − f(a)) − 2f'(z)/(z − a)`: with `q = dslope f a`,
`u = dslope q a`, `D̂ = 2(−u (q + q(a)) − q q')/q`. -/
def dHat (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  2 * (-(dslope (dslope f a) a z) * (dslope f a z + dslope f a a) - dslope f a z * deriv (dslope f a) z) /
    dslope f a z

/-- **`D̂ = D` off the base point.** -/
theorem dHat_eq (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) (hza : z ≠ a)
    (hq : dslope f a z ≠ 0) :
    dHat f a z = 2 * deriv f a ^ 2 / (f z - f a) - 2 * deriv f z / (z - a) := by
  have hza' : z - a ≠ 0 := sub_ne_zero.2 hza
  have e1 : f z - f a = (z - a) * dslope f a z := by rw [eq_add_mul_dslope f a z]; ring
  have e2 := deriv_eq_dslope hU ha hf hz
  have e3 : dslope f a z - dslope f a a = (z - a) * dslope (dslope f a) a z := by
    rw [eq_add_mul_dslope (dslope f a) a z]; ring
  have e4 : deriv f a = dslope f a a := (dslope_same f a).symm
  rw [dHat, e1, e2, e4, div_sub_div _ _ (mul_ne_zero hza' hq) hza',
    div_eq_div_iff hq (mul_ne_zero (mul_ne_zero hza' hq) hza')]
  linear_combination 2 * dslope f a z * (z - a) * (dslope f a z + dslope f a a) * e3

/-- **(D2), first identity**: `D̂(a) = −3 f''(a)`. -/
theorem dHat_self (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U) (hq : deriv f a ≠ 0) :
    dHat f a a = -3 * deriv (deriv f) a := by
  rw [dHat, deriv_deriv_eq_two_mul hU ha hf, dslope_same (dslope f a), dslope_same f a]
  field_simp
  ring

/-- **(D2), second identity**: `D̂'(a) = f''(a)²/(2f'(a)) − (4/3) f'''(a)`. -/
theorem hasDerivAt_dHat_self (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U) (hq : deriv f a ≠ 0) :
    HasDerivAt (dHat f a)
      (deriv (deriv f) a ^ 2 / (2 * deriv f a) - 4 / 3 * deriv (deriv (deriv f)) a) a := by
  set q := dslope f a with hqdef
  have hqd := differentiableOn_dslope_of_isOpen hU ha hf
  have hud := differentiableOn_dslope_of_isOpen hU ha hqd
  have hq'd := hqd.deriv hU
  have hn := hU.mem_nhds ha
  have hu := (hud.differentiableAt hn).hasDerivAt
  have hqq := (hqd.differentiableAt hn).hasDerivAt
  have hq' := (hq'd.differentiableAt hn).hasDerivAt
  have hqa : q a ≠ 0 := by rw [hqdef, dslope_same]; exact hq
  have h := ((((hu.neg).mul (hqq.add_const (q a))).sub (hqq.mul hq')).const_mul 2).div hqq hqa
  have h' := h.congr_of_eventuallyEq (f₁ := dHat f a) (Eventually.of_forall fun z => by
    simp only [dHat, hqdef, Pi.div_apply, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply])
  refine h'.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.neg_apply]
  have e1 : dslope q a a = deriv q a := dslope_same q a
  have e2 := deriv_deriv_eq_two_mul hU ha hqd
  have e3 := deriv_deriv_eq_two_mul hU ha hf
  have e4 := deriv_deriv_deriv_eq_three_mul hU ha hf
  have e5 : deriv f a = q a := by rw [hqdef, dslope_same]
  rw [e1, e3, e4, e5, ← hqdef]
  rw [← hqdef] at e2
  rw [e2]
  field_simp
  ring

/-- `D̂` is holomorphic where `q` does not vanish. -/
theorem differentiableOn_dHat (hU : IsOpen U) (ha : a ∈ U) (hf : DifferentiableOn ℂ f U)
    (hq : ∀ z ∈ U, dslope f a z ≠ 0) : DifferentiableOn ℂ (dHat f a) U := by
  have hqd := differentiableOn_dslope_of_isOpen hU ha hf
  have hud := differentiableOn_dslope_of_isOpen hU ha hqd
  have hq'd := hqd.deriv hU
  intro z hz
  have h := (((((hud.neg).mul (hqd.add_const (dslope f a a))).sub (hqd.mul hq'd)).const_smul (2 : ℂ)).div hqd hq) z hz
  refine h.congr (fun w hw => ?_) ?_ <;> simp [dHat]

end InteractingSLE.ZhanGT4
