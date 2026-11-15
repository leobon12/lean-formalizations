/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import InteractingSLE.Spec.Ito.Observable

/-!
# Lemma DS1: the regularized test function and its Itô generator

Packet PROVE-T14-TIP (specification supplement §12, **Lemma DS1**, `source/spec/p529-576.md` L523–L575, pp. 551–553).
The proof of DS1 applies Itô's formula to "a bounded nondecreasing smooth function with
`f'_ν(x) = p(x + ν)^{p−1}` (`0 ≤ x ≤ r`), `f'_ν(x) = 0` (`x ≥ 2r`) [and] a fixed smooth interpolation on `[r, 2r]`"
of the nearest right gap `X₁`. This file uses the product form

  `f(x) = ((x + ν)^p − ν^p) · φ(x)`,  `φ(x) = smoothTransition(2 − x/r)`,

which equals `(x + ν)^p − ν^p` on `[0, r]` (so `f' = p(x + ν)^{p−1}` there), vanishes for `x ≥ 2r`, is bounded by
`(3r)^p` on `[0, ∞)`, and whose first two derivatives on `[r, 2r]` are bounded uniformly in `ν < r` (`fn1`, `fn2`
bounds below). Monotonicity of `f` on `[r, 2r]` is not needed: the proof only uses that `f` is bounded and that the
drift is bounded below on `[r, 2r]`.

* `cut`, `cut1`, `cut2`: the cutoff and its derivatives; `exists_bound_deriv_smoothTransition`;
* `pw`, `pw1`, `pw2`: `(x + ν)^p − ν^p` and its derivatives;
* `fn`, `fn1`, `fn2`: the test function and its derivatives (`hasDerivAt_fn`, `hasDerivAt_fn1`);
* `obs κ p ν r (Λ, b) = f(Λ.1 − √κ b)`, the observable in the Itô coordinates `Λ = (X₁ + √κ B, ·)`; it is smooth on
  `obsRegion κ ν = {Λ.1 − √κ b > −ν}` (`contDiffOn_obs`), and **`itoGen_obs`**: its Itô generator is
  `f'(x) v.1 + (κ/2) f''(x)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE

namespace Supp12

namespace DS1

/-! ### The cutoff -/

/-- The cutoff `φ_r(x) = smoothTransition(2 − x/r)`: `1` for `x ≤ r`, `0` for `x ≥ 2r` (`r > 0`). -/
def cut (r x : ℝ) : ℝ := Real.smoothTransition (2 - x / r)

/-- Its derivative. -/
def cut1 (r x : ℝ) : ℝ := -(deriv Real.smoothTransition (2 - x / r) / r)

/-- Its second derivative. -/
def cut2 (r x : ℝ) : ℝ := deriv (deriv Real.smoothTransition) (2 - x / r) / r ^ 2

theorem contDiff_smoothTransition_three : ContDiff ℝ 3 Real.smoothTransition :=
  Real.smoothTransition.contDiff

theorem contDiff_smoothTransition_two : ContDiff ℝ 2 Real.smoothTransition :=
  Real.smoothTransition.contDiff

theorem differentiable_smoothTransition : Differentiable ℝ Real.smoothTransition :=
  contDiff_smoothTransition_two.differentiable (by norm_num)

theorem contDiff_deriv_smoothTransition : ContDiff ℝ 1 (deriv Real.smoothTransition) :=
  contDiff_smoothTransition_two.iterate_deriv' 1 1

theorem differentiable_deriv_smoothTransition : Differentiable ℝ (deriv Real.smoothTransition) :=
  contDiff_deriv_smoothTransition.differentiable (by norm_num)

theorem continuous_deriv_deriv_smoothTransition : Continuous (deriv (deriv Real.smoothTransition)) :=
  (contDiff_smoothTransition_two.iterate_deriv' 0 2).continuous

theorem hasDerivAt_cut {r : ℝ} (x : ℝ) : HasDerivAt (cut r) (cut1 r x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 2 - x / r) (-(1 / r)) x := by
    simpa using ((hasDerivAt_id x).div_const r).const_sub 2
  have h2 := (differentiable_smoothTransition (2 - x / r)).hasDerivAt.comp x h1
  have e : cut1 r x = deriv Real.smoothTransition (2 - x / r) * -(1 / r) := by unfold cut1; ring
  rw [e]; exact h2

theorem hasDerivAt_cut1 {r : ℝ} (x : ℝ) : HasDerivAt (cut1 r) (cut2 r x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 2 - x / r) (-(1 / r)) x := by
    simpa using ((hasDerivAt_id x).div_const r).const_sub 2
  have h3 := (((differentiable_deriv_smoothTransition (2 - x / r)).hasDerivAt.comp x h1).div_const r).neg
  have e : cut2 r x = -(deriv (deriv Real.smoothTransition) (2 - x / r) * -(1 / r) / r) := by
    unfold cut2; ring
  rw [e]; exact h3

theorem cut_nonneg (r x : ℝ) : 0 ≤ cut r x := Real.smoothTransition.nonneg _

theorem cut_le_one (r x : ℝ) : cut r x ≤ 1 := Real.smoothTransition.le_one _

theorem cut_eq_one {r x : ℝ} (hr : 0 < r) (hx : x ≤ r) : cut r x = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have : x / r ≤ 1 := (div_le_one hr).2 hx
  linarith

theorem cut_eq_zero {r x : ℝ} (hr : 0 < r) (hx : 2 * r ≤ x) : cut r x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : 2 ≤ x / r := (le_div_iff₀ hr).2 (by linarith)
  linarith

/-- `smoothTransition` is locally constant off `[0, 1]`. -/
theorem smoothTransition_eventuallyEq_of_one_lt {y : ℝ} (hy : 1 < y) :
    Real.smoothTransition =ᶠ[𝓝 y] fun _ => 1 := by
  filter_upwards [lt_mem_nhds hy] with z hz using Real.smoothTransition.one_of_one_le hz.le

theorem smoothTransition_eventuallyEq_of_neg {y : ℝ} (hy : y < 0) :
    Real.smoothTransition =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [gt_mem_nhds hy] with z hz using Real.smoothTransition.zero_of_nonpos hz.le

theorem deriv_smoothTransition_of_one_lt {y : ℝ} (hy : 1 < y) : deriv Real.smoothTransition y = 0 := by
  rw [(smoothTransition_eventuallyEq_of_one_lt hy).deriv_eq]; exact deriv_const y 1

theorem deriv_smoothTransition_of_neg {y : ℝ} (hy : y < 0) : deriv Real.smoothTransition y = 0 := by
  rw [(smoothTransition_eventuallyEq_of_neg hy).deriv_eq]; exact deriv_const y 0

theorem deriv_deriv_smoothTransition_of_one_lt {y : ℝ} (hy : 1 < y) :
    deriv (deriv Real.smoothTransition) y = 0 := by
  have : deriv Real.smoothTransition =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [lt_mem_nhds hy] with z hz using deriv_smoothTransition_of_one_lt hz
  rw [this.deriv_eq]; exact deriv_const y 0

theorem deriv_deriv_smoothTransition_of_neg {y : ℝ} (hy : y < 0) :
    deriv (deriv Real.smoothTransition) y = 0 := by
  have : deriv Real.smoothTransition =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [gt_mem_nhds hy] with z hz using deriv_smoothTransition_of_neg hz
  rw [this.deriv_eq]; exact deriv_const y 0

theorem deriv_smoothTransition_of_nonpos {y : ℝ} (hy : y ≤ 0) : deriv Real.smoothTransition y = 0 := by
  rcases hy.lt_or_eq with h | rfl
  · exact deriv_smoothTransition_of_neg h
  · have hc : Continuous (deriv Real.smoothTransition) := contDiff_deriv_smoothTransition.continuous
    have : Tendsto (deriv Real.smoothTransition) (𝓝[<] 0) (𝓝 0) := by
      refine (tendsto_congr' ?_).1 tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz using (deriv_smoothTransition_of_neg hz).symm
    exact tendsto_nhds_unique (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) this

theorem deriv_deriv_smoothTransition_of_nonpos {y : ℝ} (hy : y ≤ 0) :
    deriv (deriv Real.smoothTransition) y = 0 := by
  rcases hy.lt_or_eq with h | rfl
  · exact deriv_deriv_smoothTransition_of_neg h
  · have : Tendsto (deriv (deriv Real.smoothTransition)) (𝓝[<] 0) (𝓝 0) := by
      refine (tendsto_congr' ?_).1 tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with z hz using (deriv_deriv_smoothTransition_of_neg hz).symm
    exact tendsto_nhds_unique
      (continuous_deriv_deriv_smoothTransition.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) this

/-- **The derivatives of the cutoff profile are bounded.** -/
theorem exists_bound_deriv_smoothTransition :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |deriv Real.smoothTransition y| ≤ K ∧
      |deriv (deriv Real.smoothTransition) y| ≤ K := by
  have hc1 : Continuous (deriv Real.smoothTransition) := contDiff_deriv_smoothTransition.continuous
  obtain ⟨K₁, hK₁⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc1.continuousOn
  obtain ⟨K₂, hK₂⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    continuous_deriv_deriv_smoothTransition.continuousOn
  simp only [Real.norm_eq_abs] at hK₁ hK₂
  refine ⟨max (max K₁ K₂) 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · exact ⟨(hK₁ y hy).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (hK₂ y hy).trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  · rcases not_and_or.1 hy with h | h
    · push Not at h
      rw [deriv_smoothTransition_of_neg h, deriv_deriv_smoothTransition_of_neg h, abs_zero]
      exact ⟨le_max_right _ _, le_max_right _ _⟩
    · push Not at h
      rw [deriv_smoothTransition_of_one_lt h, deriv_deriv_smoothTransition_of_one_lt h, abs_zero]
      exact ⟨le_max_right _ _, le_max_right _ _⟩

theorem cut1_eq_zero_of_lt {r x : ℝ} (hr : 0 < r) (hx : x < r) : cut1 r x = 0 := by
  have : 1 < 2 - x / r := by have := (div_lt_one hr).2 hx; linarith
  simp [cut1, deriv_smoothTransition_of_one_lt this]

theorem cut2_eq_zero_of_lt {r x : ℝ} (hr : 0 < r) (hx : x < r) : cut2 r x = 0 := by
  have : 1 < 2 - x / r := by have := (div_lt_one hr).2 hx; linarith
  simp [cut2, deriv_deriv_smoothTransition_of_one_lt this]

theorem cut1_eq_zero_of_ge {r x : ℝ} (hr : 0 < r) (hx : 2 * r ≤ x) : cut1 r x = 0 := by
  have : 2 - x / r ≤ 0 := by have : 2 ≤ x / r := (le_div_iff₀ hr).2 (by linarith); linarith
  simp [cut1, deriv_smoothTransition_of_nonpos this]

theorem cut2_eq_zero_of_ge {r x : ℝ} (hr : 0 < r) (hx : 2 * r ≤ x) : cut2 r x = 0 := by
  have : 2 - x / r ≤ 0 := by have : 2 ≤ x / r := (le_div_iff₀ hr).2 (by linarith); linarith
  simp [cut2, deriv_deriv_smoothTransition_of_nonpos this]

theorem abs_cut1_le {r K : ℝ} (hr : 0 < r) (hK : ∀ y, |deriv Real.smoothTransition y| ≤ K) (x : ℝ) :
    |cut1 r x| ≤ K / r := by
  rw [cut1, abs_neg, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (hK _) hr.le

theorem abs_cut2_le {r K : ℝ} (hr : 0 < r) (hK : ∀ y, |deriv (deriv Real.smoothTransition) y| ≤ K)
    (x : ℝ) : |cut2 r x| ≤ K / r ^ 2 := by
  rw [cut2, abs_div, abs_of_pos (by positivity : (0 : ℝ) < r ^ 2)]
  exact div_le_div_of_nonneg_right (hK _) (by positivity)

/-! ### The power part -/

/-- `(x + ν)^p − ν^p`. -/
def pw (p ν x : ℝ) : ℝ := (x + ν) ^ p - ν ^ p

/-- Its derivative `p (x + ν)^{p−1}`. -/
def pw1 (p ν x : ℝ) : ℝ := p * (x + ν) ^ (p - 1)

/-- Its second derivative `p (p − 1) (x + ν)^{p−2}`. -/
def pw2 (p ν x : ℝ) : ℝ := p * (p - 1) * (x + ν) ^ (p - 2)

theorem hasDerivAt_pw {p ν x : ℝ} (hx : 0 < x + ν) : HasDerivAt (pw p ν) (pw1 p ν x) x := by
  have h0 : HasDerivAt (fun y : ℝ => y + ν) 1 x := (hasDerivAt_id x).add_const ν
  have h := (h0.rpow_const (p := p) (Or.inl hx.ne')).sub_const (ν ^ p)
  have e : pw1 p ν x = 1 * p * (x + ν) ^ (p - 1) := by unfold pw1; ring
  rw [e]; exact h

theorem hasDerivAt_pw1 {p ν x : ℝ} (hx : 0 < x + ν) : HasDerivAt (pw1 p ν) (pw2 p ν x) x := by
  have h0 : HasDerivAt (fun y : ℝ => y + ν) 1 x := (hasDerivAt_id x).add_const ν
  have h := (h0.rpow_const (p := p - 1) (Or.inl hx.ne')).const_mul p
  have e : pw2 p ν x = p * (1 * (p - 1) * (x + ν) ^ (p - 1 - 1)) := by
    unfold pw2; rw [show p - 1 - 1 = p - 2 by ring]; ring
  rw [e]; exact h

/-! ### The test function -/

/-- The test function `f(x) = ((x + ν)^p − ν^p) φ_r(x)`. -/
def fn (p ν r x : ℝ) : ℝ := pw p ν x * cut r x

/-- `f'`. -/
def fn1 (p ν r x : ℝ) : ℝ := pw1 p ν x * cut r x + pw p ν x * cut1 r x

/-- `f''`. -/
def fn2 (p ν r x : ℝ) : ℝ := pw2 p ν x * cut r x + 2 * (pw1 p ν x * cut1 r x) + pw p ν x * cut2 r x

theorem hasDerivAt_fn {p ν r x : ℝ} (hx : 0 < x + ν) : HasDerivAt (fn p ν r) (fn1 p ν r x) x :=
  (hasDerivAt_pw hx).mul (hasDerivAt_cut x)

theorem hasDerivAt_fn1 {p ν r x : ℝ} (hx : 0 < x + ν) : HasDerivAt (fn1 p ν r) (fn2 p ν r x) x := by
  have h := ((hasDerivAt_pw1 (p := p) hx).mul (hasDerivAt_cut (r := r) x)).add
    ((hasDerivAt_pw (p := p) hx).mul (hasDerivAt_cut1 (r := r) x))
  have e : fn2 p ν r x = pw2 p ν x * cut r x + pw1 p ν x * cut1 r x +
      (pw1 p ν x * cut1 r x + pw p ν x * cut2 r x) := by unfold fn2; ring
  rw [e]; exact h

theorem contDiffAt_fn {p ν r x : ℝ} (hx : 0 < x + ν) {n : WithTop ℕ∞} (hn : n ≤ 3) :
    ContDiffAt ℝ n (fn p ν r) x := by
  have h1 : ContDiffAt ℝ n (fun x : ℝ => (x + ν) ^ p) x :=
    (Real.contDiffAt_rpow_const_of_ne (p := p) hx.ne').comp x (contDiffAt_id.add contDiffAt_const)
  have h2 : ContDiffAt ℝ n (cut r) x :=
    ((contDiff_smoothTransition_three.of_le hn).comp (contDiff_const.sub (contDiff_id.div_const r))).contDiffAt
  exact (h1.sub contDiffAt_const).mul h2

/-! ### The observable in the Itô coordinates -/

/-- The observable `(Λ, b) ↦ f(Λ.1 − √κ b)`. -/
def obs (κ p ν r : ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ := fn p ν r (q.1.1 - Real.sqrt κ * q.2)

/-- The gap read off the coordinates: `x = Λ.1 − √κ b`. -/
def gapX (κ : ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ := q.1.1 - Real.sqrt κ * q.2

/-- The region where the observable is smooth: `x > −ν`. -/
def obsRegion (κ ν : ℝ) : Set ((ℝ × ℝ) × ℝ) := {q | 0 < gapX κ q + ν}

theorem continuous_gapX (κ : ℝ) : Continuous (gapX κ) := by
  unfold gapX; fun_prop

theorem isOpen_obsRegion (κ ν : ℝ) : IsOpen (obsRegion κ ν) :=
  isOpen_lt continuous_const ((continuous_gapX κ).add continuous_const)

theorem contDiffAt_obs {κ p ν r : ℝ} {q : (ℝ × ℝ) × ℝ} (hq : q ∈ obsRegion κ ν) {n : WithTop ℕ∞}
    (hn : n ≤ 3) : ContDiffAt ℝ n (obs κ p ν r) q := by
  have hl : ContDiff ℝ n (gapX κ) := by unfold gapX; fun_prop
  exact (contDiffAt_fn (r := r) hq hn).comp q hl.contDiffAt

theorem contDiffOn_obs (κ p ν r : ℝ) : ContDiffOn ℝ 3 (obs κ p ν r) (obsRegion κ ν) :=
  fun _ hq => (contDiffAt_obs hq le_rfl).contDiffWithinAt

/-- **The Itô generator of the observable**: `itoGen F (Λ, b) v = f'(x) v.1 + (κ/2) f''(x)`, `x = Λ.1 − √κ b`. -/
theorem itoGen_obs {κ p ν r : ℝ} (hκ : 0 ≤ κ) {q : (ℝ × ℝ) × ℝ} (hq : q ∈ obsRegion κ ν) (v : ℝ × ℝ) :
    Ito.itoGen (obs κ p ν r) q v = fn1 p ν r (gapX κ q) * v.1 + κ / 2 * fn2 p ν r (gapX κ q) := by
  have hd : DifferentiableAt ℝ (obs κ p ν r) q := (contDiffAt_obs hq (n := 1) (by norm_num)).differentiableAt
    (by norm_num)
  -- the first partial derivative
  have h1 : Ito.partialFst (obs κ p ν r) q v = fn1 p ν r (gapX κ q) * v.1 := by
    refine Ito.partialFst_eq_of_hasDerivAt hd ?_
    have hl : HasDerivAt (fun t : ℝ => gapX κ q + t * v.1) v.1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.1).const_add (gapX κ q)
    have hfx : HasDerivAt (fn p ν r) (fn1 p ν r (gapX κ q)) (gapX κ q + 0 * v.1) := by
      rw [zero_mul, add_zero]; exact hasDerivAt_fn hq
    have hc := hfx.comp (0 : ℝ) hl
    have e : (fun t : ℝ => obs κ p ν r (q.1 + t • v, q.2)) =
        fn p ν r ∘ fun t : ℝ => gapX κ q + t * v.1 := by
      funext t; simp only [obs, gapX, Function.comp_apply, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      ring_nf
    rw [e]; exact hc
  -- the second partial derivative in `b`
  have hlin : ∀ y : ℝ, HasDerivAt (fun y' : ℝ => q.1.1 - Real.sqrt κ * y') (-(Real.sqrt κ)) y := fun y => by
    simpa using ((hasDerivAt_id y).const_mul (Real.sqrt κ)).const_sub q.1.1
  have hfun : (fun y : ℝ => obs κ p ν r (q.1, y)) = fn p ν r ∘ fun y' : ℝ => q.1.1 - Real.sqrt κ * y' := rfl
  have hsnd : ∀ᶠ y in 𝓝 q.2, Ito.partialSnd (obs κ p ν r) (q.1, y) =
      fn1 p ν r (q.1.1 - Real.sqrt κ * y) * -(Real.sqrt κ) := by
    have hopen : ∀ᶠ y in 𝓝 q.2, (q.1, y) ∈ obsRegion κ ν := by
      have hc : Continuous fun y : ℝ => ((q.1, y) : (ℝ × ℝ) × ℝ) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds ((isOpen_obsRegion κ ν).mem_nhds hq)
    filter_upwards [hopen] with y hy
    have hdy : DifferentiableAt ℝ (obs κ p ν r) (q.1, y) :=
      (contDiffAt_obs hy (n := 1) (by norm_num)).differentiableAt (by norm_num)
    refine Ito.partialSnd_eq_of_hasDerivAt hdy ?_
    have hc := (hasDerivAt_fn (r := r) (p := p) (show 0 < q.1.1 - Real.sqrt κ * y + ν from hy)).comp y
      (hlin y)
    rw [hfun]; exact hc
  have h2 : Ito.partialSndSnd (obs κ p ν r) q = κ * fn2 p ν r (gapX κ q) := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt (contDiffAt_obs hq (by norm_num)) hsnd ?_
    have hc := ((hasDerivAt_fn1 (r := r) (p := p) hq).comp q.2 (hlin q.2)).mul_const (-(Real.sqrt κ))
    have hk : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ
    have e : κ * fn2 p ν r (gapX κ q) = fn2 p ν r (gapX κ q) * -(Real.sqrt κ) * -(Real.sqrt κ) := by
      rw [show fn2 p ν r (gapX κ q) * -(Real.sqrt κ) * -(Real.sqrt κ) =
        (Real.sqrt κ * Real.sqrt κ) * fn2 p ν r (gapX κ q) by ring, hk]
    rw [e]; exact hc
  rw [Ito.itoGen, h1, h2]
  ring

end DS1

end Supp12

end InteractingSLE
