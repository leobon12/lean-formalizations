/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Noncollision on the strip life: the one-dimensional Lyapunov functions and the generator bound

Packet PROVE-ZHAN-A3. Astra, *Formalization proofs and dependency audit*, "Complete proof of noncollision"
(`source/external/AstraIG1/ig1_formalization_proofs.txt` L1103–L1169). In strip time the nearest left strip gap
`X = ξ − p^L_1` has drift `b ≥ κ/(2X) − C` while every opposite gap is bounded below ((3.12)–(3.13), Abel summation
of the prefix sums `≥ c = κ/2 − 2`). Instead of the scale-function comparison (3.14), this file prepares a single
**Lyapunov function** for the whole strip state, which gives noncollision on the strip life (including its end) and
the unboundedness of the strip clock at once:

  `H = ψ(G) + h(X) + h(Y)`,  `ψ(G) = log(1 + G²) − log G`,  `h = χ · k₀`,  `k₀(x) = −log(1 − e^{−x}) + β e^{−x}`,

where `G = W − v` is the chordal end-mark gap (`ξ − t = log G`), `X`, `Y` the nearest left and right strip gaps, and
`χ` a smooth cutoff (`1` on `(−∞, c₁]`, `0` on `[c₂, ∞)`). The function `−log(1 − e^{−x})` is the critical (scale)
function of the repulsion `κ/(2x)`; the extra `β e^{−x}` produces the strictly negative drift `−(βκ/2)/x` near
`x = 0` that absorbs all other singular terms.

In strip variables (`u = 1/(1 − e^{−X})`, `w = e^{−Y}/(1 − e^{−Y})`, `A` the force sum of the driver), the strip
generator of `H` is `g + genL X A + genR Y A` with `g ≤ |A| + 2κ`; `ncGen_bound` shows it is bounded above by a
constant, given the Abel bounds of `A` and the opposite-gap separation `X ≤ c₂ → Y > c₂` (from the increasing
strip distance `X + Y` of the two nearest lower marks).

## Main definitions

* `ncPsi`, `ncK`, `ncCut`, `ncH`: `ψ`, `k₀`, `χ`, `h = χ k₀`;
* `uOf`, `wOf`: `1/(1 − e^{−x})`, `e^{−y}/(1 − e^{−y})`;
* `genL`, `genR`: the strip generators of `h(X)`, `h(Y)` in terms of `A`;
* `ncBeta`: the choice of `β`.

## Main results

* derivative facts: `hasDerivAt_ncPsi`, `hasDerivAt_ncPsiD`, `hasDerivAt_ncK`, `hasDerivAt_ncKD`,
  `deriv_ncH_of_lt`, `deriv_deriv_ncH_of_lt`, `deriv_ncH_of_gt`, `deriv_deriv_ncH_of_gt`,
  `exists_bound_deriv_ncH`;
* bounds: `log_two_le_ncPsi`, `abs_mul_ncPsiD_le`, `abs_sq_mul_ncPsiDD_le`, `log_le_ncH`, `ncPsi_ge_*`;
* `genL_le`, `genR_le` (the repulsion near `0`), **`ncGen_bound`** (the generator bound).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE

namespace Zhan

/-! ### `ψ(x) = log(1 + x²) − log x` -/

/-- `ψ(x) = log(1 + x²) − log x = log(x + 1/x)`, the part of the Lyapunov function that controls `G = W − v`. -/
def ncPsi (x : ℝ) : ℝ := Real.log (1 + x ^ 2) - Real.log x

/-- `ψ'`. -/
def ncPsiD (x : ℝ) : ℝ := 2 * x / (1 + x ^ 2) - x⁻¹

/-- `ψ''`. -/
def ncPsiDD (x : ℝ) : ℝ := 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2 + (x ^ 2)⁻¹

theorem hasDerivAt_ncPsi {x : ℝ} (hx : 0 < x) : HasDerivAt ncPsi (ncPsiD x) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have h2 := (h1.log hpos.ne').sub (Real.hasDerivAt_log hx.ne')
  exact h2

theorem hasDerivAt_ncPsiD {x : ℝ} (hx : 0 < x) : HasDerivAt ncPsiD (ncPsiDD x) x := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
  have h3 := (h2.div h1 hpos.ne').sub (hasDerivAt_inv hx.ne')
  refine h3.congr_deriv ?_
  simp only [ncPsiDD]
  field_simp
  ring

theorem contDiffOn_ncPsi {n : WithTop ℕ∞} : ContDiffOn ℝ n ncPsi (Ioi 0) := by
  have h1 : ContDiffOn ℝ n (fun x : ℝ => Real.log (1 + x ^ 2)) (Ioi 0) :=
    ContDiffOn.log (by fun_prop) fun x _ => by positivity
  have h2 : ContDiffOn ℝ n (fun x : ℝ => Real.log x) (Ioi 0) :=
    ContDiffOn.log contDiffOn_id fun x hx => (mem_Ioi.1 hx).ne'
  exact h1.sub h2

theorem ncPsi_eq {x : ℝ} (hx : 0 < x) : ncPsi x = Real.log (x + x⁻¹) := by
  rw [ncPsi, ← Real.log_div (by positivity) hx.ne']
  congr 1
  field_simp
  ring

theorem log_two_le_ncPsi {x : ℝ} (hx : 0 < x) : Real.log 2 ≤ ncPsi x := by
  rw [ncPsi_eq hx]
  refine Real.log_le_log (by norm_num) ?_
  have h : 0 ≤ (x - 1) ^ 2 / x := div_nonneg (sq_nonneg _) hx.le
  have e : (x - 1) ^ 2 / x = x + x⁻¹ - 2 := by field_simp; ring
  linarith

theorem neg_log_le_ncPsi (x : ℝ) : -Real.log x ≤ ncPsi x := by
  have : 0 ≤ Real.log (1 + x ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg x])
  simp only [ncPsi]; linarith

theorem log_le_ncPsi {x : ℝ} (hx : 0 < x) : Real.log x ≤ ncPsi x := by
  have h : Real.log (x ^ 2) ≤ Real.log (1 + x ^ 2) := Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_pow] at h
  simp only [ncPsi]; push_cast at h; linarith

/-- `|x ψ'(x)| ≤ 1`. -/
theorem abs_mul_ncPsiD_le {x : ℝ} (hx : 0 < x) : |x * ncPsiD x| ≤ 1 := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have e : x * ncPsiD x = 2 * x ^ 2 / (1 + x ^ 2) - 1 := by
    simp only [ncPsiD]; field_simp
  rw [e, abs_le]
  have h0 : 0 ≤ 2 * x ^ 2 / (1 + x ^ 2) := by positivity
  have h1 : 2 * x ^ 2 / (1 + x ^ 2) ≤ 2 := by
    rw [div_le_iff₀ hpos]; nlinarith
  constructor <;> linarith

/-- `|x² ψ''(x)| ≤ 3`. -/
theorem abs_sq_mul_ncPsiDD_le {x : ℝ} (hx : 0 < x) : |x ^ 2 * ncPsiDD x| ≤ 3 := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have e : x ^ 2 * ncPsiDD x = 2 * x ^ 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2 + 1 := by
    simp only [ncPsiDD]; field_simp
  rw [e]
  have h1 : |2 * x ^ 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2| ≤ 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + x ^ 2) ^ 2), div_le_iff₀ (by positivity)]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * x ^ 2)]
    have h2 : |1 - x ^ 2| ≤ 1 + x ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg x]
    have h3 : 2 * x ^ 2 ≤ 2 * (1 + x ^ 2) := by nlinarith
    calc 2 * x ^ 2 * |1 - x ^ 2| ≤ 2 * (1 + x ^ 2) * (1 + x ^ 2) :=
          mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
      _ = 2 * (1 + x ^ 2) ^ 2 := by ring
  calc |2 * x ^ 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2 + 1|
      ≤ |2 * x ^ 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2| + |(1 : ℝ)| := abs_add_le _ _
    _ ≤ 3 := by rw [abs_one]; linarith

/-! ### `k₀(x) = −log(1 − e^{−x}) + β e^{−x}` -/

/-- `k₀(x) = −log(1 − e^{−x}) + β e^{−x}`. -/
def ncK (β x : ℝ) : ℝ := -Real.log (1 - Real.exp (-x)) + β * Real.exp (-x)

/-- `k₀'`. -/
def ncKD (β x : ℝ) : ℝ := -(Real.exp (-x) / (1 - Real.exp (-x))) - β * Real.exp (-x)

/-- `k₀''`. -/
def ncKDD (β x : ℝ) : ℝ := Real.exp (-x) / (1 - Real.exp (-x)) ^ 2 + β * Real.exp (-x)

theorem one_sub_exp_neg_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - Real.exp (-x) := by
  have : Real.exp (-x) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

theorem hasDerivAt_exp_neg (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
  simpa using (hasDerivAt_neg x).exp

theorem hasDerivAt_ncK (β : ℝ) {x : ℝ} (hx : 0 < x) : HasDerivAt (ncK β) (ncKD β x) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) (Real.exp (-x)) x := by
    simpa using (hasDerivAt_exp_neg x).const_sub 1
  have h2 := ((h1.log (one_sub_exp_neg_pos hx).ne').neg).add ((hasDerivAt_exp_neg x).const_mul β)
  refine h2.congr_deriv ?_
  simp only [ncKD]; ring

theorem hasDerivAt_ncKD (β : ℝ) {x : ℝ} (hx : 0 < x) : HasDerivAt (ncKD β) (ncKDD β x) x := by
  have hpos := one_sub_exp_neg_pos hx
  have h1 : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) (Real.exp (-x)) x := by
    simpa using (hasDerivAt_exp_neg x).const_sub 1
  have h2 := (((hasDerivAt_exp_neg x).div h1 hpos.ne').neg).sub ((hasDerivAt_exp_neg x).const_mul β)
  refine h2.congr_deriv ?_
  simp only [ncKDD]
  field_simp
  ring

theorem contDiffOn_ncK (β : ℝ) {n : WithTop ℕ∞} : ContDiffOn ℝ n (ncK β) (Ioi 0) := by
  have h1 : ContDiffOn ℝ n (fun x : ℝ => Real.log (1 - Real.exp (-x))) (Ioi 0) :=
    ContDiffOn.log (by fun_prop) fun x hx => (one_sub_exp_neg_pos (mem_Ioi.1 hx)).ne'
  have h2 : ContDiffOn ℝ n (fun x : ℝ => β * Real.exp (-x)) (Ioi 0) := by fun_prop
  exact h1.neg.add h2

theorem neg_log_le_ncK {β x : ℝ} (hβ : 0 ≤ β) (hx : 0 < x) : -Real.log x ≤ ncK β x := by
  have h1 : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  have h2 := Real.log_le_log (one_sub_exp_neg_pos hx) h1
  have h3 : 0 ≤ β * Real.exp (-x) := mul_nonneg hβ (Real.exp_pos _).le
  simp only [ncK]; linarith

theorem ncK_nonneg {β x : ℝ} (hβ : 0 ≤ β) (hx : 0 < x) : 0 ≤ ncK β x := by
  have h1 : 1 - Real.exp (-x) ≤ 1 := by linarith [Real.exp_pos (-x)]
  have h2 := Real.log_nonpos (one_sub_exp_neg_pos hx).le h1
  have h3 : 0 ≤ β * Real.exp (-x) := mul_nonneg hβ (Real.exp_pos _).le
  simp only [ncK]; linarith

/-! ### The cutoff and `h = χ k₀` -/

/-- The smooth cutoff `χ`: `1` on `(−∞, c₁]`, `0` on `[c₂, ∞)`. -/
def ncCut (c₁ c₂ x : ℝ) : ℝ := Real.smoothTransition ((c₂ - x) / (c₂ - c₁))

/-- `h = χ k₀`. -/
def ncH (β c₁ c₂ x : ℝ) : ℝ := ncCut c₁ c₂ x * ncK β x

variable {β c₁ c₂ : ℝ}

theorem ncCut_eq_one (hc : c₁ < c₂) {x : ℝ} (hx : x ≤ c₁) : ncCut c₁ c₂ x = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ (by linarith)]; linarith

theorem ncCut_eq_zero (hc : c₁ < c₂) {x : ℝ} (hx : c₂ ≤ x) : ncCut c₁ c₂ x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem ncCut_nonneg (x : ℝ) : 0 ≤ ncCut c₁ c₂ x := Real.smoothTransition.nonneg _

theorem contDiff_ncCut {n : ℕ∞} : ContDiff ℝ n (ncCut c₁ c₂) := by
  unfold ncCut
  exact (Real.smoothTransition.contDiff (n := n)).comp (by fun_prop)

theorem contDiffOn_ncH {n : ℕ∞} : ContDiffOn ℝ n (ncH β c₁ c₂) (Ioi 0) :=
  (contDiff_ncCut (n := n)).contDiffOn.mul (contDiffOn_ncK β)

theorem ncH_nonneg (hβ : 0 ≤ β) {x : ℝ} (hx : 0 < x) : 0 ≤ ncH β c₁ c₂ x :=
  mul_nonneg (ncCut_nonneg x) (ncK_nonneg hβ hx)

theorem ncH_eventuallyEq_ncK (hc : c₁ < c₂) {x : ℝ} (hx : x < c₁) : ncH β c₁ c₂ =ᶠ[𝓝 x] ncK β := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  simp only [ncH, ncCut_eq_one hc (le_of_lt hy), one_mul]

theorem ncH_eventuallyEq_zero (hc : c₁ < c₂) {x : ℝ} (hx : c₂ < x) : ncH β c₁ c₂ =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [ncH, ncCut_eq_zero hc (le_of_lt hy), zero_mul]

theorem log_le_ncH (hβ : 0 ≤ β) (hc : c₁ < c₂) {x : ℝ} (hx : 0 < x) (hx₁ : x ≤ c₁) :
    -Real.log x ≤ ncH β c₁ c₂ x := by
  simp only [ncH, ncCut_eq_one hc hx₁, one_mul]
  exact neg_log_le_ncK hβ hx

theorem deriv_ncH_of_lt (hc : c₁ < c₂) {x : ℝ} (hx : 0 < x) (hx₁ : x < c₁) :
    deriv (ncH β c₁ c₂) x = ncKD β x := by
  rw [(ncH_eventuallyEq_ncK hc hx₁).deriv_eq]
  exact (hasDerivAt_ncK β hx).deriv

theorem deriv_deriv_ncH_of_lt (hc : c₁ < c₂) {x : ℝ} (hx : 0 < x) (hx₁ : x < c₁) :
    deriv (deriv (ncH β c₁ c₂)) x = ncKDD β x := by
  have hev : deriv (ncH β c₁ c₂) =ᶠ[𝓝 x] ncKD β := by
    filter_upwards [Ioo_mem_nhds hx hx₁] with y hy
    exact deriv_ncH_of_lt hc hy.1 hy.2
  rw [hev.deriv_eq]
  exact (hasDerivAt_ncKD β hx).deriv

theorem deriv_ncH_of_gt (hc : c₁ < c₂) {x : ℝ} (hx : c₂ < x) : deriv (ncH β c₁ c₂) x = 0 := by
  rw [(ncH_eventuallyEq_zero hc hx).deriv_eq]
  exact deriv_const x 0

theorem deriv_deriv_ncH_of_gt (hc : c₁ < c₂) {x : ℝ} (hx : c₂ < x) :
    deriv (deriv (ncH β c₁ c₂)) x = 0 := by
  have hev : deriv (ncH β c₁ c₂) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact deriv_ncH_of_gt hc hy
  rw [hev.deriv_eq]
  exact deriv_const x 0

/-- On the transition interval `[c₁, c₂] ⊂ (0, ∞)` the first two derivatives of `h` are bounded. -/
theorem exists_bound_deriv_ncH (hc₁ : 0 < c₁) :
    ∃ M₁ M₂ : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ ∀ x ∈ Icc c₁ c₂,
      |deriv (ncH β c₁ c₂) x| ≤ M₁ ∧ |deriv (deriv (ncH β c₁ c₂)) x| ≤ M₂ := by
  have hH : ContDiffOn ℝ 3 (ncH β c₁ c₂) (Ioi 0) := contDiffOn_ncH (n := 3)
  have hD : ContDiffOn ℝ 2 (deriv (ncH β c₁ c₂)) (Ioi 0) :=
    hH.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc1 : ContinuousOn (deriv (ncH β c₁ c₂)) (Ioi 0) := hD.continuousOn
  have hc2 : ContinuousOn (deriv (deriv (ncH β c₁ c₂))) (Ioi 0) :=
    hD.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hsub : Icc c₁ c₂ ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hc₁ hx.1
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc1.mono hsub)
  obtain ⟨M₂, hM₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc2.mono hsub)
  refine ⟨max M₁ 0, max M₂ 0, le_max_right _ _, le_max_right _ _, fun x hx => ⟨?_, ?_⟩⟩
  · exact (hM₁ x hx).trans (le_max_left _ _)
  · exact (hM₂ x hx).trans (le_max_left _ _)

/-! ### Strip variables and the generator bound -/

/-- `u = 1/(1 − e^{−x})`: along the evolution, `G/(W − V)` for the nearest lower left mark `V` at strip gap `x`. -/
def uOf (x : ℝ) : ℝ := (1 - Real.exp (-x))⁻¹

/-- `w = e^{−y}/(1 − e^{−y})`: along the evolution, `G/(V − W)` for the nearest right mark `V` at strip gap `y`. -/
def wOf (y : ℝ) : ℝ := Real.exp (-y) * (1 - Real.exp (-y))⁻¹

theorem uOf_pos {x : ℝ} (hx : 0 < x) : 0 < uOf x := inv_pos.2 (one_sub_exp_neg_pos hx)

theorem one_le_uOf {x : ℝ} (hx : 0 < x) : 1 ≤ uOf x :=
  one_le_inv₀ (one_sub_exp_neg_pos hx) |>.2 (by linarith [Real.exp_pos (-x)])

theorem wOf_eq {x : ℝ} (hx : 0 < x) : wOf x = uOf x - 1 := by
  have h := (one_sub_exp_neg_pos hx).ne'
  simp only [wOf, uOf]
  field_simp
  ring

theorem wOf_pos {x : ℝ} (hx : 0 < x) : 0 < wOf x :=
  mul_pos (Real.exp_pos _) (inv_pos.2 (one_sub_exp_neg_pos hx))

theorem uOf_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : uOf y ≤ uOf x := by
  refine inv_anti₀ (one_sub_exp_neg_pos hx) ?_
  have := Real.exp_le_exp.2 (neg_le_neg hxy)
  linarith

theorem wOf_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : wOf y ≤ wOf x := by
  rw [wOf_eq hx, wOf_eq (hx.trans_le hxy)]
  linarith [uOf_anti hx hxy]

/-- The strip generator of `h(X)` for the nearest left strip gap `X`, in terms of the driver force sum `A`
(`G²` times the chordal generator; the drift of `X` is `A − κ/2 + 2u`, its diffusion coefficient `√κ`). -/
def genL (β c₁ c₂ κ X A : ℝ) : ℝ :=
  deriv (ncH β c₁ c₂) X * (A - κ / 2 + 2 * uOf X) + κ / 2 * deriv (deriv (ncH β c₁ c₂)) X

/-- The strip generator of `h(Y)` for the nearest right strip gap `Y` (drift `−A + κ/2 + 2w`). -/
def genR (β c₁ c₂ κ Y A : ℝ) : ℝ :=
  deriv (ncH β c₁ c₂) Y * (-A + κ / 2 + 2 * wOf Y) + κ / 2 * deriv (deriv (ncH β c₁ c₂)) Y

variable {κ : ℝ}

theorem genL_eq_zero (hc : c₁ < c₂) {X A : ℝ} (hX : c₂ < X) : genL β c₁ c₂ κ X A = 0 := by
  rw [genL, deriv_ncH_of_gt hc hX, deriv_deriv_ncH_of_gt hc hX]; ring

theorem genR_eq_zero (hc : c₁ < c₂) {Y A : ℝ} (hY : c₂ < Y) : genR β c₁ c₂ κ Y A = 0 := by
  rw [genR, deriv_ncH_of_gt hc hY, deriv_deriv_ncH_of_gt hc hY]; ring

theorem ncKD_eq {x : ℝ} (hx : 0 < x) : ncKD β x = -(Real.exp (-x) * (uOf x + β)) := by
  have h := (one_sub_exp_neg_pos hx).ne'
  simp only [ncKD, uOf]
  field_simp
  ring

theorem ncKDD_eq {x : ℝ} (hx : 0 < x) : ncKDD β x = Real.exp (-x) * (uOf x ^ 2 + β) := by
  have h := (one_sub_exp_neg_pos hx).ne'
  simp only [ncKDD, uOf]
  field_simp

theorem exp_neg_mul_uOf {x : ℝ} (hx : 0 < x) : Real.exp (-x) * uOf x = uOf x - 1 := by
  have h := (one_sub_exp_neg_pos hx).ne'
  simp only [uOf]
  field_simp
  ring

/-- **Repulsion of the nearest left gap near `0`** (the strip form of (3.13)): if `A ≥ c u − K`, `c = κ/2 − 2`, then
`genL ≤ (u − 1)(K + κ/2 − βκ/2) + β(K + κ)`. -/
theorem genL_le (hβ : 0 ≤ β) (hc : c₁ < c₂) {X A K : ℝ} (hX : 0 < X) (hX₁ : X < c₁) (hK : 0 ≤ K)
    (hκ : 0 < κ) (hA : (κ / 2 - 2) * uOf X - K ≤ A) :
    genL β c₁ c₂ κ X A ≤ (uOf X - 1) * (K + κ / 2 - β * κ / 2) + β * (K + κ) := by
  rw [genL, deriv_ncH_of_lt hc hX hX₁, deriv_deriv_ncH_of_lt hc hX hX₁, ncKD_eq hX, ncKDD_eq hX]
  set r := Real.exp (-X) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 := (Real.exp_lt_one_iff.2 (by linarith)).le
  set u := uOf X with hu
  have hru : r * u = u - 1 := exp_neg_mul_uOf hX
  have hu1 : 1 ≤ u := one_le_uOf hX
  have hcoef : 0 ≤ r * (u + β) := mul_nonneg hr0.le (by linarith)
  have h1 : -(r * (u + β)) * (A - κ / 2 + 2 * u) ≤
      -(r * (u + β)) * ((κ / 2 - 2) * u - K - κ / 2 + 2 * u) :=
    mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.2 hcoef)
  have h2 : r * β * (K + κ) ≤ β * (K + κ) :=
    mul_le_of_le_one_left (mul_nonneg hβ (by linarith)) hr1 |>.trans_eq' (by ring)
  calc -(r * (u + β)) * (A - κ / 2 + 2 * u) + κ / 2 * (r * (u ^ 2 + β))
      ≤ -(r * (u + β)) * ((κ / 2 - 2) * u - K - κ / 2 + 2 * u) + κ / 2 * (r * (u ^ 2 + β)) := by
        linarith
    _ = (r * u) * (K + κ / 2 - β * κ / 2) + r * β * (K + κ) := by ring
    _ = (u - 1) * (K + κ / 2 - β * κ / 2) + r * β * (K + κ) := by rw [hru]
    _ ≤ (u - 1) * (K + κ / 2 - β * κ / 2) + β * (K + κ) := by linarith

/-- **Repulsion of the nearest right gap near `0`**: if `A ≤ −c w + K`, then
`genR ≤ w(K − βκ/2) + β(K + κ/2)`. -/
theorem genR_le (hβ : 0 ≤ β) (hc : c₁ < c₂) {Y A K : ℝ} (hY : 0 < Y) (hY₁ : Y < c₁) (hK : 0 ≤ K)
    (hκ : 0 < κ) (hA : A ≤ -((κ / 2 - 2) * wOf Y) + K) :
    genR β c₁ c₂ κ Y A ≤ wOf Y * (K - β * κ / 2) + β * (K + κ / 2) := by
  rw [genR, deriv_ncH_of_lt hc hY hY₁, deriv_deriv_ncH_of_lt hc hY hY₁, ncKD_eq hY, ncKDD_eq hY]
  set q := Real.exp (-Y) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := (Real.exp_lt_one_iff.2 (by linarith)).le
  have hw : wOf Y = uOf Y - 1 := wOf_eq hY
  set u := uOf Y with hu
  have hqu : q * u = u - 1 := exp_neg_mul_uOf hY
  have hu1 : 1 ≤ u := one_le_uOf hY
  rw [hw]
  have hcoef : 0 ≤ q * (u + β) := mul_nonneg hq0.le (by linarith)
  have h1 : -(q * (u + β)) * (-A + κ / 2 + 2 * (u - 1)) ≤ -(q * (u + β)) * (κ / 2 * u - K) := by
    refine mul_le_mul_of_nonpos_left ?_ (neg_nonpos.2 hcoef)
    rw [hw] at hA
    nlinarith
  have h2 : q * β * (K + κ / 2) ≤ β * (K + κ / 2) :=
    mul_le_of_le_one_left (mul_nonneg hβ (by linarith)) hq1 |>.trans_eq' (by ring)
  calc -(q * (u + β)) * (-A + κ / 2 + 2 * (u - 1)) + κ / 2 * (q * (u ^ 2 + β))
      ≤ -(q * (u + β)) * (κ / 2 * u - K) + κ / 2 * (q * (u ^ 2 + β)) := by linarith
    _ = (q * u) * (K - β * κ / 2) + q * β * (K + κ / 2) := by ring
    _ = (u - 1) * (K - β * κ / 2) + q * β * (K + κ / 2) := by rw [hqu]
    _ ≤ (u - 1) * (K - β * κ / 2) + β * (K + κ / 2) := by linarith

/-- On the transition interval the generator of `h` is bounded by the derivative bounds. -/
theorem abs_genL_le {M₁ M₂ X A : ℝ} (hκ : 0 < κ) (hX : 0 < X) (h1 : |deriv (ncH β c₁ c₂) X| ≤ M₁)
    (h2 : |deriv (deriv (ncH β c₁ c₂)) X| ≤ M₂) :
    |genL β c₁ c₂ κ X A| ≤ M₁ * (|A| + κ / 2 + 2 * uOf X) + κ / 2 * M₂ := by
  have hu := (uOf_pos hX).le
  have hM₁ : 0 ≤ M₁ := (abs_nonneg _).trans h1
  have e1 : |A - κ / 2 + 2 * uOf X| ≤ |A| + κ / 2 + 2 * uOf X := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * uOf X)]
    have := abs_sub (A) (κ / 2)
    rw [abs_of_pos (by positivity : (0 : ℝ) < κ / 2)] at this
    linarith
  calc |genL β c₁ c₂ κ X A|
      ≤ |deriv (ncH β c₁ c₂) X| * |A - κ / 2 + 2 * uOf X| + κ / 2 * |deriv (deriv (ncH β c₁ c₂)) X| := by
        rw [genL]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < κ / 2)]
    _ ≤ M₁ * (|A| + κ / 2 + 2 * uOf X) + κ / 2 * M₂ := by
        gcongr

theorem abs_genR_le {M₁ M₂ Y A : ℝ} (hκ : 0 < κ) (hY : 0 < Y) (h1 : |deriv (ncH β c₁ c₂) Y| ≤ M₁)
    (h2 : |deriv (deriv (ncH β c₁ c₂)) Y| ≤ M₂) :
    |genR β c₁ c₂ κ Y A| ≤ M₁ * (|A| + κ / 2 + 2 * wOf Y) + κ / 2 * M₂ := by
  have hw := (wOf_pos hY).le
  have hM₁ : 0 ≤ M₁ := (abs_nonneg _).trans h1
  have e1 : |-A + κ / 2 + 2 * wOf Y| ≤ |A| + κ / 2 + 2 * wOf Y := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * wOf Y)]
    have := abs_add_le (-A) (κ / 2)
    rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < κ / 2)] at this
    linarith
  calc |genR β c₁ c₂ κ Y A|
      ≤ |deriv (ncH β c₁ c₂) Y| * |-A + κ / 2 + 2 * wOf Y| + κ / 2 * |deriv (deriv (ncH β c₁ c₂)) Y| := by
        rw [genR]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < κ / 2)]
    _ ≤ M₁ * (|A| + κ / 2 + 2 * wOf Y) + κ / 2 * M₂ := by
        gcongr

/-- The choice of `β`: `βκ/2` dominates every constant drift of the opposite gap and the force sum. -/
def ncBeta (κ c₂ BL BR τ : ℝ) : ℝ := 2 / κ * (BL + BR + BL * uOf c₂ + BR * wOf c₂ + |τ| + 2 + κ / 2)

/-- **The generator bound.** Fix `0 < c₁ < c₂`, weights bounds `BL, BR ≥ 0` (sums of `|ρ|` of the lower left and right
marks) and the end charge `τ = τ₋`. There is `M` such that, for strip gaps `X, Y > 0` that are never both `≤ c₂`, a
force sum `A` with the Abel bounds `A ≥ c u − BR w + τ + 2` (used when `X < c₁`), `A ≤ −c w + BL u + τ + 2` (used when
`Y < c₁`) and `|A| ≤ BL u + BR w + |τ| + 2`, and any `g ≤ |A| + 2κ` (the generator of `ψ(G)`), the total strip
generator `g + genL X A + genR Y A` is at most `M`. -/
theorem ncGen_bound (hκ : 0 < κ) (hc₁ : 0 < c₁) (hc : c₁ < c₂) {BL BR τ : ℝ} (hBL : 0 ≤ BL)
    (hBR : 0 ≤ BR) :
    ∃ M : ℝ, ∀ X Y A g : ℝ, 0 < X → 0 < Y → (X ≤ c₂ → c₂ < Y) → (Y ≤ c₂ → c₂ < X) →
      (X < c₁ → (κ / 2 - 2) * uOf X - BR * wOf Y + τ + 2 ≤ A) →
      (Y < c₁ → A ≤ -((κ / 2 - 2) * wOf Y) + BL * uOf X + τ + 2) →
      |A| ≤ BL * uOf X + BR * wOf Y + |τ| + 2 → g ≤ |A| + 2 * κ →
      g + genL (ncBeta κ c₂ BL BR τ) c₁ c₂ κ X A + genR (ncBeta κ c₂ BL BR τ) c₁ c₂ κ Y A ≤ M := by
  have hc₂ : 0 < c₂ := hc₁.trans hc
  have hu₂ : 0 < uOf c₂ := uOf_pos hc₂
  have hw₂ : 0 < wOf c₂ := wOf_pos hc₂
  have hτ := abs_nonneg τ
  have hβκ : ncBeta κ c₂ BL BR τ * κ / 2 =
      BL + BR + BL * uOf c₂ + BR * wOf c₂ + |τ| + 2 + κ / 2 := by
    simp only [ncBeta]; field_simp
  have hβ : 0 ≤ ncBeta κ c₂ BL BR τ := by
    simp only [ncBeta]
    have : 0 ≤ BL * uOf c₂ := mul_nonneg hBL hu₂.le
    have : 0 ≤ BR * wOf c₂ := mul_nonneg hBR hw₂.le
    positivity
  set β := ncBeta κ c₂ BL BR τ with hβdef
  set u₁ := uOf c₁
  set u₂ := uOf c₂
  set w₁ := wOf c₁
  set w₂ := wOf c₂
  have hu₁ : 0 < u₁ := uOf_pos hc₁
  have hw₁ : 0 < w₁ := wOf_pos hc₁
  obtain ⟨M₁, M₂, hM₁, hM₂, hM⟩ := exists_bound_deriv_ncH (β := β) (c₂ := c₂) hc₁
  set K₁ := BR * w₂ + |τ| + 2 with hK₁
  set K₂ := BL * u₂ + |τ| + 2 with hK₂
  set K₃ := BL * u₁ + BR * w₂ + |τ| + 2
  set K₄ := BL * u₂ + BR * w₁ + |τ| + 2
  have hK₁0 : 0 ≤ K₁ := by have := mul_nonneg hBR hw₂.le; linarith
  have hK₂0 : 0 ≤ K₂ := by have := mul_nonneg hBL hu₂.le; linarith
  set Ma := BL + K₁ + 2 * κ + β * (K₁ + κ) with hMa
  set Mb := K₃ + 2 * κ + (M₁ * (K₃ + κ / 2 + 2 * u₁) + κ / 2 * M₂) with hMb
  set Mc := K₂ + 2 * κ + β * (K₂ + κ / 2) with hMc
  set Md := K₄ + 2 * κ + (M₁ * (K₄ + κ / 2 + 2 * w₁) + κ / 2 * M₂) with hMd
  set Me := BL * u₂ + BR * w₂ + |τ| + 2 + 2 * κ with hMe
  refine ⟨max (max (max (max Ma Mb) Mc) Md) Me, ?_⟩
  intro X Y A g hX hY hXY hYX hAl hAr hA hg
  have huX := one_le_uOf hX
  have hwY := (wOf_pos hY).le
  rcases lt_or_ge c₂ X with hX₂ | hX₂
  · -- `X > c₂`: the left term vanishes
    rw [genL_eq_zero hc hX₂, add_zero]
    have huX₂ : uOf X ≤ u₂ := uOf_anti hc₂ hX₂.le
    rcases lt_or_ge Y c₁ with hY₁ | hY₁
    · -- the right gap is near `0`
      have hAr' : A ≤ -((κ / 2 - 2) * wOf Y) + K₂ := by
        have := hAr hY₁
        have : BL * uOf X ≤ BL * u₂ := mul_le_mul_of_nonneg_left huX₂ hBL
        have : τ ≤ |τ| := le_abs_self τ
        linarith
      have hgen := genR_le (κ := κ) hβ hc hY hY₁ hK₂0 hκ hAr'
      have hA' : |A| ≤ K₂ + BR * wOf Y := by
        have : BL * uOf X ≤ BL * u₂ := mul_le_mul_of_nonneg_left huX₂ hBL
        linarith
      have hneg : wOf Y * (K₂ - β * κ / 2) ≤ -(BR * wOf Y) := by
        have : K₂ - β * κ / 2 ≤ -BR := by
          rw [hβκ]; have := mul_nonneg hBR hw₂.le; linarith
        nlinarith
      have : g + genR β c₁ c₂ κ Y A ≤ Mc := by rw [hMc]; linarith
      exact this.trans (by simp only [le_max_iff, le_refl, true_or, or_true])
    rcases le_or_gt Y c₂ with hY₂ | hY₂
    · -- the right gap in the transition interval
      obtain ⟨h1, h2⟩ := hM Y ⟨hY₁, hY₂⟩
      have hgen := abs_genR_le (A := A) hκ hY h1 h2
      have hwY₁ : wOf Y ≤ w₁ := wOf_anti hc₁ hY₁
      have hA' : |A| ≤ K₄ := by
        have : BL * uOf X ≤ BL * u₂ := mul_le_mul_of_nonneg_left huX₂ hBL
        have : BR * wOf Y ≤ BR * w₁ := mul_le_mul_of_nonneg_left hwY₁ hBR
        linarith
      have h3 : M₁ * (|A| + κ / 2 + 2 * wOf Y) ≤ M₁ * (K₄ + κ / 2 + 2 * w₁) :=
        mul_le_mul_of_nonneg_left (by linarith) hM₁
      have : g + genR β c₁ c₂ κ Y A ≤ Md := by
        rw [hMd]; linarith [le_abs_self (genR β c₁ c₂ κ Y A)]
      exact this.trans (by simp only [le_max_iff, le_refl, true_or, or_true])
    · -- both gaps away from `0`
      rw [genR_eq_zero hc hY₂, add_zero]
      have hwY₂ : wOf Y ≤ w₂ := wOf_anti hc₂ hY₂.le
      have : BL * uOf X ≤ BL * u₂ := mul_le_mul_of_nonneg_left huX₂ hBL
      have : BR * wOf Y ≤ BR * w₂ := mul_le_mul_of_nonneg_left hwY₂ hBR
      have : g ≤ Me := by rw [hMe]; linarith
      exact this.trans (by simp only [le_max_iff, le_refl, or_true])
  · -- `X ≤ c₂`: the right gap is away from `0`
    have hY₂ := hXY hX₂
    rw [genR_eq_zero hc hY₂, add_zero]
    have hwY₂ : wOf Y ≤ w₂ := wOf_anti hc₂ hY₂.le
    have hBRw : BR * wOf Y ≤ BR * w₂ := mul_le_mul_of_nonneg_left hwY₂ hBR
    rcases lt_or_ge X c₁ with hX₁ | hX₁
    · have hAl' : (κ / 2 - 2) * uOf X - K₁ ≤ A := by
        have := hAl hX₁
        have : -|τ| ≤ τ := neg_abs_le τ
        linarith
      have hgen := genL_le (κ := κ) hβ hc hX hX₁ hK₁0 hκ hAl'
      have hneg : (uOf X - 1) * (K₁ + κ / 2 - β * κ / 2) ≤ -(BL * (uOf X - 1)) := by
        have : K₁ + κ / 2 - β * κ / 2 ≤ -BL := by
          rw [hβκ]; have := mul_nonneg hBL hu₂.le; linarith
        nlinarith
      have : g + genL β c₁ c₂ κ X A ≤ Ma := by rw [hMa]; linarith
      exact this.trans (by simp only [le_max_iff, le_refl, true_or])
    · obtain ⟨h1, h2⟩ := hM X ⟨hX₁, hX₂⟩
      have hgen := abs_genL_le (A := A) hκ hX h1 h2
      have huX₁ : uOf X ≤ u₁ := uOf_anti hc₁ hX₁
      have hA' : |A| ≤ K₃ := by
        have : BL * uOf X ≤ BL * u₁ := mul_le_mul_of_nonneg_left huX₁ hBL
        linarith
      have h3 : M₁ * (|A| + κ / 2 + 2 * uOf X) ≤ M₁ * (K₃ + κ / 2 + 2 * u₁) :=
        mul_le_mul_of_nonneg_left (by linarith) hM₁
      have : g + genL β c₁ c₂ κ X A ≤ Mb := by
        rw [hMb]; linarith [le_abs_self (genL β c₁ c₂ κ X A)]
      exact this.trans (by simp only [le_max_iff, le_refl, true_or, or_true])

end Zhan

end InteractingSLE
