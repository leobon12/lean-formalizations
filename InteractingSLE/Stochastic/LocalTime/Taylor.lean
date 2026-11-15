/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Second-order Taylor bounds and the `C²` test functions of the Tanaka argument

Packet PROVE-TANAKA. Deterministic ingredients of the expectation form of Itô's formula used in
`InteractingSLE.Stochastic.LocalTime.ItoExpectation`:

* `abs_taylor_two_le`: the second-order Taylor remainder of a function with a second derivative is
  bounded by the oscillation of the second derivative times the square of the increment;
* `tent`, `bump`: a continuous unit-mass bump on `[0, ε]` (a normalized tent, rescaled), with
  `bump ε ≤ K / ε` for a constant `K` independent of `ε`;
* `prim g x = ∫₀ˣ g`, the primitive used to build `C²` functions from their second derivative;
* `tanakaFn ε`: the `C²` approximation of `x ↦ x⁺` with `tanakaFn ε'' = bump ε`, `tanakaFn ε' = 0`
  on `(-∞, 0]` and `= 1` on `[ε, ∞)` ([RY] Ch. VI, proof of Thm (1.1), p. 221: smoothing a convex
  function);
* `zeroFn δ`: a `1`-Lipschitz `C²` function whose second derivative is a unit-mass bump on
  `[-δ/2, δ/2]`, at least `1 / (4 m δ)` on `[-δ/4, δ/4]` (used for the occupation of the zero set).
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE.LocalTime

/-! ### Taylor's formula of order two -/

/-- **Second-order Taylor bound.** If `f' = f'` and `f'' = (f')'` everywhere and `f''` varies by at
most `M` from `f'' x` on the segment `[x, y]`, then the second-order Taylor remainder at `x` is at
most `M (y - x)²`. -/
theorem abs_taylor_two_le {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) {x y M : ℝ}
    (hM : ∀ z ∈ uIcc x y, |f'' z - f'' x| ≤ M) :
    |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ M * (y - x) ^ 2 := by
  have hg : ∀ z, HasDerivAt (fun z => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2)
      (f' z - f' x - f'' x * (z - x)) z := by
    intro z
    have h1 := ((hasDerivAt_id z).sub_const x).const_mul (f' x)
    have h0 : HasDerivAt (fun z : ℝ => z - x) 1 z := (hasDerivAt_id z).sub_const x
    have h2 := ((h0.fun_mul h0).const_mul (f'' x)).div_const 2
    have := (((hf z).sub_const (f x)).fun_sub h1).fun_sub h2
    have hfun : (fun z => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2) =
        fun i => f i - f x - f' x * (id i - x) - f'' x * ((i - x) * (i - x)) / 2 := by
      funext w; simp only [id]; ring
    rw [hfun]
    exact this.congr_deriv (by ring)
  have hg' : ∀ z, HasDerivAt (fun z => f' z - f' x - f'' x * (z - x)) (f'' z - f'' x) z := by
    intro z
    have := ((hf' z).sub_const (f' x)).fun_sub
      (((hasDerivAt_id z).sub_const x).const_mul (f'' x))
    exact this.congr_deriv (by simp)
  have hconv : Convex ℝ (uIcc x y) := convex_uIcc x y
  have hx : x ∈ uIcc x y := left_mem_uIcc
  have hy : y ∈ uIcc x y := right_mem_uIcc
  have hM0 : 0 ≤ M := by simpa using hM x hx
  have h1 : ∀ z ∈ uIcc x y, ‖f' z - f' x - f'' x * (z - x)‖ ≤ M * |y - x| := by
    intro z hz
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z => f' z - f' x - f'' x * (z - x)) (fun w _ => (hg' w).hasDerivWithinAt)
      (fun w hw => by simpa [Real.norm_eq_abs] using hM w hw) hconv hx hz
    simp only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at this ⊢
    exact this.trans (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hz) hM0)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => f z - f x - f' x * (z - x) - f'' x * (z - x) ^ 2 / 2)
    (fun w _ => (hg w).hasDerivWithinAt) h1 hconv hx hy
  simp only [sub_self, mul_zero, sub_zero, zero_pow two_ne_zero, zero_div,
    Real.norm_eq_abs] at this
  calc _ ≤ M * |y - x| * |y - x| := this
    _ = M * (y - x) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-! ### Primitives -/

/-- The primitive `x ↦ ∫₀ˣ g`. -/
def prim (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, g y

lemma hasDerivAt_prim {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    HasDerivAt (prim g) (g x) x :=
  (hg.integral_hasStrictDerivAt 0 x).hasDerivAt

lemma prim_zero (g : ℝ → ℝ) : prim g 0 = 0 := by simp [prim]

lemma continuous_prim {g : ℝ → ℝ} (hg : Continuous g) : Continuous (prim g) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_prim hg x).continuousAt

lemma integral_eq_zero_of_eqOn_zero {g : ℝ → ℝ} {x y : ℝ} (h : ∀ z ∈ uIcc x y, g z = 0) :
    ∫ z in x..y, g z = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) h]
  simp

/-- A continuous nonnegative function vanishing outside `[p, q]` with `∫_p^q g = 1` has
`|∫_x^y g| ≤ 1` for all `x, y`. -/
lemma abs_integral_le_one_of_unit_mass {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z)
    {p q : ℝ} (hout : ∀ z, z ≤ p ∨ q ≤ z → g z = 0)
    (hmass : ∫ z in p..q, g z = 1) (x y : ℝ) : |∫ z in x..y, g z| ≤ 1 := by
  have key : ∀ x y, x ≤ y → ∫ z in x..y, g z ≤ 1 := by
    intro x y hxy
    have hle : ∫ z in x..y, g z ≤ ∫ z in (min x p)..(max y q), g z :=
      intervalIntegral.integral_mono_interval (min_le_left _ _) hxy (le_max_left _ _)
        (Eventually.of_forall hg0) (hg.intervalIntegrable _ _)
    have hsplit : ∫ z in (min x p)..(max y q), g z =
        (∫ z in (min x p)..p, g z) + (∫ z in p..q, g z) + ∫ z in q..(max y q), g z := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _)
          (hg.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _)
          (hg.intervalIntegrable _ _)]
    have h1 : ∫ z in (min x p)..p, g z = 0 := integral_eq_zero_of_eqOn_zero fun z hz => by
      rw [uIcc_of_le (min_le_right _ _)] at hz
      exact hout z (Or.inl hz.2)
    have h2 : ∫ z in q..(max y q), g z = 0 := integral_eq_zero_of_eqOn_zero fun z hz => by
      rw [uIcc_of_le (le_max_right _ _)] at hz
      exact hout z (Or.inr hz.1)
    linarith
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hxy fun z _ => hg0 z)]
    exact key x y hxy
  · rw [intervalIntegral.integral_symm, abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg hxy fun z _ => hg0 z)]
    exact key y x hxy

/-! ### A unit-mass bump -/

/-- The tent `y ↦ max 0 (1/2 - |y - 1/2|)`, supported on `[0, 1]`. -/
def tent (y : ℝ) : ℝ := max 0 (1 / 2 - |y - 1 / 2|)

lemma continuous_tent : Continuous tent := by unfold tent; fun_prop

lemma tent_nonneg (y : ℝ) : 0 ≤ tent y := le_max_left _ _

lemma tent_le (y : ℝ) : tent y ≤ 1 / 2 :=
  max_le (by norm_num) (by linarith [abs_nonneg (y - 1 / 2)])

lemma tent_eq_zero {y : ℝ} (hy : y ≤ 0 ∨ 1 ≤ y) : tent y = 0 := by
  unfold tent; apply max_eq_left
  rcases hy with hy | hy
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma tent_pos {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : 0 < tent y := by
  unfold tent; apply lt_max_of_lt_right
  rcases le_total y (1 / 2) with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma quarter_le_tent {y : ℝ} (h0 : 1 / 4 ≤ y) (h1 : y ≤ 3 / 4) : 1 / 4 ≤ tent y := by
  unfold tent; apply le_max_of_le_right
  rcases le_total y (1 / 2) with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- The mass `∫₀¹ tent` (its value `1/4` is not needed). -/
def tentMass : ℝ := ∫ y in (0 : ℝ)..1, tent y

lemma tentMass_pos : 0 < tentMass :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (continuous_tent.intervalIntegrable _ _)
    (fun _ hy => tent_pos hy.1 hy.2) zero_lt_one

/-- The unit-mass bump on `[0, ε]`: `bump ε x = tent (x / ε) / (tentMass ε)`. -/
def bump (ε x : ℝ) : ℝ := tent (x / ε) / tentMass / ε

/-- The constant `K` of `bump ε ≤ K / ε`. -/
def bumpConst : ℝ := 1 / 2 / tentMass

lemma continuous_bump (ε : ℝ) : Continuous (bump ε) := by
  unfold bump; exact ((continuous_tent.comp (continuous_id.div_const ε)).div_const _).div_const _

lemma bump_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ bump ε x :=
  div_nonneg (div_nonneg (tent_nonneg _) tentMass_pos.le) hε.le

lemma bump_eq_zero {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : x ≤ 0 ∨ ε ≤ x) : bump ε x = 0 := by
  unfold bump
  rw [tent_eq_zero, zero_div, zero_div]
  rcases hx with hx | hx
  · exact Or.inl (div_nonpos_of_nonpos_of_nonneg hx hε.le)
  · exact Or.inr ((one_le_div hε).2 hx)

lemma bump_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : bump ε x ≤ bumpConst / ε := by
  unfold bump bumpConst
  gcongr
  · exact tentMass_pos.le
  · exact tent_le _

lemma le_bump {ε : ℝ} (hε : 0 < ε) {x : ℝ} (h0 : ε / 4 ≤ x) (h1 : x ≤ 3 * ε / 4) :
    1 / 4 / tentMass / ε ≤ bump ε x := by
  unfold bump
  have := tentMass_pos
  gcongr
  apply quarter_le_tent
  · rw [le_div_iff₀ hε]; linarith
  · rw [div_le_iff₀ hε]; linarith

lemma integral_bump {ε : ℝ} (hε : 0 < ε) : ∫ x in (0 : ℝ)..ε, bump ε x = 1 := by
  unfold bump
  rw [intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_comp_div (fun y => tent y) hε.ne', zero_div, div_self hε.ne',
    smul_eq_mul]
  have := tentMass_pos
  unfold tentMass at this ⊢
  field_simp

/-! ### The Tanaka test function: a `C²` approximation of `x ↦ x⁺` -/

/-- `tanakaFn' ε = ∫₀ˣ bump ε`: `0` on `(-∞, 0]`, `1` on `[ε, ∞)`. -/
def tanakaFn' (ε : ℝ) : ℝ → ℝ := prim (bump ε)

/-- `tanakaFn ε = ∫₀ˣ tanakaFn' ε`, a `C²` approximation of `x ↦ x⁺`. -/
def tanakaFn (ε : ℝ) : ℝ → ℝ := prim (tanakaFn' ε)

lemma hasDerivAt_tanakaFn' (ε x : ℝ) : HasDerivAt (tanakaFn' ε) (bump ε x) x :=
  hasDerivAt_prim (continuous_bump ε) x

lemma continuous_tanakaFn' (ε : ℝ) : Continuous (tanakaFn' ε) :=
  continuous_prim (continuous_bump ε)

lemma hasDerivAt_tanakaFn (ε x : ℝ) : HasDerivAt (tanakaFn ε) (tanakaFn' ε x) x :=
  hasDerivAt_prim (continuous_tanakaFn' ε) x

lemma tanakaFn'_zero (ε : ℝ) : tanakaFn' ε 0 = 0 := prim_zero _

lemma tanakaFn'_of_nonpos {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : x ≤ 0) : tanakaFn' ε x = 0 := by
  unfold tanakaFn' prim
  refine integral_eq_zero_of_eqOn_zero fun z hz => bump_eq_zero hε (Or.inl ?_)
  rw [uIcc_of_ge hx] at hz
  exact hz.2

lemma tanakaFn'_of_ge {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : ε ≤ x) : tanakaFn' ε x = 1 := by
  unfold tanakaFn' prim
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := ε)
      ((continuous_bump ε).intervalIntegrable _ _) ((continuous_bump ε).intervalIntegrable _ _),
    integral_bump hε, integral_eq_zero_of_eqOn_zero (x := ε) (y := x), add_zero]
  intro z hz
  rw [uIcc_of_le hx] at hz
  exact bump_eq_zero hε (Or.inr hz.1)

lemma tanakaFn'_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 ≤ tanakaFn' ε x := by
  rcases le_total x 0 with hx | hx
  · rw [tanakaFn'_of_nonpos hε hx]
  · exact intervalIntegral.integral_nonneg hx fun z _ => bump_nonneg hε z

lemma tanakaFn'_le_one {ε : ℝ} (hε : 0 < ε) (x : ℝ) : tanakaFn' ε x ≤ 1 := by
  have := abs_integral_le_one_of_unit_mass (continuous_bump ε) (bump_nonneg hε)
    (fun z hz => bump_eq_zero hε hz) (integral_bump hε) 0 x
  exact (le_abs_self _).trans this

lemma abs_tanakaFn'_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : |tanakaFn' ε x| ≤ 1 := by
  rw [abs_of_nonneg (tanakaFn'_nonneg hε x)]; exact tanakaFn'_le_one hε x

/-- `x - ε ≤ tanakaFn ε x ≤ x` for `x ≥ 0`. -/
lemma tanakaFn_bounds {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 ≤ x) :
    x - ε ≤ tanakaFn ε x ∧ tanakaFn ε x ≤ x := by
  have hint : ∀ a b, IntervalIntegrable (tanakaFn' ε) volume a b :=
    fun _ _ => (continuous_tanakaFn' ε).intervalIntegrable _ _
  have hdiff : x - tanakaFn ε x = ∫ z in (0 : ℝ)..x, (1 - tanakaFn' ε z) := by
    unfold tanakaFn prim
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint _ _)]
    simp
  have hnn : 0 ≤ ∫ z in (0 : ℝ)..x, (1 - tanakaFn' ε z) :=
    intervalIntegral.integral_nonneg hx fun z _ => by linarith [tanakaFn'_le_one hε z]
  have hle : ∫ z in (0 : ℝ)..x, (1 - tanakaFn' ε z) ≤ ε := by
    have hcont : Continuous fun z => 1 - tanakaFn' ε z := continuous_const.sub
      (continuous_tanakaFn' ε)
    have hmono : ∫ z in (0 : ℝ)..x, (1 - tanakaFn' ε z) ≤
        ∫ z in (0 : ℝ)..(max x ε), (1 - tanakaFn' ε z) :=
      intervalIntegral.integral_mono_interval le_rfl hx (le_max_left _ _)
        (Eventually.of_forall fun z => by
          simp only [Pi.zero_apply]; linarith [tanakaFn'_le_one hε z])
        (hcont.intervalIntegrable _ _)
    have hsplit : ∫ z in (0 : ℝ)..(max x ε), (1 - tanakaFn' ε z) =
        (∫ z in (0 : ℝ)..ε, (1 - tanakaFn' ε z)) + ∫ z in ε..(max x ε), (1 - tanakaFn' ε z) :=
      (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _)).symm
    have h2 : ∫ z in ε..(max x ε), (1 - tanakaFn' ε z) = 0 :=
      integral_eq_zero_of_eqOn_zero fun z hz => by
        rw [uIcc_of_le (le_max_right _ _)] at hz
        rw [tanakaFn'_of_ge hε hz.1, sub_self]
    have h1 : ∫ z in (0 : ℝ)..ε, (1 - tanakaFn' ε z) ≤ ∫ z in (0 : ℝ)..ε, (1 : ℝ) :=
      intervalIntegral.integral_mono_on hε.le (hcont.intervalIntegrable _ _)
        intervalIntegrable_const fun z _ => by linarith [tanakaFn'_nonneg hε z]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h1
    linarith
  constructor <;> linarith

/-! ### The zero-set test function -/

/-- `zeroFn'' δ x = bump δ (x + δ / 2)`, a unit-mass bump on `[-δ/2, δ/2]`. -/
def zeroFn'' (δ : ℝ) (x : ℝ) : ℝ := bump δ (x + δ / 2)

/-- `zeroFn' δ = ∫₀ˣ zeroFn'' δ`. -/
def zeroFn' (δ : ℝ) : ℝ → ℝ := prim (zeroFn'' δ)

/-- `zeroFn δ = ∫₀ˣ zeroFn' δ`. -/
def zeroFn (δ : ℝ) : ℝ → ℝ := prim (zeroFn' δ)

lemma continuous_zeroFn'' (δ : ℝ) : Continuous (zeroFn'' δ) :=
  (continuous_bump δ).comp (continuous_id.add continuous_const)

lemma hasDerivAt_zeroFn' (δ x : ℝ) : HasDerivAt (zeroFn' δ) (zeroFn'' δ x) x :=
  hasDerivAt_prim (continuous_zeroFn'' δ) x

lemma continuous_zeroFn' (δ : ℝ) : Continuous (zeroFn' δ) :=
  continuous_prim (continuous_zeroFn'' δ)

lemma hasDerivAt_zeroFn (δ x : ℝ) : HasDerivAt (zeroFn δ) (zeroFn' δ x) x :=
  hasDerivAt_prim (continuous_zeroFn' δ) x

lemma zeroFn'_zero (δ : ℝ) : zeroFn' δ 0 = 0 := prim_zero _

lemma zeroFn''_nonneg {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : 0 ≤ zeroFn'' δ x := bump_nonneg hδ _

lemma abs_zeroFn'_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : |zeroFn' δ x| ≤ 1 := by
  refine abs_integral_le_one_of_unit_mass (continuous_zeroFn'' δ) (zeroFn''_nonneg hδ)
    (p := -(δ / 2)) (q := δ / 2) (fun z hz => ?_) ?_ 0 x
  · unfold zeroFn''
    refine bump_eq_zero hδ ?_
    rcases hz with hz | hz
    · left; linarith
    · right; linarith
  · unfold zeroFn''
    rw [intervalIntegral.integral_comp_add_right (fun y => bump δ y)]
    have : -(δ / 2) + δ / 2 = 0 := by ring
    rw [this, show δ / 2 + δ / 2 = δ by ring, integral_bump hδ]

lemma abs_zeroFn_sub_le {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    |zeroFn δ y - zeroFn δ x| ≤ |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ) (C := 1)
    (f := zeroFn δ) (fun w _ => (hasDerivAt_zeroFn δ w).hasDerivWithinAt)
    (fun w _ => by rw [Real.norm_eq_abs]; exact abs_zeroFn'_le hδ w) convex_univ
    (mem_univ x) (mem_univ y)
  simpa [Real.norm_eq_abs] using this

lemma le_zeroFn'' {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : |x| ≤ δ / 4) :
    1 / 4 / tentMass / δ ≤ zeroFn'' δ x := by
  unfold zeroFn''
  rw [abs_le] at hx
  exact le_bump hδ (by linarith) (by linarith)

end InteractingSLE.LocalTime
