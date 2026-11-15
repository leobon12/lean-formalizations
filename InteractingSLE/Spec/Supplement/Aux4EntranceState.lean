/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProof
import InteractingSLE.Spec.Supplement.Aux4EntranceMoments

/-!
# Aux. lemma 4, IV: the restart state as a continuous functional of the entrance path

Packet PROVE-T14-DS3. In the proof of Aux. lemma 4 (spec p. 29) the two-seed state is reconstructed from the stationary
Jacobi path by integrals, "the lower tails of its defining integrals obey deterministic bounds … Thus `t_n, L_n^−, L_n^+`
and `w_n` converge", and the additional marks solve `dY = 2 r_δ(Y − W) dt`, "continuous functions of their initial
conditions and of the driving path … by Grönwall's inequality". At the restart of Lemma DS3 (the hitting time of the
cross-gap level `R`), everything is read in the **level variable** `y ∈ [0, R]` (the cross gap), in which the entrance
path is `V(y) = y · U(log y)` (`U` the logarithmic-clock angle; `0 ≤ V(y) ≤ y`, continuous at `0`):

* `ang V y = clamp(V(y)/y)` (the angle `U(log y)`), `low V y = −∫₀^y (1 − ang)`, `upp V y = ∫₀^y ang`,
  `drv V y = low V y + y · ang V y` (the source's `L^−`, `L^+`, `w`, with `dv = dy/y`);
* a separated mark solves `Y(y) = x + ∫₀^y z·ang(1 − ang)·F(Y(z) − drv(z)) dz` (`dt = ½ y U(1−U) dy` and
  `dY/dt = 2/(Y − W)`), with the cut reciprocal `F = FL δ` / `FR δ`; its solution `mark` is the limit of the Picard
  iterates `pic`, which contract with ratio `k = R²/(8δ²)` (`abs_pic_succ_sub_le`), and every solution of the equation
  equals it (`eq_mark_of_eq`);
* **`continuous_mark`**, **`continuous_low`**, … : all of them are continuous in `V ∈ C([0, R])` (dominated
  convergence; uniform convergence of the Picard iterates).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace Aux4

variable {R : ℝ≥0}

/-- A path on `[0, R]` evaluated at a real level (clamped to `[0, R]`). -/
def evR (V : C(Icc (0 : ℝ≥0) R, ℝ)) (y : ℝ) : ℝ := V (projIcc 0 R zero_le y.toNNReal)

theorem continuous_evR (V : C(Icc (0 : ℝ≥0) R, ℝ)) : Continuous (evR V) :=
  V.continuous.comp (continuous_projIcc.comp continuous_real_toNNReal)

theorem continuous_evR_left (y : ℝ) : Continuous fun V : C(Icc (0 : ℝ≥0) R, ℝ) => evR V y :=
  continuous_eval_const _

/-- Clamping to `[0, 1]`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

theorem continuous_clamp01 : Continuous clamp01 := continuous_const.max (continuous_const.min continuous_id)

theorem clamp01_mem (x : ℝ) : clamp01 x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- The angle at level `y`. -/
def ang (V : C(Icc (0 : ℝ≥0) R, ℝ)) (y : ℝ) : ℝ := clamp01 (evR V y / y)

theorem ang_mem (V : C(Icc (0 : ℝ≥0) R, ℝ)) (y : ℝ) : ang V y ∈ Icc (0 : ℝ) 1 := clamp01_mem _

theorem measurable_ang (V : C(Icc (0 : ℝ≥0) R, ℝ)) : Measurable (ang V) :=
  continuous_clamp01.measurable.comp ((continuous_evR V).measurable.div measurable_id)

theorem continuous_ang_left {y : ℝ} (_hy : y ≠ 0) : Continuous fun V : C(Icc (0 : ℝ≥0) R, ℝ) => ang V y :=
  continuous_clamp01.comp ((continuous_evR_left y).div_const y)

/-- `L^−` at level `y`. -/
def low (V : C(Icc (0 : ℝ≥0) R, ℝ)) (y : ℝ) : ℝ := -∫ z in (0 : ℝ)..y, (1 - ang V z)

/-- `L^+` at level `y`. -/
def upp (V : C(Icc (0 : ℝ≥0) R, ℝ)) (y : ℝ) : ℝ := ∫ z in (0 : ℝ)..y, ang V z

/-- The driver at level `y`. -/
def drv (V : C(Icc (0 : ℝ≥0) R, ℝ)) (y : ℝ) : ℝ := low V y + y * ang V y

/-- The clock density in the level variable: `dt = ½ coef dy`, `coef = y · ang (1 − ang)`. -/
def coef (V : C(Icc (0 : ℝ≥0) R, ℝ)) (z : ℝ) : ℝ := z * (ang V z * (1 - ang V z))

theorem abs_coef_le (V : C(Icc (0 : ℝ≥0) R, ℝ)) (z : ℝ) : |coef V z| ≤ |z| / 4 := by
  obtain ⟨h0, h1⟩ := ang_mem V z
  have : ang V z * (1 - ang V z) ≤ 1 / 4 := by nlinarith [sq_nonneg (ang V z - 1 / 2)]
  have hnn : 0 ≤ ang V z * (1 - ang V z) := mul_nonneg h0 (by linarith)
  rw [coef, abs_mul, abs_of_nonneg hnn]
  nlinarith [abs_nonneg z]

theorem measurable_coef (V : C(Icc (0 : ℝ≥0) R, ℝ)) : Measurable (coef V) :=
  measurable_id.mul ((measurable_ang V).mul (measurable_const.sub (measurable_ang V)))

theorem continuous_coef_left {z : ℝ} (hz : z ≠ 0) : Continuous fun V : C(Icc (0 : ℝ≥0) R, ℝ) => coef V z :=
  continuous_const.mul ((continuous_ang_left hz).mul (continuous_const.sub (continuous_ang_left hz)))

theorem ae_ne_zero_of_mem : ∀ᵐ z : ℝ ∂volume, z ≠ 0 := by
  rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton]; exact Real.volume_singleton

theorem continuous_low (y : ℝ) : Continuous fun V : C(Icc (0 : ℝ≥0) R, ℝ) => low V y := by
  refine (intervalIntegral.continuous_of_dominated_interval (bound := fun _ => 1)
    (fun V => (measurable_const.sub (measurable_ang V)).aestronglyMeasurable)
    (fun V => ae_of_all _ fun z _ => ?_) intervalIntegrable_const
    (ae_ne_zero_of_mem.mono fun z hz _ => continuous_const.sub (continuous_ang_left hz))).neg
  obtain ⟨h0, h1⟩ := ang_mem V z
  simp only [Pi.sub_apply]
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

theorem continuous_upp (y : ℝ) : Continuous fun V : C(Icc (0 : ℝ≥0) R, ℝ) => upp V y := by
  refine intervalIntegral.continuous_of_dominated_interval (bound := fun _ => 1)
    (fun V => (measurable_ang V).aestronglyMeasurable)
    (fun V => ae_of_all _ fun z _ => ?_) intervalIntegrable_const
    (ae_ne_zero_of_mem.mono fun z hz _ => continuous_ang_left hz)
  obtain ⟨h0, h1⟩ := ang_mem V z
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

theorem continuous_drv {y : ℝ} (hy : y ≠ 0) : Continuous fun V : C(Icc (0 : ℝ≥0) R, ℝ) => drv V y :=
  (continuous_low y).add (continuous_const.mul (continuous_ang_left hy))

theorem continuous_low_right (V : C(Icc (0 : ℝ≥0) R, ℝ)) : Continuous (low V) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun z => 1 - ang V z) volume a b := fun a b =>
    (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
      (measurable_const.sub (measurable_ang V)).aestronglyMeasurable (ae_of_all _ fun z => by
        obtain ⟨h0, h1⟩ := ang_mem V z
        simp only [Real.norm_eq_abs]; rw [abs_le]; constructor <;> linarith)
  exact (intervalIntegral.continuous_primitive hi 0).neg

theorem measurable_drv (V : C(Icc (0 : ℝ≥0) R, ℝ)) : Measurable (drv V) :=
  (continuous_low_right V).measurable.add (measurable_id.mul (measurable_ang V))

/-! ### The separated marks: Picard iteration -/

/-- The cut reciprocal for a left mark (`Y < W`): `1/x` for `x ≤ −δ`. -/
def FL (δ x : ℝ) : ℝ := -1 / max (-x) δ

/-- The cut reciprocal for a right mark (`Y > W`): `1/x` for `x ≥ δ`. -/
def FR (δ x : ℝ) : ℝ := 1 / max x δ

/-- The properties of a cut reciprocal used by the Picard iteration. -/
structure IsCut (δ : ℝ) (F : ℝ → ℝ) : Prop where
  pos : 0 < δ
  cont : Continuous F
  bound : ∀ x, |F x| ≤ 1 / δ
  lip : ∀ x x', |F x - F x'| ≤ |x - x'| / δ ^ 2

theorem abs_inv_max_sub_le {δ : ℝ} (hδ : 0 < δ) (x x' : ℝ) :
    |1 / max x δ - 1 / max x' δ| ≤ |x - x'| / δ ^ 2 := by
  have ha : δ ≤ max x δ := le_max_right _ _
  have hb : δ ≤ max x' δ := le_max_right _ _
  have hapos : 0 < max x δ := lt_of_lt_of_le hδ ha
  have hbpos : 0 < max x' δ := lt_of_lt_of_le hδ hb
  rw [div_sub_div _ _ hapos.ne' hbpos.ne', one_mul, mul_one, abs_div, abs_of_pos (mul_pos hapos hbpos)]
  have hnum : |max x' δ - max x δ| ≤ |x - x'| := by
    rw [abs_sub_comm x x']; exact abs_max_sub_max_le_abs _ _ _
  have hden : δ ^ 2 ≤ max x δ * max x' δ := by nlinarith
  calc |max x' δ - max x δ| / (max x δ * max x' δ) ≤ |x - x'| / (max x δ * max x' δ) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ |x - x'| / δ ^ 2 := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hden

theorem isCut_FR {δ : ℝ} (hδ : 0 < δ) : IsCut δ (FR δ) where
  pos := hδ
  cont := continuous_const.div (continuous_id.max continuous_const) fun x =>
    (lt_of_lt_of_le hδ (le_max_right x δ)).ne'
  bound x := by
    have hpos : 0 < max x δ := lt_of_lt_of_le hδ (le_max_right _ _)
    rw [FR, abs_div, abs_one, abs_of_pos hpos]
    exact one_div_le_one_div_of_le hδ (le_max_right _ _)
  lip x x' := abs_inv_max_sub_le hδ x x'

theorem isCut_FL {δ : ℝ} (hδ : 0 < δ) : IsCut δ (FL δ) where
  pos := hδ
  cont := continuous_const.div (continuous_neg.max continuous_const) fun x =>
    (lt_of_lt_of_le hδ (le_max_right (-x) δ)).ne'
  bound x := by
    have hpos : 0 < max (-x) δ := lt_of_lt_of_le hδ (le_max_right _ _)
    rw [FL, abs_div, abs_neg, abs_one, abs_of_pos hpos]
    exact one_div_le_one_div_of_le hδ (le_max_right _ _)
  lip x x' := by
    have h := abs_inv_max_sub_le hδ (-x) (-x')
    rw [show -x - -x' = -(x - x') by ring, abs_neg] at h
    rw [FL, FL, neg_div, neg_div, neg_sub_neg, abs_sub_comm]
    exact h

variable {δ : ℝ} {F : ℝ → ℝ}

/-- The Picard iterates of `Y(y) = x + ∫₀^y coef · F(Y − drv)`. -/
def pic (F : ℝ → ℝ) (x₀ : ℝ) (V : C(Icc (0 : ℝ≥0) R, ℝ)) : ℕ → ℝ → ℝ
  | 0 => fun _ => x₀
  | n + 1 => fun y => x₀ + ∫ z in (0 : ℝ)..y, coef V z * F (pic F x₀ V n z - drv V z)

/-- The separated mark: the limit of the Picard iterates. -/
def mark (F : ℝ → ℝ) (x₀ : ℝ) (V : C(Icc (0 : ℝ≥0) R, ℝ)) (y : ℝ) : ℝ :=
  limUnder atTop fun n => pic F x₀ V n y

theorem abs_coef_mul_le (hF : IsCut δ F) (V : C(Icc (0 : ℝ≥0) R, ℝ)) (z a : ℝ) :
    |coef V z * F a| ≤ |z| / 4 * (1 / δ) := by
  rw [abs_mul]
  exact mul_le_mul (abs_coef_le V z) (hF.bound a) (abs_nonneg _) (by positivity)

theorem intervalIntegrable_coef_mul (hF : IsCut δ F) (V : C(Icc (0 : ℝ≥0) R, ℝ)) {g : ℝ → ℝ}
    (hg : Measurable g) (a b : ℝ) :
    IntervalIntegrable (fun z => coef V z * F (g z)) volume a b :=
  (Continuous.intervalIntegrable (by fun_prop : Continuous fun z : ℝ => |z| / 4 * (1 / δ)) a b).mono_fun'
    ((measurable_coef V).mul (hF.cont.measurable.comp hg)).aestronglyMeasurable
    (ae_of_all _ fun z => by simp only [Real.norm_eq_abs]; exact abs_coef_mul_le hF V z _)

theorem continuous_pic (hF : IsCut δ F) (x₀ : ℝ) (V : C(Icc (0 : ℝ≥0) R, ℝ)) :
    ∀ n, Continuous (pic F x₀ V n)
  | 0 => continuous_const
  | n + 1 => continuous_const.add (intervalIntegral.continuous_primitive
      (intervalIntegrable_coef_mul hF V ((continuous_pic hF x₀ V n).measurable.sub (measurable_drv V))) 0)

/-- The basic estimate: `|∫₀^y coef (F a − F b)| ≤ y²/(8δ²) · sup |a − b|` for `0 ≤ y`. -/
theorem abs_integral_coef_sub_le (hF : IsCut δ F) (V : C(Icc (0 : ℝ≥0) R, ℝ)) {a b : ℝ → ℝ}
    (ha : Measurable a) (hb : Measurable b) {y M : ℝ} (hy : 0 ≤ y) (hM : ∀ z ∈ Icc 0 y, |a z - b z| ≤ M) :
    |(∫ z in (0 : ℝ)..y, coef V z * F (a z)) - ∫ z in (0 : ℝ)..y, coef V z * F (b z)| ≤
      y ^ 2 / (8 * δ ^ 2) * M := by
  rw [← intervalIntegral.integral_sub (intervalIntegrable_coef_mul hF V ha 0 y)
    (intervalIntegrable_coef_mul hF V hb 0 y)]
  have hδ := hF.pos
  have hbound : ∀ z ∈ uIoc (0 : ℝ) y, ‖coef V z * F (a z) - coef V z * F (b z)‖ ≤ z / 4 * (M / δ ^ 2) := by
    intro z hz
    rw [uIoc_of_le hy] at hz
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    have h1 := abs_coef_le V z
    rw [abs_of_pos hz.1] at h1
    exact mul_le_mul h1 ((hF.lip _ _).trans (div_le_div_of_nonneg_right (hM z ⟨hz.1.le, hz.2⟩)
      (by positivity))) (abs_nonneg _) (by linarith [hz.1])
  refine (intervalIntegral.norm_integral_le_of_norm_le hy (ae_of_all _ fun z hz => hbound z
    (by rw [uIoc_of_le hy]; exact hz)) ((by fun_prop : Continuous fun z : ℝ => z / 4 * (M / δ ^ 2)).intervalIntegrable
      (μ := volume) 0 y)).trans_eq ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div, integral_id]
  field_simp
  ring

theorem abs_pic_one_sub_le (hF : IsCut δ F) (x₀ : ℝ) (V : C(Icc (0 : ℝ≥0) R, ℝ)) {y : ℝ} (hy : 0 ≤ y) :
    |pic F x₀ V 1 y - x₀| ≤ y ^ 2 / (8 * δ) := by
  simp only [pic, add_sub_cancel_left]
  have hδ := hF.pos
  have h := intervalIntegral.norm_integral_le_of_norm_le (f := fun z => coef V z * F (x₀ - drv V z))
    (g := fun z : ℝ => z / 4 * (1 / δ)) hy (ae_of_all _ fun z hz => by
      have := abs_coef_mul_le hF V z (x₀ - drv V z)
      rwa [abs_of_pos hz.1, ← Real.norm_eq_abs] at this)
    ((by fun_prop : Continuous fun z : ℝ => z / 4 * (1 / δ)).intervalIntegrable (μ := volume) 0 y)
  rw [Real.norm_eq_abs] at h
  refine h.trans_eq ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div, integral_id]
  field_simp
  ring

theorem abs_integral_coef_le (hF : IsCut δ F) (V : C(Icc (0 : ℝ≥0) R, ℝ)) {g : ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y) :
    |∫ z in (0 : ℝ)..y, coef V z * F (g z)| ≤ y ^ 2 / (8 * δ) := by
  have hδ := hF.pos
  have h := intervalIntegral.norm_integral_le_of_norm_le (f := fun z => coef V z * F (g z))
    (g := fun z : ℝ => z / 4 * (1 / δ)) hy (ae_of_all _ fun z hz => by
      have := abs_coef_mul_le hF V z (g z)
      rwa [abs_of_pos hz.1, ← Real.norm_eq_abs] at this)
    ((by fun_prop : Continuous fun z : ℝ => z / 4 * (1 / δ)).intervalIntegrable (μ := volume) 0 y)
  rw [Real.norm_eq_abs] at h
  refine h.trans_eq ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div, integral_id]
  field_simp
  ring

/-- **The Picard iterates contract**: `|pic_{n+1} − pic_n| ≤ c₀ kⁿ` on `[0, R]`, `c₀ = R²/(8δ)`, `k = R²/(8δ²)`. -/
theorem abs_pic_succ_sub_le (hF : IsCut δ F) (x₀ : ℝ) (V : C(Icc (0 : ℝ≥0) R, ℝ)) :
    ∀ n : ℕ, ∀ y ∈ Icc (0 : ℝ) R, |pic F x₀ V (n + 1) y - pic F x₀ V n y| ≤
      (R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n := by
  have hδ := hF.pos
  intro n
  induction n with
  | zero =>
    intro y hy
    simp only [pow_zero, mul_one]
    refine (abs_pic_one_sub_le hF x₀ V hy.1).trans ?_
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hy.1 hy.2 2) (by positivity)
  | succ n ih =>
    intro y hy
    have e : pic F x₀ V (n + 1 + 1) y - pic F x₀ V (n + 1) y =
        (∫ z in (0 : ℝ)..y, coef V z * F (pic F x₀ V (n + 1) z - drv V z)) -
          ∫ z in (0 : ℝ)..y, coef V z * F (pic F x₀ V n z - drv V z) := by
      simp only [pic]; ring
    rw [e]
    have hM : ∀ z ∈ Icc 0 y, |(pic F x₀ V (n + 1) z - drv V z) - (pic F x₀ V n z - drv V z)| ≤
        (R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n := fun z hz => by
      rw [sub_sub_sub_cancel_right]; exact ih z ⟨hz.1, hz.2.trans hy.2⟩
    refine (abs_integral_coef_sub_le hF V ((continuous_pic hF x₀ V _).measurable.sub (measurable_drv V))
      ((continuous_pic hF x₀ V _).measurable.sub (measurable_drv V)) hy.1 hM).trans ?_
    have hy2 : y ^ 2 / (8 * δ ^ 2) ≤ (R : ℝ) ^ 2 / (8 * δ ^ 2) := by gcongr; exact hy.1; exact hy.2
    calc y ^ 2 / (8 * δ ^ 2) * ((R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n)
        ≤ (R : ℝ) ^ 2 / (8 * δ ^ 2) * ((R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n) :=
          mul_le_mul_of_nonneg_right hy2 (by positivity)
      _ = _ := by ring

theorem tendsto_pic_mark (hF : IsCut δ F) (hk : (R : ℝ) ^ 2 / (8 * δ ^ 2) < 1) (x₀ : ℝ)
    (V : C(Icc (0 : ℝ≥0) R, ℝ)) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) R) :
    Tendsto (fun n => pic F x₀ V n y) atTop (𝓝 (mark F x₀ V y)) := by
  have hc : CauchySeq fun n => pic F x₀ V n y :=
    cauchySeq_of_le_geometric _ _ hk fun n => by
      rw [dist_comm, Real.dist_eq]; exact abs_pic_succ_sub_le hF x₀ V n y hy
  exact hc.tendsto_limUnder

theorem abs_pic_sub_mark_le (hF : IsCut δ F) (hk : (R : ℝ) ^ 2 / (8 * δ ^ 2) < 1) (x₀ : ℝ)
    (V : C(Icc (0 : ℝ≥0) R, ℝ)) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) R) (n : ℕ) :
    |pic F x₀ V n y - mark F x₀ V y| ≤
      (R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n / (1 - (R : ℝ) ^ 2 / (8 * δ ^ 2)) := by
  rw [← Real.dist_eq]
  exact dist_le_of_le_geometric_of_tendsto _ _ hk (fun n => by
    rw [dist_comm, Real.dist_eq]; exact abs_pic_succ_sub_le hF x₀ V n y hy) (tendsto_pic_mark hF hk x₀ V hy) n

/-- **Uniqueness**: a measurable solution of the integral equation on `[0, R]` is the mark. -/
theorem eq_mark_of_eq (hF : IsCut δ F) (hk : (R : ℝ) ^ 2 / (8 * δ ^ 2) < 1) (x₀ : ℝ)
    (V : C(Icc (0 : ℝ≥0) R, ℝ)) {Y : ℝ → ℝ} (hYm : Measurable Y)
    (hY : ∀ y ∈ Icc (0 : ℝ) R, Y y = x₀ + ∫ z in (0 : ℝ)..y, coef V z * F (Y z - drv V z))
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) R) : Y y = mark F x₀ V y := by
  have hδ := hF.pos
  have key : ∀ n : ℕ, ∀ y ∈ Icc (0 : ℝ) R, |Y y - pic F x₀ V n y| ≤
      (R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n := by
    intro n
    induction n with
    | zero =>
      intro y hy
      rw [hY y hy]
      simp only [pic, add_sub_cancel_left, pow_zero, mul_one]
      refine (abs_integral_coef_le hF V hy.1).trans ?_
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hy.1 hy.2 2) (by positivity)
    | succ n ih =>
      intro y hy
      rw [hY y hy]
      have e : x₀ + (∫ z in (0 : ℝ)..y, coef V z * F (Y z - drv V z)) - pic F x₀ V (n + 1) y =
          (∫ z in (0 : ℝ)..y, coef V z * F (Y z - drv V z)) -
            ∫ z in (0 : ℝ)..y, coef V z * F (pic F x₀ V n z - drv V z) := by
        simp only [pic]; ring
      rw [e]
      have hM : ∀ z ∈ Icc 0 y, |(Y z - drv V z) - (pic F x₀ V n z - drv V z)| ≤
          (R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n := fun z hz => by
        rw [sub_sub_sub_cancel_right]; exact ih z ⟨hz.1, hz.2.trans hy.2⟩
      refine (abs_integral_coef_sub_le hF V (hYm.sub (measurable_drv V))
        ((continuous_pic hF x₀ V _).measurable.sub (measurable_drv V)) hy.1 hM).trans ?_
      have hy2 : y ^ 2 / (8 * δ ^ 2) ≤ (R : ℝ) ^ 2 / (8 * δ ^ 2) := by gcongr; exact hy.1; exact hy.2
      calc y ^ 2 / (8 * δ ^ 2) * ((R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n)
          ≤ (R : ℝ) ^ 2 / (8 * δ ^ 2) * ((R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n) :=
            mul_le_mul_of_nonneg_right hy2 (by positivity)
        _ = _ := by ring
  have hk0 : 0 ≤ (R : ℝ) ^ 2 / (8 * δ ^ 2) := by positivity
  have hlim : Tendsto (fun n => pic F x₀ V n y) atTop (𝓝 (Y y)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (g := fun n => (R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n)
      (fun n => dist_nonneg) (fun n => ?_) ?_
    · rw [Real.dist_eq, abs_sub_comm]; exact key n y hy
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk).const_mul ((R : ℝ) ^ 2 / (8 * δ))
  exact tendsto_nhds_unique hlim (tendsto_pic_mark hF hk x₀ V hy)

/-- Each Picard iterate is continuous in the path. -/
theorem continuous_pic_left (hF : IsCut δ F) (x₀ : ℝ) :
    ∀ (n : ℕ) (y : ℝ), Continuous fun V : C(Icc (0 : ℝ≥0) R, ℝ) => pic F x₀ V n y
  | 0, _ => continuous_const
  | n + 1, y => by
    refine continuous_const.add (intervalIntegral.continuous_of_dominated_interval
      (bound := fun z => |z| / 4 * (1 / δ)) (fun V => ?_) (fun V => ?_) ?_ ?_)
    · exact ((measurable_coef V).mul (hF.cont.measurable.comp ((continuous_pic hF x₀ V n).measurable.sub
        (measurable_drv V)))).aestronglyMeasurable
    · exact ae_of_all _ fun z _ => by rw [Real.norm_eq_abs]; exact abs_coef_mul_le hF V z _
    · exact (by fun_prop : Continuous fun z : ℝ => |z| / 4 * (1 / δ)).intervalIntegrable 0 y
    · exact ae_ne_zero_of_mem.mono fun z hz _ => (continuous_coef_left hz).mul
        (hF.cont.comp ((continuous_pic_left hF x₀ n z).sub (continuous_drv hz)))

/-- **The separated mark is continuous in the path.** -/
theorem continuous_mark (hF : IsCut δ F) (hk : (R : ℝ) ^ 2 / (8 * δ ^ 2) < 1) (x₀ : ℝ) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) R) : Continuous fun V : C(Icc (0 : ℝ≥0) R, ℝ) => mark F x₀ V y := by
  have hδ := hF.pos
  have hk0 : 0 ≤ (R : ℝ) ^ 2 / (8 * δ ^ 2) := by positivity
  refine TendstoUniformly.continuous (F := fun n V => pic F x₀ V n y) (p := atTop) ?_
    (Frequently.of_forall fun n => continuous_pic_left hF x₀ n y)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have h0 : Tendsto (fun n : ℕ => (R : ℝ) ^ 2 / (8 * δ) * ((R : ℝ) ^ 2 / (8 * δ ^ 2)) ^ n /
      (1 - (R : ℝ) ^ 2 / (8 * δ ^ 2))) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk).const_mul
      ((R : ℝ) ^ 2 / (8 * δ))).div_const (1 - (R : ℝ) ^ 2 / (8 * δ ^ 2))
  filter_upwards [h0.eventually (gt_mem_nhds hε)] with n hn V
  rw [dist_comm, Real.dist_eq]
  exact lt_of_le_of_lt (abs_pic_sub_mark_le hF hk x₀ V hy n) hn

/-! ### The restart map and the entrance path of an angle path -/

/-- **The restart state as a functional of the entrance path**: the driver at level `R` and the word seen from it
(seeds from `low`/`upp`, separated marks from `mark`). -/
def restartMap {nL nR : ℕ} (δ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (V : C(Icc (0 : ℝ≥0) R, ℝ)) :
    ℝ × ((Fin nL → ℝ) × (Fin nR → ℝ)) :=
  (drv V R, (fun i => (if xL i = 0 then low V R else mark (FL δ) (xL i) V R) - drv V R),
    fun j => (if xR j = 0 then upp V R else mark (FR δ) (xR j) V R) - drv V R)

theorem continuous_restartMap {nL nR : ℕ} (hR : 0 < R) {δ : ℝ} (hδ : 0 < δ)
    (hk : (R : ℝ) ^ 2 / (8 * δ ^ 2) < 1) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    Continuous (restartMap (R := R) δ xL xR) := by
  have hR' : (R : ℝ) ≠ 0 := (NNReal.coe_pos.2 hR).ne'
  have hRmem : (R : ℝ) ∈ Icc (0 : ℝ) R := ⟨NNReal.coe_nonneg R, le_rfl⟩
  refine (continuous_drv hR').prodMk ((continuous_pi fun i => ?_).prodMk (continuous_pi fun j => ?_))
  · refine Continuous.sub ?_ (continuous_drv hR')
    split_ifs
    · exact continuous_low R
    · exact continuous_mark (isCut_FL hδ) hk _ hRmem
  · refine Continuous.sub ?_ (continuous_drv hR')
    split_ifs
    · exact continuous_upp R
    · exact continuous_mark (isCut_FR hδ) hk _ hRmem

theorem abs_clamp01_le (x : ℝ) : |clamp01 x| ≤ 1 := by
  obtain ⟨h0, h1⟩ := clamp01_mem x
  rw [abs_le]; constructor <;> linarith

theorem continuous_mul_clamp_log {U : ℝ → ℝ} (hU : Continuous U) :
    Continuous fun y : ℝ => y * clamp01 (U (Real.log y)) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : y = 0
  · subst hy
    have hb : ∀ z : ℝ, ‖z * clamp01 (U (Real.log z))‖ ≤ |z| := fun z => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_of_le_one_right (abs_nonneg z) (abs_clamp01_le _)
    rw [ContinuousAt, zero_mul]
    exact squeeze_zero_norm hb (by simpa using (continuous_abs.tendsto (0 : ℝ)))
  · exact continuousAt_id.mul (continuous_clamp01.continuousAt.comp
      (hU.continuousAt.comp (Real.continuousAt_log hy)))

/-- The entrance path `V(y) = y · U(log y)` of an angle path `U` (clamped to `[0, 1]`). -/
def vPath (U : ℝ → ℝ) (hU : Continuous U) : C(Icc (0 : ℝ≥0) R, ℝ) :=
  ⟨fun y => (y : ℝ) * clamp01 (U (Real.log y)),
    (continuous_mul_clamp_log hU).comp (NNReal.continuous_coe.comp continuous_subtype_val)⟩

theorem evR_vPath {U : ℝ → ℝ} (hU : Continuous U) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) R) :
    evR (vPath (R := R) U hU) y = y * clamp01 (U (Real.log y)) := by
  simp only [evR, vPath, ContinuousMap.coe_mk]
  rw [projIcc_of_mem _ ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hy.2⟩, Real.coe_toNNReal _ hy.1]

theorem ang_vPath {U : ℝ → ℝ} (hU : Continuous U) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) R) :
    ang (vPath (R := R) U hU) y = clamp01 (U (Real.log y)) := by
  rw [ang, evR_vPath hU ⟨hy.1.le, hy.2⟩, mul_div_cancel_left₀ _ hy.1.ne']
  obtain ⟨h0, h1⟩ := clamp01_mem (U (Real.log y))
  conv_lhs => rw [clamp01, min_eq_right h1, max_eq_right h0]

end Aux4

end Supp12

end InteractingSLE
