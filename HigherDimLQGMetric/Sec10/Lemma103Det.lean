import HigherDimLQGMetric.Metric.WeylCompose
import HigherDimLQGMetric.CM.Basic
import HigherDimLQGMetric.Field.Basic
import HigherDimLQGMetric.Field.SphereAvgBasic
import HigherDimLQGMetric.Sphere.Growth
import HigherDimLFPP.Paths.DistOn
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# [S] Lemma 10.3, deterministic part

Packet S8b (MA4 Details (a) A20; blueprint Part A, Lemma `lem:10-3`; source l. 1547–1570).

The bump `f` of the proof is a `ContDiffBump` centred at `e₁/2`, equal to `1` on the convex open
domain `U = B(e₁/2, 3/4)` (which contains `0` and `e₁`) and supported in `B(e₁/2, 1)`. On the unit
sphere `f(x) + f(-x) ≤ 1` (the two points are at distance `2`), so the antipodal invariance of the
uniform sphere measure gives `f₁(0) = ∫ f dσ ≤ 1/2 < 1`. With `g = f - f₁(0)` and `a = 1 - f₁(0) > 0`,
the shift `t g` satisfies `h + t g = shiftNorm h (t f)` (`s8b_shiftNorm_eq`).

For a continuous length metric `E` (the realization `D_h`), the real function
`ψ(t) = (e^{ξ t g}·E)(0, e₁)` satisfies (`ξ > 0`):
* `ψ(t') ≤ e^{ξ|t' - t|} ψ(t)` (Lemma 2.1(d) in ratio form), hence `ψ` is continuous;
* `ψ(t) ≤ e^{ξ t a} E(0, e₁; U)` with `E(0, e₁; U) < ∞` (connected open sets of a length space are
  rectifiably connected), hence `ψ(t) → 0` as `t → -∞`;
* `ψ(t) ≥ e^{ξ t a} min(E(0, e₁), R)` with `R > 0` an `E`-radius whose ball lies in `U` (first exit),
  hence `ψ(t) → ∞` as `t → ∞`;
so every interval `(u, v)` with `0 < u < v` contains `ψ(q)` for some rational `q`
(`s8b_exists_rat_psi_mem`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ### The bump `f` and the domain `U` -/

/-- The centre `e₁/2` of the bump of Lemma 10.3. -/
def s8bCenter (d : ℕ) : Rd d := (2⁻¹ : ℝ) • e₁ d

theorem s8b_norm_center (hd : 1 ≤ d) : ‖s8bCenter d‖ = 2⁻¹ := by
  rw [s8bCenter, norm_smul, HigherDimLFPP.norm_e₁ (by omega), mul_one, Real.norm_eq_abs,
    abs_of_pos (by norm_num)]

theorem s8b_e₁_sub_center : e₁ d - s8bCenter d = s8bCenter d := by
  rw [sub_eq_iff_eq_add, s8bCenter, ← add_smul]
  norm_num

theorem s8b_zero_ne_e₁ (hd : 1 ≤ d) : (0 : Rd d) ≠ e₁ d := by
  intro h
  have := HigherDimLFPP.norm_e₁ (d := d) (by omega)
  rw [← h, norm_zero] at this
  exact zero_ne_one this

/-- The smooth bump of Lemma 10.3: `1` on `B̄(e₁/2, 3/4)`, with support `B(e₁/2, 1)`. -/
def s8bBumpData (d : ℕ) : ContDiffBump (s8bCenter d) where
  rIn := 3 / 4
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The bump `f` of Lemma 10.3 as a continuous function. -/
def s8bBump (d : ℕ) : C(Rd d, ℝ) := ⟨s8bBumpData d, (s8bBumpData d).continuous⟩

theorem s8bBump_apply (x : Rd d) : s8bBump d x = s8bBumpData d x := rfl

theorem s8bBump_coe : (⇑(s8bBump d) : Rd d → ℝ) = ⇑(s8bBumpData d) := rfl

/-- The domain `U = B(e₁/2, 3/4)` of Lemma 10.3: a convex open neighbourhood of `[0, e₁]`. -/
def s8bDom (d : ℕ) : Set (Rd d) := ball (s8bCenter d) (3 / 4)

theorem s8b_isOpen_dom : IsOpen (s8bDom d) := isOpen_ball

theorem s8b_isPreconnected_dom : IsPreconnected (s8bDom d) := (convex_ball _ _).isPreconnected

theorem s8b_mem_dom_of_norm_lt (hd : 1 ≤ d) {x : Rd d} (hx : ‖x‖ < 4⁻¹) : x ∈ s8bDom d := by
  rw [s8bDom, mem_ball, dist_eq_norm]
  calc ‖x - s8bCenter d‖ ≤ ‖x‖ + ‖s8bCenter d‖ := norm_sub_le _ _
    _ < 4⁻¹ + 2⁻¹ := by rw [s8b_norm_center hd]; linarith
    _ = 3 / 4 := by norm_num

theorem s8b_zero_mem_dom (hd : 1 ≤ d) : (0 : Rd d) ∈ s8bDom d :=
  s8b_mem_dom_of_norm_lt hd (by rw [norm_zero]; norm_num)

theorem s8b_e₁_mem_dom (hd : 1 ≤ d) : e₁ d ∈ s8bDom d := by
  rw [s8bDom, mem_ball, dist_eq_norm, s8b_e₁_sub_center, s8b_norm_center hd]
  norm_num

theorem s8bBump_eq_one {x : Rd d} (hx : x ∈ s8bDom d) : s8bBump d x = 1 :=
  (s8bBumpData d).one_of_mem_closedBall (ball_subset_closedBall hx)

theorem s8bBump_nonneg (x : Rd d) : 0 ≤ s8bBump d x := (s8bBumpData d).nonneg

theorem s8bBump_le_one (x : Rd d) : s8bBump d x ≤ 1 := (s8bBumpData d).le_one

theorem s8bBump_eq_zero_of_le {x : Rd d} (hx : 1 ≤ ‖x - s8bCenter d‖) : s8bBump d x = 0 := by
  rw [s8bBump_apply, ← Function.notMem_support, (s8bBumpData d).support_eq, mem_ball,
    dist_eq_norm, not_lt]
  exact hx

theorem s8b_contDiff_bump : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑(s8bBump d)) := by
  rw [s8bBump_coe]
  exact (s8bBumpData d).contDiff

theorem s8b_hasCompactSupport_bump : HasCompactSupport (⇑(s8bBump d)) := by
  rw [s8bBump_coe]
  exact (s8bBumpData d).hasCompactSupport

/-- On the unit sphere, at most one of `x`, `-x` lies in the support `B(e₁/2, 1)` of the bump. -/
theorem s8bBump_add_neg_le {x : Rd d} (hx : ‖x‖ = 1) : s8bBump d x + s8bBump d (-x) ≤ 1 := by
  have key : 2 ≤ ‖x - s8bCenter d‖ + ‖-x - s8bCenter d‖ := by
    calc (2 : ℝ) = ‖(x - s8bCenter d) - (-x - s8bCenter d)‖ := by
          rw [show (x - s8bCenter d) - (-x - s8bCenter d) = (2 : ℝ) • x by rw [two_smul]; abel,
            norm_smul, hx]
          norm_num
      _ ≤ ‖x - s8bCenter d‖ + ‖-x - s8bCenter d‖ := norm_sub_le _ _
  rcases le_or_gt 1 ‖x - s8bCenter d‖ with h1 | h1
  · rw [s8bBump_eq_zero_of_le h1, zero_add]
    exact s8bBump_le_one _
  · rw [s8bBump_eq_zero_of_le (by linarith : 1 ≤ ‖-x - s8bCenter d‖), add_zero]
    exact s8bBump_le_one _

/-! ### Antipodal invariance of the uniform sphere measure -/

theorem s8b_unitSphereProb_neg (hd : 1 ≤ d) {A : Set (Rd d)} (hA : MeasurableSet A) :
    unitSphereProb d (-A) = unitSphereProb d A := by
  rw [unitSphereProb_apply_eq hd hA.neg, unitSphereProb_apply_eq hd hA]
  congr 1
  have hset : sphere (0 : Rd d) 1 ∩ -A = -(sphere (0 : Rd d) 1 ∩ A) := by
    ext x
    simp only [mem_inter_iff, Set.mem_neg, mem_sphere_zero_iff_norm, norm_neg]
  rw [hset, Set.smul_neg, Measure.measure_neg]

theorem s8b_map_neg_unitSphereProb (hd : 1 ≤ d) :
    (unitSphereProb d).map (fun x : Rd d => -x) = unitSphereProb d := by
  ext A hA
  rw [Measure.map_apply measurable_neg hA]
  exact s8b_unitSphereProb_neg hd hA

theorem s8b_integral_comp_neg (hd : 1 ≤ d) {g : Rd d → ℝ} (hg : Continuous g) :
    ∫ x, g (-x) ∂(unitSphereProb d) = ∫ x, g x ∂(unitSphereProb d) := by
  conv_rhs => rw [← s8b_map_neg_unitSphereProb hd]
  rw [integral_map measurable_neg.aemeasurable hg.aestronglyMeasurable]

/-! ### The sphere average `f₁(0)` and the shifts `g_t = t (f - f₁(0))` -/

/-- The unit-sphere average `f₁(0) = ∫ f dσ` of the bump. -/
def s8bMean (d : ℕ) : ℝ := ∫ x, s8bBump d x ∂(unitSphereProb d)

theorem s8bMean_nonneg : 0 ≤ s8bMean d := integral_nonneg fun x => s8bBump_nonneg x

/-- `f₁(0) ≤ 1/2`: integrate `f(x) + f(-x) ≤ 1` over the sphere and use antipodal invariance. -/
theorem s8bMean_le (hd : 1 ≤ d) : s8bMean d ≤ 2⁻¹ := by
  have := isProbabilityMeasure_unitSphereProb hd
  have hint : Integrable (fun x => s8bBump d x) (unitSphereProb d) :=
    integrable_unitSphereProb_of_continuous (s8bBump d).continuous
  have hint' : Integrable (fun x => s8bBump d (-x)) (unitSphereProb d) :=
    integrable_unitSphereProb_of_continuous ((s8bBump d).continuous.comp continuous_neg)
  have hsum : ∫ x, (s8bBump d x + s8bBump d (-x)) ∂(unitSphereProb d) ≤ 1 := by
    calc ∫ x, (s8bBump d x + s8bBump d (-x)) ∂(unitSphereProb d)
        ≤ ∫ _x, (1 : ℝ) ∂(unitSphereProb d) :=
          integral_mono_ae (hint.add hint') (integrable_const 1)
            ((ae_unitSphereProb_norm_eq_one d).mono fun x hx => s8bBump_add_neg_le hx)
      _ = 1 := by simp
  rw [integral_add hint hint', s8b_integral_comp_neg hd (s8bBump d).continuous] at hsum
  rw [s8bMean]
  linarith

/-- `a = 1 - f₁(0) > 0`. -/
theorem s8b_one_sub_mean_pos (hd : 1 ≤ d) : 0 < 1 - s8bMean d := by
  have := s8bMean_le hd
  linarith

/-- The shift `g_t = t (f - f₁(0))`. -/
def s8bShift (d : ℕ) (t : ℝ) : C(Rd d, ℝ) :=
  t • (s8bBump d - ContinuousMap.const (Rd d) (s8bMean d))

theorem s8bShift_apply (t : ℝ) (x : Rd d) : s8bShift d t x = t * (s8bBump d x - s8bMean d) := by
  simp only [s8bShift, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, smul_eq_mul]

/-- `h + t g = shiftNorm h (t f)` (MA4 E13). -/
theorem s8b_shiftNorm_eq (g : DistRd d) (t : ℝ) :
    shiftNorm g (t • s8bBump d) = addFun g (s8bShift d t) := by
  rw [shiftNorm, addConst_addFun]
  congr 1
  ext x
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.const_apply,
    smul_eq_mul, s8bShift_apply]
  rw [integral_const_mul, s8bMean]
  ring

theorem s8bShift_eq_of_mem (t : ℝ) {x : Rd d} (hx : x ∈ s8bDom d) :
    s8bShift d t x = t * (1 - s8bMean d) := by
  rw [s8bShift_apply, s8bBump_eq_one hx]

theorem s8b_abs_bump_sub_mean_le (hd : 1 ≤ d) (x : Rd d) : |s8bBump d x - s8bMean d| ≤ 1 := by
  have h0 := s8bBump_nonneg (d := d) x
  have h1 := s8bBump_le_one (d := d) x
  have m0 := s8bMean_nonneg (d := d)
  have m1 := s8bMean_le hd
  rw [abs_le]
  constructor <;> linarith

/-- The Lipschitz bound in `t` used for Lemma 2.1(d): `ξ g_{t'} ≤ ξ g_t + ξ |t' - t|`. -/
theorem s8bShift_le (hd : 1 ≤ d) {ξ : ℝ} (hξ : 0 ≤ ξ) (t t' : ℝ) (x : Rd d) :
    ξ * s8bShift d t' x ≤ ξ * s8bShift d t x + ξ * |t' - t| := by
  rw [s8bShift_apply, s8bShift_apply]
  have hb : (t' - t) * (s8bBump d x - s8bMean d) ≤ |t' - t| := by
    calc (t' - t) * (s8bBump d x - s8bMean d)
        ≤ |(t' - t) * (s8bBump d x - s8bMean d)| := le_abs_self _
      _ = |t' - t| * |s8bBump d x - s8bMean d| := abs_mul _ _
      _ ≤ |t' - t| * 1 := mul_le_mul_of_nonneg_left (s8b_abs_bump_sub_mean_le hd x) (abs_nonneg _)
      _ = |t' - t| := mul_one _
  calc ξ * (t' * (s8bBump d x - s8bMean d))
      = ξ * (t * (s8bBump d x - s8bMean d)) + ξ * ((t' - t) * (s8bBump d x - s8bMean d)) := by
        ring
    _ ≤ ξ * (t * (s8bBump d x - s8bMean d)) + ξ * |t' - t| := by gcongr

/-! ### The point distance along the Weyl family -/

/-- `ψ(t) = (e^{ξ g_t}·E)(0, e₁)`, as a real number. -/
def s8bPsi (ξ : ℝ) (E : ContMetric d) (t : ℝ) : ℝ :=
  (weylScale ξ (s8bShift d t) E 0 (e₁ d)).toReal

variable {ξ : ℝ} {E : ContMetric d}

/-- Lemma 2.1(d) in ratio form: `ψ(t') ≤ e^{ξ |t' - t|} ψ(t)`. -/
theorem s8bPsi_le_exp_mul (hd : 1 ≤ d) (hξ : 0 ≤ ξ) (hE : E.IsLength) (t t' : ℝ) :
    s8bPsi ξ E t' ≤ Real.exp (ξ * |t' - t|) * s8bPsi ξ E t := by
  have h := weylScale_le_exp_mul (D := E) (z := 0) (w := e₁ d)
    (fun x => s8bShift_le hd hξ t t' x)
  have hne : ENNReal.ofReal (Real.exp (ξ * |t' - t|)) *
      weylScale ξ (s8bShift d t) E 0 (e₁ d) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (weylScale_ne_top hE _ _)
  have := ENNReal.toReal_mono hne h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this

/-- `t ↦ (e^{ξ g_t}·E)(0, e₁)` is continuous. -/
theorem s8b_continuous_psi (hd : 1 ≤ d) (hξ : 0 ≤ ξ) (hE : E.IsLength) :
    Continuous (s8bPsi ξ E) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hlow : (fun t' => Real.exp (-(ξ * |t' - t|)) * s8bPsi ξ E t) ≤ s8bPsi ξ E := by
    intro t'
    have h := s8bPsi_le_exp_mul hd hξ hE t' t
    rw [abs_sub_comm] at h
    show Real.exp (-(ξ * |t' - t|)) * s8bPsi ξ E t ≤ s8bPsi ξ E t'
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    exact h
  have hup : s8bPsi ξ E ≤ fun t' => Real.exp (ξ * |t' - t|) * s8bPsi ξ E t :=
    fun t' => s8bPsi_le_exp_mul hd hξ hE t t'
  have hc1 : Continuous fun t' => Real.exp (-(ξ * |t' - t|)) * s8bPsi ξ E t := by fun_prop
  have hc2 : Continuous fun t' => Real.exp (ξ * |t' - t|) * s8bPsi ξ E t := by fun_prop
  have e1 := hc1.tendsto t
  have e2 := hc2.tendsto t
  simp only [sub_self, abs_zero, mul_zero, neg_zero, Real.exp_zero, one_mul] at e1 e2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le e1 e2 hlow hup

/-- Paths inside `U`, where `ξ g_t = ξ t a`: `ψ(t) ≤ e^{ξ t a} E(0, e₁; U)`. -/
theorem s8bPsi_le_internal (hd : 1 ≤ d) (hE : E.IsLength) (t : ℝ) :
    s8bPsi ξ E t ≤
      Real.exp (ξ * (t * (1 - s8bMean d))) * (E.internal (s8bDom d) 0 (e₁ d)).toReal := by
  have h1 : weylScale ξ (s8bShift d t) E 0 (e₁ d) ≤
      weylScaleOn ξ (s8bShift d t) E (s8bDom d) 0 (e₁ d) := weylScale_le_weylScaleOn
  rw [weylScaleOn_of_eq_const (a := ξ * (t * (1 - s8bMean d)))
    (fun x hx => by rw [s8bShift_eq_of_mem t hx])] at h1
  have hne : ENNReal.ofReal (Real.exp (ξ * (t * (1 - s8bMean d)))) *
      E.internal (s8bDom d) 0 (e₁ d) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (E.internal_ne_top_of_isPreconnected hE s8b_isOpen_dom s8b_isPreconnected_dom
        (s8b_zero_mem_dom hd) (s8b_e₁_mem_dom hd))
  have := ENNReal.toReal_mono hne h1
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this

/-- First exit from an `E`-ball inside `U`: `ψ(t) ≥ e^{ξ t a} m₀` with `m₀ > 0` independent of
`ξ` and `t`. -/
theorem s8b_exists_psi_lower (hd : 1 ≤ d) (hE : E.IsLength) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ ξ t : ℝ,
      Real.exp (ξ * (t * (1 - s8bMean d))) * m₀ ≤ s8bPsi ξ E t := by
  obtain ⟨δ, hδ, hsmall⟩ := E.2.euclidean_of_small 0 4⁻¹ (by norm_num)
  set R : ℝ≥0∞ := ENNReal.ofReal (δ / 2) with hR
  have hball : ∀ y : E.Space, edist (E.pt 0) y ≤ R → E.unpt y ∈ s8bDom d := by
    intro y hy
    apply s8b_mem_dom_of_norm_lt hd
    rw [← E.pt_unpt y, E.edist_pt, hR, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hy
    have := hsmall (E.unpt y) (by linarith)
    rwa [zero_sub, norm_neg] at this
  set m : ℝ≥0∞ := min (edist (E.pt 0) (E.pt (e₁ d))) R with hm
  have hm0 : 0 < m := by
    refine lt_min ?_ ?_
    · exact edist_pos.2 fun h => s8b_zero_ne_e₁ hd (E.pt_injective h)
    · exact ENNReal.ofReal_pos.2 (by positivity)
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
  refine ⟨m.toReal, ENNReal.toReal_pos hm0.ne' hmtop, fun ξ t => ?_⟩
  have h := weylDistOn_ge_min (w := E.weylWeight ξ (s8bShift d t)) (U := univ) (x := E.pt 0)
    (R := R) (m := Real.exp (ξ * (t * (1 - s8bMean d)))) (fun y _ hy => by
      rw [ContMetric.weylWeight, s8bShift_eq_of_mem t (hball y hy)]) (E.pt (e₁ d))
  rw [← weylScale_eq_weylDistOn] at h
  have := ENNReal.toReal_mono (weylScale_ne_top hE _ _) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this

/-- **IVT over the rationals**: every interval `(u, v)` with `0 < u < v` contains `ψ(q)` for a
rational `q`. -/
theorem s8b_exists_rat_psi_mem (hd : 1 ≤ d) (hξ : 0 < ξ) (hE : E.IsLength) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) : ∃ q : ℚ, s8bPsi ξ E q ∈ Ioo u v := by
  have ha := s8b_one_sub_mean_pos hd
  have hc := s8b_continuous_psi hd hξ.le hE
  obtain ⟨m₀, hm₀, hlow⟩ := s8b_exists_psi_lower hd hE
  have hlin : ∀ t : ℝ, ξ * (t * (1 - s8bMean d)) = (ξ * (1 - s8bMean d)) * t := fun t => by ring
  have hbot : Tendsto (fun t : ℝ => ξ * (t * (1 - s8bMean d))) atBot atBot := by
    simp only [hlin]
    exact tendsto_id.const_mul_atBot (mul_pos hξ ha)
  have htop : Tendsto (fun t : ℝ => ξ * (t * (1 - s8bMean d))) atTop atTop := by
    simp only [hlin]
    exact tendsto_id.const_mul_atTop (mul_pos hξ ha)
  have h0 : Tendsto (fun t : ℝ => Real.exp (ξ * (t * (1 - s8bMean d))) *
      (E.internal (s8bDom d) 0 (e₁ d)).toReal) atBot (𝓝 0) := by
    simpa only [Function.comp_def, zero_mul] using
      (Real.tendsto_exp_atBot.comp hbot).mul_const (E.internal (s8bDom d) 0 (e₁ d)).toReal
  have hinf : Tendsto (fun t : ℝ => Real.exp (ξ * (t * (1 - s8bMean d))) * m₀) atTop atTop :=
    (Real.tendsto_exp_atTop.comp htop).atTop_mul_const hm₀
  obtain ⟨t₁, ht₁⟩ := (h0.eventually (gt_mem_nhds hu)).exists
  obtain ⟨t₂, ht₂⟩ := (hinf.eventually_gt_atTop v).exists
  have hψ₁ : s8bPsi ξ E t₁ < u := (s8bPsi_le_internal hd hE t₁).trans_lt ht₁
  have hψ₂ : v < s8bPsi ξ E t₂ := ht₂.trans_le (hlow ξ t₂)
  obtain ⟨t, ht⟩ : (u + v) / 2 ∈ range (s8bPsi ξ E) :=
    intermediate_value_univ t₁ t₂ hc ⟨by linarith, by linarith⟩
  have hopen : IsOpen (s8bPsi ξ E ⁻¹' Ioo u v) := isOpen_Ioo.preimage hc
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hopen
    ⟨t, by rw [mem_preimage, ht]; constructor <;> linarith⟩
  exact ⟨q, hq⟩

end HigherDimLQGMetric
