/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiExistsQuartic
import BrownianMotion.Continuity.KolmogorovChentsov
import BrownianMotion.Continuity.HasBoundedInternalCoveringNumber

/-!
# A continuous version of the coordinate process (Kolmogorov–Chentsov)

Packet PROVE-YW-JACOBI. Under `pathMeasure κ a b`, the coordinate process `X_t(ω) = ω t` satisfies
`E |X_t - X_s|^4 ≤ M |t - s|^2` (`integral_quartic_le`), so it is a Kolmogorov process with exponents
`(4, 2)` on the index space `ℝ` (covering exponent `1`, `isCoverWithBoundedCoveringNumber_Ioo_real`).
The vendored Kolmogorov–Chentsov theorem (`exists_modification_holder_iSup`, RemyDegenne/brownian-motion)
gives a modification `Y` that is locally `1/8`-Hölder, hence continuous, for **every** `ω`
(`exists_continuous_modification`). Clamping to `[0, 1]` (`jacU`) keeps continuity and the
modification property, since `X_t ∈ [0, 1]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace InteractingSLE

namespace Sec2

namespace JacobiExists

/-- The intervals `(-(n+1), n+1)` cover `ℝ` with covering exponent `1`. -/
theorem isCoverWithBoundedCoveringNumber_Ioo_real :
    IsCoverWithBoundedCoveringNumber (fun n : ℕ ↦ Set.Ioo (-((n : ℝ) + 1)) (n + 1)) Set.univ
      (fun n ↦ 3 * (2 * ((n : ℝ≥0∞) + 1))) (fun _ ↦ 1) where
  c_ne_top n := by finiteness
  d_pos := by simp
  isOpen n := isOpen_Ioo
  totallyBounded n := totallyBounded_Ioo _ _
  hasBoundedCoveringNumber n := by
    have h_diam : Metric.ediam (Set.Ioo (-((n : ℝ) + 1)) (n + 1)) = 2 * ((n : ℝ≥0∞) + 1) := by
      rw [Real.ediam_Ioo, show (n : ℝ) + 1 - -((n : ℝ) + 1) = 2 * ((n : ℝ) + 1) by ring,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      congr 1
      rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    constructor
    · rw [h_diam]; finiteness
    intro ε hε_le
    simp only [ENNReal.rpow_one]
    rw [h_diam] at hε_le
    have hsub : Set.Ioo (-((n : ℝ) + 1)) (n + 1) ⊆
        Metric.closedEBall (0 : ℝ) ((n : ℝ≥0) + 1) := by
      intro x hx
      simp only [Set.mem_Ioo] at hx
      simp only [Metric.mem_closedEBall, edist_dist, Real.dist_eq, sub_zero]
      refine ENNReal.ofReal_le_of_le_toReal ?_
      simp only [ENNReal.coe_natCast]
      rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast, ENNReal.toReal_one]
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hε2 : ε / 2 ≤ (n : ℝ≥0) + 1 := by
      have h' : (ε : ℝ≥0∞) ≤ 2 * (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) := by
        simpa using hε_le
      have h'' : ε ≤ 2 * ((n : ℝ≥0) + 1) := by exact_mod_cast h'
      rw [div_le_iff₀ (by norm_num), mul_comm]
      exact h''
    by_cases hε0 : ε = 0
    · subst hε0
      simp
    calc (coveringNumber ε (Set.Ioo (-((n : ℝ) + 1)) (n + 1)) : ℝ≥0∞)
    _ ≤ coveringNumber (ε / 2) (Metric.closedEBall (0 : ℝ) ((n : ℝ≥0) + 1)) := by
      gcongr
      exact coveringNumber_subset_le hsub
    _ ≤ (3 * (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) / ((ε / 2 : ℝ≥0) : ℝ≥0∞)) ^ 1 := by
      have h := coveringNumber_closedEBall_le_three_mul (E := ℝ) (x := 0) (r := (n : ℝ≥0) + 1)
        (ε := ε / 2) (by positivity) hε2
      simpa using h
    _ = 3 * (2 * ((n : ℝ≥0∞) + 1)) * (ε : ℝ≥0∞)⁻¹ := by
      rw [pow_one, ENNReal.coe_div (by norm_num), div_eq_mul_inv, ENNReal.div_eq_inv_mul,
        ENNReal.mul_inv (by simp) (by simp), inv_inv]
      push_cast
      ring
  mono n m hnm x hx := by
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  subset_iUnion x _ := by
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact mem_iUnion.2 ⟨n, by
      constructor <;> linarith [neg_abs_le x, le_abs_self x]⟩

variable {κ a b : ℝ}

theorem integrable_pow_toConfig_sub (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (s t : ℝ) :
    Integrable (fun ω => (toConfig ω t - toConfig ω s) ^ 4) (pathMeasure κ a b hκ ha hb) := by
  refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun ω => ?_)
  · exact (((continuous_toConfig_apply t).sub (continuous_toConfig_apply s)).pow 4).aestronglyMeasurable
  · have ht := inCube_toConfig ω t
    have hs := inCube_toConfig ω s
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.2 ⟨by linarith [ht.1, hs.2], by linarith [ht.2, hs.1]⟩)

/-- The coordinate process is a Kolmogorov process with exponents `(4, 2)`. -/
theorem isKolmogorovProcess_toConfig (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    ∃ M : ℝ≥0, IsKolmogorovProcess (fun t ω => toConfig ω t) (pathMeasure κ a b hκ ha hb) 4 2 M := by
  obtain ⟨M, hM0, hM⟩ := integral_quartic_le hκ ha hb
  refine ⟨M.toNNReal, ⟨fun s t => ?_, fun s t => ?_, by norm_num, by norm_num⟩⟩
  · rw [← BorelSpace.measurable_eq (α := ℝ × ℝ)]
    exact ((continuous_toConfig_apply s).prodMk (continuous_toConfig_apply t)).measurable
  · have e : ∀ ω : PathSpace, edist (toConfig ω s) (toConfig ω t) ^ (4 : ℝ) =
        ENNReal.ofReal ((toConfig ω t - toConfig ω s) ^ 4) := by
      intro ω
      rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs,
        abs_of_nonneg (by positivity)]
      congr 1
      ring
    simp only [e]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_pow_toConfig_sub hκ ha hb s t)
      (ae_of_all _ fun ω => by positivity)]
    rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hMe : ((M.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal M := rfl
    rw [hMe, ← ENNReal.ofReal_mul hM0]
    refine ENNReal.ofReal_le_ofReal ((hM s t).trans (le_of_eq ?_))
    ring

/-- **A continuous modification of the coordinate process.** -/
theorem exists_continuous_modification (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    ∃ Y : ℝ → PathSpace → ℝ, (∀ t, Measurable (Y t)) ∧
      (∀ t, Y t =ᵐ[pathMeasure κ a b hκ ha hb] fun ω => toConfig ω t) ∧
      ∀ ω, Continuous fun t => Y t ω := by
  obtain ⟨M, hK⟩ := isKolmogorovProcess_toConfig hκ ha hb
  obtain ⟨Y, hYm, hYeq, hYH⟩ := exists_modification_holder_iSup
    (C := fun n : ℕ ↦ Set.Ioo (-((n : ℝ) + 1)) (n + 1)) (p := fun _ => 4) (q := fun _ => 2)
    (M := fun _ => M) (d := 1) isCoverWithBoundedCoveringNumber_Ioo_real
    (fun _ => hK.IsAEKolmogorovProcess) (fun n => by finiteness) one_pos (fun _ => by norm_num)
  refine ⟨Y, hYm, hYeq, fun ω => continuous_iff_continuousAt.2 fun t => ?_⟩
  have hβ : ((1 / 8 : ℝ≥0) : ℝ) < ⨆ _n : ℕ, ((2 : ℝ) - 1) / 4 := by
    rw [ciSup_const]; norm_num
  obtain ⟨U, hU, C, hC⟩ := hYH ω t (1 / 8) (by norm_num) hβ
  exact (hC.continuousOn (by norm_num)).continuousAt hU

variable (κ a b) in
/-- The continuous modification (chosen). -/
def modY (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) : ℝ → PathSpace → ℝ :=
  Classical.choose (exists_continuous_modification hκ ha hb)

variable (κ a b) in
/-- **The stationary Jacobi process**: the continuous modification clamped to `[0, 1]`. -/
def jacU (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) (ω : PathSpace) : ℝ :=
  max 0 (min 1 (modY κ a b hκ ha hb t ω))

theorem jacU_mem_Icc (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) (ω : PathSpace) :
    jacU κ a b hκ ha hb t ω ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem continuous_jacU (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (ω : PathSpace) :
    Continuous fun t => jacU κ a b hκ ha hb t ω :=
  continuous_const.max (continuous_const.min
    ((Classical.choose_spec (exists_continuous_modification hκ ha hb)).2.2 ω))

theorem measurable_jacU (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    Measurable (jacU κ a b hκ ha hb t) :=
  measurable_const.max (measurable_const.min
    ((Classical.choose_spec (exists_continuous_modification hκ ha hb)).1 t))

theorem jacU_ae_eq (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    jacU κ a b hκ ha hb t =ᵐ[pathMeasure κ a b hκ ha hb] fun ω => toConfig ω t := by
  filter_upwards [(Classical.choose_spec (exists_continuous_modification hκ ha hb)).2.1 t]
    with ω hω
  have h := inCube_toConfig ω t
  simp only [jacU, modY]
  rw [hω, min_eq_right h.2, max_eq_right h.1]

end JacobiExists

end Sec2

end InteractingSLE
