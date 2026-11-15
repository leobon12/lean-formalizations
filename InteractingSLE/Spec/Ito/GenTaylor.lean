import QuantumZipper.Proofs.ItoLite.Dynkin
import MathFin.Probability.Martingales.LevyQuadraticSums

/-!
# Taylor sums for a continuous martingale with a prescribed bracket

The finite-partition part of the martingale-problem proof of Itô's formula.
`M` and `M² − A` are martingales; no Brownian representation of `M` is assumed.
The bracket terms are left-point Riemann–Stieltjes sums. This module does not
identify their limit with a Stieltjes integral.

The deterministic Taylor estimate is reused from `QuantumZipper.Dynkin`,
and the conditional second-moment identity and cubic-increment convergence
are reused from `MathFin.LevyQuadraticSums`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.Gen

/-- The first derivative of a real function, evaluated on the unit vector. -/
def first (f : ℝ → ℝ) (x : ℝ) : ℝ := fderiv ℝ f x 1

/-- The second derivative of a real function, evaluated on two unit vectors. -/
def second (f : ℝ → ℝ) (x : ℝ) : ℝ := fderiv ℝ (fderiv ℝ f) x 1 1

@[simp] lemma first_eq_deriv (f : ℝ → ℝ) (x : ℝ) : first f x = deriv f x := rfl

lemma second_eq_deriv_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    second f x = deriv (deriv f) x := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (show ContDiff ℝ 1 (fderiv ℝ f) from hf.fderiv_right (by norm_num)).differentiable
      (by norm_num)
  have he : (fun y => fderiv ℝ f y 1) = deriv f := funext fun _ => rfl
  have h := ((hd x).hasDerivAt.clm_apply (hasDerivAt_const x (1 : ℝ))).deriv.symm
  rw [he] at h
  simpa only [map_zero, add_zero, second, deriv] using h

lemma first_apply (f : ℝ → ℝ) (x v : ℝ) :
    fderiv ℝ f x v = first f x * v :=
  fderiv_eq_deriv_mul

lemma second_apply (f : ℝ → ℝ) (x v : ℝ) :
    fderiv ℝ (fderiv ℝ f) x v v = second f x * v ^ 2 := by
  have h : fderiv ℝ (fderiv ℝ f) x v = v • fderiv ℝ (fderiv ℝ f) x 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (fderiv ℝ (fderiv ℝ f) x).map_smul v (1 : ℝ)
  have h' : fderiv ℝ (fderiv ℝ f) x 1 v = v * second f x := by
    simpa only [smul_eq_mul, mul_one, second] using
      (fderiv ℝ (fderiv ℝ f) x 1).map_smul v (1 : ℝ)
  rw [h, smul_apply, smul_eq_mul, h']
  ring

/-- The second-order Taylor remainder for a scalar increment. -/
def remainder (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  f y - f x - first f x * (y - x) - (1 / 2) * second f x * (y - x) ^ 2

lemma abs_remainder_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ C * ‖x - y‖)
    (x y : ℝ) : |remainder f x y| ≤ C * |y - x| ^ 3 := by
  have h := QuantumZipper.Dynkin.taylor2_bound hf hC hLip x (y - x)
  rw [add_sub_cancel, QuantumZipper.Dynkin.iteratedFDeriv_two_vec,
    first_apply, second_apply, Real.norm_eq_abs] at h
  simpa only [remainder, mul_assoc] using h

lemma continuous_first {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) : Continuous (first f) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma continuous_second {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) : Continuous (second f) :=
  (((hf.fderiv_right (show 2 + 1 ≤ (3 : WithTop ℕ∞) by norm_num)).continuous_fderiv
    (by norm_num)).clm_apply continuous_const).clm_apply continuous_const

lemma abs_first_le {f : ℝ → ℝ} {C : ℝ} (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (x : ℝ) :
    |first f x| ≤ C := by
  simpa only [first, Real.norm_eq_abs, norm_one, mul_one] using
    ((fderiv ℝ f x).le_opNorm (1 : ℝ)).trans (by simpa using hD x)

lemma abs_second_le {f : ℝ → ℝ} {C : ℝ}
    (hD : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C) (x : ℝ) : |second f x| ≤ C := by
  have h₁ := (fderiv ℝ (fderiv ℝ f) x 1).le_opNorm (1 : ℝ)
  have h₂ := (fderiv ℝ (fderiv ℝ f) x).le_opNorm (1 : ℝ)
  simp only [norm_one, mul_one] at h₁ h₂
  exact h₁.trans (h₂.trans (hD x))

lemma continuous_remainder {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) :
    Continuous (fun p : ℝ × ℝ => remainder f p.1 p.2) :=
  ((hf.continuous.comp continuous_snd).sub (hf.continuous.comp continuous_fst)).sub
    (((continuous_first hf).comp continuous_fst).mul (continuous_snd.sub continuous_fst)) |>.sub
      ((continuous_const.mul ((continuous_second hf).comp continuous_fst)).mul
        ((continuous_snd.sub continuous_fst).pow 2))

section Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ} {K : ℝ}

/-- A left-point sum for the half-bracket term in scalar Itô's formula. -/
def bracketSum (f : ℝ → ℝ) (M A : ℝ≥0 → Ω → ℝ) (π : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  (1 / 2) * ∑ k ∈ Finset.range n,
    second f (M (π k) ω) * (A (π (k + 1)) ω - A (π k) ω)

lemma integrable_clock (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (t : ℝ≥0) : Integrable (A t) P := by
  have hiM2 : Integrable (fun ω => M t ω ^ 2) P :=
    (MathFin.LevyQuadraticSums.memLp_of_abs_le
      ((hM.stronglyAdapted t).mono (𝓕.le t)).aestronglyMeasurable
      (hK t) 2).integrable_sq
  exact (hiM2.sub (hM2.integrable t)).congr (.of_forall fun ω => by dsimp; ring)

lemma integrable_compensated_increment (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {C : ℝ}
    (hF : ∀ x, |f x| ≤ C) (hD2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C)
    (a b : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    Integrable (fun ω => ξ ω * (f (M b ω) - f (M a ω) -
      (1 / 2) * second f (M a ω) * (A b ω - A a ω))) P := by
  have hMa (t : ℝ≥0) := (hM.stronglyAdapted t).mono (𝓕.le t)
  have hiF (t : ℝ≥0) : Integrable (fun ω => f (M t ω)) P :=
    (MathFin.LevyQuadraticSums.memLp_of_abs_le
      (hf.continuous.stronglyMeasurable.comp_measurable (hMa t).measurable).aestronglyMeasurable
      (fun ω => hF (M t ω)) 1).integrable le_rfl
  have hiQuad := ((integrable_clock hM hM2 hK b).sub (integrable_clock hM hM2 hK a)).bdd_mul
    ((continuous_second hf).stronglyMeasurable.comp_measurable
      (hMa a).measurable).aestronglyMeasurable
    (.of_forall fun ω => abs_second_le hD2 (M a ω))
  exact (((hiF b).sub (hiF a)).sub (hiQuad.const_mul (1 / 2))).bdd_mul
    hξ.aestronglyMeasurable (.of_forall hξb) |>.congr
      (.of_forall fun ω => by dsimp; ring)

/-- Orthogonality removes the first two Taylor terms on a single cell. The
clock `A` need not be absolutely continuous or Lipschitz in this identity. -/
theorem integral_compensated_increment_eq (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {C : ℝ}
    (hF : ∀ x, |f x| ≤ C) (hD1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hD2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C)
    {a b : ℝ≥0} (hab : a ≤ b) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[𝓕 a] ξ)
    (hξb : ∀ ω, |ξ ω| ≤ 1) :
    (∫ ω, ξ ω * (f (M b ω) - f (M a ω) -
      (1 / 2) * second f (M a ω) * (A b ω - A a ω)) ∂P) =
      ∫ ω, ξ ω * remainder f (M a ω) (M b ω) ∂P := by
  have hMa (t : ℝ≥0) : StronglyMeasurable (M t) :=
    (hM.stronglyAdapted t).mono (𝓕.le t)
  have hξm := (hξ.mono (𝓕.le a)).aestronglyMeasurable (μ := P)
  have hfirst : StronglyMeasurable[𝓕 a] (fun ω => ξ ω * first f (M a ω)) :=
    hξ.mul ((continuous_first hf).stronglyMeasurable.comp_measurable
      (hM.stronglyAdapted a).measurable)
  have hsecond : StronglyMeasurable[𝓕 a] (fun ω => ξ ω * second f (M a ω)) :=
    hξ.mul ((continuous_second hf).stronglyMeasurable.comp_measurable
      (hM.stronglyAdapted a).measurable)
  have hb1 (ω : Ω) : |ξ ω * first f (M a ω)| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hξb ω) (abs_nonneg _)).trans
      (by simpa only [one_mul] using abs_first_le hD1 (M a ω))
  have hb2 (ω : Ω) : |ξ ω * second f (M a ω)| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hξb ω) (abs_nonneg _)).trans
      (by simpa only [one_mul] using abs_second_le hD2 (M a ω))
  have hiF (t : ℝ≥0) : Integrable (fun ω => f (M t ω)) P :=
    (MathFin.LevyQuadraticSums.memLp_of_abs_le
      (hf.continuous.stronglyMeasurable.comp_measurable (hMa t).measurable).aestronglyMeasurable
      (fun ω => hF (M t ω)) 1).integrable le_rfl
  have hiA := integrable_clock hM hM2 hK
  have hiSq : Integrable (fun ω => (M b ω - M a ω) ^ 2) P :=
    (MathFin.LevyQuadraticSums.memLp_of_abs_le
      ((hMa b).sub (hMa a)).aestronglyMeasurable
      (MathFin.LevyQuadraticSums.abs_sub_le_two_mul hK a b) 2).integrable_sq
  have hi1 : Integrable (fun ω => (ξ ω * first f (M a ω)) * (M b ω - M a ω)) P :=
    ((hM.integrable b).sub (hM.integrable a)).bdd_mul
      (hfirst.mono (𝓕.le a)).aestronglyMeasurable (.of_forall hb1)
  have hi2 : Integrable (fun ω => (ξ ω * second f (M a ω)) *
      ((M b ω - M a ω) ^ 2 - (A b ω - A a ω))) P :=
    (hiSq.sub ((hiA b).sub (hiA a))).bdd_mul
      (hsecond.mono (𝓕.le a)).aestronglyMeasurable (.of_forall hb2)
  have hiR : Integrable (fun ω => ξ ω * remainder f (M a ω) (M b ω)) P := by
    have hiLin : Integrable (fun ω => first f (M a ω) * (M b ω - M a ω)) P :=
      ((hM.integrable b).sub (hM.integrable a)).bdd_mul
        ((continuous_first hf).stronglyMeasurable.comp_measurable
          (hMa a).measurable).aestronglyMeasurable
        (.of_forall fun ω => abs_first_le hD1 (M a ω))
    have hiQuad : Integrable (fun ω => second f (M a ω) * (M b ω - M a ω) ^ 2) P :=
      hiSq.bdd_mul ((continuous_second hf).stronglyMeasurable.comp_measurable
        (hMa a).measurable).aestronglyMeasurable
        (.of_forall fun ω => abs_second_le hD2 (M a ω))
    exact (((hiF b).sub (hiF a)).sub hiLin |>.sub (hiQuad.const_mul (1 / 2))).bdd_mul
      hξm (.of_forall hξb) |>.congr (.of_forall fun ω => by dsimp [remainder]; ring)
  have hz1 := MathFin.LevyQuadraticSums.integral_mul_increment_eq_zero hM hab hfirst hb1
  have hz2 := MathFin.LevyQuadraticSums.integral_mul_sq_increment_sub hM hM2 hK hab hsecond hb2
  calc
    (∫ ω, ξ ω * (f (M b ω) - f (M a ω) -
        (1 / 2) * second f (M a ω) * (A b ω - A a ω)) ∂P) =
        ∫ ω, (ξ ω * remainder f (M a ω) (M b ω) +
          (ξ ω * first f (M a ω)) * (M b ω - M a ω) +
          (1 / 2) * ((ξ ω * second f (M a ω)) *
            ((M b ω - M a ω) ^ 2 - (A b ω - A a ω)))) ∂P :=
      integral_congr_ae (.of_forall fun ω => by dsimp [remainder]; ring)
    _ = _ := by
      have hsum := integral_add (hiR.add hi1) (hi2.const_mul (1 / 2))
      have hsum' := integral_add hiR hi1
      simp only [Pi.add_apply] at hsum hsum'
      rw [hsum, hsum', integral_const_mul, hz1, hz2, add_zero, mul_zero, add_zero]

/-- The expected compensated increment is bounded by the cubic Taylor error. -/
theorem abs_integral_compensated_increment_le (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x, |f x| ≤ C) (hD1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hD2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C)
    (hLip : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ C * ‖x - y‖)
    {a b : ℝ≥0} (hab : a ≤ b) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[𝓕 a] ξ)
    (hξb : ∀ ω, |ξ ω| ≤ 1) :
    |∫ ω, ξ ω * (f (M b ω) - f (M a ω) -
      (1 / 2) * second f (M a ω) * (A b ω - A a ω)) ∂P| ≤
        C * ∫ ω, |M b ω - M a ω| ^ 3 ∂P := by
  have hMa (t : ℝ≥0) := (hM.stronglyAdapted t).mono (𝓕.le t)
  have hiCube : Integrable (fun ω => |M b ω - M a ω| ^ 3) P :=
    (MathFin.LevyQuadraticSums.memLp_of_abs_le
      (((hMa b).sub (hMa a)).norm.pow 3).aestronglyMeasurable
      (C := (2 * K) ^ 3) (fun ω => by
        change |(|M b ω - M a ω| ^ 3)| ≤ (2 * K) ^ 3
        rw [abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (MathFin.LevyQuadraticSums.abs_sub_le_two_mul hK a b ω) 3) 1).integrable le_rfl
  have hb (ω : Ω) : |ξ ω * remainder f (M a ω) (M b ω)| ≤ C * |M b ω - M a ω| ^ 3 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hξb ω) (abs_nonneg _)).trans
      (by simpa only [one_mul] using abs_remainder_le hf hC hLip (M a ω) (M b ω))
  have hRm : AEStronglyMeasurable (fun ω => ξ ω * remainder f (M a ω) (M b ω)) P :=
    ((hξ.mono (𝓕.le a)).mul ((continuous_remainder hf).stronglyMeasurable.comp_measurable
      ((hMa a).measurable.prodMk (hMa b).measurable))).aestronglyMeasurable
  have hiR : Integrable (fun ω => ξ ω * remainder f (M a ω) (M b ω)) P :=
    (hiCube.const_mul C).mono' hRm (.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hb ω)
  rw [integral_compensated_increment_eq hM hM2 hK hf hF hD1 hD2 hab hξ hξb,
    ← integral_const_mul]
  exact (abs_integral_le_integral_abs).trans (integral_mono hiR.abs (hiCube.const_mul C) hb)

/-- The finite-partition Itô estimate, tested against a bounded past variable.
This still allows an arbitrary clock `A`. -/
theorem abs_integral_compensated_sum_le (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x, |f x| ≤ C) (hD1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hD2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C)
    (hLip : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ C * ‖x - y‖)
    {π : ℕ → ℝ≥0} (hπ : Monotone π) (n : ℕ) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[𝓕 (π 0)] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    |∫ ω, ξ ω * (f (M (π n) ω) - f (M (π 0) ω) - bracketSum f M A π n ω) ∂P| ≤
      C * ∑ k ∈ Finset.range n, ∫ ω, |M (π (k + 1)) ω - M (π k) ω| ^ 3 ∂P := by
  have heq (ω : Ω) : ξ ω * (f (M (π n) ω) - f (M (π 0) ω) - bracketSum f M A π n ω) =
      ∑ k ∈ Finset.range n, ξ ω * (f (M (π (k + 1)) ω) - f (M (π k) ω) -
        (1 / 2) * second f (M (π k) ω) * (A (π (k + 1)) ω - A (π k) ω)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => f (M (π k) ω))]
    simp only [bracketSum, mul_assoc, Finset.mul_sum]
  rw [integral_congr_ae (.of_forall heq), integral_finsetSum _ (fun k _ =>
    integrable_compensated_increment hM hM2 hK hf hF hD2 _ _
      (hξ.mono (𝓕.le (π 0))) hξb), Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
    abs_integral_compensated_increment_le hM hM2 hK hf hC hF hD1 hD2 hLip
      (hπ (Nat.le_succ k)) (hξ.mono (𝓕.mono (hπ (Nat.zero_le k)))) hξb)

/-- For a slow bracket, the expected compensated Taylor sum tends to zero.
The cubic-increment convergence is an existing result of the vendored port. -/
theorem tendsto_integral_compensated_sum (hA : MathFin.LevyQuadraticSums.IsSlowClock A)
    (hM : Martingale M 𝓕 P) (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hcont : ∀ ω, Continuous (M · ω))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x, |f x| ≤ C) (hD1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hD2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C)
    (hLip : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ C * ‖x - y‖)
    {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[𝓕 s] ξ)
    (hξb : ∀ ω, |ξ ω| ≤ 1) :
    Tendsto (fun n : ℕ => ∫ ω, ξ ω * (f (M t ω) - f (M s ω) -
      bracketSum f M A (MathFin.unifPartIcc s t n) n ω) ∂P) atTop (𝓝 0) := by
  have hlim := (MathFin.LevyQuadraticSums.tendsto_sum_integral_abs_cube
    hA hM hK hcont hst hM2).const_mul C
  rw [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hb := abs_integral_compensated_sum_le hM hM2 hK hf hC hF hD1 hD2 hLip
    (MathFin.unifPartIcc_mono s t n) n
    (by rw [MathFin.unifPartIcc_zero]; exact hξ) hξb
  simpa only [Real.norm_eq_abs, MathFin.unifPartIcc_self hst hn,
    MathFin.unifPartIcc_zero] using hb

end Martingale

end InteractingSLE.Ito.Gen
