import InteractingSLE.Spec.Ito.GenCvQuadratic

/-!
# The Itô–Dynkin engine for a continuous martingale with a general bracket

Packet PROVE-ITO-GEN2 (Theorem 2.6's Itô step, `source/spec/p001-048.md` L977–L986: "The semimartingale
argument in the proof of Theorem 2.4 applies using this one point `z`"). The landed engine
`Ito.integral_mul_sub_eq_zero_of_defectExcess` (`Stochastic/ItoAdapted.lean`) is for a Brownian motion
`B` (bracket `t`). Theorem 2.6 applies Itô's formula to a continuous local martingale `𝔥_t(z)` whose
bracket is the conformal-radius clock, so the engine is restated here for a bounded continuous
martingale `M` with an arbitrary continuous increasing bounded bracket `A` (`M² − A` a martingale):

**`integral_mul_sub_eq_zero_of_defectExcess`.** If `X` is a measurable integrable process and `c₁, c₂`
are adapted coefficients bounded by `C`, and if the excesses of the Itô defects
`X_b − X_a − c₁(a) ΔM − ½ c₂(a) (ΔM² − ΔA)` over `C |ΔM|³` along the uniform grids of `[s, t]` are
uniformly bounded and tend to `0` along every path, then `E[ξ (X_t − X_s)] = 0` for every
`𝓕_s`-measurable `|ξ| ≤ 1`.

The two orthogonality identities are MathFin's (`integral_mul_increment_eq_zero`,
`integral_mul_sq_increment_sub`). The cubic increments vanish in mean by
`Σ |ΔM|³ ≤ max |ΔM| · Σ ΔM² ≤ ½ max² + ½ (Σ ΔM² − ΔA)² + 2L max` and the landed mean-square
convergence of quadratic sums for a general bracket (`GenCont.tendsto_integral_quadError_sq`); no
slow-clock hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open MathFin MathFin.LevyQuadraticSums
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.Gm2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {M A : ℝ≥0 → Ω → ℝ} {K L : ℝ}

/-- The Itô defect of `X` over `[a, b]` against the martingale `M` with bracket `A`, with frozen
coefficients read at `a`: `X_b − X_a − c₁(a) ΔM − ½ c₂(a) (ΔM² − ΔA)`. -/
def itoDefect (X c1 c2 M A : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (ω : Ω) : ℝ :=
  X b ω - X a ω - c1 a ω * (M b ω - M a ω) -
    1 / 2 * c2 a ω * ((M b ω - M a ω) ^ 2 - (A b ω - A a ω))

/-- The excess of the Itô defects over `C |ΔM|³`, summed over the `n`-th uniform grid of `[s, t]`. -/
def defectExcess (X c1 c2 M A : ℝ≥0 → Ω → ℝ) (C : ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ range n, max (|itoDefect X c1 c2 M A (unifPartIcc s t n k) (unifPartIcc s t n (k + 1)) ω| -
    C * |M (unifPartIcc s t n (k + 1)) ω - M (unifPartIcc s t n k) ω| ^ 3) 0

lemma le_unifPartIcc (s t : ℝ≥0) (n k : ℕ) : s ≤ unifPartIcc s t n k := by
  have := unifPartIcc_mono s t n (Nat.zero_le k)
  rwa [unifPartIcc_zero] at this

lemma defectExcess_nonneg (X c1 c2 M A : ℝ≥0 → Ω → ℝ) (C : ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) :
    0 ≤ defectExcess X c1 c2 M A C s t n ω :=
  sum_nonneg fun _ _ => le_max_right _ _

/-- A bounded measurable real function is integrable for a finite measure. -/
lemma integrable_of_abs_le [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hb ω)

/-- The sum of the cubed increments of `M` over the `n`-th uniform grid of `[s, t]`. -/
def cubeSum (M : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ range n, |M (unifPartIcc s t n (k + 1)) ω - M (unifPartIcc s t n k) ω| ^ 3

/-- **Pathwise cubic bound**: `Σ |ΔM|³ ≤ ½ (max |ΔM|)² + ½ (Σ ΔM² − ΔA)² + 2L max |ΔM|`. -/
lemma sum_abs_cube_le (hL : ∀ t ω, |A t ω| ≤ L) (s t : ℝ≥0) (n : ℕ) (ω : Ω) :
    cubeSum M s t n ω ≤
      maxIncr M s t n ω ^ 2 / 2 + GenCont.quadError M A (unifPartIcc s t n) n ω ^ 2 / 2 +
        2 * L * maxIncr M s t n ω := by
  set π := unifPartIcc s t n
  set m := maxIncr M s t n ω with hm
  have hm0 : 0 ≤ m := maxIncr_nonneg s t n ω
  have hcell : ∀ k ∈ range n, |M (π (k + 1)) ω - M (π k) ω| ^ 3 ≤
      m * (M (π (k + 1)) ω - M (π k) ω) ^ 2 := by
    intro k hk
    have h1 : |M (π (k + 1)) ω - M (π k) ω| ≤ m := abs_le_maxIncr s t hk ω
    rw [show |M (π (k + 1)) ω - M (π k) ω| ^ 3 =
        |M (π (k + 1)) ω - M (π k) ω| * (M (π (k + 1)) ω - M (π k) ω) ^ 2 by
      rw [pow_succ', sq_abs]]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have htel : (∑ k ∈ range n, (A (π (k + 1)) ω - A (π k) ω)) = A (π n) ω - A (π 0) ω :=
    sum_range_sub (fun k => A (π k) ω) n
  have hsum : (∑ k ∈ range n, (M (π (k + 1)) ω - M (π k) ω) ^ 2) =
      GenCont.quadError M A π n ω + (A (π n) ω - A (π 0) ω) := by
    simp only [GenCont.quadError, sum_sub_distrib, htel, sub_add_cancel]
  have hA2 : A (π n) ω - A (π 0) ω ≤ 2 * L :=
    (le_abs_self _).trans (abs_sub_le_two_mul hL _ _ ω)
  calc cubeSum M s t n ω
      ≤ ∑ k ∈ range n, m * (M (π (k + 1)) ω - M (π k) ω) ^ 2 := sum_le_sum hcell
    _ = m * GenCont.quadError M A π n ω + m * (A (π n) ω - A (π 0) ω) := by
      rw [← mul_sum, hsum, mul_add]
    _ ≤ _ := by
      nlinarith [sq_nonneg (m - GenCont.quadError M A π n ω), mul_le_mul_of_nonneg_left hA2 hm0]

/-- **The cubic increments vanish in mean** for a bounded continuous martingale with a bounded
continuous increasing bracket, along the uniform grids of `[s, t]`. -/
theorem tendsto_integral_sum_abs_cube [IsProbabilityMeasure P] (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hL : ∀ t ω, |A t ω| ≤ L)
    (hAm : ∀ ω, Monotone (A · ω)) (hMc : ∀ ω, Continuous (M · ω))
    (hAc : ∀ ω, Continuous (A · ω)) (s t : ℝ≥0) :
    Tendsto (fun n => ∫ ω, cubeSum M s t n ω ∂P) atTop (𝓝 0) := by
  have hMm (r : ℝ≥0) : Measurable (M r) := ((hM.stronglyAdapted r).mono (𝓕.le r)).measurable
  have hAmeas (r : ℝ≥0) : Measurable (A r) :=
    ((stronglyAdapted_of_martingale_sq_sub hM hM2 r).mono (𝓕.le r)).measurable
  have hmaxi (n : ℕ) (p : ℕ) : Integrable (fun ω => maxIncr M s t n ω ^ p) P :=
    (memLp_of_abs_le ((measurable_maxIncr hMm s t n).pow_const p).aestronglyMeasurable
      (C := (2 * K) ^ p) (fun ω => by
        rw [abs_pow, abs_of_nonneg (maxIncr_nonneg s t n ω)]
        exact pow_le_pow_left₀ (maxIncr_nonneg s t n ω) (maxIncr_le hK s t n ω) p) 1).integrable
      le_rfl
  have hqi (n : ℕ) : Integrable (fun ω => GenCont.quadError M A (unifPartIcc s t n) n ω ^ 2) P :=
    (memLp_finsetSum _ fun k _ => GenCont.memLp_centred hM hM2 hK hL _ _ 2).integrable_sq
  have hci (n : ℕ) : Integrable (cubeSum M s t n) P :=
    integrable_finsetSum _ fun k _ => (memLp_of_abs_le
      (((hMm _).sub (hMm _)).abs.pow_const 3).aestronglyMeasurable (C := (2 * K) ^ 3)
      (fun ω => by
        rw [abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_two_mul hK _ _ ω) 3) 1).integrable le_rfl
  have hlim : Tendsto (fun n => (∫ ω, maxIncr M s t n ω ^ 2 ∂P) / 2 +
      (∫ ω, GenCont.quadError M A (unifPartIcc s t n) n ω ^ 2 ∂P) / 2 +
        2 * L * ∫ ω, maxIncr M s t n ω ^ 1 ∂P) atTop (𝓝 0) := by
    have h1 := GenCont.tendsto_integral_maxIncr_pow (P := P) hMm hK hMc s t two_ne_zero
    have h2 := GenCont.tendsto_integral_quadError_sq hM hM2 hK hL hAm hMc hAc s t
    have h3 := GenCont.tendsto_integral_maxIncr_pow (P := P) hMm hK hMc s t one_ne_zero
    simpa only [zero_div, add_zero, mul_zero] using ((h1.div_const 2).add (h2.div_const 2)).add
      (h3.const_mul (2 * L))
  refine squeeze_zero (fun n => integral_nonneg fun ω => sum_nonneg fun k _ => by positivity)
    (fun n => ?_) hlim
  have hb1 : Integrable (fun ω => maxIncr M s t n ω ^ 2 / 2 +
      GenCont.quadError M A (unifPartIcc s t n) n ω ^ 2 / 2) P :=
    ((hmaxi n 2).div_const 2).add ((hqi n).div_const 2)
  have hb3 : Integrable (fun ω => 2 * L * maxIncr M s t n ω ^ 1) P := (hmaxi n 1).const_mul (2 * L)
  have hb : Integrable (fun ω => maxIncr M s t n ω ^ 2 / 2 +
      GenCont.quadError M A (unifPartIcc s t n) n ω ^ 2 / 2 + 2 * L * maxIncr M s t n ω ^ 1) P :=
    hb1.add hb3
  refine (integral_mono (hci n) hb fun ω => ?_).trans_eq ?_
  · simpa only [pow_one] using sum_abs_cube_le (M := M) hL s t n ω
  · rw [integral_add hb1 hb3, integral_add ((hmaxi n 2).div_const 2) ((hqi n).div_const 2),
      integral_div, integral_div, integral_const_mul]

/-- **The Itô–Dynkin engine for a martingale with a general bracket.** Let `M` be a bounded continuous
`𝓕`-martingale and `A` a bounded continuous increasing process with `M² − A` a martingale. Let `X` be a
measurable integrable process and `c₁, c₂` adapted coefficients bounded by `C`. If the excesses of the
Itô defects over `C |ΔM|³` along the uniform grids of `[s, t]` are uniformly bounded by `D` and tend to
`0` along every path, then `E[ξ (X_t − X_s)] = 0` for every `𝓕_s`-measurable `|ξ| ≤ 1`. -/
theorem integral_mul_sub_eq_zero_of_defectExcess [IsProbabilityMeasure P] (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hL : ∀ t ω, |A t ω| ≤ L)
    (hAm : ∀ ω, Monotone (A · ω)) (hMc : ∀ ω, Continuous (M · ω))
    (hAc : ∀ ω, Continuous (A · ω))
    {X c1 c2 : ℝ≥0 → Ω → ℝ} {C D : ℝ} {s t : ℝ≥0} (hst : s ≤ t)
    (hXm : ∀ r, Measurable (X r)) (hXi : ∀ r, Integrable (X r) P)
    (hc1 : ∀ r, StronglyMeasurable[𝓕 r] (c1 r)) (hc2 : ∀ r, StronglyMeasurable[𝓕 r] (c2 r))
    (hc1b : ∀ r ω, |c1 r ω| ≤ C) (hc2b : ∀ r ω, |c2 r ω| ≤ C)
    (hdom : ∀ n ω, defectExcess X c1 c2 M A C s t n ω ≤ D)
    (hlim : ∀ ω, Tendsto (fun n => defectExcess X c1 c2 M A C s t n ω) atTop (𝓝 0))
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (X t ω - X s ω) ∂P = 0 := by
  have hMm (r : ℝ≥0) : Measurable (M r) := ((hM.stronglyAdapted r).mono (𝓕.le r)).measurable
  have hAmeas (r : ℝ≥0) : Measurable (A r) :=
    ((stronglyAdapted_of_martingale_sq_sub hM hM2 r).mono (𝓕.le r)).measurable
  have hξm : Measurable ξ := (hξ.mono (𝓕.le s)).measurable
  set g := unifPartIcc s t with hg
  set ρ : ℕ → ℕ → Ω → ℝ := fun n k => itoDefect X c1 c2 M A (g n k) (g n (k + 1)) with hρ
  -- measurability and integrability of the defects
  have hc1m (r : ℝ≥0) : Measurable (c1 r) := ((hc1 r).mono (𝓕.le r)).measurable
  have hc2m (r : ℝ≥0) : Measurable (c2 r) := ((hc2 r).mono (𝓕.le r)).measurable
  have hρm (n k : ℕ) : Measurable (ρ n k) :=
    (((hXm _).sub (hXm _)).sub ((hc1m _).mul ((hMm _).sub (hMm _)))).sub
      ((measurable_const.mul (hc2m _)).mul ((((hMm _).sub (hMm _)).pow_const 2).sub
        ((hAmeas _).sub (hAmeas _))))
  have hρi (n k : ℕ) : Integrable (ρ n k) P := by
    have i1 : Integrable (fun ω => c1 (g n k) ω * (M (g n (k + 1)) ω - M (g n k) ω)) P :=
      integrable_of_abs_le (f := fun ω => c1 (g n k) ω * (M (g n (k + 1)) ω - M (g n k) ω))
        ((hc1m (g n k)).mul ((hMm (g n (k + 1))).sub (hMm (g n k))))
        (C := C * (2 * K)) fun ω => by
          rw [abs_mul]
          exact mul_le_mul (hc1b _ ω) (abs_sub_le_two_mul hK _ _ ω) (abs_nonneg _)
            ((abs_nonneg _).trans (hc1b (g n k) ω))
    have i2 : Integrable (fun ω => 1 / 2 * c2 (g n k) ω *
        ((M (g n (k + 1)) ω - M (g n k) ω) ^ 2 - (A (g n (k + 1)) ω - A (g n k) ω))) P :=
      integrable_of_abs_le (f := fun ω => 1 / 2 * c2 (g n k) ω *
          ((M (g n (k + 1)) ω - M (g n k) ω) ^ 2 - (A (g n (k + 1)) ω - A (g n k) ω)))
        ((measurable_const.mul (hc2m (g n k))).mul
        ((((hMm (g n (k + 1))).sub (hMm (g n k))).pow_const 2).sub
          ((hAmeas (g n (k + 1))).sub (hAmeas (g n k)))))
        (C := 1 / 2 * C * ((2 * K) ^ 2 + 2 * L)) fun ω => by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul (hc2b _ ω) (GenCont.abs_centred_le hK hL _ _ ω) (abs_nonneg _)
            ((abs_nonneg _).trans (hc2b (g n k) ω))
    exact (((hXi _).sub (hXi _)).sub i1).sub i2
  have hξρi (n k : ℕ) : Integrable (fun ω => ξ ω * ρ n k ω) P :=
    (hρi n k).bdd_mul hξm.aestronglyMeasurable (.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hξb ω)
  -- the expectation of a step is that of its defect
  have hstep (n k : ℕ) : ∫ ω, ξ ω * (X (g n (k + 1)) ω - X (g n k) ω) ∂P =
      ∫ ω, ξ ω * ρ n k ω ∂P := by
    have hsa : s ≤ g n k := le_unifPartIcc s t n k
    have hab : g n k ≤ g n (k + 1) := unifPartIcc_mono s t n (Nat.le_succ k)
    have hξa : StronglyMeasurable[𝓕 (g n k)] ξ := hξ.mono (𝓕.mono hsa)
    set a := g n k
    set b := g n (k + 1)
    have hv1 : StronglyMeasurable[𝓕 a] (fun ω => ξ ω * c1 a ω) := hξa.mul (hc1 a)
    have hv2 : StronglyMeasurable[𝓕 a] (fun ω => ξ ω * (1 / 2 * c2 a ω)) :=
      hξa.mul (stronglyMeasurable_const.mul (hc2 a))
    have hv1b (ω : Ω) : |ξ ω * c1 a ω| ≤ C := by
      rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) (hξb ω)).trans (hc1b a ω)
    have hv2b (ω : Ω) : |ξ ω * (1 / 2 * c2 a ω)| ≤ C := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      refine (mul_le_of_le_one_left (by positivity) (hξb ω)).trans ?_
      linarith [hc2b a ω, abs_nonneg (c2 a ω)]
    have hz1 : ∫ ω, ξ ω * c1 a ω * (M b ω - M a ω) ∂P = 0 :=
      integral_mul_increment_eq_zero hM hab hv1 hv1b
    have hz2 : ∫ ω, ξ ω * (1 / 2 * c2 a ω) * ((M b ω - M a ω) ^ 2 - (A b ω - A a ω)) ∂P = 0 :=
      integral_mul_sq_increment_sub hM hM2 hK hab hv2 hv2b
    have hi1 : Integrable (fun ω => ξ ω * c1 a ω * (M b ω - M a ω)) P :=
      ((hM.integrable b).sub (hM.integrable a)).bdd_mul
        ((hv1.mono (𝓕.le a)).aestronglyMeasurable) (.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact hv1b ω)
    have hi2 : Integrable (fun ω => ξ ω * (1 / 2 * c2 a ω) *
        ((M b ω - M a ω) ^ 2 - (A b ω - A a ω))) P :=
      (GenCont.memLp_centred hM hM2 hK hL a b 1 |>.integrable le_rfl).bdd_mul
        ((hv2.mono (𝓕.le a)).aestronglyMeasurable) (.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact hv2b ω)
    have hi12 : Integrable (fun ω => ξ ω * c1 a ω * (M b ω - M a ω) +
        ξ ω * (1 / 2 * c2 a ω) * ((M b ω - M a ω) ^ 2 - (A b ω - A a ω))) P := hi1.add hi2
    have hsplit : (fun ω => ξ ω * (X b ω - X a ω)) = fun ω => ξ ω * ρ n k ω +
        (ξ ω * c1 a ω * (M b ω - M a ω) +
          ξ ω * (1 / 2 * c2 a ω) * ((M b ω - M a ω) ^ 2 - (A b ω - A a ω))) := by
      funext ω; simp only [hρ, itoDefect, a, b]; ring
    rw [hsplit, integral_add (hξρi n k) hi12, integral_add hi1 hi2, hz1, hz2, add_zero, add_zero]
  -- the total expectation is the sum of the defect expectations
  have hsum (n : ℕ) (hn : n ≠ 0) :
      ∫ ω, ξ ω * (X t ω - X s ω) ∂P = ∑ k ∈ range n, ∫ ω, ξ ω * ρ n k ω ∂P := by
    have htel : (fun ω => ξ ω * (X t ω - X s ω)) =
        fun ω => ∑ k ∈ range n, ξ ω * (X (g n (k + 1)) ω - X (g n k) ω) := by
      funext ω
      have h : (∑ k ∈ range n, (X (g n (k + 1)) ω - X (g n k) ω)) = X (g n n) ω - X (g n 0) ω :=
        sum_range_sub (fun k => X (g n k) ω) n
      rw [← mul_sum, h, hg, unifPartIcc_self hst hn, unifPartIcc_zero]
    have hi (k : ℕ) : Integrable (fun ω => ξ ω * (X (g n (k + 1)) ω - X (g n k) ω)) P :=
      ((hXi _).sub (hXi _)).bdd_mul hξm.aestronglyMeasurable
        (.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
    rw [htel, integral_finsetSum _ fun k _ => hi k]
    exact sum_congr rfl fun k _ => hstep n k
  -- the bound by the cubic sums and the excesses
  have hTi (n : ℕ) : Integrable (cubeSum M s t n) P :=
    integrable_finsetSum _ fun k _ => integrable_of_abs_le
      (f := fun ω => |M (g n (k + 1)) ω - M (g n k) ω| ^ 3)
      (((hMm _).sub (hMm _)).abs.pow_const 3) (C := (2 * K) ^ 3) fun ω => by
        rw [abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_two_mul hK _ _ ω) 3
  have hDm (n : ℕ) : Measurable (defectExcess X c1 c2 M A C s t n) :=
    Finset.measurable_sum _ fun k _ =>
      ((hρm n k).abs.sub (measurable_const.mul (((hMm _).sub (hMm _)).abs.pow_const 3))).max
        measurable_const
  have hD0 (n : ℕ) (ω : Ω) : 0 ≤ defectExcess X c1 c2 M A C s t n ω :=
    defectExcess_nonneg X c1 c2 M A C s t n ω
  have hDi (n : ℕ) : Integrable (defectExcess X c1 c2 M A C s t n) P :=
    integrable_of_abs_le (hDm n) (C := D) fun ω => by
      rw [abs_of_nonneg (hD0 n ω)]; exact hdom n ω
  have hbound (n : ℕ) (hn : n ≠ 0) :
      |∫ ω, ξ ω * (X t ω - X s ω) ∂P| ≤ C * (∫ ω, cubeSum M s t n ω ∂P) +
        ∫ ω, defectExcess X c1 c2 M A C s t n ω ∂P := by
    rw [hsum n hn]
    have hpt (ω : Ω) : (∑ k ∈ range n, |ξ ω * ρ n k ω|) ≤
        C * cubeSum M s t n ω + defectExcess X c1 c2 M A C s t n ω := by
      unfold cubeSum defectExcess
      rw [mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun k _ => ?_
      have h1 : |ξ ω * ρ n k ω| ≤ |ρ n k ω| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (hξb ω)
      have h2 := le_max_left (|ρ n k ω| -
        C * |M (g n (k + 1)) ω - M (g n k) ω| ^ 3) 0
      simp only [hρ] at h1 h2
      linarith
    calc |∑ k ∈ range n, ∫ ω, ξ ω * ρ n k ω ∂P|
        ≤ ∑ k ∈ range n, |∫ ω, ξ ω * ρ n k ω ∂P| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range n, ∫ ω, |ξ ω * ρ n k ω| ∂P := sum_le_sum fun k _ => by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => ξ ω * ρ n k ω)
      _ = ∫ ω, ∑ k ∈ range n, |ξ ω * ρ n k ω| ∂P :=
          (integral_finsetSum _ fun k _ => (hξρi n k).abs).symm
      _ ≤ ∫ ω, (C * cubeSum M s t n ω + defectExcess X c1 c2 M A C s t n ω) ∂P :=
          integral_mono (integrable_finsetSum _ fun k _ => (hξρi n k).abs)
            (((hTi n).const_mul C).add (hDi n)) hpt
      _ = C * (∫ ω, cubeSum M s t n ω ∂P) + ∫ ω, defectExcess X c1 c2 M A C s t n ω ∂P := by
          rw [integral_add ((hTi n).const_mul C) (hDi n), integral_const_mul]
  -- both bounds vanish
  have hT0 : Tendsto (fun n => ∫ ω, cubeSum M s t n ω ∂P) atTop (𝓝 0) :=
    tendsto_integral_sum_abs_cube hM hM2 hK hL hAm hMc hAc s t
  have hD0' : Tendsto (fun n => ∫ ω, defectExcess X c1 c2 M A C s t n ω ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun _ : Ω => D)
      (fun n => (hDm n).aestronglyMeasurable) (integrable_const (μ := P) D)
      (fun n => .of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hD0 n ω)]; exact hdom n ω)
      (.of_forall hlim)
    simpa only [integral_zero] using this
  have hlim' : Tendsto (fun n => C * (∫ ω, cubeSum M s t n ω ∂P) +
      ∫ ω, defectExcess X c1 c2 M A C s t n ω ∂P) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hT0.const_mul C).add hD0'
  have habs : |∫ ω, ξ ω * (X t ω - X s ω) ∂P| ≤ 0 :=
    ge_of_tendsto hlim' (eventually_atTop.2 ⟨1, fun n hn => hbound n (by omega)⟩)
  exact abs_nonpos_iff.1 habs

end InteractingSLE.Ito.Gm2
