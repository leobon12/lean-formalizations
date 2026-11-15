import InteractingSLE.Spec.Ito.GenTaylor

/-!
# Quadratic sums for bounded continuous martingales with general bounded brackets

This extends the estimates of `MathFin.LevyQuadraticSums` beyond slow clocks.
The martingale orthogonality identities are reused directly. The new estimates
use the largest bracket increment in place of the largest deterministic time step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open MathFin MathFin.LevyQuadraticSums
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.GenCont

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ} {K L : ℝ}

lemma abs_centred_le (hM : ∀ t ω, |M t ω| ≤ K) (hA : ∀ t ω, |A t ω| ≤ L)
    (a b : ℝ≥0) (ω : Ω) :
    |(M b ω - M a ω) ^ 2 - (A b ω - A a ω)| ≤ (2 * K) ^ 2 + 2 * L :=
  (abs_sq_sub_le (abs_sub_le_two_mul hM a b ω)).trans
    (add_le_add le_rfl (abs_sub_le_two_mul hA a b ω))

lemma memLp_centred (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hL : ∀ t ω, |A t ω| ≤ L)
    (a b : ℝ≥0) (p : ℝ≥0∞) :
    MemLp (fun ω => (M b ω - M a ω) ^ 2 - (A b ω - A a ω)) p P :=
  memLp_of_abs_le (((((hM.stronglyAdapted b).mono (𝓕.le b)).sub
    ((hM.stronglyAdapted a).mono (𝓕.le a))).pow 2).sub
    (((stronglyAdapted_of_martingale_sq_sub hM hM2 b).mono (𝓕.le b)).sub
    ((stronglyAdapted_of_martingale_sq_sub hM hM2 a).mono (𝓕.le a)))).aestronglyMeasurable
    (abs_centred_le hK hL a b) p

/-- Orthogonality of centered squared increments for a bounded bracket.
The bracket need not be Lipschitz, or even continuous, for this identity. -/
theorem integral_sq_sum_centred (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hL : ∀ t ω, |A t ω| ≤ L)
    {π : ℕ → ℝ≥0} (hπ : Monotone π) (n : ℕ) :
    (∫ ω, (∑ k ∈ range n, ((M (π (k + 1)) ω - M (π k) ω) ^ 2 -
      (A (π (k + 1)) ω - A (π k) ω))) ^ 2 ∂P) =
      ∑ k ∈ range n, ∫ ω, ((M (π (k + 1)) ω - M (π k) ω) ^ 2 -
        (A (π (k + 1)) ω - A (π k) ω)) ^ 2 ∂P := by
  let Y : ℕ → Ω → ℝ := fun k ω => (M (π (k + 1)) ω - M (π k) ω) ^ 2 -
    (A (π (k + 1)) ω - A (π k) ω)
  have hAm := stronglyAdapted_of_martingale_sq_sub hM hM2
  have hY (k : ℕ) : MemLp (Y k) 2 P := memLp_centred hM hM2 hK hL _ _ 2
  have hi (k l : ℕ) : Integrable (fun ω => Y k ω * Y l ω) P :=
    (hY k).integrable_mul (hY l)
  have hz (k l : ℕ) (hlk : l < k) : (∫ ω, Y l ω * Y k ω ∂P) = 0 := by
    have h₁ : π (l + 1) ≤ π k := hπ hlk
    have h₀ : π l ≤ π k := (hπ (Nat.le_succ l)).trans h₁
    exact integral_mul_sq_increment_sub hM hM2 hK (hπ (Nat.le_succ k))
      (((((hM.stronglyAdapted _).mono (𝓕.mono h₁)).sub
        ((hM.stronglyAdapted _).mono (𝓕.mono h₀))).pow 2).sub
        (((hAm _).mono (𝓕.mono h₁)).sub ((hAm _).mono (𝓕.mono h₀))))
      (abs_centred_le hK hL _ _)
  change (∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂P) = _
  calc
    (∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂P) =
        ∫ ω, ∑ k ∈ range n, ∑ l ∈ range n, Y k ω * Y l ω ∂P := by
      simp_rw [sq, sum_mul_sum]
    _ = ∑ k ∈ range n, ∑ l ∈ range n, ∫ ω, Y k ω * Y l ω ∂P := by
      rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hi k l]
      exact sum_congr rfl fun k _ => integral_finsetSum _ fun l _ => hi k l
    _ = ∑ k ∈ range n, ∫ ω, Y k ω ^ 2 ∂P := by
      refine sum_congr rfl fun k hk => ?_
      rw [sum_eq_single k (fun l _ hlk => ?_) (fun h => (h hk).elim)]
      · simp only [sq]
      · rcases lt_or_gt_of_ne hlk with hlt | hgt
        · exact (integral_congr_ae (.of_forall fun ω => mul_comm _ _)).trans (hz k l hlt)
        · exact hz l k hgt

/-- The centered quadratic sum over a deterministic partition. -/
def quadError (M A : ℝ≥0 → Ω → ℝ) (π : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ range n, ((M (π (k + 1)) ω - M (π k) ω) ^ 2 -
    (A (π (k + 1)) ω - A (π k) ω))

/-- A bounded-bracket estimate using random bounds for the increments of both
the martingale and the bracket. There is no time-step bound. -/
theorem integral_quadError_sq_le (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hL : ∀ t ω, |A t ω| ≤ L)
    (hAm : ∀ ω, Monotone (A · ω)) {π : ℕ → ℝ≥0} (hπ : Monotone π) (n : ℕ)
    {δ ε : Ω → ℝ} (hδm : Measurable δ) (hεm : Measurable ε)
    (hδ0 : ∀ ω, 0 ≤ δ ω) (hδb : ∀ ω, δ ω ≤ 2 * K)
    (hε0 : ∀ ω, 0 ≤ ε ω) (hεb : ∀ ω, ε ω ≤ 2 * L)
    (hδ : ∀ ω, ∀ k ∈ range n, |M (π (k + 1)) ω - M (π k) ω| ≤ δ ω)
    (hε : ∀ ω, ∀ k ∈ range n, |A (π (k + 1)) ω - A (π k) ω| ≤ ε ω) :
    (∫ ω, quadError M A π n ω ^ 2 ∂P) ≤
      4 * (∫ ω, δ ω ^ 4 ∂P) + 8 * L * (∫ ω, δ ω ^ 2 ∂P) +
        8 * L * ∫ ω, ε ω ∂P := by
  let Y : ℕ → Ω → ℝ := fun k ω => (M (π (k + 1)) ω - M (π k) ω) ^ 2 -
    (A (π (k + 1)) ω - A (π k) ω)
  have hY (k : ℕ) : MemLp (Y k) 2 P := memLp_centred hM hM2 hK hL _ _ 2
  have hiS : Integrable (fun ω => (∑ k ∈ range n, Y k ω) ^ 2) P :=
    (memLp_finsetSum _ fun k _ => hY k).integrable_sq
  have hiδ (p : ℕ) : Integrable (fun ω => δ ω ^ p) P :=
    (memLp_of_abs_le (hδm.pow_const p).aestronglyMeasurable
      (C := (2 * K) ^ p) (fun ω => by
        rw [abs_pow, abs_of_nonneg (hδ0 ω)]
        exact pow_le_pow_left₀ (hδ0 ω) (hδb ω) p) 1).integrable le_rfl
  have hiε : Integrable ε P := (memLp_of_abs_le hεm.aestronglyMeasurable
    (fun ω => by rw [abs_of_nonneg (hε0 ω)]; exact hεb ω) 1).integrable le_rfl
  have htel (ω : Ω) : (∑ k ∈ range n, (A (π (k + 1)) ω - A (π k) ω)) =
      A (π n) ω - A (π 0) ω := sum_range_sub (fun k => A (π k) ω) n
  have hAb (ω : Ω) : A (π n) ω - A (π 0) ω ≤ 2 * L :=
    (le_abs_self _).trans (abs_sub_le_two_mul hL _ _ ω)
  have hpt (ω : Ω) : (∑ k ∈ range n, Y k ω ^ 2) ≤
      2 * δ ω ^ 4 + (∑ k ∈ range n, Y k ω) ^ 2 / 2 +
        4 * L * δ ω ^ 2 + 4 * L * ε ω := by
    have hcell (k : ℕ) (hk : k ∈ range n) : Y k ω ^ 2 ≤
        2 * δ ω ^ 2 * (M (π (k + 1)) ω - M (π k) ω) ^ 2 +
          2 * ε ω * (A (π (k + 1)) ω - A (π k) ω) := by
      have ha0 := sub_nonneg.2 (hAm ω (hπ (Nat.le_succ k)))
      have haε := (le_abs_self (A (π (k + 1)) ω - A (π k) ω)).trans (hε ω k hk)
      have hx : (M (π (k + 1)) ω - M (π k) ω) ^ 2 ≤ δ ω ^ 2 :=
        sq_le_sq' (abs_le.1 (hδ ω k hk)).1 (abs_le.1 (hδ ω k hk)).2
      dsimp only [Y]
      nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg (M (π (k + 1)) ω - M (π k) ω)),
        mul_le_mul_of_nonneg_right haε ha0,
        sq_nonneg ((M (π (k + 1)) ω - M (π k) ω) ^ 2 +
          (A (π (k + 1)) ω - A (π k) ω))]
    have hsum : (∑ k ∈ range n, (M (π (k + 1)) ω - M (π k) ω) ^ 2) =
        (∑ k ∈ range n, Y k ω) + (A (π n) ω - A (π 0) ω) := by
      simp only [Y, sum_sub_distrib, htel, sub_add_cancel]
    calc
      (∑ k ∈ range n, Y k ω ^ 2) ≤ ∑ k ∈ range n,
          (2 * δ ω ^ 2 * (M (π (k + 1)) ω - M (π k) ω) ^ 2 +
            2 * ε ω * (A (π (k + 1)) ω - A (π k) ω)) := sum_le_sum hcell
      _ = 2 * δ ω ^ 2 * ((∑ k ∈ range n, Y k ω) + (A (π n) ω - A (π 0) ω)) +
          2 * ε ω * (A (π n) ω - A (π 0) ω) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, hsum, htel]
      _ ≤ _ := by
        nlinarith [sq_nonneg (2 * δ ω ^ 2 - ∑ k ∈ range n, Y k ω),
          mul_le_mul_of_nonneg_right (hAb ω) (sq_nonneg (δ ω)),
          mul_le_mul_of_nonneg_right (hAb ω) (hε0 ω)]
  have i₁ : Integrable (fun ω => 2 * δ ω ^ 4 + (∑ k ∈ range n, Y k ω) ^ 2 / 2) P :=
    ((hiδ 4).const_mul 2).add (hiS.div_const 2)
  have i₂ : Integrable (fun ω => 2 * δ ω ^ 4 + (∑ k ∈ range n, Y k ω) ^ 2 / 2 +
      4 * L * δ ω ^ 2) P := i₁.add ((hiδ 2).const_mul (4 * L))
  have i₃ : Integrable (fun ω => 2 * δ ω ^ 4 + (∑ k ∈ range n, Y k ω) ^ 2 / 2 +
      4 * L * δ ω ^ 2 + 4 * L * ε ω) P := i₂.add (hiε.const_mul (4 * L))
  have hi := integral_mono (integrable_finsetSum _ fun k _ => (hY k).integrable_sq) i₃ hpt
  rw [integral_finsetSum _ fun k _ => (hY k).integrable_sq,
    integral_add i₂ (hiε.const_mul (4 * L)), integral_add i₁ ((hiδ 2).const_mul (4 * L)),
    integral_add ((hiδ 4).const_mul 2) (hiS.div_const 2),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_div] at hi
  have he := integral_sq_sum_centred hM hM2 hK hL hπ n
  change (∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂P) = _ at he
  rw [← he] at hi
  change (∫ ω, (∑ k ∈ range n, Y k ω) ^ 2 ∂P) ≤ _
  linarith

/-- Every positive moment of the maximal increment tends to zero for a bounded
measurable continuous process; the process need not be a martingale. -/
theorem tendsto_integral_maxIncr_pow {X : ℝ≥0 → Ω → ℝ} {B : ℝ}
    (hm : ∀ t, Measurable (X t)) (hb : ∀ t ω, |X t ω| ≤ B)
    (hc : ∀ ω, Continuous (X · ω)) (s t : ℝ≥0) {p : ℕ} (hp : p ≠ 0) :
    Tendsto (fun n => ∫ ω, maxIncr X s t n ω ^ p ∂P) atTop (𝓝 0) := by
  have hlim := tendsto_integral_of_dominated_convergence (fun _ : Ω => (2 * B) ^ p)
    (fun n => ((measurable_maxIncr hm s t n).pow_const p).aestronglyMeasurable)
    (integrable_const (μ := P) _) (fun n => .of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (maxIncr_nonneg s t n ω)]
      exact pow_le_pow_left₀ (maxIncr_nonneg s t n ω) (maxIncr_le hb s t n ω) p)
    (.of_forall fun ω => (tendsto_maxIncr hc s t ω).pow p)
  simpa only [zero_pow hp, integral_zero] using hlim

/-- Quadratic sums converge in mean square for a general continuous bounded
bracket, including singular continuous brackets. -/
theorem tendsto_integral_quadError_sq (hM : Martingale M 𝓕 P)
    (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hL : ∀ t ω, |A t ω| ≤ L)
    (hAm : ∀ ω, Monotone (A · ω)) (hMc : ∀ ω, Continuous (M · ω))
    (hAc : ∀ ω, Continuous (A · ω)) (s t : ℝ≥0) :
    Tendsto (fun n => ∫ ω, quadError M A (unifPartIcc s t n) n ω ^ 2 ∂P) atTop (𝓝 0) := by
  have hMm (r : ℝ≥0) := ((hM.stronglyAdapted r).mono (𝓕.le r)).measurable
  have hAmeas (r : ℝ≥0) :=
    ((stronglyAdapted_of_martingale_sq_sub hM hM2 r).mono (𝓕.le r)).measurable
  have hlim : Tendsto (fun n =>
      4 * (∫ ω, maxIncr M s t n ω ^ 4 ∂P) +
        8 * L * (∫ ω, maxIncr M s t n ω ^ 2 ∂P) +
          8 * L * ∫ ω, maxIncr A s t n ω ∂P) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, add_zero] using
      (((tendsto_integral_maxIncr_pow hMm hK hMc s t four_ne_zero).const_mul 4).add
        ((tendsto_integral_maxIncr_pow hMm hK hMc s t two_ne_zero).const_mul (8 * L))).add
        ((tendsto_integral_maxIncr_pow hAmeas hL hAc s t one_ne_zero).const_mul (8 * L))
  refine squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) ?_ hlim
  exact fun n => integral_quadError_sq_le hM hM2 hK hL hAm (unifPartIcc_mono s t n) n
    (measurable_maxIncr hMm s t n) (measurable_maxIncr hAmeas s t n)
    (maxIncr_nonneg s t n) (maxIncr_le hK s t n)
    (maxIncr_nonneg s t n) (maxIncr_le hL s t n)
    (fun ω k hk => abs_le_maxIncr s t hk ω) (fun ω k hk => abs_le_maxIncr s t hk ω)

end InteractingSLE.Ito.GenCont
