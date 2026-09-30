import QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FIRSTMODE, step 1: reduction to summable dyadic-block tails (Borel–Cantelli)

Task N2Z-FIRSTMODE. We reduce `N2ZFirstModeStmt` (`D3PlusN2FirstModeDef.lean`) to the
**block-tail node** `N2ZFirstModeBlockStmt`: there is a regular version `G` such that for every
`m`, the probabilities of the dyadic-block events

`E_{m,n} = {∃ w ∈ fmBox m, τ ∈ (2^{-(n+1)}, 2^{-n}], s ∈ (0, τ): ‖M(w, τ, s)‖ > 2^{n/2}}`

(`M` = first circle Fourier mode `fmInt`, `fmBox m = {‖z‖ ≤ m, Im z ≥ 1/(m+1)}`) are summable
in `n`. The reduction (`n2ZFirstMode_of_block`) is Borel–Cantelli
(`MeasureTheory.ae_eventually_notMem`, any sets, outer measure), a countable exhaustion of the
compacts of `H` by the boxes `fmBox m`, and `2^{n/2} ≤ τ^{-1/2}` on block `n`: own elementary
bookkeeping, the standard dyadic-scale Borel–Cantelli step of Hu–Miller–Peres, *Thick points of
the Gaussian free field*, Ann. Probab. 38 (2010), proof of Prop. 2.1.

Note: each block probability is `≤ 1`, so summability only concerns large `n` (blocks where the
circles `∂B(w, τ)` leave `H` do not matter).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real ENNReal

namespace QuantumZipper
namespace D3Plus

/-- First circle Fourier mode `∫_0^{2π} g(w + τ e^{iθ}, s) e^{iθ} dθ`. -/
def fmInt (g : ℂ × ℝ → ℝ) (w : ℂ) (τ s : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π),
    ((g (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I), s) : ℝ) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I)

/-- The exhausting boxes `{‖z‖ ≤ m, Im z ≥ 1/(m+1)}` of `H`. -/
def fmBox (m : ℕ) : Set ℂ := {z | ‖z‖ ≤ m ∧ 1 / ((m : ℝ) + 1) ≤ z.im}

/-- Dyadic block event: some first mode with centre in `fmBox m`, radius
`τ ∈ (2^{-(n+1)}, 2^{-n}]` and smoothing `s ∈ (0, τ)` exceeds `2^{n/2}`. -/
def fmBlockEvent {Ω : Type} (G : Ω → ℂ × ℝ → ℝ) (m n : ℕ) : Set Ω :=
  {ω | ∃ w ∈ fmBox m, ∃ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n), ∃ s ∈ Ioo 0 τ,
    Real.sqrt ((2 : ℝ) ^ n) < ‖fmInt (G ω) w τ s‖}

/-- **Node N2Z-FIRSTMODE-BLOCK.** For a free field there is a regular version `G` whose
dyadic-block first-mode events have summable probabilities, for every box `fmBox m`.
(True: the first mode has variance `O(1)` uniformly, so by Kolmogorov chaining and Gaussian
tails `P(E_{m,n}) ≤ C_m e^{-c 2^n}`.) -/
def N2ZFirstModeBlockStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∃ G : Ω → ℂ × ℝ → ℝ, WedgeTK.IsRegVersion X P G ∧
      ∀ m : ℕ, ∑' n, P (fmBlockEvent G m n) ≠ ∞

/-- Every compact subset of `H` lies in some box `fmBox m`. -/
theorem exists_subset_fmBox {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ m : ℕ, K ⊆ fmBox m := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨0, by simp [hE]⟩
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨z₀, hz₀K, hz₀⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hz₀H : 0 < z₀.im := hKH hz₀K
  obtain ⟨m, hm⟩ := exists_nat_gt (max r (1 / z₀.im))
  refine ⟨m, fun z hz => ⟨?_, ?_⟩⟩
  · have := hr hz
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_max_left r (1 / z₀.im)]
  · have h1 : 1 / z₀.im < (m : ℝ) + 1 := by linarith [le_max_right r (1 / z₀.im)]
    have h2 : 1 / ((m : ℝ) + 1) < z₀.im := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hz₀H] at h1
      linarith
    exact h2.le.trans (hz₀ hz)

/-- Every `τ ∈ (0, 2^{-N})` lies in a dyadic block `n ≥ N`. -/
theorem exists_block_of_lt {τ : ℝ} (hτ : 0 < τ) {N : ℕ} (hτN : τ < (2 : ℝ)⁻¹ ^ N) :
    ∃ n ≥ N, τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n) := by
  have hN1 : (2 : ℝ)⁻¹ ^ N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hx : 1 ≤ τ⁻¹ := by
    rw [one_le_inv₀ hτ]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  have hinv : ∀ k : ℕ, (2 : ℝ)⁻¹ ^ k = ((2 : ℝ) ^ k)⁻¹ := fun k => inv_pow 2 k
  refine ⟨n, ?_, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have h1 : (2 : ℝ) ^ (n + 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hlt
    have h3 : ((2 : ℝ) ^ N)⁻¹ < τ := by
      rw [inv_lt_comm₀ (by positivity) hτ]; exact lt_of_lt_of_le hn2 h1
    rw [hinv] at hτN
    linarith
  · rw [hinv]
    rw [inv_lt_comm₀ (by positivity) hτ]; exact hn2
  · rw [hinv]
    rw [le_inv_comm₀ hτ (by positivity)]; exact hn1

/-- On block `n`, `2^{n/2} ≤ 1/√τ`. -/
theorem sqrt_two_pow_le_of_block {τ : ℝ} {n : ℕ}
    (hτ : τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n)) :
    Real.sqrt ((2 : ℝ) ^ n) ≤ 1 / Real.sqrt τ := by
  have hτ0 : 0 < τ := lt_of_le_of_lt (by positivity) hτ.1
  have h2 : (2 : ℝ) ^ n ≤ τ⁻¹ := by
    have := hτ.2
    rw [inv_pow, le_inv_comm₀ hτ0 (by positivity)] at this
    exact this
  rw [one_div, ← Real.sqrt_inv]
  exact Real.sqrt_le_sqrt h2

/-- **Reduction**: the block-tail node implies the first-mode node. -/
theorem n2ZFirstMode_of_block (hB : N2ZFirstModeBlockStmt) : N2ZFirstModeStmt := by
  intro Ω _ P _ X hX
  obtain ⟨G, hG, hsum⟩ := hB P X hX
  refine ⟨G, hG, ?_⟩
  have hev : ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ᶠ n in atTop, ω ∉ fmBlockEvent G m n :=
    ae_all_iff.2 fun m => ae_eventually_notMem (hsum m)
  filter_upwards [hev] with ω hω K hK hKH
  obtain ⟨m, hm⟩ := exists_subset_fmBox hK hKH
  obtain ⟨N, hN⟩ := (hω m).exists_forall_of_atTop
  refine ⟨1, (2 : ℝ)⁻¹ ^ N, by positivity, fun w hw τ hτ s hs => ?_⟩
  obtain ⟨n, hnN, hτn⟩ := exists_block_of_lt hτ.1 hτ.2
  have hnot := hN n hnN
  simp only [fmBlockEvent, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hnot
  have hle := hnot w (hm hw) τ hτn s hs
  exact hle.trans (sqrt_two_pow_le_of_block hτn)

end D3Plus
end QuantumZipper
