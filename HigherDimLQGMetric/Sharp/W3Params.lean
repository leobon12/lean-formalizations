import HigherDimLQGMetric.Sharp.W3Joint

/-! Choice of the exponents in the sharp diameter tail estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Filter
open scoped Topology

private theorem w3_choose_q {d : ℕ} {ξ Q a : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (ha : a < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ) :
    ∃ q : ℝ, Real.sqrt (2 * d) < q ∧ q < Q ∧
      ξ * a < q + Real.sqrt (q ^ 2 - 2 * d) := by
  let f : ℝ → ℝ := fun x => x + Real.sqrt (x ^ 2 - 2 * d)
  have hf : ContinuousAt f Q := by fun_prop
  have hfa : ξ * a < f Q := by
    dsimp [f]
    have := (lt_div_iff₀ hξ).mp ha
    nlinarith only [this]
  have hlim : Tendsto f (𝓝[<] Q) (𝓝 (f Q)) :=
    hf.mono_left nhdsWithin_le_nhds
  have hgood : ∀ᶠ q in 𝓝[<] Q, ξ * a < f q :=
    hlim.eventually (eventually_gt_nhds hfa)
  have hlow : ∀ᶠ q in 𝓝[<] Q, Real.sqrt (2 * d) < q :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (eventually_gt_nhds hQ)
  have hhigh : ∀ᶠ q in 𝓝[<] Q, q < Q := self_mem_nhdsWithin
  obtain ⟨q, ⟨hq, hq0⟩, hqQ⟩ := ((hgood.and hlow).and hhigh).exists
  exact ⟨q, hq0, hqQ, hq⟩

/-- Exponents for the two-parameter tail can be chosen to beat any requested
order below the sharp threshold. -/
theorem w3_choose_parameters {d : ℕ} {ξ Q a : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (ha : a < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ) :
    ∃ q ζ p a' θ : ℝ,
      Real.sqrt (2 * d) < q ∧ q < Q ∧
      0 < ζ ∧ ζ < ξ * (Q - q) ∧
      0 < p ∧ (d : ℝ) < ζ * p ∧
      0 < a' ∧ a' < q + Real.sqrt (q ^ 2 - 2 * d) ∧
      0 < θ ∧ θ < 1 ∧ a < θ * p ∧ a < (1 - θ) * a' / ξ := by
  obtain ⟨q, hq0, hqQ, hqa⟩ := w3_choose_q hξ hQ ha
  let ζ : ℝ := ξ * (Q - q) / 2
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hζsmall : ζ < ξ * (Q - q) := by dsimp [ζ]; nlinarith only [hξ, hqQ]
  let f : ℝ := q + Real.sqrt (q ^ 2 - 2 * d)
  have hf : 0 < f := by
    dsimp [f]
    have hqpos : 0 < q := (Real.sqrt_nonneg _).trans_lt hq0
    linarith only [hqpos, Real.sqrt_nonneg (q ^ 2 - 2 * d)]
  let low : ℝ := max 0 (ξ * a)
  have hlow0 : 0 ≤ low := le_max_left _ _
  have hlowA : ξ * a ≤ low := le_max_right _ _
  have hlowF : low < f := max_lt hf hqa
  let a' : ℝ := (low + f) / 2
  have ha'0 : 0 < a' := by dsimp [a']; linarith only [hlow0, hf]
  have ha'F : a' < f := by dsimp [a']; linarith only [hlowF]
  have ha'A : ξ * a < a' := by dsimp [a']; linarith only [hlowA, hlowF]
  let θ : ℝ := min (1 / 2) ((a' - ξ * a) / (2 * a')) / 2
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by
    have hm : θ ≤ 1 / 4 := by
      dsimp [θ]
      nlinarith only [min_le_left (1 / 2 : ℝ) ((a' - ξ * a) / (2 * a'))]
    linarith only [hm]
  have hθgap : θ * a' ≤ (a' - ξ * a) / 4 := by
    have hm : θ ≤ (a' - ξ * a) / (4 * a') := by
      dsimp [θ]
      have hm' := min_le_right (1 / 2 : ℝ) ((a' - ξ * a) / (2 * a'))
      calc
        min (1 / 2 : ℝ) ((a' - ξ * a) / (2 * a')) / 2 ≤
            ((a' - ξ * a) / (2 * a')) / 2 :=
          div_le_div_of_nonneg_right hm' (by norm_num)
        _ = (a' - ξ * a) / (4 * a') := by ring_nf
    have hm' := mul_le_mul_of_nonneg_right hm ha'0.le
    have he : ((a' - ξ * a) / (4 * a')) * a' = (a' - ξ * a) / 4 := by
      field_simp
    rw [he] at hm'
    exact hm'
  have htail : a < (1 - θ) * a' / ξ := by
    apply (lt_div_iff₀ hξ).2
    nlinarith only [hθgap, ha'A]
  let p : ℝ := ((d : ℝ) + 1) / ζ + (max 0 a + 1) / θ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hp : 0 < p := by dsimp [p]; positivity
  have hζp : (d : ℝ) < ζ * p := by
    have he : ζ * (((d : ℝ) + 1) / ζ) = d + 1 := by field_simp
    have hrest : 0 ≤ ζ * ((max 0 a + 1) / θ) := by positivity
    dsimp [p]
    nlinarith only [he, hrest]
  have hθp : a < θ * p := by
    have he : θ * ((max 0 a + 1) / θ) = max 0 a + 1 := by field_simp
    have hrest : 0 ≤ θ * (((d : ℝ) + 1) / ζ) := by positivity
    have ha0 : a ≤ max 0 a := le_max_right _ _
    dsimp [p]
    nlinarith only [he, hrest, ha0]
  exact ⟨q, ζ, p, a', θ, hq0, hqQ, hζ, hζsmall, hp, hζp,
    ha'0, ha'F, hθ0, hθ1, hθp, htail⟩

end HigherDimLQGMetric
