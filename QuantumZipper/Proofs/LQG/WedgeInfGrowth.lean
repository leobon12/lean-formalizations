import QuantumZipper.Proofs.Probability.BMLLN
import QuantumZipper.LQG.WedgeProcess

/-!
# WEDGE-INF, step 1: linear growth of the wedge radial process at `−∞`

For the radial process `A` of an α-wedge (`IsWedgeProcess α Q A P`), almost surely, for every
`ε > 0` there is `C` with `A(−t) ≥ (Q − α − ε) t − C` for all `t ≥ 0`. This is the growth input
of the "infinite mass at ∞" facts (Sheffield, arXiv:1012.4797, §1.6 p. 21; Duplantier–Sheffield
§3.3): for `t ≥ 0`, `A(−t) = B̃(t + s₀)` with `B̃_s = √2 b'_s + (Q − α) s`, and the
continuous-time law of large numbers `b'_s / s → 0` (`BMLLN.ae_tendsto_div_atTop`, Le Gall 2016,
Exercise 2.25) gives `|√2 b'_s| ≤ ε s + K`. Own elementary bookkeeping on top of that.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace QuantumZipper

namespace WedgeInf

/-- A continuous path with `b_t / t → 0` grows sublinearly: `|b_s| ≤ ε s + K`. -/
theorem exists_abs_le_of_tendsto_div {b : ℝ≥0 → ℝ} (hb : Continuous b)
    (hlim : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * b t) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ s : ℝ≥0, |b s| ≤ ε * s + K := by
  obtain ⟨S, hS⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := max S 1)).exists_bound_of_continuousOn
    hb.continuousOn
  refine ⟨max K 0, fun s => ?_⟩
  by_cases hs : s ≤ max S 1
  · have := hK s ⟨zero_le, hs⟩
    rw [Real.norm_eq_abs] at this
    have : 0 ≤ ε * (s : ℝ) := by positivity
    linarith [le_max_left K 0]
  · push Not at hs
    have hs1 : (1 : ℝ) < s := by
      have := (le_max_right S 1).trans_lt hs
      exact_mod_cast this
    have h := hS s ((le_max_left S 1).trans hs.le)
    rw [Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos (by linarith : (0 : ℝ) < s)] at h
    have hs0 : (0 : ℝ) < s := by linarith
    rw [inv_mul_lt_iff₀ hs0] at h
    linarith [le_max_right K 0, mul_comm ε (s : ℝ)]

/-- Almost-sure sublinear growth of a Brownian motion. -/
theorem ae_abs_le_of_isBrownianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ s : ℝ≥0, |B s ω| ≤ ε * s + K := by
  filter_upwards [BMLLN.ae_tendsto_div_atTop hB, hB.cont] with ω h1 h2 ε hε
  exact exists_abs_le_of_tendsto_div h2 h1 hε

/-- Deterministic growth of the wedge path at `−∞`. -/
theorem wedgePath_neg_ge {α Q : ℝ} {b b' : ℝ≥0 → ℝ}
    (hb' : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ s : ℝ≥0, |b' s| ≤ ε * s + K) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → (Q - α - ε) * t - C ≤ wedgePath α Q b b' (-t) := by
  set Bt : ℝ → ℝ := fun s => Real.sqrt 2 * b' s.toNNReal - (α - Q) * s with hBt
  set s₀ := lastZero Bt with hs₀
  have hs₀0 : 0 ≤ s₀ := Real.sSup_nonneg fun x hx => hx.1
  have hsq : 0 < Real.sqrt 2 := by positivity
  obtain ⟨K, hK⟩ := hb' (ε / Real.sqrt 2) (div_pos hε hsq)
  refine ⟨Real.sqrt 2 * |K| + |Q - α - ε| * s₀ + |Real.sqrt 2 * b 0|, fun t ht => ?_⟩
  rcases ht.lt_or_eq with htp | rfl
  · have hnot : ¬ (0 ≤ -t) := by linarith
    have hval : wedgePath α Q b b' (-t) = Bt (-(-t) + s₀) := by
      simp only [wedgePath, hnot, if_false]; rfl
    rw [hval, neg_neg]
    set u := t + s₀ with hu
    have hu0 : 0 ≤ u := by linarith
    have hKu := hK u.toNNReal
    rw [Real.coe_toNNReal _ hu0] at hKu
    have h1 : -(Real.sqrt 2 * (ε / Real.sqrt 2 * u + K)) ≤ Real.sqrt 2 * b' u.toNNReal := by
      have := neg_abs_le (b' u.toNNReal)
      nlinarith
    have h2 : Real.sqrt 2 * (ε / Real.sqrt 2 * u + K) = ε * u + Real.sqrt 2 * K := by
      field_simp
    have h3 : (Q - α - ε) * s₀ ≥ -(|Q - α - ε| * s₀) := by
      have := neg_abs_le (Q - α - ε)
      nlinarith
    have h4 : Real.sqrt 2 * K ≤ Real.sqrt 2 * |K| := by
      exact mul_le_mul_of_nonneg_left (le_abs_self K) hsq.le
    show (Q - α - ε) * t - _ ≤ Real.sqrt 2 * b' u.toNNReal - (α - Q) * u
    have := abs_nonneg (Real.sqrt 2 * b 0)
    nlinarith
  · have hval : wedgePath α Q b b' (-0) = Real.sqrt 2 * b 0 := by
      simp [wedgePath]
    rw [hval]
    have := neg_abs_le (Real.sqrt 2 * b 0)
    have : 0 ≤ Real.sqrt 2 * |K| := by positivity
    have : 0 ≤ |Q - α - ε| * s₀ := by positivity
    linarith

/-- **Growth of the wedge radial process at `−∞`.** Almost surely, for every `ε > 0` there is
`C` with `A(−t) ≥ (Q − α − ε) t − C` for all `t ≥ 0`. -/
theorem ae_wedgeProcess_neg_ge {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α Q : ℝ}
    {A : ℝ → Ω → ℝ} (hA : IsWedgeProcess α Q A P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → (Q - α - ε) * t - C ≤ A (-t) ω := by
  obtain ⟨B, B', -, hB', -, hAe⟩ := hA
  filter_upwards [ae_abs_le_of_isBrownianReal hB'] with ω hω ε hε
  obtain ⟨C, hC⟩ := wedgePath_neg_ge (α := α) (Q := Q) (b := fun s => B s ω) hω hε
  exact ⟨C, fun t ht => (hAe ω (-t)).symm ▸ hC t ht⟩

end WedgeInf

end QuantumZipper
