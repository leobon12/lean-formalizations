/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12Max
import InteractingSLE.Spec.Supplement.G11Escape

/-!
# Lemma G12: the escape of the mark gap bounds the budget (pathwise)

Packet PROVE-G12. Supplement §7.9, Lemma G12 (p. 504). Fix one path of an integrated evolution of an ordered force
word, the innermost right mark `i₀` and a right mark `j₀` with `x_{i₀} < y = x_{j₀}`. With `u = V^{j₀} − W`,
`o = V^{i₀} − W`, `e = V^{j₀} − V^{i₀}`, the clock `T = ∫ u⁻²`, `L = −log e`, `X = log u − log e` and the mark
observable `Φ` of `G12Obs.lean`,

  `X = Φ − c' T + A L − Θ − F`,  `A = 1 + S'/2`, `S' = Σ_{x_k < y} ρ_k`

where `Θ = Σ_{near} (ρ_k/2) log θ_k` (`θ_k = (V^{j₀} − V^k)/e ∈ [θ_k(0), 1]`, monotone by the span formulas) and `F`
collects the left marks and the marks beyond `y`. With `−2 < S'`, `L ≥ 2T − log(y − x_{i₀})`, and the almost sure
bound `|Φ − Φ_0| < a + αT` (`G12Max.lean`), the gap escapes linearly: `X ≥ αT − K` for `α = (S_y − d_*)/2`.

* `IsPairPath.two_mul_clockR_le`, `IsPairPath.integral_budget_le_tail`, `IsPairPath.span_ratio_ge`: the pair estimates
  of G11 for general starting points;
* the budget bound on a bounded life, both for an unbounded clock (`integral_budget_le_tail`) and for a bounded clock
  (where `log u ≥ (S'/2) L − K` keeps the budget integrable: `∫ 2/u ≤ t + T` by AM–GM).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12

open G11 (spanRate budget clockR IsMarkLife)

/-! ### Pair estimates -/

namespace IsPairPath

variable {w v0 v1 : ℝ → ℝ} {a b T : ℝ} (h : IsPairPath w v0 v1 a b T)
include h

theorem continuousOn_inv_sq : ContinuousOn (fun s => 1 / (v1 s - w s) ^ 2) (Icc 0 T) :=
  continuousOn_const.div (h.continuousOn_gap.pow 2) fun t ht => pow_ne_zero 2 (h.gap_pos t ht).ne'

theorem intervalIntegrable_inv_sq {x : ℝ} (hx : x ∈ Icc 0 T) :
    IntervalIntegrable (fun s => 1 / (v1 s - w s) ^ 2) volume 0 x :=
  (h.continuousOn_inv_sq.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1

theorem intervalIntegrable_spanRate' {x : ℝ} (hx : x ∈ Icc 0 T) :
    IntervalIntegrable (spanRate w v0 v1) volume 0 x :=
  h.intervalIntegrable_spanRate.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le h.nonneg]; exact hx))

/-- `2 t(x) ≤ ∫₀ˣ 2/(u o) = −log e(x) + log(b − a)`. -/
theorem two_mul_clockR_le_integral (x : ℝ) (hx : x ∈ Icc 0 T) :
    2 * clockR w v1 x ≤ ∫ s in (0 : ℝ)..x, spanRate w v0 v1 s := by
  rw [clockR, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_ae_restrict hx.1 ((h.intervalIntegrable_inv_sq hx).const_mul 2)
    (h.intervalIntegrable_spanRate' hx) ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h.ae_ne] with s hne hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hx.2⟩
  have hu := h.gap_pos s hsT
  have ho : 0 < v0 s - w s := lt_of_le_of_ne (sub_nonneg.2 (h.w_le_v0 s hsT)) (Ne.symm (sub_ne_zero.2 (hne hsT)))
  have hou : v0 s - w s ≤ v1 s - w s := by linarith [h.v0_le_v1 s hsT]
  simp only [spanRate]
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem neg_log_span_eq (x : ℝ) (hx : x ∈ Icc 0 T) :
    -Real.log (v1 x - v0 x) = -Real.log (b - a) + ∫ s in (0 : ℝ)..x, spanRate w v0 v1 s := by
  rw [h.span_eq_exp x hx, Real.log_mul (sub_pos.2 h.lt).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- `2 t(x) ≤ −log e(x) + log(b − a)`. -/
theorem two_mul_clockR_le (x : ℝ) (hx : x ∈ Icc 0 T) :
    2 * clockR w v1 x ≤ -Real.log (v1 x - v0 x) + Real.log (b - a) := by
  have := h.two_mul_clockR_le_integral x hx
  rw [h.neg_log_span_eq x hx]
  linarith

theorem span_le (x : ℝ) (hx : x ∈ Icc 0 T) : v1 x - v0 x ≤ b - a := by
  rw [h.span_eq_exp x hx]
  have h0 : 0 ≤ ∫ s in (0 : ℝ)..x, spanRate w v0 v1 s := by
    have := h.two_mul_clockR_le_integral x hx
    have h2 : 0 ≤ clockR w v1 x := intervalIntegral.integral_nonneg hx.1 fun s _ => by positivity
    linarith
  have hba : 0 < b - a := sub_pos.2 h.lt
  have : Real.exp (-∫ s in (0 : ℝ)..x, spanRate w v0 v1 s) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  nlinarith

/-- **The budget on a tail where the gap escapes linearly** (G11's `integral_budget_le_tail`): if `e/u ≤ 1/2` and
`e/u ≤ M e^{−α t}` on `[s₁, s₂] ⊆ [0, T]`, then `∫_{s₁}^{s₂} β ≤ 12 M/α`. -/
theorem integral_budget_le_tail {s₁ s₂ M α : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (h0 : 0 ≤ s₁) (h12 : s₁ ≤ s₂)
    (h2T : s₂ ≤ T)
    (hhalf : ∀ x ∈ Icc s₁ s₂, (v1 x - v0 x) / (v1 x - w x) ≤ 1 / 2)
    (hdecay : ∀ x ∈ Icc s₁ s₂, (v1 x - v0 x) / (v1 x - w x) ≤ M * Real.exp (-α * clockR w v1 x)) :
    ∫ x in s₁..s₂, budget w v0 v1 x ≤ 12 * M / α := by
  have hsub : Icc s₁ s₂ ⊆ Icc 0 T := Icc_subset_Icc h0 h2T
  obtain ⟨g, hgc, hg⟩ := G11.exists_continuous_eqOn_Icc (h.nonneg) h.continuousOn_inv_sq
  have hclk : ∀ x ∈ Icc 0 T, clockR w v1 x = ∫ s in (0 : ℝ)..x, g s := fun x hx =>
    (G11.integral_congr_Icc hg hx).symm
  have hprim : Continuous fun x => ∫ s in (0 : ℝ)..x, g s :=
    continuous_iff_continuousAt.2 fun x => (hgc.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt
  have hdc : Continuous fun x => Real.exp (-α * ∫ s in (0 : ℝ)..x, g s) * g x :=
    (continuous_const.mul hprim).rexp.mul hgc
  set F : ℝ → ℝ := fun x => -Real.exp (-α * ∫ s in (0 : ℝ)..x, g s) / α with hF
  have hFd : ∀ x, HasDerivAt F (Real.exp (-α * ∫ s in (0 : ℝ)..x, g s) * g x) x := by
    intro x
    have h1 := ((hgc.integral_hasStrictDerivAt 0 x).hasDerivAt.const_mul (-α)).exp
    refine ((h1.neg).div_const α).congr_deriv ?_
    field_simp
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := s₁) (b := s₂)
    (fun x _ => hFd x) (hdc.intervalIntegrable s₁ s₂)
  have hpt : ∀ x ∈ Icc s₁ s₂, budget w v0 v1 x ≤
      12 * M * (Real.exp (-α * ∫ s in (0 : ℝ)..x, g s) * g x) := by
    intro x hx
    have hxT := hsub hx
    have hu := h.gap_pos x hxT
    have he := h.span_pos x hxT
    have hrat := hhalf x hx
    rw [div_le_iff₀ hu] at hrat
    have ho : (v1 x - w x) / 2 ≤ v0 x - w x := by linarith
    have hopos : 0 < v0 x - w x := lt_of_lt_of_le (by positivity) ho
    have hdec := hdecay x hx
    rw [hclk x hxT] at hdec
    rw [hg hxT]
    set u := v1 x - w x
    set e := v1 x - v0 x
    set o := v0 x - w x
    set E := Real.exp (-α * ∫ s in (0 : ℝ)..x, g s)
    have h1 : 4 * e / (u ^ 2 * o) ≤ 8 * e / u ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : u ^ 3 ≤ 2 * (u ^ 2 * o) := by nlinarith [sq_nonneg u]
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 4 * e)]
    have h2 : e / u ^ 3 ≤ M * E * (1 / u ^ 2) := by
      have : e / u ^ 3 = e / u * (1 / u ^ 2) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right hdec (by positivity)
    simp only [budget]
    have h3 : 8 * e / u ^ 3 + 4 * e / u ^ 3 = 12 * (e / u ^ 3) := by ring
    nlinarith
  have hint : IntervalIntegrable (budget w v0 v1) volume s₁ s₂ :=
    h.intervalIntegrable_budget.mono_set (by
      rw [uIcc_of_le h.nonneg, uIcc_of_le h12]; exact hsub)
  calc ∫ x in s₁..s₂, budget w v0 v1 x
      ≤ ∫ x in s₁..s₂, 12 * M * (Real.exp (-α * ∫ s in (0 : ℝ)..x, g s) * g x) := by
        exact intervalIntegral.integral_mono_on h12 hint ((hdc.const_mul _).intervalIntegrable _ _) hpt
    _ = 12 * M * (F s₂ - F s₁) := by rw [intervalIntegral.integral_const_mul, hFT]
    _ ≤ 12 * M / α := by
        simp only [hF]
        have hE1 : 0 ≤ Real.exp (-α * ∫ s in (0 : ℝ)..s₂, g s) := (Real.exp_pos _).le
        have hE2 : Real.exp (-α * ∫ s in (0 : ℝ)..s₁, g s) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ ∫ s in (0 : ℝ)..s₁, g s := by
            rw [← hclk s₁ ⟨h0, h12.trans h2T⟩]
            exact intervalIntegral.integral_nonneg h0 fun x _ => by positivity
          nlinarith
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        have hαi : 0 < α⁻¹ := inv_pos.2 hα
        nlinarith [mul_nonneg hM hαi.le, mul_nonneg (mul_nonneg hM hαi.le) hE1]

end IsPairPath

/-- **The span ratio is monotone**: for two inner points `v₀ ≤ v` of the mark `v₁` (`v₀` innermost),
`(v₁ − v)/(v₁ − v₀) ≥ (b − a)/(b − a₀)`. -/
theorem span_ratio_ge {w v0 v v1 : ℝ → ℝ} {a₀ a b T : ℝ} (h0 : IsPairPath w v0 v1 a₀ b T)
    (h : IsPairPath w v v1 a b T) (hle : ∀ s ∈ Icc 0 T, v0 s ≤ v s) (x : ℝ) (hx : x ∈ Icc 0 T) :
    (b - a) / (b - a₀) ≤ (v1 x - v x) / (v1 x - v0 x) := by
  rw [h.span_eq_exp x hx, h0.span_eq_exp x hx]
  have hba := sub_pos.2 h.lt
  have hba0 := sub_pos.2 h0.lt
  have hI : ∫ s in (0 : ℝ)..x, spanRate w v v1 s ≤ ∫ s in (0 : ℝ)..x, spanRate w v0 v1 s := by
    refine intervalIntegral.integral_mono_ae_restrict hx.1 (h.intervalIntegrable_spanRate' hx)
      (h0.intervalIntegrable_spanRate' hx) ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h0.ae_ne] with s hne hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hx.2⟩
    have hu := h.gap_pos s hsT
    have ho : 0 < v0 s - w s :=
      lt_of_le_of_ne (sub_nonneg.2 (h0.w_le_v0 s hsT)) (Ne.symm (sub_ne_zero.2 (hne hsT)))
    have hov : v0 s - w s ≤ v s - w s := by linarith [hle s hsT]
    simp only [spanRate]
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  rw [div_le_div_iff₀ hba0 (by positivity)]
  have hE : Real.exp (-∫ s in (0 : ℝ)..x, spanRate w v0 v1 s) ≤
      Real.exp (-∫ s in (0 : ℝ)..x, spanRate w v v1 s) := Real.exp_le_exp.2 (by linarith)
  have := mul_le_mul_of_nonneg_left hE (mul_pos hba hba0).le
  nlinarith [this]

/-! ### Along one path of a word -/

section Path

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {i₀ j₀ : Fin nR}

/-- The right marks strictly before `y = x_{j₀}`. -/
def nearR (xR : Fin nR → ℝ) (j₀ : Fin nR) : Finset (Fin nR) := univ.filter fun k => xR k < xR j₀

/-- The right marks strictly beyond `y`. -/
def farR (xR : Fin nR → ℝ) (j₀ : Fin nR) : Finset (Fin nR) := univ.filter fun k => xR j₀ < xR k

/-- The near weight `S' = Σ_{x_k < y} ρ_k`. -/
def nearW (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR) : ℝ := ∑ k ∈ nearR xR j₀, ρR k

theorem offY_eq (xR : Fin nR → ℝ) (j₀ : Fin nR) : offY xR j₀ = nearR xR j₀ ∪ farR xR j₀ := by
  ext k
  simp only [offY, nearR, farR, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro h; rcases lt_or_gt_of_ne h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact h.ne
    · exact h.ne'

theorem disjoint_nearR_farR (xR : Fin nR → ℝ) (j₀ : Fin nR) : Disjoint (nearR xR j₀) (farR xR j₀) := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [nearR, farR, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
  linarith

/-- The cumulative weight up to `y` is the near weight plus the weight of the group of `y`. -/
theorem sum_le_eq_nearW_add (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR) :
    ∑ k ∈ univ.filter (fun k => xR k ≤ xR j₀), ρR k = nearW xR ρR j₀ + rhoY xR ρR j₀ := by
  have e : univ.filter (fun k => xR k ≤ xR j₀) = nearR xR j₀ ∪ onY xR j₀ := by
    ext k
    simp only [nearR, onY, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h; rcases h.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact h.le
      · exact h.le
  have hd : Disjoint (nearR xR j₀) (onY xR j₀) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [nearR, onY, Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
    linarith
  rw [e, sum_union hd, nearW, rhoY]

/-- The pair data of two right marks on `[0, T]` inside the life of the outer one (`G12Det.lean`). -/
theorem isPairPath_of_life (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {i j : Fin nR} (hij : i ≤ j)
    (hx : xR i < xR j) {s : ℝ≥0} (hs : IsMarkLife w (vR j) ζ s) :
    ∃ T₂ : ℝ, (s : ℝ) < T₂ ∧ ENNReal.ofReal T₂ < ζ ∧ IsPairPath (frozenDrive w T₂)
      (fun x => vR i x.toNNReal) (fun x => vR j x.toNNReal) (xR i) (xR j) s := by
  obtain ⟨T₂, hsT₂, hT₂⟩ := G11.exists_real_gt_lt hs.1
  exact ⟨T₂, hsT₂, hT₂, isPairPath_of_isForcePath hF hij hx s.coe_nonneg hsT₂.le hT₂ fun x hx =>
    hs.2 x.toNNReal (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal x hx.1]; exact hx.2)⟩

/-- The mark `j₀` stays separated from the farther marks on its life. -/
theorem far_bounds (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hord : IsOrderedForceWord xL xR)
    {k : Fin nR} (hk : xR j₀ < xR k) {s : ℝ≥0} (hs : IsMarkLife w (vR j₀) ζ s) :
    0 < vR k s - vR j₀ s ∧ vR k s - vR j₀ s ≤ xR k - xR j₀ := by
  have hjk : j₀ ≤ k := by
    by_contra h; rw [not_le] at h; exact absurd (hord.2.2.1 h.le) (not_le.2 hk)
  have hlife : IsMarkLife w (vR k) ζ s := ⟨hs.1, fun u hu =>
    lt_of_lt_of_le (hs.2 u hu) (hF.monotone_vR (lt_of_le_of_lt (by exact_mod_cast hu) hs.1) hjk)⟩
  obtain ⟨T₂, hsT₂, hT₂, hP⟩ := isPairPath_of_life hF hjk hk hlife
  have hsI : (s : ℝ) ∈ Icc 0 (s : ℝ) := ⟨s.coe_nonneg, le_rfl⟩
  have h1 := hP.span_pos s hsI
  have h2 := hP.span_le s hsI
  simp only [Real.toNNReal_coe] at h1 h2
  exact ⟨h1, h2⟩

/-- `V^{j₀}` only moves right and the left marks only move left. -/
theorem left_gap_ge (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (i : Fin nL) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ) : xR j₀ - xL i ≤ vR j₀ s - vL i s := by
  have hR := hF.vR_eq hs j₀
  have hL := hF.vL_eq hs i
  have hR0 : 0 ≤ ∫ x in (0 : ℝ)..s, 2 / (vR j₀ x.toNNReal - w x.toNNReal) :=
    intervalIntegral.integral_nonneg s.coe_nonneg fun x hx =>
      div_nonneg zero_le_two (sub_nonneg.2 (hF.w_le_vR (Sec2.toNNReal_lt_of_mem_Icc hs hx) j₀))
  have hL0 : ∫ x in (0 : ℝ)..s, 2 / (vL i x.toNNReal - w x.toNNReal) ≤ 0 := by
    have := intervalIntegral.integral_nonneg (μ := volume) (f := fun x : ℝ => -(2 / (vL i x.toNNReal - w x.toNNReal)))
      s.coe_nonneg fun x hx => neg_nonneg.2
        (div_nonpos_of_nonneg_of_nonpos zero_le_two (sub_nonpos.2 (hF.vL_le_w (Sec2.toNNReal_lt_of_mem_Icc hs hx) i)))
    rw [intervalIntegral.integral_neg] at this
    linarith
  linarith

/-- The mark observable `Φ` along the path. -/
def phiAt (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR)
    (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  g12Obs κ xL xR ρL ρR j₀ (coordAtG w vL vR j₀ s, b s)

/-- The near-mark correction `Θ = Σ_{x_k < y} (ρ_k/2) log((V^{j₀} − V^k)/e)`. -/
def thetaAt (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (i₀ j₀ : Fin nR) (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  ∑ k ∈ nearR xR j₀, ρR k / 2 * Real.log ((vR j₀ s - vR k s) / (vR j₀ s - vR i₀ s))

/-- The left and far terms `F`. -/
def farAt (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  ∑ i, ρL i / 2 * Real.log (vR j₀ s - vL i s) + ∑ k ∈ farR xR j₀, ρR k / 2 * Real.log (vR j₀ s - vR k s)

/-- The bound `C_Θ` on `Θ`. -/
def thetaMax (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (i₀ j₀ : Fin nR) : ℝ :=
  ∑ k ∈ nearR xR j₀, |ρR k| / 2 * -Real.log ((xR j₀ - xR k) / (xR j₀ - xR i₀))

/-- The bound `F_max` on `F` (left weights `≤ 0`, far weights `≥ 0`). -/
def farMax (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR) : ℝ :=
  ∑ i, ρL i / 2 * Real.log (xR j₀ - xL i) + ∑ k ∈ farR xR j₀, ρR k / 2 * Real.log (xR k - xR j₀)

theorem gGap_coordAtG (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) :
    gGap κ xL xR ρL ρR j₀ (coordAtG w vL vR j₀ s, b s) = vR j₀ s - w s := by
  have := w_eq_gDriftLin (j₀ := j₀) hp hs
  simp only [gGap, coordAtG] at this ⊢
  rw [this]

/-- **Near marks**: the gap to the mark is positive and the span ratio lies in `[θ(0), 1]`. -/
theorem near_bounds (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hord : IsOrderedForceWord xL xR)
    (hi₀ : ∀ k, i₀ ≤ k) (hx : xR i₀ < xR j₀) {k : Fin nR} (hk : xR k < xR j₀) {s : ℝ≥0}
    (hs : IsMarkLife w (vR j₀) ζ s) :
    0 < vR j₀ s - vR k s ∧ (xR j₀ - xR k) / (xR j₀ - xR i₀) ≤ (vR j₀ s - vR k s) / (vR j₀ s - vR i₀ s) ∧
      (vR j₀ s - vR k s) / (vR j₀ s - vR i₀ s) ≤ 1 := by
  have hkj : k ≤ j₀ := by
    by_contra h; rw [not_le] at h; exact absurd (hord.2.2.1 h.le) (not_le.2 hk)
  obtain ⟨T₂, hsT₂, hT₂⟩ := G11.exists_real_gt_lt hs.1
  have hlifeR : ∀ x ∈ Icc 0 (s : ℝ), w x.toNNReal < vR j₀ x.toNNReal := fun x hx =>
    hs.2 x.toNNReal (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal x hx.1]; exact hx.2)
  have P0 := isPairPath_of_isForcePath hF (hi₀ j₀) hx s.coe_nonneg hsT₂.le hT₂ hlifeR
  have Pk := isPairPath_of_isForcePath hF hkj hk s.coe_nonneg hsT₂.le hT₂ hlifeR
  have hsI : (s : ℝ) ∈ Icc 0 (s : ℝ) := ⟨s.coe_nonneg, le_rfl⟩
  have hpos := Pk.span_pos s hsI
  have hge := span_ratio_ge P0 Pk (fun x hx => hF.monotone_vR
    (G11.lt_of_toNNReal hT₂ (hx.2.trans hsT₂.le)) (hi₀ k)) s hsI
  have he := P0.span_pos s hsI
  simp only [Real.toNNReal_coe] at hpos hge he
  refine ⟨hpos, hge, ?_⟩
  rw [div_le_one he]
  linarith [hF.monotone_vR hs.1 (hi₀ k)]

/-- **The identity** `log u − log e = Φ − c' T + A L − Θ − F` on the life of the mark. -/
theorem log_sub_log_eq (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ) (hnear : ∀ k ∈ nearR xR j₀, 0 < vR j₀ s - vR k s)
    (he : 0 < vR j₀ s - vR i₀ s) :
    Real.log (vR j₀ s - w s) - Real.log (vR j₀ s - vR i₀ s) =
      phiAt κ xL xR ρL ρR j₀ w vL vR b s - chargeY κ xR ρR j₀ * clockAt w (vR j₀) s +
        (1 + nearW xR ρR j₀ / 2) * -Real.log (vR j₀ s - vR i₀ s) - thetaAt xR ρR i₀ j₀ vR s -
        farAt xR ρL ρR j₀ vL vR s := by
  have hsplit : ∑ k ∈ nearR xR j₀, ρR k / 2 * Real.log (vR j₀ s - vR k s) =
      thetaAt xR ρR i₀ j₀ vR s + nearW xR ρR j₀ / 2 * Real.log (vR j₀ s - vR i₀ s) := by
    rw [thetaAt, nearW, Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Real.log_div (hnear k hk).ne' he.ne']
    ring
  have hg := gGap_coordAtG (j₀ := j₀) (b := b) hp hs
  simp only [coordAtG] at hg
  simp only [phiAt, g12Obs, g12Psi, coordAtG, offY_eq, sum_union (disjoint_nearR_farR xR j₀), hsplit, farAt,
    hg]
  ring

theorem thetaAt_le (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hord : IsOrderedForceWord xL xR)
    (hi₀ : ∀ k, i₀ ≤ k) (hx : xR i₀ < xR j₀) {s : ℝ≥0} (hs : IsMarkLife w (vR j₀) ζ s) :
    thetaAt xR ρR i₀ j₀ vR s ≤ thetaMax xR ρR i₀ j₀ := by
  refine Finset.sum_le_sum fun k hk => ?_
  obtain ⟨-, hlo, hhi⟩ := near_bounds hF hord hi₀ hx (by simpa [nearR] using hk) hs
  have hk' : xR k < xR j₀ := by simpa [nearR] using hk
  have h0pos : 0 < (xR j₀ - xR k) / (xR j₀ - xR i₀) := div_pos (sub_pos.2 hk') (sub_pos.2 hx)
  have hlog1 : Real.log ((vR j₀ s - vR k s) / (vR j₀ s - vR i₀ s)) ≤ 0 :=
    Real.log_nonpos (h0pos.le.trans hlo) hhi
  have hlog2 : Real.log ((xR j₀ - xR k) / (xR j₀ - xR i₀)) ≤
      Real.log ((vR j₀ s - vR k s) / (vR j₀ s - vR i₀ s)) := Real.log_le_log h0pos hlo
  rcases le_or_gt 0 (ρR k) with hρ | hρ
  · have : ρR k / 2 * Real.log ((vR j₀ s - vR k s) / (vR j₀ s - vR i₀ s)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog1
    have : 0 ≤ |ρR k| / 2 * -Real.log ((xR j₀ - xR k) / (xR j₀ - xR i₀)) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  · rw [abs_of_neg hρ]
    nlinarith

theorem farAt_le (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hord : IsOrderedForceWord xL xR)
    (hx : xR i₀ < xR j₀) (hfar : ∀ k ∈ farR xR j₀, 0 ≤ ρR k) (hleft : ∀ i, ρL i ≤ 0)
    {s : ℝ≥0} (hs : IsMarkLife w (vR j₀) ζ s) : farAt xR ρL ρR j₀ vL vR s ≤ farMax xL xR ρL ρR j₀ := by
  refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun k hk => ?_)
  · have hpos : 0 < xR j₀ - xL i := by
      have := hord.2.1 i; linarith [lt_of_le_of_lt (hord.2.2.2 i₀) hx]
    have hge := left_gap_ge (j₀ := j₀) hF i hs.1
    exact mul_le_mul_of_nonpos_left (Real.log_le_log hpos hge) (by linarith [hleft i])
  · obtain ⟨hpos, hle⟩ := far_bounds hF hord (by simpa [farR] using hk) hs
    have e : Real.log (vR j₀ s - vR k s) = Real.log (vR k s - vR j₀ s) := by
      rw [← Real.log_neg_eq_log, neg_sub]
    rw [e]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hle) (by linarith [hfar k hk])

/-- **The escape inequality** `X ≥ Φ + (2A − c') T − K₀` on the life of the mark (`−2 < S'`), given a bound `F ≤ F_b`
on the left and far terms. -/
theorem log_sub_log_ge (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hord : IsOrderedForceWord xL xR)
    (hi₀ : ∀ k, i₀ ≤ k) (hx : xR i₀ < xR j₀) (hS' : -2 < nearW xR ρR j₀) {s : ℝ≥0}
    (hs : IsMarkLife w (vR j₀) ζ s) {Fb : ℝ} (hFs : farAt xR ρL ρR j₀ vL vR s ≤ Fb) :
    phiAt κ xL xR ρL ρR j₀ w vL vR b s +
        (2 * (1 + nearW xR ρR j₀ / 2) - chargeY κ xR ρR j₀) * clockAt w (vR j₀) s -
        ((1 + nearW xR ρR j₀ / 2) * Real.log (xR j₀ - xR i₀) + thetaMax xR ρR i₀ j₀ + Fb) ≤
      Real.log (vR j₀ s - w s) - Real.log (vR j₀ s - vR i₀ s) := by
  have hF := hp.isForcePath
  have hnear : ∀ k ∈ nearR xR j₀, 0 < vR j₀ s - vR k s := fun k hk =>
    (near_bounds hF hord hi₀ hx (by simpa [nearR] using hk) hs).1
  obtain ⟨T₂, hsT₂, hT₂, P0⟩ := isPairPath_of_life hF (hi₀ j₀) hx hs
  have hsI : (s : ℝ) ∈ Icc 0 (s : ℝ) := ⟨s.coe_nonneg, le_rfl⟩
  have he := P0.span_pos s hsI
  have hL := P0.two_mul_clockR_le s hsI
  simp only [Real.toNNReal_coe] at he hL
  have hclk : clockR (frozenDrive w T₂) (fun x => vR j₀ x.toNNReal) s = clockAt w (vR j₀) s := by
    simp only [clockR, clockAt, one_div]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le s.coe_nonneg] at hx
    simp only [frozenDrive_eq (show x ∈ Icc 0 T₂ from ⟨hx.1, hx.2.trans hsT₂.le⟩)]
  rw [hclk] at hL
  have hΘ := thetaAt_le hF hord hi₀ hx hs
  have hid := log_sub_log_eq hp hs.1 hnear he
  have hA : 0 ≤ 1 + nearW xR ρR j₀ / 2 := by linarith
  have hL' := mul_le_mul_of_nonneg_left hL hA
  rw [hid]
  nlinarith

/-! ### Elementary facts along the life -/

theorem clockAt_mono (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {s s' : ℝ≥0} (hss' : s ≤ s')
    (hs' : IsMarkLife w (vR j₀) ζ s') : clockAt w (vR j₀) s ≤ clockAt w (vR j₀) s' := by
  have hint := intervalIntegrable_clockRate hF hs'
  rw [clockAt, clockAt]
  refine intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg (by exact_mod_cast hss') ?_ hint
  exact Filter.Eventually.of_forall fun x => inv_nonneg.2 (sq_nonneg _)

theorem clockAt_nonneg (s : ℝ≥0) : 0 ≤ clockAt w (vR j₀) s :=
  intervalIntegral.integral_nonneg s.coe_nonneg fun _ _ => inv_nonneg.2 (sq_nonneg _)

/-- `V^{j₀}_s ≤ y + s + T(s)` (from `2/u ≤ 1 + u⁻²`). -/
theorem vR_le_add_clock (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {s : ℝ≥0}
    (hs : IsMarkLife w (vR j₀) ζ s) : vR j₀ s ≤ xR j₀ + s + clockAt w (vR j₀) s := by
  rw [hF.vR_eq hs.1 j₀, add_assoc]
  suffices h : ∫ x in (0 : ℝ)..s, 2 / (vR j₀ x.toNNReal - w x.toNNReal) ≤ s + clockAt w (vR j₀) s by linarith
  have hi1 := hF.intervalIntegrable_forceR hs.1 j₀
  have hi2 := intervalIntegrable_clockRate hF hs
  calc ∫ x in (0 : ℝ)..s, 2 / (vR j₀ x.toNNReal - w x.toNNReal)
      ≤ ∫ x in (0 : ℝ)..s, (1 + ((vR j₀ x.toNNReal - w x.toNNReal) ^ 2)⁻¹) := by
        refine intervalIntegral.integral_mono_on s.coe_nonneg hi1 (intervalIntegrable_const.add hi2)
          fun x hx => ?_
        have hu : 0 < vR j₀ x.toNNReal - w x.toNNReal := sub_pos.2 (hs.2 _ (Sec2.toNNReal_le_of_mem_Icc hx))
        rw [div_le_iff₀ hu]
        have : ((vR j₀ x.toNNReal - w x.toNNReal) ^ 2)⁻¹ * (vR j₀ x.toNNReal - w x.toNNReal) =
            (vR j₀ x.toNNReal - w x.toNNReal)⁻¹ := by field_simp
        rw [add_mul, one_mul, this]
        have h1 : 0 ≤ ((vR j₀ x.toNNReal - w x.toNNReal) - 1) ^ 2 / (vR j₀ x.toNNReal - w x.toNNReal) := by
          positivity
        have h2 : ((vR j₀ x.toNNReal - w x.toNNReal) - 1) ^ 2 / (vR j₀ x.toNNReal - w x.toNNReal) =
            (vR j₀ x.toNNReal - w x.toNNReal) - 2 + (vR j₀ x.toNNReal - w x.toNNReal)⁻¹ := by
          field_simp; ring
        linarith
    _ = s + clockAt w (vR j₀) s := by
        rw [intervalIntegral.integral_add intervalIntegrable_const hi2, intervalIntegral.integral_const,
          smul_eq_mul, mul_one, sub_zero, clockAt]

/-- `∫₀ˢ 2/o = V^{i₀}_s − x_{i₀}`. -/
theorem integral_two_div_inner (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ) : ∫ x in (0 : ℝ)..s, 2 / (vR i₀ x.toNNReal - w x.toNNReal) = vR i₀ s - xR i₀ := by
  rw [hF.vR_eq hs i₀]; ring

/-- **The pointwise budget bound** used on a bounded clock: if a small gap `u < u₀` forces `e ≤ u/2`, then
`β ≤ (4Y/u₀²) o⁻¹ + 4Y/u₀³ + 6 u⁻²` (`e ≤ Y`). -/
theorem budget_le_of_small {u o e Y u₀ : ℝ} (hu : 0 < u) (ho : 0 ≤ o) (he : 0 ≤ e) (heu : e = u - o)
    (hey : e ≤ Y) (hu₀ : 0 < u₀) (hsmall : u < u₀ → e ≤ u / 2) :
    4 * e / (u ^ 2 * o) + 4 * e / u ^ 3 ≤ 4 * Y / u₀ ^ 2 * o⁻¹ + 4 * Y / u₀ ^ 3 + 6 * (u ^ 2)⁻¹ := by
  have hY : 0 ≤ Y := he.trans hey
  have h6 : 0 ≤ 6 * (u ^ 2)⁻¹ := by positivity
  have hoi : 0 ≤ 4 * Y / u₀ ^ 2 * o⁻¹ := by positivity
  rcases le_or_gt u₀ u with hbig | hlt
  · -- large gap
    have h1 : 4 * e / (u ^ 2 * o) ≤ 4 * Y / u₀ ^ 2 * o⁻¹ := by
      rcases ho.eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hu2 : u₀ ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hu₀.le hbig 2
        have : 4 * e * (u₀ ^ 2 * o) ≤ 4 * Y * (u ^ 2 * o) := by
          have := mul_le_mul hey hu2 (by positivity) hY
          nlinarith
        calc 4 * e * u₀ ^ 2 = 4 * e * (u₀ ^ 2 * o) * o⁻¹ := by field_simp
          _ ≤ 4 * Y * (u ^ 2 * o) * o⁻¹ := by gcongr
          _ = 4 * Y * o⁻¹ * (u ^ 2 * o) := by ring
    have h2 : 4 * e / u ^ 3 ≤ 4 * Y / u₀ ^ 3 := by
      have hu3 : u₀ ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hu₀.le hbig 3
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul hey hu3 (by positivity) hY]
    linarith
  · -- small gap: `o ≥ u/2`
    have hhalf := hsmall hlt
    have hou : u / 2 ≤ o := by linarith
    have hopos : 0 < o := lt_of_lt_of_le (by positivity) hou
    have h1 : 4 * e / (u ^ 2 * o) ≤ 4 * (u ^ 2)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have : 4 * (u ^ 2)⁻¹ * (u ^ 2 * o) = 4 * o := by field_simp
      rw [this]; linarith
    have h2 : 4 * e / u ^ 3 ≤ 2 * (u ^ 2)⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      have : 2 * (u ^ 2)⁻¹ * u ^ 3 = 2 * u := by field_simp
      rw [this]; linarith
    have h3 : 0 ≤ 4 * Y / u₀ ^ 3 := by positivity
    linarith

theorem clockR_frozen_eq {T₂ x : ℝ} (hx : x ∈ Icc 0 T₂) :
    clockR (frozenDrive w T₂) (fun x => vR j₀ x.toNNReal) x = clockAt w (vR j₀) x.toNNReal := by
  simp only [clockR, clockAt, one_div, Real.coe_toNNReal x hx.1]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hx.1] at hr
  simp only [frozenDrive_eq (show r ∈ Icc 0 T₂ from ⟨hr.1, hr.2.trans hx.2⟩)]

theorem intervalIntegrable_pairBudget (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hij : i₀ ≤ j₀)
    (hx : xR i₀ < xR j₀) {s : ℝ≥0} (hs : IsMarkLife w (vR j₀) ζ s) :
    IntervalIntegrable (pairBudget w (vR i₀) (vR j₀)) volume 0 s := by
  obtain ⟨T₂, hsT₂, hT₂, P⟩ := isPairPath_of_life hF hij hx hs
  refine P.intervalIntegrable_budget.congr fun x hx => ?_
  rw [uIoc_of_le s.coe_nonneg] at hx
  simp only [pairBudget, budget, frozenDrive_eq (show x ∈ Icc 0 T₂ from ⟨hx.1.le, hx.2.trans hsT₂.le⟩)]

/-- **The budget is bounded when the gap escapes linearly and the clock is unbounded.** -/
theorem budget_bound_of_escape (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hi₀ : ∀ k, i₀ ≤ k)
    (hx : xR i₀ < xR j₀) {α K : ℝ} (hα : 0 < α)
    (hesc : ∀ s, IsMarkLife w (vR j₀) ζ s →
      α * clockAt w (vR j₀) s - K ≤ Real.log (vR j₀ s - w s) - Real.log (vR j₀ s - vR i₀ s))
    (hunb : ∀ T : ℝ, ∃ s, IsMarkLife w (vR j₀) ζ s ∧ T < clockAt w (vR j₀) s) :
    ∃ C, ∀ s, IsMarkLife w (vR j₀) ζ s → ∫ x in (0 : ℝ)..s, pairBudget w (vR i₀) (vR j₀) x ≤ C := by
  obtain ⟨s₁, hs₁, hT₁⟩ := hunb ((K + Real.log 2) / α)
  have hC0 : 0 ≤ 12 * Real.exp K / α := by positivity
  refine ⟨(∫ x in (0 : ℝ)..s₁, pairBudget w (vR i₀) (vR j₀) x) + 12 * Real.exp K / α, fun s hs => ?_⟩
  by_cases hss : s ≤ s₁
  · have hmono : ∫ x in (0 : ℝ)..s, pairBudget w (vR i₀) (vR j₀) x ≤
        ∫ x in (0 : ℝ)..s₁, pairBudget w (vR i₀) (vR j₀) x := by
      refine intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg (by exact_mod_cast hss) ?_
        (intervalIntegrable_pairBudget hF (hi₀ j₀) hx hs₁)
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall fun x hx => pairBudget_nonneg hF (hi₀ j₀) hs₁ ⟨hx.1.le, hx.2⟩
    linarith
  rw [not_le] at hss
  obtain ⟨T₂, hsT₂, hT₂, P⟩ := isPairPath_of_life hF (hi₀ j₀) hx hs
  have hs₁s : (s₁ : ℝ) ≤ s := by exact_mod_cast hss.le
  have hI := P.intervalIntegrable_budget
  have hI1 : IntervalIntegrable (budget (frozenDrive w T₂) (fun x => vR i₀ x.toNNReal)
      (fun x => vR j₀ x.toNNReal)) volume 0 s₁ :=
    hI.mono_set (by rw [uIcc_of_le s₁.coe_nonneg, uIcc_of_le s.coe_nonneg]; exact Icc_subset_Icc le_rfl hs₁s)
  have hI2 : IntervalIntegrable (budget (frozenDrive w T₂) (fun x => vR i₀ x.toNNReal)
      (fun x => vR j₀ x.toNNReal)) volume s₁ s :=
    hI.mono_set (by rw [uIcc_of_le hs₁s, uIcc_of_le s.coe_nonneg]; exact Icc_subset_Icc s₁.coe_nonneg le_rfl)
  rw [← integral_pairBudget_frozen s.coe_nonneg hsT₂.le, ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2,
    integral_pairBudget_frozen s₁.coe_nonneg (hs₁s.trans hsT₂.le)]
  -- the tail
  have hratio : ∀ x ∈ Icc (s₁ : ℝ) s, (vR j₀ x.toNNReal - vR i₀ x.toNNReal) /
      (vR j₀ x.toNNReal - frozenDrive w T₂ x) =
        Real.exp (-(Real.log (vR j₀ x.toNNReal - w x.toNNReal) - Real.log (vR j₀ x.toNNReal - vR i₀ x.toNNReal))) := by
    intro x hx
    have hx0 : 0 ≤ x := s₁.coe_nonneg.trans hx.1
    have hxs : x.toNNReal ≤ s := by rw [← NNReal.coe_le_coe, Real.coe_toNNReal x hx0]; exact hx.2
    have hxI : x ∈ Icc 0 (s : ℝ) := ⟨hx0, hx.2⟩
    rw [frozenDrive_eq ⟨hx0, hx.2.trans hsT₂.le⟩]
    have hu : 0 < vR j₀ x.toNNReal - w x.toNNReal := sub_pos.2 (hs.2 _ hxs)
    have he : 0 < vR j₀ x.toNNReal - vR i₀ x.toNNReal := P.span_pos x hxI
    rw [neg_sub, Real.exp_sub, Real.exp_log he, Real.exp_log hu]
  have hlife_x : ∀ x ∈ Icc (s₁ : ℝ) s, IsMarkLife w (vR j₀) ζ x.toNNReal := fun x hx =>
    isMarkLife_mono hs (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal x (s₁.coe_nonneg.trans hx.1)]; exact hx.2)
  have hT_x : ∀ x ∈ Icc (s₁ : ℝ) s, (K + Real.log 2) / α < clockAt w (vR j₀) x.toNNReal := by
    intro x hx
    have hle : s₁ ≤ x.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal x (s₁.coe_nonneg.trans hx.1)]; exact hx.1
    exact lt_of_lt_of_le hT₁ (clockAt_mono hF hle (hlife_x x hx))
  have htail := P.integral_budget_le_tail hα (Real.exp_pos K).le s₁.coe_nonneg hs₁s le_rfl
    (fun x hx => by
      rw [hratio x hx]
      have h1 := hesc _ (hlife_x x hx)
      have h2 := hT_x x hx
      rw [div_lt_iff₀ hα] at h2
      calc Real.exp (-(Real.log (vR j₀ x.toNNReal - w x.toNNReal) -
            Real.log (vR j₀ x.toNNReal - vR i₀ x.toNNReal))) ≤ Real.exp (-Real.log 2) :=
            Real.exp_le_exp.2 (by linarith)
        _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log two_pos, one_div])
    (fun x hx => by
      rw [hratio x hx, clockR_frozen_eq ⟨s₁.coe_nonneg.trans hx.1, hx.2.trans hsT₂.le⟩, ← Real.exp_add]
      have h1 := hesc _ (hlife_x x hx)
      exact Real.exp_le_exp.2 (by linarith))
  linarith

/-- **The budget is bounded on a bounded life with a bounded clock** when a small gap forces `e ≤ u/2`. -/
theorem budget_bound_of_small (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hi₀ : ∀ k, i₀ ≤ k)
    (hx0 : 0 ≤ xR i₀) (hx : xR i₀ < xR j₀) {t : ℝ≥0} (hlt : ∀ s, IsMarkLife w (vR j₀) ζ s → s < t)
    {Tm : ℝ} (hT : ∀ s, IsMarkLife w (vR j₀) ζ s → clockAt w (vR j₀) s ≤ Tm) {u₀ : ℝ} (hu₀ : 0 < u₀)
    (hsmall : ∀ s, IsMarkLife w (vR j₀) ζ s → vR j₀ s - w s < u₀ →
      vR j₀ s - vR i₀ s ≤ (vR j₀ s - w s) / 2) :
    ∃ C, ∀ s, IsMarkLife w (vR j₀) ζ s → ∫ x in (0 : ℝ)..s, pairBudget w (vR i₀) (vR j₀) x ≤ C := by
  set y := xR j₀ with hy
  have hy0 : 0 < y := lt_of_le_of_lt hx0 hx
  refine ⟨4 * y / u₀ ^ 2 * ((y + t + Tm - xR i₀) / 2) + 4 * y / u₀ ^ 3 * t + 6 * Tm, fun s hs => ?_⟩
  have hst : (s : ℝ) ≤ t := by exact_mod_cast (hlt s hs).le
  obtain ⟨T₂, hsT₂, hT₂, P⟩ := isPairPath_of_life hF (hi₀ j₀) hx hs
  have hgap : IntervalIntegrable (fun x : ℝ => (vR i₀ x.toNNReal - w x.toNNReal)⁻¹) volume 0 s := by
    have := (hF.integrable_gapR hs.1 i₀).neg
    refine this.congr fun x _ => ?_
    simp only [Pi.neg_apply]
    rw [← inv_neg, neg_sub]
  have hclk := intervalIntegrable_clockRate hF hs
  have hRHS : IntervalIntegrable (fun x : ℝ => 4 * y / u₀ ^ 2 * (vR i₀ x.toNNReal - w x.toNNReal)⁻¹ +
      4 * y / u₀ ^ 3 + 6 * ((vR j₀ x.toNNReal - w x.toNNReal) ^ 2)⁻¹) volume 0 s :=
    ((hgap.const_mul _).add intervalIntegrable_const).add (hclk.const_mul 6)
  have hle : ∫ x in (0 : ℝ)..s, pairBudget w (vR i₀) (vR j₀) x ≤ ∫ x in (0 : ℝ)..s,
      (4 * y / u₀ ^ 2 * (vR i₀ x.toNNReal - w x.toNNReal)⁻¹ + 4 * y / u₀ ^ 3 +
        6 * ((vR j₀ x.toNNReal - w x.toNNReal) ^ 2)⁻¹) := by
    refine intervalIntegral.integral_mono_on s.coe_nonneg (intervalIntegrable_pairBudget hF (hi₀ j₀) hx hs) hRHS
      fun x hx => ?_
    have hxs : x.toNNReal ≤ s := Sec2.toNNReal_le_of_mem_Icc hx
    have hxζ : (x.toNNReal : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hxs) hs.1
    have hlx := isMarkLife_mono hs hxs
    have hu : 0 < vR j₀ x.toNNReal - w x.toNNReal := sub_pos.2 (hs.2 _ hxs)
    have ho : 0 ≤ vR i₀ x.toNNReal - w x.toNNReal := sub_nonneg.2 (hF.w_le_vR hxζ i₀)
    have he : 0 ≤ vR j₀ x.toNNReal - vR i₀ x.toNNReal := sub_nonneg.2 (hF.monotone_vR hxζ (hi₀ j₀))
    have hey : vR j₀ x.toNNReal - vR i₀ x.toNNReal ≤ y := by
      have := P.span_le x hx
      linarith
    have hb := budget_le_of_small hu ho he (by ring) hey hu₀ (hsmall _ hlx)
    simp only [pairBudget, budget]
    exact hb
  refine hle.trans ?_
  rw [intervalIntegral.integral_add (hgap.const_mul _ |>.add intervalIntegrable_const) (hclk.const_mul 6),
    intervalIntegral.integral_add (hgap.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul, sub_zero]
  have hinner : ∫ x in (0 : ℝ)..s, (vR i₀ x.toNNReal - w x.toNNReal)⁻¹ = (vR i₀ s - xR i₀) / 2 := by
    have h2 := integral_two_div_inner (i₀ := i₀) hF hs.1
    have : ∫ x in (0 : ℝ)..s, 2 / (vR i₀ x.toNNReal - w x.toNNReal) =
        2 * ∫ x in (0 : ℝ)..s, (vR i₀ x.toNNReal - w x.toNNReal)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]; rfl
    linarith
  rw [hinner]
  have hV : vR i₀ s ≤ y + t + Tm := by
    have h1 := hF.monotone_vR hs.1 (hi₀ j₀)
    have h2 := vR_le_add_clock (j₀ := j₀) hF hs
    linarith [hT s hs]
  have hTs : clockAt w (vR j₀) s ≤ Tm := hT s hs
  have hcl : ∫ x in (0 : ℝ)..s, ((vR j₀ x.toNNReal - w x.toNNReal) ^ 2)⁻¹ = clockAt w (vR j₀) s := rfl
  rw [hcl]
  have hk1 : 0 ≤ 4 * y / u₀ ^ 2 := by positivity
  have hk2 : 0 ≤ 4 * y / u₀ ^ 3 := by positivity
  have hVi : xR i₀ ≤ vR i₀ s := by
    have := integral_two_div_inner (i₀ := i₀) hF hs.1
    have h0 : 0 ≤ ∫ x in (0 : ℝ)..s, 2 / (vR i₀ x.toNNReal - w x.toNNReal) :=
      intervalIntegral.integral_nonneg s.coe_nonneg fun x hx =>
        div_nonneg zero_le_two (sub_nonneg.2 (hF.w_le_vR (Sec2.toNNReal_lt_of_mem_Icc hs.1 hx) i₀))
    linarith
  have := mul_le_mul_of_nonneg_left (show (vR i₀ s - xR i₀) / 2 ≤ (y + t + Tm - xR i₀) / 2 by linarith) hk1
  have := mul_le_mul_of_nonneg_left hst hk2
  linarith

/-- The escape rate `α = (S_y − d_*)/2`. -/
def escRate (κ : ℝ) (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR) : ℝ :=
  (nearW xR ρR j₀ + rhoY xR ρR j₀ - (κ / 2 - 4)) / 2

/-- **Lemma G12 along one path.** If the mark observable satisfies `|Φ − Φ_0| < a + αT` on the life of the mark
(`α = (S_y − d_*)/2`), with `−2 < S'`, `d_* < S_y`, and the left and far terms `F` are bounded above on every bounded
life, then the trace never visits `y` on `[0, ζ]`. -/
theorem trace_ne_of_phi_bound (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hord : IsOrderedForceWord xL xR) (hi₀ : ∀ k, i₀ ≤ k) (hx : xR i₀ < xR j₀) (hS' : -2 < nearW xR ρR j₀)
    (hS : κ / 2 - 4 < nearW xR ρR j₀ + rhoY xR ρR j₀)
    (hFb : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → ¬ IsMarkLife w (vR j₀) ζ t →
      ∃ Fb, ∀ s, IsMarkLife w (vR j₀) ζ s → farAt xR ρL ρR j₀ vL vR s ≤ Fb)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) {Φ₀ a : ℝ}
    (hΦ : ∀ s, IsMarkLife w (vR j₀) ζ s →
      |phiAt κ xL xR ρL ρR j₀ w vL vR b s - Φ₀| < a + escRate κ xR ρR j₀ * clockAt w (vR j₀) s) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η t ≠ xR j₀ := by
  have hF := hp.isForcePath
  have hx0 : 0 ≤ xR i₀ := hord.2.2.2 i₀
  intro t ht
  by_cases htl : IsMarkLife w (vR j₀) ζ t
  · exact trace_ne_of_isMarkLife hF (hi₀ j₀) hx0 hx hη htl
  have hlt : ∀ s, IsMarkLife w (vR j₀) ζ s → s < t := by
    intro s hs
    by_contra hts; rw [not_lt] at hts
    exact htl (isMarkLife_mono hs hts)
  obtain ⟨Fb, hFbs⟩ := hFb t ht htl
  set α := escRate κ xR ρR j₀ with hαdef
  have hα : 0 < α := by rw [hαdef, escRate]; linarith
  set A := 1 + nearW xR ρR j₀ / 2 with hAdef
  set c' := chargeY κ xR ρR j₀ with hc'
  have h2A : 2 * A - c' = 2 * α := by rw [hAdef, hc', hαdef, chargeY, escRate]; ring
  set K₀ := A * Real.log (xR j₀ - xR i₀) + thetaMax xR ρR i₀ j₀ + Fb with hK₀
  have hesc : ∀ s, IsMarkLife w (vR j₀) ζ s →
      α * clockAt w (vR j₀) s - (K₀ + a - Φ₀) ≤ Real.log (vR j₀ s - w s) - Real.log (vR j₀ s - vR i₀ s) := by
    intro s hs
    have h1 := log_sub_log_ge (b := b) hp hord hi₀ hx hS' hs (hFbs s hs)
    have h2 := hΦ s hs
    rw [abs_lt] at h2
    rw [← hAdef, ← hc', h2A] at h1
    linarith [h2.1]
  obtain ⟨C, hC⟩ : ∃ C, ∀ s, IsMarkLife w (vR j₀) ζ s →
      ∫ x in (0 : ℝ)..s, pairBudget w (vR i₀) (vR j₀) x ≤ C := by
    by_cases hunb : ∀ T : ℝ, ∃ s, IsMarkLife w (vR j₀) ζ s ∧ T < clockAt w (vR j₀) s
    · exact budget_bound_of_escape hF hi₀ hx hα hesc hunb
    push Not at hunb
    obtain ⟨Tm, hTm⟩ := hunb
    have hTm0 : ∀ s, IsMarkLife w (vR j₀) ζ s → 0 ≤ clockAt w (vR j₀) s := fun s _ => clockAt_nonneg s
    set K₂ := -Φ₀ + a + α * |Tm| + |c'| * |Tm| + thetaMax xR ρR i₀ j₀ + Fb with hK₂
    -- `log u ≥ −(S'/2) log e − K₂`
    have hlogu : ∀ s, IsMarkLife w (vR j₀) ζ s →
        -(nearW xR ρR j₀ / 2) * Real.log (vR j₀ s - vR i₀ s) - K₂ ≤ Real.log (vR j₀ s - w s) := by
      intro s hs
      have hnear : ∀ k ∈ nearR xR j₀, 0 < vR j₀ s - vR k s := fun k hk =>
        (near_bounds hF hord hi₀ hx (by simpa [nearR] using hk) hs).1
      obtain ⟨T₂, hsT₂, hT₂, P0⟩ := isPairPath_of_life hF (hi₀ j₀) hx hs
      have he := P0.span_pos s ⟨s.coe_nonneg, le_rfl⟩
      simp only [Real.toNNReal_coe] at he
      have hid := log_sub_log_eq (b := b) hp hs.1 hnear he
      have hΘ := thetaAt_le hF hord hi₀ hx hs
      have hFb' := hFbs s hs
      have h2 := hΦ s hs
      rw [abs_lt] at h2
      have hT0 := hTm0 s hs
      have hTs := hTm s hs
      have hc1 : c' * clockAt w (vR j₀) s ≤ |c'| * |Tm| := by
        calc c' * clockAt w (vR j₀) s ≤ |c'| * clockAt w (vR j₀) s :=
              mul_le_mul_of_nonneg_right (le_abs_self c') hT0
          _ ≤ |c'| * |Tm| := mul_le_mul_of_nonneg_left (hTs.trans (le_abs_self Tm)) (abs_nonneg c')
      have hc2 : α * clockAt w (vR j₀) s ≤ α * |Tm| :=
        mul_le_mul_of_nonneg_left (hTs.trans (le_abs_self Tm)) hα.le
      rw [← hAdef, ← hc'] at hid
      rw [hAdef] at hid
      nlinarith [h2.1]
    have hℓ : ∀ s, IsMarkLife w (vR j₀) ζ s → Real.log (vR j₀ s - vR i₀ s) ≤ Real.log (xR j₀ - xR i₀) := by
      intro s hs
      obtain ⟨T₂, hsT₂, hT₂, P0⟩ := isPairPath_of_life hF (hi₀ j₀) hx hs
      have he := P0.span_pos s ⟨s.coe_nonneg, le_rfl⟩
      have hle := P0.span_le s ⟨s.coe_nonneg, le_rfl⟩
      simp only [Real.toNNReal_coe] at he hle
      exact Real.log_le_log he hle
    rcases le_or_gt 0 (nearW xR ρR j₀) with hS0 | hS0
    · -- `S' ≥ 0`: the gap stays above `u₀`
      set u₀ := Real.exp (-(nearW xR ρR j₀ / 2) * Real.log (xR j₀ - xR i₀) - K₂) with hu₀
      refine budget_bound_of_small (u₀ := u₀) hF hi₀ hx0 hx hlt hTm (Real.exp_pos _) fun s hs hsmall => ?_
      exfalso
      have hu : 0 < vR j₀ s - w s := sub_pos.2 (hs.2 s le_rfl)
      have h1 := hlogu s hs
      have h2 := hℓ s hs
      have h3 : -(nearW xR ρR j₀ / 2) * Real.log (xR j₀ - xR i₀) ≤
          -(nearW xR ρR j₀ / 2) * Real.log (vR j₀ s - vR i₀ s) :=
        mul_le_mul_of_nonpos_left h2 (by linarith)
      have h4 : Real.log u₀ ≤ Real.log (vR j₀ s - w s) := by rw [hu₀, Real.log_exp]; linarith
      have h5 := Real.log_lt_log hu hsmall
      linarith
    · -- `−2 < S' < 0`: a small gap forces `X ≥ log 2`
      set q := -(nearW xR ρR j₀ / 2) with hq
      have hq0 : 0 < q := by rw [hq]; linarith
      have hq1 : q < 1 := by rw [hq]; linarith
      set m := (Real.log 2 + K₂ / q) / (1 / q - 1) with hm
      have hq' : 0 < 1 / q - 1 := by rw [sub_pos, lt_div_iff₀ hq0]; linarith
      refine budget_bound_of_small hF hi₀ hx0 hx hlt hTm (Real.exp_pos (-m)) fun s hs hsmall => ?_
      have hu : 0 < vR j₀ s - w s := sub_pos.2 (hs.2 s le_rfl)
      obtain ⟨T₂, hsT₂, hT₂, P0⟩ := isPairPath_of_life hF (hi₀ j₀) hx hs
      have he := P0.span_pos s ⟨s.coe_nonneg, le_rfl⟩
      simp only [Real.toNNReal_coe] at he
      have h1 := hlogu s hs
      have hlu : Real.log (vR j₀ s - w s) < -m := by
        have := Real.log_lt_log hu hsmall; rwa [Real.log_exp] at this
      -- `log e ≤ (log u + K₂)/q`
      have hle : Real.log (vR j₀ s - vR i₀ s) ≤ (Real.log (vR j₀ s - w s) + K₂) / q := by
        rw [le_div_iff₀ hq0]; linarith
      -- `X ≥ log 2`
      have hX : Real.log 2 ≤ Real.log (vR j₀ s - w s) - Real.log (vR j₀ s - vR i₀ s) := by
        have hmm : (1 / q - 1) * m = Real.log 2 + K₂ / q := by
          rw [hm, mul_comm]; exact div_mul_cancel₀ _ hq'.ne'
        have : Real.log (vR j₀ s - w s) - (Real.log (vR j₀ s - w s) + K₂) / q =
            (1 / q - 1) * (-Real.log (vR j₀ s - w s)) - K₂ / q := by field_simp; ring
        have h6 : (1 / q - 1) * m < (1 / q - 1) * (-Real.log (vR j₀ s - w s)) :=
          mul_lt_mul_of_pos_left (by linarith) hq'
        linarith
      have hratio : (vR j₀ s - vR i₀ s) / (vR j₀ s - w s) ≤ 1 / 2 := by
        rw [div_le_iff₀ hu]
        have := Real.exp_le_exp.2 hX
        rw [Real.exp_sub, Real.exp_log hu, Real.exp_log he, Real.exp_log two_pos, le_div_iff₀ he] at this
        linarith
      rw [div_le_iff₀ hu] at hratio
      linarith
  exact trace_ne_of_budget_lt hF (hi₀ j₀) hx0 hx hη ht fun s hs _ => hC s hs

end Path

end G12

end Supp7

end InteractingSLE
