/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G11Trace

/-!
# Lemma G11: a linear escape of the strip gap bounds the budget

Packet PROVE-G11-G4. Supplement §7.9, Lemma G11 (p. 503–504). With `u₁ = v₁ − w`, `e = v₁ − v₀`, the strip clock
`t(x) = ∫₀ˣ u₁⁻²`, the strip gap `X = log u₁ − log e` and the strip observable

  `Φ = log u₁ + (r/2) log e + c' t`,  `c' = κ/2 − 2 − ρ`

(the observable `stripMartObs` of PROVE-ZHAN-A2 for the reflected word, `√κ` times a Brownian motion in strip time),
the span identity `−log e = ∫ 2/(u₁ o) ≥ 2t` gives the source's comparison (Q3)

  `X ≥ Φ + (2A − c') t = Φ + (S − d_*) t`,  `A = 1 + r/2`, `S = r + ρ`, `d_* = κ/2 − 4`

(`IsSeedMarkPath.sub_log_ge`). Once `X ≥ log 2`, the budget is at most `12 e^{−X}/u₁²`, and `e^{−X} ≤ M e^{−α t}` makes
its integral at most `12 M/α` (`IsSeedMarkPath.integral_budget_le_tail`, the fundamental theorem of calculus for
`−e^{−α t(x)}/α`). `budget_bdd_of_phi_ge` assembles this along one path: a lower bound `Φ ≥ −K − α t` on the life
before the swallow (from Brownian sublinearity) and an unbounded strip clock bound the budget.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G11

/-- The strip clock `t(x) = ∫₀ˣ (v₁ − w)⁻²`. -/
def clockR (w v1 : ℝ → ℝ) (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, 1 / (v1 s - w s) ^ 2

/-- The strip observable `Φ = log u₁ + (r/2) log e + c' t`. -/
def phiR (r c' : ℝ) (w v0 v1 : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.log (v1 x - w x) + r / 2 * Real.log (v1 x - v0 x) + c' * clockR w v1 x

variable {w v0 v1 : ℝ → ℝ} {T : ℝ}

namespace IsSeedMarkPath

variable (h : IsSeedMarkPath w v0 v1 T)
include h

theorem continuousOn_inv_sq : ContinuousOn (fun s => 1 / (v1 s - w s) ^ 2) (Icc 0 T) :=
  continuousOn_const.div (h.continuousOn_gap.pow 2) fun t ht => pow_ne_zero 2 (h.gap_pos t ht).ne'

theorem intervalIntegrable_inv_sq {x : ℝ} (hx : x ∈ Icc 0 T) :
    IntervalIntegrable (fun s => 1 / (v1 s - w s) ^ 2) volume 0 x :=
  (h.continuousOn_inv_sq.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1

/-- `2 t(x) ≤ −log e(x)`: the span decays at least at rate `2` in the strip clock. -/
theorem two_mul_clockR_le (x : ℝ) (hx : x ∈ Icc 0 T) :
    2 * clockR w v1 x ≤ -Real.log (v1 x - v0 x) := by
  rw [h.span_eq_exp x hx, Real.log_exp, neg_neg, clockR, ← intervalIntegral.integral_const_mul]
  have hsr : IntervalIntegrable (spanRate w v0 v1) volume 0 x :=
    h.intervalIntegrable_spanRate.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le h.nonneg]; exact hx))
  refine intervalIntegral.integral_mono_ae_restrict hx.1 ((h.intervalIntegrable_inv_sq hx).const_mul 2) hsr ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h.ae_ne] with s hne hs
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hx.2⟩
  have hu := h.gap_pos s hsT
  have ho : 0 < v0 s - w s := lt_of_le_of_ne (sub_nonneg.2 (h.w_le_v0 s hsT)) (Ne.symm (sub_ne_zero.2 (hne hsT)))
  have hou : v0 s - w s ≤ v1 s - w s := by linarith [h.v0_le_v1 s hsT]
  simp only [spanRate]
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **(Q3)**: `X = log u₁ − log e ≥ Φ + (2A − c') t` with `A = 1 + r/2 > 0`. -/
theorem sub_log_ge {r c' : ℝ} (hr : -2 < r) (x : ℝ) (hx : x ∈ Icc 0 T) :
    phiR r c' w v0 v1 x + (2 * (1 + r / 2) - c') * clockR w v1 x ≤
      Real.log (v1 x - w x) - Real.log (v1 x - v0 x) := by
  have h2 := h.two_mul_clockR_le x hx
  have hA : 0 ≤ 1 + r / 2 := by linarith
  have := mul_le_mul_of_nonneg_left h2 hA
  simp only [phiR]
  nlinarith

/-- **The budget on a tail where the strip gap escapes linearly**: if `e/u₁ ≤ 1/2` and `e/u₁ ≤ M e^{−α t}` on
`[s₁, s₂] ⊆ [0, T]`, then `∫_{s₁}^{s₂} β ≤ 12 M/α`. -/
theorem integral_budget_le_tail {s₁ s₂ M α : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (h0 : 0 ≤ s₁) (h12 : s₁ ≤ s₂)
    (h2T : s₂ ≤ T)
    (hhalf : ∀ x ∈ Icc s₁ s₂, (v1 x - v0 x) / (v1 x - w x) ≤ 1 / 2)
    (hdecay : ∀ x ∈ Icc s₁ s₂, (v1 x - v0 x) / (v1 x - w x) ≤ M * Real.exp (-α * clockR w v1 x)) :
    ∫ x in s₁..s₂, budget w v0 v1 x ≤ 12 * M / α := by
  have hsub : Icc s₁ s₂ ⊆ Icc 0 T := Icc_subset_Icc h0 h2T
  -- the clock is differentiable with derivative `u₁⁻²` (continuous extension)
  obtain ⟨g, hgc, hg⟩ := exists_continuous_eqOn_Icc (h.nonneg) h.continuousOn_inv_sq
  have hclk : ∀ x ∈ Icc 0 T, clockR w v1 x = ∫ s in (0 : ℝ)..x, g s := fun x hx =>
    (integral_congr_Icc hg hx).symm
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
  -- pointwise bound on `[s₁, s₂]`
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

end IsSeedMarkPath

/-! ### Along one path -/

section Path

variable {r ρ : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ} {v : Fin 2 → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The strip clock of the path, read on `ℝ`. -/
def clockP (w : ℝ≥0 → ℝ) (v : Fin 2 → ℝ≥0 → ℝ) (x : ℝ) : ℝ :=
  clockR (fun x : ℝ => w x.toNNReal) (fun x : ℝ => v 1 x.toNNReal) x

/-- The strip observable of the path, read on `ℝ`. -/
def phiP (r c' : ℝ) (w : ℝ≥0 → ℝ) (v : Fin 2 → ℝ≥0 → ℝ) (x : ℝ) : ℝ :=
  phiR r c' (fun x : ℝ => w x.toNNReal) (fun x : ℝ => v 0 x.toNNReal) (fun x : ℝ => v 1 x.toNNReal) x

theorem clockR_frozen {T₂ x : ℝ} (hx : x ∈ Icc 0 T₂) :
    clockR (frozenDrive w T₂) (fun x : ℝ => v 1 x.toNNReal) x = clockP w v x := by
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le hx.1] at hy
  simp only [frozenDrive_eq (show y ∈ Icc 0 T₂ from ⟨hy.1, hy.2.trans hx.2⟩)]

theorem phiR_frozen {r c' T₂ x : ℝ} (hx : x ∈ Icc 0 T₂) :
    phiR r c' (frozenDrive w T₂) (fun x : ℝ => v 0 x.toNNReal) (fun x : ℝ => v 1 x.toNNReal) x =
      phiP r c' w v x := by
  simp only [phiR, phiP, clockR_frozen hx, frozenDrive_eq hx]
  rfl

theorem isMarkLife_toNNReal {s : ℝ≥0} (hs : IsMarkLife w (v 1) ζ s) {x : ℝ} (hx : x ∈ Icc 0 (s : ℝ)) :
    IsMarkLife w (v 1) ζ x.toNNReal := by
  have hxs : x.toNNReal ≤ s := by rw [← NNReal.coe_le_coe, Real.coe_toNNReal x hx.1]; exact hx.2
  exact ⟨lt_of_le_of_lt (ENNReal.coe_le_coe.2 hxs) hs.1, fun u hu => hs.2 u (hu.trans hxs)⟩

/-- **The budget is bounded** along one path of the two-mark word, if the strip observable has the lower bound
`Φ ≥ −K − α t` on the life before the swallow, `2α ≤ 2A − c'`, and the strip clock is unbounded on that life. -/
theorem budget_bdd_of_phi_ge (hF : Sec2.IsForcePath ![] ![0, 1] ![] ![r, ρ] w vL v ζ) (hr : -2 < r)
    {c' α K : ℝ} (hα : 0 < α) (hrate : 2 * α ≤ 2 * (1 + r / 2) - c')
    (hΦ : ∀ s : ℝ≥0, IsMarkLife w (v 1) ζ s → -K - α * clockP w v s ≤ phiP r c' w v s)
    (hcl : ∀ N : ℝ, ∃ s : ℝ≥0, IsMarkLife w (v 1) ζ s ∧ N ≤ clockP w v s) :
    ∃ C : ℝ, ∀ s : ℝ≥0, IsMarkLife w (v 1) ζ s → ∫ x in (0 : ℝ)..s, pathBudget w v x ≤ C := by
  obtain ⟨s₁, hs₁, hcl₁⟩ := hcl ((K + Real.log 2) / α)
  set M := Real.exp K with hMdef
  have hM : 0 ≤ M := (Real.exp_pos K).le
  -- the data on `[0, m]` for `m ≥ s₁` in the life, with the driver frozen after `T₂ > m`
  have hdata : ∀ m : ℝ≥0, IsMarkLife w (v 1) ζ m → ∃ T₂ : ℝ, (m : ℝ) < T₂ ∧
      IsSeedMarkPath (frozenDrive w T₂) (fun x => v 0 x.toNNReal) (fun x => v 1 x.toNNReal) m := by
    intro m hm
    obtain ⟨T₂, hmT₂, hT₂⟩ := exists_real_gt_lt hm.1
    exact ⟨T₂, hmT₂, isSeedMarkPath_of_isForcePath hF m.coe_nonneg hmT₂.le hT₂ fun x hx =>
      (isMarkLife_toNNReal hm hx).2 _ le_rfl⟩
  -- the budget is nonnegative and integrable on the life
  have hbudget : ∀ m : ℝ≥0, IsMarkLife w (v 1) ζ m →
      IntervalIntegrable (pathBudget w v) volume 0 m ∧ ∀ x ∈ Icc 0 (m : ℝ), 0 ≤ pathBudget w v x := by
    intro m hm
    obtain ⟨T₂, hmT₂, hp⟩ := hdata m hm
    have heq : EqOn (budget (frozenDrive w T₂) (fun x => v 0 x.toNNReal) (fun x => v 1 x.toNNReal))
        (pathBudget w v) (Icc 0 (m : ℝ)) := fun x hx => by
      simp only [pathBudget, budget, frozenDrive_eq (show x ∈ Icc 0 T₂ from ⟨hx.1, hx.2.trans hmT₂.le⟩)]
    refine ⟨hp.intervalIntegrable_budget.congr fun x hx => heq ?_, fun x hx => heq hx ▸ hp.budget_nonneg x hx⟩
    rw [uIoc_of_le m.coe_nonneg] at hx
    exact ⟨hx.1.le, hx.2⟩
  set C₀ := ∫ x in (0 : ℝ)..s₁, pathBudget w v x
  refine ⟨C₀ + 12 * M / α, fun s hs => ?_⟩
  have h12 : 0 ≤ 12 * M / α := by positivity
  rcases le_or_gt s s₁ with hss₁ | hss₁
  · -- before `s₁`: the integral is at most the one up to `s₁`
    have := intervalIntegral.integral_mono_interval (c := 0) (d := s₁) le_rfl s.coe_nonneg
      (by exact_mod_cast hss₁) (by
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall fun x hx => (hbudget s₁ hs₁).2 x ⟨hx.1.le, hx.2⟩)
      (hbudget s₁ hs₁).1 (f := pathBudget w v)
    linarith
  · -- after `s₁`: the tail estimate
    obtain ⟨T₂, hsT₂, hp⟩ := hdata s hs
    have hs₁s : (s₁ : ℝ) ≤ s := by exact_mod_cast hss₁.le
    have hint₁ := (hbudget s₁ hs₁).1
    have hint₂ : IntervalIntegrable (pathBudget w v) volume s₁ s :=
      (hbudget s hs).1.mono_set (by
        rw [uIcc_of_le hs₁s, uIcc_of_le s.coe_nonneg]; exact Icc_subset_Icc_left s₁.coe_nonneg)
    rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
    have htail : ∫ x in (s₁ : ℝ)..s, pathBudget w v x ≤ 12 * M / α := by
      have heq : ∫ x in (s₁ : ℝ)..s, pathBudget w v x = ∫ x in (s₁ : ℝ)..s,
          budget (frozenDrive w T₂) (fun x => v 0 x.toNNReal) (fun x => v 1 x.toNNReal) x := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [uIcc_of_le hs₁s] at hx
        simp only [pathBudget, budget,
          frozenDrive_eq (show x ∈ Icc 0 T₂ from ⟨s₁.coe_nonneg.trans hx.1, hx.2.trans hsT₂.le⟩)]
      rw [heq]
      -- the escape bound on `[s₁, s]`
      have hX : ∀ x ∈ Icc (s₁ : ℝ) s, -K + α * clockR (frozenDrive w T₂) (fun x => v 1 x.toNNReal) x ≤
          Real.log (v 1 x.toNNReal - frozenDrive w T₂ x) - Real.log (v 1 x.toNNReal - v 0 x.toNNReal) := by
        intro x hx
        have hx0 : x ∈ Icc 0 (s : ℝ) := ⟨s₁.coe_nonneg.trans hx.1, hx.2⟩
        have hxT₂ : x ∈ Icc 0 T₂ := ⟨hx0.1, hx0.2.trans hsT₂.le⟩
        have h1 := hp.sub_log_ge (c' := c') hr x hx0
        have h2 := hΦ x.toNNReal (isMarkLife_toNNReal hs hx0)
        rw [Real.coe_toNNReal x hx0.1] at h2
        rw [phiR_frozen hxT₂, clockR_frozen hxT₂] at h1
        rw [clockR_frozen hxT₂]
        have hc0 : 0 ≤ clockP w v x := by
          simp only [clockP, clockR]
          exact intervalIntegral.integral_nonneg hx0.1 fun y _ => by positivity
        nlinarith
      have hclk_mono : ∀ x ∈ Icc (s₁ : ℝ) s, (K + Real.log 2) / α ≤
          clockR (frozenDrive w T₂) (fun x => v 1 x.toNNReal) x := by
        intro x hx
        have hx0 : x ∈ Icc 0 (s : ℝ) := ⟨s₁.coe_nonneg.trans hx.1, hx.2⟩
        have hs₁T : (s₁ : ℝ) ∈ Icc 0 (s : ℝ) := ⟨s₁.coe_nonneg, hs₁s⟩
        have hmono : clockR (frozenDrive w T₂) (fun x => v 1 x.toNNReal) s₁ ≤
            clockR (frozenDrive w T₂) (fun x => v 1 x.toNNReal) x := by
          simp only [clockR]
          refine intervalIntegral.integral_mono_interval le_rfl s₁.coe_nonneg hx.1 ?_
            (hp.intervalIntegrable_inv_sq hx0)
          exact Filter.Eventually.of_forall fun y => by positivity
        rw [clockR_frozen ⟨s₁.coe_nonneg, hs₁s.trans hsT₂.le⟩] at hmono
        linarith
      have hratio : ∀ x ∈ Icc (s₁ : ℝ) s, (v 1 x.toNNReal - v 0 x.toNNReal) /
          (v 1 x.toNNReal - frozenDrive w T₂ x) =
          Real.exp (-(Real.log (v 1 x.toNNReal - frozenDrive w T₂ x) -
            Real.log (v 1 x.toNNReal - v 0 x.toNNReal))) := by
        intro x hx
        have hx0 : x ∈ Icc 0 (s : ℝ) := ⟨s₁.coe_nonneg.trans hx.1, hx.2⟩
        rw [neg_sub, Real.exp_sub, Real.exp_log (hp.span_pos x hx0), Real.exp_log (hp.gap_pos x hx0)]
      refine hp.integral_budget_le_tail hα hM s₁.coe_nonneg hs₁s le_rfl (fun x hx => ?_) (fun x hx => ?_)
      · rw [hratio x hx]
        have h1 := hX x hx
        have h2 := hclk_mono x hx
        have h3 : Real.log 2 ≤ Real.log (v 1 x.toNNReal - frozenDrive w T₂ x) -
            Real.log (v 1 x.toNNReal - v 0 x.toNNReal) := by
          have := (div_le_iff₀ hα).1 h2
          linarith
        calc Real.exp _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
          _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
      · rw [hratio x hx, hMdef, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith [hX x hx])
    linarith

end Path

end G11

end Supp7

end InteractingSLE
