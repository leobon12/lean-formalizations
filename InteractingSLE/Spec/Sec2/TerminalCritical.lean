/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalEscape
import InteractingSLE.Spec.Ito.ACChain

/-!
# The critical side total `−2`: deterministic ingredients of (N5)–(N8)

Packet PROVE-SEC2-TERM. Specification pp. 27–28 (`source/spec/p001-048.md` L612–L648). In the
critical case `∑ ρ^{i,L} = −2` the source applies Itô's formula to `F(Q) = Q log Q`, where
`Q = W − V^out` is the gap between the driver and the outermost left force point. This file proves
the pathwise ingredients of that argument:

* `IsForcePath.gap_out_sub` — (N5) as an integral identity: `Q_u − Q_s = √κ (B_u − B_s) + ∫ₛᵘ μ_Q`
  with `μ_Q = drift − 2/(V^out − W)` (`gapOutDrift`);
* `gapOutDrift_eq_of_sum_eq` — in the critical case `μ_Q = ∑ᵢ ρ^{i,L} δᵢ + b^R` with
  `δᵢ = (W − V^{i,L})⁻¹ − (W − V^out)⁻¹` (the source's `−½ dΔᵢ/dt`) and `b^R = ∑ ρ^{j,R}/(W − V^{j,R})`;
* `IsForcePath.integral_spreadRate` — `∫ₛᵘ δᵢ = ½ (Δᵢ(s) − Δᵢ(u))` for the spread
  `Δᵢ = V^{i,L} − V^out`, and `spreadRate_nonneg` — `δᵢ ≥ 0` off the collision set;
* `IsForcePath.integral_abs_one_add_log_mul_spreadRate_le` — **(N7)**: while `ε ≤ Q ≤ M`,
  `∫ₛᵘ |1 + log Q| δᵢ ≤ ((1 + log M) Δᵢ(s) + 1)/2`, uniformly in `ε` (via the cut-off logarithm
  `logCut ε y = max 0 (−log (max y ε))`, whose primitive is at most `1`, and the chain rule for
  absolutely continuous paths `Ito.comp_eq_add_integral_of_lipschitz`);
* `mul_abs_one_add_log_le` — the bound `C |1 + log x| ≤ κ/(4x) + C (1 + log M) + 4C²/κ` on `(0, M]`
  used to absorb the drift term into the second-order Itô term (p. 27).

The probabilistic part (Itô's formula for `F(Q)` in expectation, the localization, and the
conclusion `∫ dt/Q < ∞` almost surely, which contradicts `integral_inv_gap_out_unbounded`) is not
in this file; see `planning/handoffs/PROVE-SEC2-TERM.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-- The drift of `Q = W − V^out` at real time `r` (outermost left index `o`):
`μ_Q = driverDrift − 2/(V^out − W)`. -/
def gapOutDrift {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (o : Fin nL) (r : ℝ) : ℝ :=
  driverDrift ρL ρR w vL vR r - 2 / (vL o r.toNNReal - w r.toNNReal)

/-- The rate `δᵢ = (W − V^{i,L})⁻¹ − (W − V^out)⁻¹` at which the spread `Δᵢ = V^{i,L} − V^out`
decreases (`dΔᵢ/dt = −2 δᵢ`). -/
def spreadRate {nL : ℕ} (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (o i : Fin nL) (r : ℝ) : ℝ :=
  (w r.toNNReal - vL i r.toNNReal)⁻¹ - (w r.toNNReal - vL o r.toNNReal)⁻¹

/-- The right-side drift `b^R = ∑ ρ^{j,R}/(W − V^{j,R})` of (N5). -/
def rightDrift {nR : ℕ} (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (r : ℝ) : ℝ :=
  ∑ j, ρR j / (w r.toNNReal - vR j r.toNNReal)

/-- **(N5), drift form**: if the left side total is `−2`, the drift of `Q = W − V^out` is
`∑ᵢ ρ^{i,L} δᵢ + b^R`. -/
theorem gapOutDrift_eq_of_sum_eq {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} (o : Fin nL)
    (hS : ∑ i, ρL i = -2) (r : ℝ) :
    gapOutDrift ρL ρR w vL vR o r =
      ∑ i, ρL i * spreadRate w vL o i r + rightDrift ρR w vR r := by
  unfold gapOutDrift driverDrift spreadRate rightDrift
  have e1 : 2 / (vL o r.toNNReal - w r.toNNReal) =
      (∑ i, ρL i) * (w r.toNNReal - vL o r.toNNReal)⁻¹ := by
    rw [hS, ← neg_sub (w r.toNNReal), div_neg, div_eq_mul_inv]
    ring
  have e2 : ∑ i, ρL i * ((w r.toNNReal - vL i r.toNNReal)⁻¹ - (w r.toNNReal - vL o r.toNNReal)⁻¹) =
      ∑ i, ρL i / (w r.toNNReal - vL i r.toNNReal) -
        (∑ i, ρL i) * (w r.toNNReal - vL o r.toNNReal)⁻¹ := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]; ring
  rw [e1, e2]
  ring

/-- `δᵢ ≥ 0` when the driver does not touch `V^{i,L}`: `0 < W − V^{i,L} ≤ W − V^out`. -/
theorem spreadRate_nonneg {nL : ℕ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {o i : Fin nL} {r : ℝ}
    (hpos : vL i r.toNNReal < w r.toNNReal) (hle : vL o r.toNNReal ≤ vL i r.toNNReal) :
    0 ≤ spreadRate w vL o i r := by
  unfold spreadRate
  rw [sub_nonneg]
  exact inv_anti₀ (sub_pos.2 hpos) (sub_le_sub_left hle _)


/-! ### The cut-off logarithm (for (N7)) -/

/-- The cut-off logarithm `max 0 (−log (max y ε))`: equal to `(−log y)₊` for `y ≥ ε` and to
`−log ε` below `ε`. -/
def logCut (ε y : ℝ) : ℝ := max 0 (-Real.log (max y ε))

/-- Its primitive `∫₀ʸ logCut ε`. -/
def logCutPrim (ε y : ℝ) : ℝ := ∫ x in (0 : ℝ)..y, logCut ε x

theorem logCut_nonneg (ε y : ℝ) : 0 ≤ logCut ε y := le_max_left _ _

theorem continuous_logCut {ε : ℝ} (hε : 0 < ε) : Continuous (logCut ε) := by
  unfold logCut
  refine continuous_const.max (Continuous.neg ?_)
  exact Real.continuousOn_log.comp_continuous (continuous_id.max continuous_const)
    fun y => (lt_of_lt_of_le hε (le_max_right y ε)).ne'

theorem logCut_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (y : ℝ) : logCut ε y ≤ -Real.log ε := by
  unfold logCut
  refine max_le (by linarith [Real.log_nonpos hε.le hε1]) ?_
  exact neg_le_neg (Real.log_le_log hε (le_max_right _ _))

/-- `−log Q ≤ logCut ε Δ` whenever `Q ≥ ε` and `Q ≥ Δ`. -/
theorem neg_log_le_logCut {ε Q Δ : ℝ} (hε : 0 < ε) (hQε : ε ≤ Q) (hQΔ : Δ ≤ Q) :
    -Real.log Q ≤ logCut ε Δ := by
  unfold logCut
  refine le_max_of_le_right (neg_le_neg ?_)
  exact Real.log_le_log (lt_of_lt_of_le hε (le_max_right _ _)) (max_le hQΔ hQε)

theorem hasDerivAt_logCutPrim {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    HasDerivAt (logCutPrim ε) (logCut ε y) y :=
  ((continuous_logCut hε).integral_hasStrictDerivAt 0 y).hasDerivAt

theorem lipschitzWith_logCutPrim {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    LipschitzWith (Real.toNNReal (-Real.log ε)) (logCutPrim ε) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hint : ∀ a b : ℝ, IntervalIntegrable (logCut ε) volume a b := fun a b =>
    (continuous_logCut hε).intervalIntegrable a b
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith [Real.log_nonpos hε.le hε1]),
    logCutPrim, logCutPrim, intervalIntegral.integral_interval_sub_left (hint 0 x) (hint 0 y)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x)
    (C := -Real.log ε) (f := logCut ε) fun z _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (logCut_nonneg ε z)]
      exact logCut_le hε hε1 z
  rwa [Real.norm_eq_abs] at this

/-- The primitive of the cut-off logarithm is at most `1`: `∫₀¹ logCut ε = 1 − ε` and the integrand
vanishes beyond `1`. -/
theorem logCutPrim_le_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (y : ℝ) :
    logCutPrim ε y ≤ 1 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (logCut ε) volume a b := fun a b =>
    (continuous_logCut hε).intervalIntegrable a b
  have h0 : ∀ x, 1 ≤ x → logCut ε x = 0 := fun x hx => by
    unfold logCut
    exact max_eq_left (neg_nonpos.2 (Real.log_nonneg (hx.trans (le_max_left _ _))))
  -- `∫₀^y ≤ ∫₀^{max y 1} = ∫₀¹`
  have h1 : logCutPrim ε y ≤ logCutPrim ε (max y 1) := by
    unfold logCutPrim
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 y) (hint y (max y 1))]
    have : 0 ≤ ∫ x in y..max y 1, logCut ε x :=
      intervalIntegral.integral_nonneg (le_max_left _ _) fun x _ => logCut_nonneg ε x
    linarith
  have h2 : logCutPrim ε (max y 1) = logCutPrim ε 1 := by
    unfold logCutPrim
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 (max y 1))]
    have : ∫ x in (1 : ℝ)..max y 1, logCut ε x = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => h0 x ?_]
      · simp
      · rw [uIcc_of_le (le_max_right _ _)] at hx
        exact hx.1
    rw [this, add_zero]
  have h3 : logCutPrim ε 1 = 1 - ε := by
    unfold logCutPrim
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 ε) (hint ε 1)]
    have e1 : ∫ x in (0 : ℝ)..ε, logCut ε x = ∫ _ in (0 : ℝ)..ε, -Real.log ε := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hε.le] at hx
      simp only [logCut, max_eq_right hx.2]
      exact max_eq_right (neg_nonneg.2 (Real.log_nonpos hε.le hε1))
    have e2 : ∫ x in ε..(1 : ℝ), logCut ε x = ∫ x in ε..(1 : ℝ), -Real.log x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hε1] at hx
      simp only [logCut, max_eq_left hx.1]
      exact max_eq_right (neg_nonneg.2 (Real.log_nonpos (hε.le.trans hx.1) hx.2))
    rw [e1, e2, intervalIntegral.integral_const, intervalIntegral.integral_neg, integral_log,
      smul_eq_mul, Real.log_one]
    ring
  rw [← h2] at h3
  linarith

/-- `logCutPrim ε` is nonnegative on `[0, ∞)`. -/
theorem logCutPrim_nonneg (ε : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ logCutPrim ε y :=
  intervalIntegral.integral_nonneg hy fun x _ => logCut_nonneg ε x

/-- **The drift bound of (N8)** (Specification p. 27, "`C |1 + log x| ≤ κ/(4x) + C_{κ,C,M}` for
`0 < x ≤ M`, because `x |log x| → 0`"): with the explicit constant
`C_{κ,C,M} = C (1 + log M) + 4C²/κ`. -/
theorem mul_abs_one_add_log_le {κ C M x : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) (hM : 1 ≤ M) (hx : 0 < x)
    (hxM : x ≤ M) :
    C * |1 + Real.log x| ≤ κ / (4 * x) + (C * (1 + Real.log M) + 4 * C ^ 2 / κ) := by
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hκx : 0 ≤ κ / (4 * x) := by positivity
  have hCκ : 0 ≤ 4 * C ^ 2 / κ := by positivity
  have habs : |1 + Real.log x| ≤ 1 + |Real.log x| := by
    simpa using abs_add_le (1 : ℝ) (Real.log x)
  rcases le_or_gt 1 x with h1 | h1
  · have hl : |Real.log x| ≤ Real.log M := by
      rw [abs_of_nonneg (Real.log_nonneg h1)]
      exact Real.log_le_log hx hxM
    have : C * |1 + Real.log x| ≤ C * (1 + Real.log M) :=
      mul_le_mul_of_nonneg_left (habs.trans (by linarith)) hC
    linarith
  · -- `−log x ≤ 2/√x`, then `2C y ≤ (κ/4) y² + 4C²/κ` with `y = 1/√x`
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    set y := (Real.sqrt x)⁻¹ with hy
    have hy0 : 0 < y := inv_pos.2 hsx
    have hy2 : y ^ 2 = x⁻¹ := by
      rw [hy, inv_pow, Real.sq_sqrt hx.le]
    have hlog : -Real.log x ≤ 2 * y := by
      have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
        rw [Real.log_sqrt hx.le]; ring
      have h2 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
      rw [hy, Real.log_inv] at h2
      rw [h1]
      linarith
    have hl : |Real.log x| ≤ 2 * y := by
      rw [abs_of_nonpos (Real.log_nonpos hx.le h1.le)]
      exact hlog
    have hamgm : 2 * C * y ≤ κ / 4 * y ^ 2 + 4 * C ^ 2 / κ := by
      rw [div_mul_eq_mul_div, div_add_div _ _ (by norm_num) hκ.ne', le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (κ * y - 4 * C)]
    have hκx' : κ / (4 * x) = κ / 4 * y ^ 2 := by
      rw [hy2]
      field_simp
    have : C * |1 + Real.log x| ≤ C + 2 * C * y := by
      calc C * |1 + Real.log x| ≤ C * (1 + 2 * y) :=
            mul_le_mul_of_nonneg_left (habs.trans (by linarith)) hC
        _ = C + 2 * C * y := by ring
    have : C ≤ C * (1 + Real.log M) := by nlinarith
    rw [hκx']
    linarith

namespace IsForcePath

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- **(N5)** as an integral identity: `Q_u − Q_s = √a (b_u − b_s) + ∫ₛᵘ μ_Q` for
`Q = W − V^out`, `s ≤ u < ζ`. -/
theorem gap_out_sub (hw : DriverEq a ρL ρR w vL vR b ζ) (o : Fin nL) {s u : ℝ≥0} (hsu : s ≤ u)
    (hu : (u : ℝ≥0∞) < ζ) :
    (w u - vL o u) - (w s - vL o s) = Real.sqrt a * (b u - b s)
      + ∫ r in (s : ℝ)..u, gapOutDrift ρL ρR w vL vR o r := by
  have hsu' : (s : ℝ) ≤ u := by exact_mod_cast hsu
  have hsub : uIcc (s : ℝ) u ⊆ uIcc 0 (u : ℝ) := by
    rw [uIcc_of_le hsu', uIcc_of_le (NNReal.coe_nonneg u)]
    exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl
  have hint1 := (h.intervalIntegrable_driverDrift hu).mono_set hsub
  have hint2 := (h.intervalIntegrable_forceL hu o).mono_set hsub
  unfold gapOutDrift
  rw [intervalIntegral.integral_sub hint1 hint2]
  have h1 := h.w_sub hw hsu hu
  have h2 := h.vL_sub hsu hu o
  linarith

/-- The spread rate is interval integrable on `[0, t]` for `t < ζ`. -/
theorem intervalIntegrable_spreadRate {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (o i : Fin nL) :
    IntervalIntegrable (spreadRate w vL o i) volume 0 t :=
  (h.integrable_gapL ht i).sub (h.integrable_gapL ht o)

/-- `∫ₛᵘ δᵢ = ½ (Δᵢ(s) − Δᵢ(u))` with `Δᵢ = V^{i,L} − V^out` (the source's `−dΔᵢ = 2 δᵢ dt`). -/
theorem integral_spreadRate (o i : Fin nL) {s u : ℝ≥0} (hsu : s ≤ u) (hu : (u : ℝ≥0∞) < ζ) :
    ∫ r in (s : ℝ)..u, spreadRate w vL o i r =
      ((vL i s - vL o s) - (vL i u - vL o u)) / 2 := by
  have hsu' : (s : ℝ) ≤ u := by exact_mod_cast hsu
  have hsub : uIcc (s : ℝ) u ⊆ uIcc 0 (u : ℝ) := by
    rw [uIcc_of_le hsu', uIcc_of_le (NNReal.coe_nonneg u)]
    exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl
  have key : ∀ k : Fin nL, ∫ r in (s : ℝ)..u, (w r.toNNReal - vL k r.toNNReal)⁻¹ =
      -(vL k u - vL k s) / 2 := fun k => by
    rw [h.vL_sub hsu hu k]
    have hfun : (fun r : ℝ => 2 / (vL k r.toNNReal - w r.toNNReal)) =
        fun r => -2 * (w r.toNNReal - vL k r.toNNReal)⁻¹ := funext fun r => two_div_sub_eq _ _
    rw [hfun, intervalIntegral.integral_const_mul]
    ring
  unfold spreadRate
  rw [intervalIntegral.integral_sub ((h.integrable_gapL hu i).mono_set hsub)
    ((h.integrable_gapL hu o).mono_set hsub), key i, key o]
  ring

/-- **(N7)** (Specification p. 27): while `ε ≤ Q = W − V^out ≤ M` on `[s, u]`, with
`0 < ε ≤ 1 ≤ M`, `∫ₛᵘ |1 + log Q| δᵢ ≤ ((1 + log M) Δᵢ(s) + 1)/2` for every left index `i`
(`Δᵢ = V^{i,L} − V^out`). The bound does not depend on `ε` or on the signs of the weights. Proof:
`|1 + log Q| ≤ 1 + log M + logCut ε Δᵢ` (as `Q ≥ max (Δᵢ, ε)`), `∫ δᵢ = ½ (Δᵢ(s) − Δᵢ(u))`, and
`∫ logCut ε (Δᵢ) δᵢ = ½ (Φ(Δᵢ(s)) − Φ(Δᵢ(u))) ≤ ½` by the chain rule for `Φ = logCutPrim ε`. -/
theorem integral_abs_one_add_log_mul_spreadRate_le {o i : Fin nL} (hio : i ≤ o) {s u : ℝ≥0}
    (hsu : s ≤ u) (hu : (u : ℝ≥0∞) < ζ) {ε M : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 1 ≤ M)
    (hQ : ∀ r : ℝ≥0, s ≤ r → r ≤ u → ε ≤ w r - vL o r ∧ w r - vL o r ≤ M) :
    ∫ r in (s : ℝ)..u, |1 + Real.log (w r.toNNReal - vL o r.toNNReal)| * spreadRate w vL o i r ≤
      ((1 + Real.log M) * (vL i s - vL o s) + 1) / 2 := by
  have hsu' : (s : ℝ) ≤ u := by exact_mod_cast hsu
  have hsub : uIcc (s : ℝ) u ⊆ uIcc 0 (u : ℝ) := by
    rw [uIcc_of_le hsu', uIcc_of_le (NNReal.coe_nonneg u)]
    exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl
  have hloc : ∀ r ∈ uIcc (s : ℝ) u,
      (r.toNNReal : ℝ≥0∞) < ζ ∧ s ≤ r.toNNReal ∧ r.toNNReal ≤ u := fun r hr => by
    rw [uIcc_of_le hsu'] at hr
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg s).trans hr.1
    have hru : r.toNNReal ≤ u := Real.toNNReal_le_iff_le_coe.2 hr.2
    exact ⟨lt_of_le_of_lt (by exact_mod_cast hru) hu, (Real.le_toNNReal_iff_coe_le hr0).2 hr.1, hru⟩
  have hmaps : MapsTo Real.toNNReal (uIcc (s : ℝ) u) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} :=
    fun r hr => (hloc r hr).1
  have hwc : ContinuousOn (fun r : ℝ => w r.toNNReal) (uIcc (s : ℝ) u) :=
    h.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps
  have hvc : ∀ k, ContinuousOn (fun r : ℝ => vL k r.toNNReal) (uIcc (s : ℝ) u) := fun k =>
    (h.continuousOn_vL k).comp continuous_real_toNNReal.continuousOn hmaps
  set Δ : ℝ → ℝ := fun r => vL i r.toNNReal - vL o r.toNNReal with hΔ
  have hδint : IntervalIntegrable (spreadRate w vL o i) volume s u :=
    (h.intervalIntegrable_spreadRate hu o i).mono_set hsub
  have hF : ContinuousOn (fun r : ℝ => |1 + Real.log (w r.toNNReal - vL o r.toNNReal)|)
      (uIcc (s : ℝ) u) := by
    refine (continuousOn_const.add (ContinuousOn.log (hwc.sub (hvc o)) fun r hr => ?_)).abs
    have := (hQ _ (hloc r hr).2.1 (hloc r hr).2.2).1
    exact (lt_of_lt_of_le hε this).ne'
  have hG : ContinuousOn (fun r => logCut ε (Δ r)) (uIcc (s : ℝ) u) :=
    (continuous_logCut hε).comp_continuousOn ((hvc i).sub (hvc o))
  have hint1 := hδint.continuousOn_mul hF
  have hint2 := hδint.continuousOn_mul hG
  have hae : (fun r => |1 + Real.log (w r.toNNReal - vL o r.toNNReal)| * spreadRate w vL o i r)
      ≤ᵐ[volume.restrict (Icc (s : ℝ) u)]
      fun r => (1 + Real.log M) * spreadRate w vL o i r + logCut ε (Δ r) * spreadRate w vL o i r := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h.volume_collisionL i)] with r hr hrI
    have hrI' : r ∈ uIcc (s : ℝ) u := by rwa [uIcc_of_le hsu']
    obtain ⟨hrζ, hsr, hru⟩ := hloc r hrI'
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg s).trans hrI.1
    have hne : w r.toNNReal ≠ vL i r.toNNReal := fun he => hr ⟨hr0, hrζ, he⟩
    have hpos : vL i r.toNNReal < w r.toNNReal := lt_of_le_of_ne (h.vL_le_w hrζ i) (Ne.symm hne)
    have hδ0 := spreadRate_nonneg hpos (h.antitone_vL hrζ hio)
    obtain ⟨hQε, hQM⟩ := hQ _ hsr hru
    have hQpos : 0 < w r.toNNReal - vL o r.toNNReal := lt_of_lt_of_le hε hQε
    have hΔQ : Δ r ≤ w r.toNNReal - vL o r.toNNReal := by simp only [hΔ]; linarith
    have hb : |1 + Real.log (w r.toNNReal - vL o r.toNNReal)| ≤
        1 + Real.log M + logCut ε (Δ r) := by
      have h1 := Real.log_le_log hQpos hQM
      have h2 := neg_log_le_logCut hε hQε hΔQ
      have h3 := logCut_nonneg ε (Δ r)
      have h4 := Real.log_nonneg hM
      rw [abs_le]
      constructor <;> linarith
    calc |1 + Real.log (w r.toNNReal - vL o r.toNNReal)| * spreadRate w vL o i r
        ≤ (1 + Real.log M + logCut ε (Δ r)) * spreadRate w vL o i r :=
          mul_le_mul_of_nonneg_right hb hδ0
      _ = _ := by ring
  have hmono := intervalIntegral.integral_mono_ae_restrict hsu' hint1
    ((hδint.const_mul _).add hint2) hae
  rw [intervalIntegral.integral_add (hδint.const_mul _) hint2, intervalIntegral.integral_const_mul,
    h.integral_spreadRate o i hsu hu] at hmono
  -- the chain rule for `logCutPrim ε ∘ Δ`
  have hchain : logCutPrim ε (Δ u) = logCutPrim ε (Δ s) +
      ∫ r in (s : ℝ)..u, ContinuousLinearMap.toSpanSingleton ℝ (logCut ε (Δ r))
        (-2 * spreadRate w vL o i r) := by
    refine Ito.comp_eq_add_integral_of_lipschitz (E := ℝ)
      (fun y => (hasDerivAt_logCutPrim hε y).hasFDerivAt) (lipschitzWith_logCutPrim hε hε1)
      (ContinuousLinearMap.toSpanSingletonCLE.continuous.comp (continuous_logCut hε))
      (hδint.const_mul _) fun t ht => ?_
    obtain ⟨htζ, hst, htu⟩ := hloc t ht
    rw [uIcc_of_le hsu'] at ht
    have ht0 : 0 ≤ t := (NNReal.coe_nonneg s).trans ht.1
    have := h.integral_spreadRate o i hst htζ
    rw [Real.coe_toNNReal _ ht0] at this
    rw [intervalIntegral.integral_const_mul, this]
    simp only [hΔ, Real.toNNReal_coe]
    ring
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hchain
  have hchain' : ∫ r in (s : ℝ)..u, logCut ε (Δ r) * spreadRate w vL o i r =
      (logCutPrim ε (Δ s) - logCutPrim ε (Δ u)) / 2 := by
    have e : ∫ r in (s : ℝ)..u, -2 * spreadRate w vL o i r * logCut ε (Δ r) =
        -2 * ∫ r in (s : ℝ)..u, logCut ε (Δ r) * spreadRate w vL o i r := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun r _ => by ring
    rw [e] at hchain
    linarith
  rw [hchain'] at hmono
  have hΔu : 0 ≤ Δ u := by
    simp only [hΔ, Real.toNNReal_coe]
    exact sub_nonneg.2 (h.antitone_vL hu hio)
  have hΦu := logCutPrim_nonneg ε hΔu
  have hΦs := logCutPrim_le_one hε hε1 (Δ s)
  have hlogM := Real.log_nonneg hM
  simp only [hΔ, Real.toNNReal_coe] at hΔu hΦu hΦs hmono ⊢
  nlinarith

end IsForcePath

end Sec2

end InteractingSLE
