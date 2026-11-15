/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalEscape
import InteractingSLE.Stochastic.Bessel.Comparison
import InteractingSLE.Spec.Sec2.AddMarksPath

/-!
# §7.3: growth of the cross-gap between opposite force coordinates

Packet PROVE-SEC7-C2. For a left force coordinate `V^L` and a right one `V^R` of an integrated force-point
evolution, the cross-gap `D = V^R − V^L = L + R` (`L = W − V^L`, `R = V^R − W`) satisfies
`dD = (2/L + 2/R) dt ≥ 8/D dt`, hence

  `D_t² ≥ D_σ² + 16 (t − σ)`  for `σ ≤ t < ζ`.

This is (IN2) of Aux. lemma 104 (`source/spec/p337-384.md` L322, "`D_t² ≥ 16t`"), the bound
"`dD/dt = 2/L + 2/R ≥ 8/D` … gives `D_t ≥ 4√t`" of Aux. lemma 103 (L305), "`D_t² ≥ D_σ² + 16(t − σ)`" of
Aux. lemma 112 (L656–L687, graph node "∣e_t∣ ≤ Bw/R_t² ≤ 4Bw/D_t², D_t² ≥ D_σ² + 16(t − σ)"), and "`D` is
increasing" of Aux. lemmas 101 and 103 (L292). The identity holds in its integrated form; the pointwise
bound `2/L + 2/R ≥ 8/(L + R)` is used off the Lebesgue-null collision sets.

* `sq_add_le_sq_of_eq_integral` (real analysis): if `Y = Y₀ + ∫ g` on `[0, T]`, `Y₀ ≥ 0`, and almost
  everywhere `Y > 0` and `g ≥ 8/Y`, then `Y₀² + 16T ≤ Y_T²` (comparison with `√(Y₀² + 16r)`,
  `Bessel.le_of_sub_eq_integral`).
* `Sec2.IsForcePath.crossGap_le`: `D` is nondecreasing before `ζ`.
* `Sec2.IsForcePath.crossGap_sub`: `D_t − D_σ = ∫_σ^t (2/(V^R − W) + 2/(W − V^L))`.
* **`Sec2.IsForcePath.sq_crossGap_add_le`**: `D_σ² + 16 (t − σ) ≤ D_t²`.
* `Sec2.IsForcePath.abs_vL_sub_le`, `abs_vR_sub_le`: a force coordinate moves at speed at most `2/g` while
  its gap to the driver is at least `g`.
* `Sec2.IsForcePath.abs_midpoint_sub_le`: on an interval where every force gap is at least `g`, the moving
  midpoint `X = W − (V^{i,L} + V^{j,R})/2` of Aux. lemma 103 satisfies
  `|X_q − X_p| ≤ √κ |B_q − B_p| + (∑|ρ|/g + 2/g)(q − p)`.
* **`Sec2.IsForcePath.exists_pos_midpoint_traversal_time`** (Aux. lemma 103, the non-accumulation of band
  switches): on `[0, T]` every traversal of `X` from `−c` to `c` with all gaps `≥ g` lasts at least some
  `δ > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

/-- For `c ≥ 0`, `s ↦ √(c + 16 s)` has derivative `8/√(c + 16 s)` at every `s > 0`. -/
theorem hasDerivAt_sqrt_add {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) :
    HasDerivAt (fun s : ℝ => Real.sqrt (c + 16 * s)) (8 / Real.sqrt (c + 16 * x)) x := by
  have hpos : 0 < c + 16 * x := by linarith
  have h1 : HasDerivAt (fun s : ℝ => c + 16 * s) 16 x := by
    simpa using ((hasDerivAt_id x).const_mul 16).const_add c
  have h2 := h1.sqrt hpos.ne'
  convert h2 using 1
  have hs : 0 < Real.sqrt (c + 16 * x) := Real.sqrt_pos.2 hpos
  field_simp
  norm_num

/-- For `c ≥ 0`, the derivative `8/√(c + 16 s)` is integrable on `[0, r]`, `r ≥ 0`. -/
theorem intervalIntegrable_eight_div_sqrt {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    IntervalIntegrable (fun s : ℝ => 8 / Real.sqrt (c + 16 * s)) volume 0 r := by
  have hcont : ContinuousOn (fun s : ℝ => Real.sqrt (c + 16 * s)) (Icc 0 r) :=
    (Real.continuous_sqrt.comp (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
  exact intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun s : ℝ => Real.sqrt (c + 16 * s))
    (by rw [uIcc_of_le hr]; exact hcont)
    (by rw [min_eq_left hr, max_eq_right hr]; exact fun x hx => hasDerivAt_sqrt_add hc hx.1)
    (by rw [min_eq_left hr, max_eq_right hr]
        exact fun x _ => div_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- `√(c + 16 r) = √c + ∫₀ʳ 8/√(c + 16 s)` for `c, r ≥ 0`. -/
theorem sqrt_add_eq_integral {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    Real.sqrt (c + 16 * r) = Real.sqrt (c + 16 * 0) +
      ∫ s in (0 : ℝ)..r, 8 / Real.sqrt (c + 16 * s) := by
  have hcont : ContinuousOn (fun s : ℝ => Real.sqrt (c + 16 * s)) (Icc 0 r) :=
    (Real.continuous_sqrt.comp (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr hcont
    (fun x hx => hasDerivAt_sqrt_add hc hx.1) (intervalIntegrable_eight_div_sqrt hc hr)]
  ring

/-- **Comparison with `√(Y₀² + 16r)`.** If `Y = Y₀ + ∫₀ʳ g` on `[0, T]` with `Y₀ ≥ 0`, and almost every
`s ∈ [0, T]` has `Y s > 0` and `g s ≥ 8 / Y s`, then `Y₀² + 16T ≤ Y_T²`. -/
theorem sq_add_le_sq_of_eq_integral {Y g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hY : ContinuousOn Y (Icc 0 T)) (hY0 : 0 ≤ Y 0) (hg : IntervalIntegrable g volume 0 T)
    (heq : ∀ r ∈ Icc (0 : ℝ) T, Y r = Y 0 + ∫ s in (0 : ℝ)..r, g s)
    (hbd : ∀ᵐ s ∂volume, s ∈ Icc (0 : ℝ) T → 0 < Y s ∧ 8 / Y s ≤ g s) :
    Y 0 ^ 2 + 16 * T ≤ Y T ^ 2 := by
  set c := Y 0 ^ 2 with hcdef
  have hc : 0 ≤ c := sq_nonneg _
  set X : ℝ → ℝ := fun r => Real.sqrt (c + 16 * r) with hX
  set f : ℝ → ℝ := fun r => 8 / Real.sqrt (c + 16 * r) with hf
  have hXc : ContinuousOn X (Icc 0 T) :=
    (Real.continuous_sqrt.comp (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
  have hfi : IntervalIntegrable f volume 0 T := intervalIntegrable_eight_div_sqrt hc hT
  have hX0 : X 0 = Y 0 := by
    simp only [hX, mul_zero, add_zero, hcdef]
    exact Real.sqrt_sq hY0
  have hle := Bessel.le_of_sub_eq_integral hXc hY hfi hg hX0.le (fun t ht => by
      rw [heq t ht, show X t = X 0 + ∫ s in (0 : ℝ)..t, f s from sqrt_add_eq_integral hc ht.1,
        intervalIntegral.integral_sub (hfi.mono_set ?_) (hg.mono_set ?_)]
      · ring
      · rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc_right ht.2
      · rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc_right ht.2)
    (by
      filter_upwards [hbd] with s hs hsI hlt
      obtain ⟨hYpos, hgs⟩ := hs hsI
      refine le_trans ?_ hgs
      exact div_le_div_of_nonneg_left (by norm_num) hYpos hlt.le) T ⟨hT, le_rfl⟩
  have hXT : X T = Real.sqrt (c + 16 * T) := rfl
  rw [hXT] at hle
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  rwa [Real.sq_sqrt (by positivity)] at hsq

/-- The arithmetic–harmonic mean bound `8/(L + R) ≤ 2/R + 2/L` for `L, R > 0`. -/
theorem eight_div_add_le {L R : ℝ} (hL : 0 < L) (hR : 0 < R) : 8 / (L + R) ≤ 2 / R + 2 / L := by
  rw [div_add_div _ _ hR.ne' hL.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (L - R), mul_pos hL hR]

end Sec7

namespace Sec2.IsForcePath

open Sec7

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- The cross-gap between a left and a right force coordinate is nonnegative before `ζ`. -/
theorem crossGap_nonneg (i : Fin nL) (j : Fin nR) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    0 ≤ vR j t - vL i t := by
  have h1 := h.vL_le_w ht i
  have h2 := h.w_le_vR ht j
  linarith

/-- The cross-gap is nondecreasing before `ζ` (Aux. lemmas 101, 103: "`D` is increasing"). -/
theorem crossGap_le (i : Fin nL) (j : Fin nR) {σ t : ℝ≥0} (hσt : σ ≤ t) (ht : (t : ℝ≥0∞) < ζ) :
    vR j σ - vL i σ ≤ vR j t - vL i t := by
  have h1 := h.le_vR_of_le hσt ht j
  have h2 := h.vL_le_of_le hσt ht i
  linarith

/-- The cross-gap equation `dD = (2/R + 2/L) dt` in integrated form on `[σ, t]`. -/
theorem crossGap_sub (i : Fin nL) (j : Fin nR) {σ t : ℝ≥0} (hσt : σ ≤ t) (ht : (t : ℝ≥0∞) < ζ) :
    (vR j t - vL i t) - (vR j σ - vL i σ) = ∫ r in (σ : ℝ)..t,
      (2 / (vR j r.toNNReal - w r.toNNReal) + 2 / (w r.toNNReal - vL i r.toNNReal)) := by
  have hσt' : (σ : ℝ) ≤ t := by exact_mod_cast hσt
  have hsub : uIcc (σ : ℝ) t ⊆ uIcc 0 t := by
    rw [uIcc_of_le hσt', uIcc_of_le (NNReal.coe_nonneg t)]
    exact Icc_subset_Icc (NNReal.coe_nonneg σ) le_rfl
  have iR := (h.intervalIntegrable_forceR ht j).mono_set hsub
  have iL := (h.intervalIntegrable_forceL ht i).mono_set hsub
  have hneg : ∀ r : ℝ, 2 / (w r.toNNReal - vL i r.toNNReal) = -(2 / (vL i r.toNNReal - w r.toNNReal)) :=
    fun r => by rw [← neg_sub, div_neg]
  simp_rw [hneg, ← sub_eq_add_neg]
  rw [intervalIntegral.integral_sub iR iL, ← h.vR_sub hσt ht j, ← h.vL_sub hσt ht i]
  ring

/-- **(IN2): growth of the cross-gap.** For a left force coordinate `V^{i,L}` and a right one
`V^{j,R}`, with `D = V^{j,R} − V^{i,L}`: `D_σ² + 16 (t − σ) ≤ D_t²` for `σ ≤ t < ζ` (Aux. lemma 104,
(IN2); Aux. lemma 103, `D_t ≥ 4√t` from `D_0 = 0`; Aux. lemma 112, `D_t² ≥ D_σ² + 16(t − σ)`). -/
theorem sq_crossGap_add_le (i : Fin nL) (j : Fin nR) {σ t : ℝ≥0} (hσt : σ ≤ t)
    (ht : (t : ℝ≥0∞) < ζ) :
    (vR j σ - vL i σ) ^ 2 + 16 * ((t : ℝ) - σ) ≤ (vR j t - vL i t) ^ 2 := by
  have hσt' : (σ : ℝ) ≤ t := by exact_mod_cast hσt
  set T : ℝ := (t : ℝ) - σ with hTdef
  have hT : 0 ≤ T := sub_nonneg.2 hσt'
  set D : ℝ → ℝ := fun u => vR j u.toNNReal - vL i u.toNNReal with hD
  set G : ℝ → ℝ := fun u =>
    2 / (vR j u.toNNReal - w u.toNNReal) + 2 / (w u.toNNReal - vL i u.toNNReal) with hG
  set Y : ℝ → ℝ := fun r => D ((σ : ℝ) + r) with hY
  set g : ℝ → ℝ := fun r => G ((σ : ℝ) + r) with hg
  -- times `σ + r`, `r ∈ [0, T]`, stay before `ζ`
  have hmem : ∀ r ∈ Icc (0 : ℝ) T, ((σ : ℝ) + r).toNNReal ≤ t ∧
      ((((σ : ℝ) + r).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := by
    intro r hr
    have hle : ((σ : ℝ) + r).toNNReal ≤ t := by
      rw [Real.toNNReal_le_iff_le_coe]; linarith [hr.2]
    exact ⟨hle, lt_of_le_of_lt (by exact_mod_cast hle) ht⟩
  have hY0 : Y 0 = vR j σ - vL i σ := by simp [hY, hD]
  have hYT : Y T = vR j t - vL i t := by simp [hY, hD, hTdef]
  -- continuity
  have hDc : ContinuousOn D (Icc 0 t) :=
    (Sec2.continuousOn_toNNReal (h.continuousOn_vR j) ht).sub
      (Sec2.continuousOn_toNNReal (h.continuousOn_vL i) ht)
  have hYc : ContinuousOn Y (Icc 0 T) := by
    refine hDc.comp (continuous_const.add continuous_id).continuousOn fun r hr => ?_
    exact ⟨by linarith [hr.1, NNReal.coe_nonneg σ], by linarith [hr.2]⟩
  -- integrability of `g` on `[0, T]`
  have hGi : IntervalIntegrable G volume σ t := by
    have hsub : uIcc (σ : ℝ) t ⊆ uIcc 0 t := by
      rw [uIcc_of_le hσt', uIcc_of_le (NNReal.coe_nonneg t)]
      exact Icc_subset_Icc (NNReal.coe_nonneg σ) le_rfl
    have iR := (h.intervalIntegrable_forceR ht j).mono_set hsub
    have iL := (h.intervalIntegrable_forceL ht i).mono_set hsub
    have hneg : ∀ r : ℝ, 2 / (w r.toNNReal - vL i r.toNNReal) =
        -(2 / (vL i r.toNNReal - w r.toNNReal)) := fun r => by rw [← neg_sub, div_neg]
    have hGeq : G = fun r : ℝ => 2 / (vR j r.toNNReal - w r.toNNReal) -
        2 / (vL i r.toNNReal - w r.toNNReal) := by
      funext r; rw [hG]; dsimp only; rw [hneg r]; ring
    rw [hGeq]
    exact iR.sub iL
  have hgi : IntervalIntegrable g volume 0 T := by
    have := hGi.comp_add_left (σ : ℝ)
    simpa [hg, hTdef] using this
  -- the integrated equation
  have heq : ∀ r ∈ Icc (0 : ℝ) T, Y r = Y 0 + ∫ s in (0 : ℝ)..r, g s := by
    intro r hr
    obtain ⟨hle, hlt⟩ := hmem r hr
    have hσle : σ ≤ ((σ : ℝ) + r).toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by linarith [hr.1, NNReal.coe_nonneg σ])]
      linarith [hr.1]
    have key := h.crossGap_sub i j hσle hlt
    have hco : ((((σ : ℝ) + r).toNNReal : ℝ≥0) : ℝ) = (σ : ℝ) + r :=
      Real.coe_toNNReal _ (by linarith [hr.1, NNReal.coe_nonneg σ])
    rw [hco] at key
    have hint : ∫ s in (0 : ℝ)..r, g s = ∫ u in (σ : ℝ)..((σ : ℝ) + r), G u := by
      simp only [hg]
      rw [intervalIntegral.integral_comp_add_left, add_zero]
    rw [hint, hY0]
    simp only [hY, hD, hG] at key ⊢
    linarith
  -- the pointwise bound off the collision sets
  have hbd : ∀ᵐ s ∂volume, s ∈ Icc (0 : ℝ) T → 0 < Y s ∧ 8 / Y s ≤ g s := by
    have hNL : volume ((fun s : ℝ => (σ : ℝ) + s) ⁻¹'
        {u : ℝ | 0 ≤ u ∧ (u.toNNReal : ℝ≥0∞) < ζ ∧ w u.toNNReal = vL i u.toNNReal}) = 0 := by
      rw [measure_preimage_add]; exact h.volume_collisionL i
    have hNR : volume ((fun s : ℝ => (σ : ℝ) + s) ⁻¹'
        {u : ℝ | 0 ≤ u ∧ (u.toNNReal : ℝ≥0∞) < ζ ∧ w u.toNNReal = vR j u.toNNReal}) = 0 := by
      rw [measure_preimage_add]; exact h.volume_collisionR j
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hNL, measure_eq_zero_iff_ae_notMem.1 hNR]
      with s hsL hsR hs
    obtain ⟨_, hlt⟩ := hmem s hs
    have hu0 : 0 ≤ (σ : ℝ) + s := by linarith [hs.1, NNReal.coe_nonneg σ]
    have hneL : w ((σ : ℝ) + s).toNNReal ≠ vL i ((σ : ℝ) + s).toNNReal := fun he =>
      hsL ⟨hu0, hlt, he⟩
    have hneR : w ((σ : ℝ) + s).toNNReal ≠ vR j ((σ : ℝ) + s).toNNReal := fun he =>
      hsR ⟨hu0, hlt, he⟩
    have hL : 0 < w ((σ : ℝ) + s).toNNReal - vL i ((σ : ℝ) + s).toNNReal :=
      lt_of_le_of_ne (sub_nonneg.2 (h.vL_le_w hlt i)) (fun he => hneL (sub_eq_zero.1 he.symm))
    have hR : 0 < vR j ((σ : ℝ) + s).toNNReal - w ((σ : ℝ) + s).toNNReal :=
      lt_of_le_of_ne (sub_nonneg.2 (h.w_le_vR hlt j)) (fun he => hneR (sub_eq_zero.1 he.symm).symm)
    have hYs : Y s = (w ((σ : ℝ) + s).toNNReal - vL i ((σ : ℝ) + s).toNNReal) +
        (vR j ((σ : ℝ) + s).toNNReal - w ((σ : ℝ) + s).toNNReal) := by
      simp only [hY, hD]; ring
    refine ⟨by rw [hYs]; positivity, ?_⟩
    rw [hYs]
    exact eight_div_add_le hL hR
  have hσζ : (σ : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hσt) ht
  have hY0' : 0 ≤ Y 0 := by rw [hY0]; exact h.crossGap_nonneg i j hσζ
  have key := sq_add_le_sq_of_eq_integral hT hYc hY0' hgi heq hbd
  rwa [hY0, hYT] at key

/-! ### Aux. lemma 103: band traversals of the moving midpoint take a positive time -/

/-- A force coordinate moves at speed at most `2/g` while its gap to the driver is at least `g`:
`|V_q − V_p| ≤ (2/g)(q − p)` (left marks). -/
theorem abs_vL_sub_le (i : Fin nL) {g : ℝ} (hg : 0 < g) {p q : ℝ≥0} (hpq : p ≤ q)
    (hq : (q : ℝ≥0∞) < ζ) (hgap : ∀ s : ℝ≥0, p ≤ s → s ≤ q → g ≤ w s - vL i s) :
    |vL i q - vL i p| ≤ 2 / g * ((q : ℝ) - p) := by
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  rw [h.vL_sub hpq hq i]
  have hint : ‖∫ r in (p : ℝ)..q, 2 / (vL i r.toNNReal - w r.toNNReal)‖ ≤ 2 / g * |(q : ℝ) - p| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    filter_upwards with r hr
    rw [uIoc_of_le hpq'] at hr
    have hp' : p ≤ r.toNNReal := (Real.lt_toNNReal_iff_coe_lt.2 hr.1).le
    have hq' : r.toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2 hr.2
    have hgr := hgap _ hp' hq'
    rw [Real.norm_eq_abs, abs_div, abs_two, abs_sub_comm]
    rw [abs_of_pos (hg.trans_le hgr)]
    exact div_le_div_of_nonneg_left (by norm_num) hg hgr
  rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hpq')] at hint

/-- A right force coordinate moves at speed at most `2/g` while its gap to the driver is at least `g`. -/
theorem abs_vR_sub_le (j : Fin nR) {g : ℝ} (hg : 0 < g) {p q : ℝ≥0} (hpq : p ≤ q)
    (hq : (q : ℝ≥0∞) < ζ) (hgap : ∀ s : ℝ≥0, p ≤ s → s ≤ q → g ≤ vR j s - w s) :
    |vR j q - vR j p| ≤ 2 / g * ((q : ℝ) - p) := by
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  rw [h.vR_sub hpq hq j]
  have hint : ‖∫ r in (p : ℝ)..q, 2 / (vR j r.toNNReal - w r.toNNReal)‖ ≤ 2 / g * |(q : ℝ) - p| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    filter_upwards with r hr
    rw [uIoc_of_le hpq'] at hr
    have hp' : p ≤ r.toNNReal := (Real.lt_toNNReal_iff_coe_lt.2 hr.1).le
    have hq' : r.toNNReal ≤ q := Real.toNNReal_le_iff_le_coe.2 hr.2
    have hgr := hgap _ hp' hq'
    rw [Real.norm_eq_abs, abs_div, abs_two, abs_of_pos (hg.trans_le hgr)]
    exact div_le_div_of_nonneg_left (by norm_num) hg hgr
  rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hpq')] at hint

/-- **Increment of the moving midpoint on a band** (Aux. lemma 103, L298: "On the band all force gaps are
at least `D₀/3`, so the driving drift is bounded by `3∑ᵢ|ρᵢ|/D₀`, and the velocities of both nearest marks
are bounded by `6/D₀`. Set `X = W − (V^{1,L} + V^{1,R})/2`. […] Its drift is uniformly bounded on that
traversal and its martingale part is `√κ B`"). If on `[p, q]` every force gap is at least `g > 0`, then
`|X_q − X_p| ≤ √a |b_q − b_p| + (∑|ρ|/g + 2/g)(q − p)` for `X = w − (v^{i,L} + v^{j,R})/2`. -/
theorem abs_midpoint_sub_le {a : ℝ} {b : ℝ≥0 → ℝ} (hw : DriverEq a ρL ρR w vL vR b ζ)
    (i : Fin nL) (j : Fin nR) {g : ℝ} (hg : 0 < g) {p q : ℝ≥0} (hpq : p ≤ q)
    (hq : (q : ℝ≥0∞) < ζ)
    (hgap : ∀ s : ℝ≥0, p ≤ s → s ≤ q → (∀ i, g ≤ w s - vL i s) ∧ ∀ j, g ≤ vR j s - w s) :
    |(w q - (vL i q + vR j q) / 2) - (w p - (vL i p + vR j p) / 2)| ≤
      Real.sqrt a * |b q - b p| + ((∑ i, |ρL i| + ∑ j, |ρR j|) / g + 2 / g) * ((q : ℝ) - p) := by
  have hw' := h.abs_w_sub_le hw hpq hq (C := (∑ i, |ρL i| + ∑ j, |ρR j|) / g) fun r hpr hrq => by
    have hp' : p ≤ r.toNNReal := (Real.lt_toNNReal_iff_coe_lt.2 hpr).le
    have hq' : r.toNNReal ≤ q :=
      ((Real.toNNReal_lt_iff_lt_coe ((NNReal.coe_nonneg p).trans hpr.le)).2 hrq).le
    obtain ⟨hL, hR⟩ := hgap _ hp' hq'
    exact abs_driverDrift_le (L := w r.toNNReal - g) (R := w r.toNNReal + g) hg
      (fun i => by linarith [hL i]) (fun j => by linarith [hR j]) (by linarith) (by linarith)
  have hL := h.abs_vL_sub_le i hg hpq hq fun s h1 h2 => (hgap s h1 h2).1 i
  have hR := h.abs_vR_sub_le j hg hpq hq fun s h1 h2 => (hgap s h1 h2).2 j
  have hsplit : (w q - (vL i q + vR j q) / 2) - (w p - (vL i p + vR j p) / 2) =
      (w q - w p) - ((vL i q - vL i p) + (vR j q - vR j p)) / 2 := by ring
  rw [hsplit]
  have h1 := abs_sub (w q - w p) (((vL i q - vL i p) + (vR j q - vR j p)) / 2)
  have h2 : |((vL i q - vL i p) + (vR j q - vR j p)) / 2| ≤
      (|vL i q - vL i p| + |vR j q - vR j p|) / 2 := by
    rw [abs_div, abs_two]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have hqp : (0 : ℝ) ≤ (q : ℝ) - p := sub_nonneg.2 (by exact_mod_cast hpq)
  nlinarith

/-- **Band traversals take a positive time** (Aux. lemma 103, L298: "Uniform continuity of Brownian
motion on each bounded physical-time interval therefore gives a strictly positive lower bound for the
duration of each such traversal. Infinitely many switches cannot occur before a finite time"). For `b`
continuous on `[0, T]`, gap level `g > 0` and band half-width `c > 0`, there is `δ > 0` such that every
traversal of the moving midpoint `X = w − (v^{i,L} + v^{j,R})/2` from `X ≤ −c` to `X ≥ c` within
`[0, T]` before `ζ`, during which all force gaps are at least `g`, lasts at least `δ`. -/
theorem exists_pos_midpoint_traversal_time {a : ℝ} {b : ℝ≥0 → ℝ}
    (hw : DriverEq a ρL ρR w vL vR b ζ) {T : ℝ≥0} (hb : ContinuousOn b (Icc 0 T)) (i : Fin nL)
    (j : Fin nR) {g c : ℝ} (hg : 0 < g) (hc : 0 < c) :
    ∃ δ > 0, ∀ p q : ℝ≥0, p ≤ q → q ≤ T → (q : ℝ≥0∞) < ζ →
      (∀ s : ℝ≥0, p ≤ s → s ≤ q → (∀ i, g ≤ w s - vL i s) ∧ ∀ j, g ≤ vR j s - w s) →
      w p - (vL i p + vR j p) / 2 ≤ -c → c ≤ w q - (vL i q + vR j q) / 2 → δ ≤ (q : ℝ) - p := by
  set K := (∑ i, |ρL i| + ∑ j, |ρR j|) / g + 2 / g with hK
  have hK0 : 0 ≤ K := add_nonneg (div_nonneg (add_nonneg
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)) hg.le)
    (div_nonneg (by norm_num) hg.le)
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hb
  rw [Metric.uniformContinuousOn_iff] at huc
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := huc (c / (Real.sqrt a + 1)) (by positivity)
  refine ⟨min δ₁ (c / (K + 1)), lt_min hδ₁ (by positivity),
    fun p q hpq hqT hqζ hgap hp hq => ?_⟩
  by_contra hcon
  have hqp : (q : ℝ) - p < min δ₁ (c / (K + 1)) := not_le.1 hcon
  have hest := h.abs_midpoint_sub_le hw i j hg hpq hqζ hgap
  rw [← hK] at hest
  have hqp0 : (0 : ℝ) ≤ (q : ℝ) - p := sub_nonneg.2 (by exact_mod_cast hpq)
  have hbqp : |b q - b p| < c / (Real.sqrt a + 1) := by
    have hdist : dist q p < δ₁ := by
      rw [NNReal.dist_eq, abs_of_nonneg hqp0]
      exact hqp.trans_le (min_le_left _ _)
    have := hδ₁b q ⟨zero_le, hqT⟩ p ⟨zero_le, hpq.trans hqT⟩ hdist
    rwa [Real.dist_eq] at this
  have h2 : Real.sqrt a * |b q - b p| < c := by
    calc Real.sqrt a * |b q - b p| ≤ (Real.sqrt a + 1) * |b q - b p| := by
          nlinarith [abs_nonneg (b q - b p)]
      _ < (Real.sqrt a + 1) * (c / (Real.sqrt a + 1)) :=
          mul_lt_mul_of_pos_left hbqp (by positivity)
      _ = c := by field_simp
  have h3 : K * ((q : ℝ) - p) < c := by
    calc K * ((q : ℝ) - p) ≤ K * (c / (K + 1)) :=
          mul_le_mul_of_nonneg_left (hqp.le.trans (min_le_right _ _)) hK0
      _ < c := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  have hX : 2 * c ≤ |(w q - (vL i q + vR j q) / 2) - (w p - (vL i p + vR j p) / 2)| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  linarith

end Sec2.IsForcePath

end InteractingSLE
