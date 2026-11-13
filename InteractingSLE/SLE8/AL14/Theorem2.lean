import InteractingSLE.SLE8.AL14.DerivComparison
import QuantumZipper.Proofs.RS.TraceGrid
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.ItoLite.Oscillation
import Mathlib.Analysis.PSeries

/-!
# [AL14] Theorem 2 (the SLE₈ note's (2.4))

Sources: Alvisio–Lawler [AL14], `source/external/AL14/AL14.md` (anchors `thm-2`, `thm-2-proof`,
`cor-2`, `id-Dn`, §2.2 (6)–(8)); the SLE₈ note `source/sle8-continuity.pdf`, proof of Lemma 2.1
(anchor `lem-2.1-proof`, display (2.4)); `planning/EXT-S8.md` (X3, "Robustness").

With `F̄_t = barInv B t` ([AL14]'s `f_t`, normalization `∂_t ḡ = (1/4)/(ḡ − B_t)`), `y_k = 2^{-k}`,
`Δ_{j,k}` (`incDelta`), `D_k` (`derivGridMax`) and `D_k^* = max_j Δ_{j,k}^p |F̄'_{j y_k²}(i y_k)|`
(`derivGridMaxStar p`, printed with `p = 4`) as in (2.2)–(2.3) of the note:

**Theorem 2.** For every `b` and every exponent `p` there is a deterministic `C` such that almost
surely, for all large `k`, `D_k^* ≤ C (2^k k^{-b} + (log k)^{p/2} D_k)`.

For `p = 4` this is (2.4) verbatim. The exponent `p` is free because [AL14] Lemma 1 is proved with a
non-sharp power (`alExp` in `DerivComparison.lean`); the proof below works for every `p`, with the
factor `(log k)^{p/2}` in place of `(log k)²` (`planning/EXT-S8.md`, X3 "Robustness").

## Proof ([AL14] §3.1)

* **Corollary 2** ((13)): `P(|F̄_t'(iy)| > θ) ≤ θ^{-2}`. This is QuantumZipper's Rohde–Schramm
  tail bound `RS.rs_tail_bound_axis` at `κ = 8`, `r = 1/2` (where `λ + ζ = 2`), applied to the
  time-reversed Brownian motion (`RS.deriv_fwdMapInv_eq_deriv_revMap_revBM`,
  `UnzipInvariance.isBrownianReal_revBM`). It replaces [AL14]'s route (Propositions 2–4) by the
  same supermartingale bound in QuantumZipper's form.
* **(6)**: `P(Δ_{j,k} > 1 + x) ≤ 2 e^{-x²/2}` (`BMOsc.bmOsc_tail` for the shifted motion).
* **Independence**: `|F̄'_{j y_k²}(i y_k)|` is a function of the reversed past `(B_{t−u} − B_t)_{u ≤ t}`
  and `Δ_{j,k}` of the future increments (`IsPreBrownianReal.indepFun_shift`).
* **Borel–Cantelli** over the events `{|F̄'| > θ_k, Δ > 1 + √(2γ log k)}` and `{Δ > 1 + 2√k}`,
  `θ_k = 2^k k^{-(b'+p)}`, `b' = ⌈b⌉₊`, `γ = 2b' + 2p + 2`, and the deterministic case split.

## Main results

* `measure_lt_norm_deriv_barInv_le`: [AL14] Corollary 2 at the grid heights.
* `measure_incDelta_gt_le`: [AL14] (6).
* `measure_lt_norm_deriv_barInv_and_lt_incDelta_le`: the product bound from independence.
* `exists_ae_eventually_derivGridMaxStar_le`: [AL14] Theorem 2 (with exponent `p`).
-/

noncomputable section

open Complex Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
open QuantumZipper

namespace InteractingSLE.SLE8.AL14

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## [AL14] Corollary 2: `P(|F̄_t'(iy)| > θ) ≤ θ^{-2}` -/

theorem rsLam_eight_half : RS.rsLam 8 (1 / 2) = 2 := by
  norm_num [RS.rsLam]

theorem rsZeta_eight_half : RS.rsZeta 8 (1 / 2) = 0 := by
  norm_num [RS.rsZeta]

/-- **[AL14] Corollary 2, reverse-flow form** (QuantumZipper's `RS.rs_tail_bound_axis` at `κ = 8`,
`r = 1/2`): for a Brownian motion `B`, `P(|h_T'(iw)| > θ) ≤ θ^{-2}` for the reverse map `h_T`
driven by `√8 B`, at any height `w > 0` with `w ≠ 1`. -/
theorem measure_lt_norm_deriv_revMap_le {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {T : ℝ}
    (hT : 0 ≤ T) {w : ℝ} (hw : 0 < w) (hw1 : w ≠ 1) {θ : ℝ} (hθ : 0 < θ) :
    P {ω | θ < ‖deriv (revMap (drive 8 B ω) T) ((w : ℂ) * I)‖} ≤ ENNReal.ofReal ((θ ^ 2)⁻¹) := by
  have hlog : Real.log w ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.1 h with h | h | h
    · exact hw.ne' h
    · exact hw1 h
    · linarith
  have h := RS.rs_tail_bound_axis (B := B) hB (by norm_num : (0 : ℝ) < 8)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hT hw (by rw [rsLam_eight_half]; norm_num)
    (by rw [rsZeta_eight_half]) (1 + Real.log θ / Real.log w)
  have e1 : w ^ (1 + Real.log θ / Real.log w - 1) = θ := by
    rw [show 1 + Real.log θ / Real.log w - 1 = Real.log θ / Real.log w by ring,
      Real.rpow_def_of_pos hw, show Real.log w * (Real.log θ / Real.log w) = Real.log θ by
        field_simp, Real.exp_log hθ]
  have e2 : w ^ ((1 - (1 + Real.log θ / Real.log w)) * (RS.rsLam 8 (1 / 2) + RS.rsZeta 8 (1 / 2))) =
      (θ ^ 2)⁻¹ := by
    rw [rsLam_eight_half, rsZeta_eight_half,
      show (1 - (1 + Real.log θ / Real.log w)) * (2 + 0) =
        (1 + Real.log θ / Real.log w - 1) * (-2 : ℝ) by ring,
      Real.rpow_mul hw.le, e1, Real.rpow_neg hθ.le, Real.rpow_two]
  rwa [e1, e2] at h

/-- **[AL14] Corollary 2, forward form**: for a Brownian motion `B`, `P(|F_T'(iw)| > θ) ≤ θ^{-2}`
for the centered inverse Loewner map `F_T` driven by `√8 B`, at any height `w > 0`, `w ≠ 1`. -/
theorem measure_lt_norm_deriv_fwdMapInv_le {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {T : ℝ}
    (hT : 0 ≤ T) {w : ℝ} (hw : 0 < w) (hw1 : w ≠ 1) {θ : ℝ} (hθ : 0 < θ) :
    P {ω | θ < ‖deriv (fwdMapInv (drive 8 B ω) T) ((w : ℂ) * I)‖} ≤
      ENNReal.ofReal ((θ ^ 2)⁻¹) := by
  obtain ⟨B'', -, hBc, hB0, hB'', hae⟩ := RS.exists_good_version0 hB
  have hrev := UnzipInvariance.isBrownianReal_revBM hB''.toIsPreBrownianReal hBc T.toNNReal
  calc P {ω | θ < ‖deriv (fwdMapInv (drive 8 B ω) T) ((w : ℂ) * I)‖}
      = P {ω | θ < ‖deriv (revMap (drive 8 (UnzipInvariance.revBM B'' T.toNNReal) ω) T)
          ((w : ℂ) * I)‖} := by
        refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
        filter_upwards [hae] with ω hω
        have hd : drive 8 B ω = drive 8 B'' ω := funext fun r => by simp only [drive, hω]
        show _ < _ ↔ _ < _
        rw [hd, RS.deriv_fwdMapInv_eq_deriv_revMap_revBM 8 hT (hBc ω) (hB0 ω) (RS.mul_I_mem_H hw)]
    _ ≤ ENNReal.ofReal ((θ ^ 2)⁻¹) := measure_lt_norm_deriv_revMap_le hrev hT hw hw1 hθ

omit [MeasurableSpace Ω] in
/-- `F̄_t'(iy) = F_t'(i √8 y)` for the note's driver, as a derivative of QuantumZipper's map. -/
theorem deriv_barInv_eq_deriv_fwdMapInv_drive (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (t y : ℝ) :
    deriv (barInv (fun r => B r.toNNReal ω) t) ((y : ℂ) * I) =
      deriv (fwdMapInv (drive 8 B ω) t) (((Real.sqrt 8 * y : ℝ) : ℂ) * I) := by
  rw [deriv_barInv]
  show deriv (fwdMapInv (drive 8 B ω) t) _ = _
  congr 1
  push_cast
  ring

/-- **[AL14] Corollary 2** ((13)) for [AL14]'s map `F̄_t = barInv B t`: for a Brownian motion `B`,
`t ≥ 0`, `y > 0` with `√8 y ≠ 1` and `θ > 0`, `P(|F̄_t'(iy)| > θ) ≤ θ^{-2}`. -/
theorem measure_lt_norm_deriv_barInv_le {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {t : ℝ}
    (ht : 0 ≤ t) {y : ℝ} (hy : 0 < y) (hy8 : Real.sqrt 8 * y ≠ 1) {θ : ℝ} (hθ : 0 < θ) :
    P {ω | θ < ‖deriv (barInv (fun r => B r.toNNReal ω) t) ((y : ℂ) * I)‖} ≤
      ENNReal.ofReal ((θ ^ 2)⁻¹) := by
  simp_rw [deriv_barInv_eq_deriv_fwdMapInv_drive]
  exact measure_lt_norm_deriv_fwdMapInv_le hB ht (by positivity) hy8 hθ

/-! ## [AL14] (6): the Brownian oscillation `Δ_{j,k}` -/

omit [MeasurableSpace Ω] in
/-- For a continuous path, each increment on `[t, t + s]` is at most QuantumZipper's oscillation
`bmOsc B t s`. -/
theorem abs_sub_le_bmOsc {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) {t s r : ℝ≥0}
    (hr : r ∈ Icc t (t + s)) : |B r ω - B t ω| ≤ bmOsc B t s ω := by
  rw [bmOsc_eq_iSup_subtype (mΩ := ⊤) hc]
  have : CompactSpace (Icc t (t + s)) := isCompact_iff_compactSpace.1 isCompact_Icc
  have hcont : Continuous fun x : Icc t (t + s) => |B x ω - B t ω| :=
    ((hc.comp continuous_subtype_val).sub continuous_const).abs
  exact le_ciSup (isCompact_range hcont).bddAbove (⟨r, hr⟩ : Icc t (t + s))

omit [MeasurableSpace Ω] in
/-- `Δ_{j,k} ≤ 1 + y_k⁻¹ osc`, where `osc` is the oscillation on `[0, y_k²]` of the shifted path
`u ↦ B_{j y_k² + u} − B_{j y_k²}`. -/
theorem incDelta_le_one_add_bmOsc {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) (k j : ℕ) :
    incDelta (fun r => B r.toNNReal ω) k j ≤ 1 + (alHeight k)⁻¹ *
      bmOsc (fun u ω => B ((alTime k j).toNNReal + u) ω - B (alTime k j).toNNReal ω) 0
        (alHeight k ^ 2).toNNReal ω := by
  have ht := alTime_nonneg k j
  have hsup : sSup ((fun u => |B u.toNNReal ω - B (alTime k j).toNNReal ω|) ''
      Icc (alTime k j) ((j + 1) * alHeight k ^ 2)) ≤
      bmOsc (fun u ω => B ((alTime k j).toNNReal + u) ω - B (alTime k j).toNNReal ω) 0
        (alHeight k ^ 2).toNNReal ω := by
    have hne : (Icc (alTime k j) ((j + 1) * alHeight k ^ 2)).Nonempty := by
      refine ⟨alTime k j, le_rfl, ?_⟩
      unfold alTime
      nlinarith [sq_nonneg (alHeight k)]
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨u, hu, rfl⟩
    have hτu : (alTime k j).toNNReal ≤ u.toNNReal := Real.toNNReal_le_toNNReal hu.1
    have hc' : Continuous fun v => B ((alTime k j).toNNReal + v) ω - B (alTime k j).toNNReal ω :=
      (hc.comp (continuous_const.add continuous_id)).sub continuous_const
    have hmem : u.toNNReal - (alTime k j).toNNReal ∈ Icc (0 : ℝ≥0) (0 + (alHeight k ^ 2).toNNReal) := by
      refine ⟨zero_le, ?_⟩
      rw [zero_add, ← NNReal.coe_le_coe, NNReal.coe_sub hτu, Real.coe_toNNReal _ (ht.trans hu.1),
        Real.coe_toNNReal _ ht, Real.coe_toNNReal _ (sq_nonneg _)]
      have e : ((j : ℝ) + 1) * alHeight k ^ 2 = alTime k j + alHeight k ^ 2 := by
        unfold alTime
        ring
      linarith [hu.2]
    have h := abs_sub_le_bmOsc hc' hmem
    simp only [add_zero, sub_self, sub_zero, add_tsub_cancel_of_le hτu] at h
    exact h
  unfold incDelta
  exact (add_le_add_iff_left 1).2 (mul_le_mul_of_nonneg_left hsup (inv_nonneg.2 (alHeight_pos k).le))

omit [MeasurableSpace Ω] in
/-- `1 + x < Δ_{j,k}` forces the shifted oscillation on `[0, y_k²]` to exceed `x y_k`. -/
theorem lt_bmOsc_of_lt_incDelta {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω)) {k j : ℕ}
    {x : ℝ} (h : 1 + x < incDelta (fun r => B r.toNNReal ω) k j) :
    x * alHeight k < bmOsc (fun u ω => B ((alTime k j).toNNReal + u) ω - B (alTime k j).toNNReal ω)
      0 (alHeight k ^ 2).toNNReal ω := by
  have hy := alHeight_pos k
  have h1 := h.trans_le (incDelta_le_one_add_bmOsc hc k j)
  have h2 : x < (alHeight k)⁻¹ * bmOsc (fun u ω => B ((alTime k j).toNNReal + u) ω -
      B (alTime k j).toNNReal ω) 0 (alHeight k ^ 2).toNNReal ω := by linarith
  rw [lt_inv_mul_iff₀ hy] at h2
  linarith [mul_comm x (alHeight k)]

/-- The Gaussian tail of the shifted oscillation (QuantumZipper's `BMOsc.bmOsc_tail`):
`P(osc_{[0, y_k²]} > x y_k) ≤ 2 e^{-x²/2}`. -/
theorem measure_lt_bmOsc_shift_le {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (B · ω)) (hB : IsBrownianReal B P) (k j : ℕ) {x : ℝ} (hx : 0 < x) :
    P {ω | x * alHeight k < bmOsc (fun u ω => B ((alTime k j).toNNReal + u) ω -
        B (alTime k j).toNNReal ω) 0 (alHeight k ^ 2).toNNReal ω} ≤
      ENNReal.ofReal (2 * Real.exp (-x ^ 2 / 2)) := by
  have hy := alHeight_pos k
  set τ := (alTime k j).toNNReal
  have hs : 0 < (alHeight k ^ 2).toNNReal := Real.toNNReal_pos.2 (by positivity)
  have hXc : ∀ ω, Continuous fun v => B (τ + v) ω - B τ ω := fun ω =>
    ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have h := BMOsc.bmOsc_tail (hB.toIsPreBrownianReal.shift τ) (fun r => (hBm _).sub (hBm _)) hXc 0
    _ hs (a := x * alHeight k) (by positivity)
  have e : -(x * alHeight k) ^ 2 / (2 * ((alHeight k ^ 2).toNNReal : ℝ)) = -x ^ 2 / 2 := by
    rw [Real.coe_toNNReal _ (sq_nonneg _)]
    field_simp
  rwa [e] at h

/-- **[AL14] (6)** for a Brownian motion with continuous measurable paths:
`P(Δ_{j,k} > 1 + x) ≤ 2 e^{-x²/2}` for `x > 0`. -/
theorem measure_incDelta_gt_le_of_forall_continuous {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (B · ω)) (hB : IsBrownianReal B P) (k j : ℕ) {x : ℝ} (hx : 0 < x) :
    P {ω | 1 + x < incDelta (fun r => B r.toNNReal ω) k j} ≤
      ENNReal.ofReal (2 * Real.exp (-x ^ 2 / 2)) :=
  (measure_mono fun _ hω => lt_bmOsc_of_lt_incDelta (hc _) hω).trans
    (measure_lt_bmOsc_shift_le hBm hc hB k j hx)

/-! ## Independence of the grid derivative and the following oscillation -/

omit [MeasurableSpace Ω] in
/-- On `[0, t]`, the driver of QuantumZipper's time-reversed motion `revBM B t` is the reversed past
`u ↦ √κ (B_{t−u} − B_t)`, so the two reverse maps at time `t` agree. -/
theorem revMap_drive_revBM_eq (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) :
    revMap (drive κ (UnzipInvariance.revBM B t.toNNReal) ω) t =
      revMap (drive κ (fun u ω => B (t.toNNReal - u) ω - B t.toNNReal ω) ω) t := by
  funext z
  refine ReverseFlow.revMap_congr_drive z fun u hu => ?_
  have hu' : u.toNNReal ≤ t.toNNReal := Real.toNNReal_le_toNNReal hu.2
  simp only [drive, UnzipInvariance.revBM_apply, max_eq_right hu']
  ring

omit [MeasurableSpace Ω] in
/-- For a continuous path with `B 0 = 0`, `F̄_t'(iy)` is the derivative at `i √8 y` of the reverse
map driven by the reversed past `u ↦ √8 (B_{t−u} − B_t)` (QuantumZipper's
`RS.deriv_fwdMapInv_eq_deriv_revMap_revBM`). -/
theorem deriv_barInv_eq_deriv_revMap_past {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω))
    (h0 : B 0 ω = 0) {t : ℝ} (ht : 0 ≤ t) {y : ℝ} (hy : 0 < y) :
    deriv (barInv (fun r => B r.toNNReal ω) t) ((y : ℂ) * I) =
      deriv (revMap (drive 8 (fun u ω => B (t.toNNReal - u) ω - B t.toNNReal ω) ω) t)
        (((Real.sqrt 8 * y : ℝ) : ℂ) * I) := by
  let _ : MeasurableSpace Ω := ⊤
  rw [deriv_barInv_eq_deriv_fwdMapInv_drive,
    RS.deriv_fwdMapInv_eq_deriv_revMap_revBM 8 ht hc h0 (RS.mul_I_mem_H (by positivity)),
    revMap_drive_revBM_eq]

/-- **The independence step of [AL14] §3.1.** For a Brownian motion with continuous measurable paths
and `B 0 = 0`, at a grid time `t = j y_k²` with `√8 y_k ≠ 1`, and `θ, x > 0`:
`P(|F̄_t'(i y_k)| > θ, Δ_{j,k} > 1 + x) ≤ θ^{-2} · 2 e^{-x²/2}`. The derivative is a function of the
past `(B_r)_{r ≤ t}` and the oscillation bounding `Δ_{j,k}` a function of the increments after `t`,
which are independent (`IsPreBrownianReal.indepFun_shift`). -/
theorem measure_lt_norm_deriv_barInv_and_lt_incDelta_le_of_forall_continuous {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (B · ω)) (h0 : ∀ ω, B 0 ω = 0)
    (hB : IsBrownianReal B P) (k j : ℕ) (hk : Real.sqrt 8 * alHeight k ≠ 1) {θ x : ℝ}
    (hθ : 0 < θ) (hx : 0 < x) :
    P {ω | θ < ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime k j)) ((alHeight k : ℂ) * I)‖ ∧
        1 + x < incDelta (fun r => B r.toNNReal ω) k j} ≤
      ENNReal.ofReal ((θ ^ 2)⁻¹) * ENNReal.ofReal (2 * Real.exp (-x ^ 2 / 2)) := by
  have ht := alTime_nonneg k j
  have hy := alHeight_pos k
  have hw0 : 0 < Real.sqrt 8 * alHeight k := by positivity
  -- the past `π` and the future increments `ξ` at `τ = t`
  have hRm : ∀ u : ℝ≥0, Measurable[MeasurableSpace.comap
      (fun ω (r : Iic (alTime k j).toNNReal) => B r ω) MeasurableSpace.pi]
      (fun ω => B ((alTime k j).toNNReal - u) ω - B (alTime k j).toNNReal ω) := fun u => by
    have h := ((measurable_pi_apply
      (⟨(alTime k j).toNNReal - u, mem_Iic.2 tsub_le_self⟩ : Iic (alTime k j).toNNReal)).sub
      (measurable_pi_apply (⟨(alTime k j).toNNReal, mem_Iic.2 le_rfl⟩ : Iic (alTime k j).toNNReal))).comp
      (comap_measurable (m := MeasurableSpace.pi)
        (fun ω (r : Iic (alTime k j).toNNReal) => B r ω))
    exact h
  have hRc : ∀ ω, Continuous fun u => B ((alTime k j).toNNReal - u) ω - B (alTime k j).toNNReal ω :=
    fun ω => ((hc ω).comp (continuous_const.sub continuous_id)).sub continuous_const
  have hAm : MeasurableSet[MeasurableSpace.comap
      (fun ω (r : Iic (alTime k j).toNNReal) => B r ω) MeasurableSpace.pi]
      {ω | θ < ‖deriv (revMap (drive 8 (fun u ω => B ((alTime k j).toNNReal - u) ω -
        B (alTime k j).toNNReal ω) ω) (alTime k j)) (((Real.sqrt 8 * alHeight k : ℝ) : ℂ) * I)‖} :=
    (measurable_norm.comp (@RS.measurable_deriv_revMap_drive Ω (MeasurableSpace.comap
      (fun ω (r : Iic (alTime k j).toNNReal) => B r ω) MeasurableSpace.pi) 8 _ hRm hRc _
      (RS.mul_I_mem_H hw0) _ ht)) measurableSet_Ioi
  have hXm : ∀ u : ℝ≥0, Measurable[MeasurableSpace.comap
      (fun ω u => B ((alTime k j).toNNReal + u) ω - B (alTime k j).toNNReal ω) MeasurableSpace.pi]
      (fun ω => B ((alTime k j).toNNReal + u) ω - B (alTime k j).toNNReal ω) := fun u => by
    have h := (measurable_pi_apply u).comp (comap_measurable (m := MeasurableSpace.pi)
      (fun ω u => B ((alTime k j).toNNReal + u) ω - B (alTime k j).toNNReal ω))
    exact h
  have hXc : ∀ ω, Continuous fun u => B ((alTime k j).toNNReal + u) ω - B (alTime k j).toNNReal ω :=
    fun ω => ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hDm : MeasurableSet[MeasurableSpace.comap
      (fun ω u => B ((alTime k j).toNNReal + u) ω - B (alTime k j).toNNReal ω) MeasurableSpace.pi]
      {ω | x * alHeight k < bmOsc (fun u ω => B ((alTime k j).toNNReal + u) ω -
        B (alTime k j).toNNReal ω) 0 (alHeight k ^ 2).toNNReal ω} :=
    measurable_bmOsc (mΩ := MeasurableSpace.comap
      (fun ω u => B ((alTime k j).toNNReal + u) ω - B (alTime k j).toNNReal ω) MeasurableSpace.pi)
      hXm hXc 0 _ measurableSet_Ioi
  obtain ⟨A', hA', hA'e⟩ := MeasurableSpace.measurableSet_comap.1 hAm
  obtain ⟨D', hD', hD'e⟩ := MeasurableSpace.measurableSet_comap.1 hDm
  have hprod := (indepFun_iff_measure_inter_preimage_eq_mul.1
    (hB.toIsPreBrownianReal.indepFun_shift (alTime k j).toNNReal)) D' A' hD' hA'
  rw [hD'e, hA'e] at hprod
  -- the derivative event under the reversed past has the Corollary 2 bound
  have hPA : P {ω | θ < ‖deriv (revMap (drive 8 (fun u ω => B ((alTime k j).toNNReal - u) ω -
      B (alTime k j).toNNReal ω) ω) (alTime k j)) (((Real.sqrt 8 * alHeight k : ℝ) : ℂ) * I)‖} ≤
      ENNReal.ofReal ((θ ^ 2)⁻¹) := by
    simp_rw [← revMap_drive_revBM_eq]
    exact measure_lt_norm_deriv_revMap_le
      (UnzipInvariance.isBrownianReal_revBM hB.toIsPreBrownianReal hc _) ht hw0 hk hθ
  have hsub : {ω | θ < ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime k j)) ((alHeight k : ℂ) * I)‖ ∧
      1 + x < incDelta (fun r => B r.toNNReal ω) k j} ⊆
      {ω | x * alHeight k < bmOsc (fun u ω => B ((alTime k j).toNNReal + u) ω -
        B (alTime k j).toNNReal ω) 0 (alHeight k ^ 2).toNNReal ω} ∩
      {ω | θ < ‖deriv (revMap (drive 8 (fun u ω => B ((alTime k j).toNNReal - u) ω -
        B (alTime k j).toNNReal ω) ω) (alTime k j)) (((Real.sqrt 8 * alHeight k : ℝ) : ℂ) * I)‖} := by
    rintro ω ⟨h1, h2⟩
    refine ⟨lt_bmOsc_of_lt_incDelta (hc ω) h2, ?_⟩
    rw [deriv_barInv_eq_deriv_revMap_past (hc ω) (h0 ω) ht hy] at h1
    exact h1
  calc _ ≤ _ := measure_mono hsub
    _ = _ := hprod
    _ ≤ ENNReal.ofReal (2 * Real.exp (-x ^ 2 / 2)) * ENNReal.ofReal ((θ ^ 2)⁻¹) :=
        mul_le_mul' (measure_lt_bmOsc_shift_le hBm hc hB k j hx) hPA
    _ = _ := mul_comm _ _

/-! ## Real-number bookkeeping for the Borel–Cantelli sum -/

/-- `√8 y_k ≠ 1` for `k ≥ 2` (the height `√8 y_k` where Corollary 2 is applied). -/
theorem sqrt_eight_mul_alHeight_ne_one {k : ℕ} (hk : 2 ≤ k) : Real.sqrt 8 * alHeight k ≠ 1 := by
  have h8 : Real.sqrt 8 < 3 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h4 : (4 : ℝ) ≤ 2 ^ k :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hlt : Real.sqrt 8 * alHeight k < 1 := by
    rw [alHeight, ← div_eq_mul_inv, div_lt_one (by positivity)]
    linarith
  exact hlt.ne

/-- `√a ^ p = a ^ (p/2)` for `a ≥ 0`. -/
theorem sqrt_pow_eq_rpow {a : ℝ} (ha : 0 ≤ a) (p : ℕ) : Real.sqrt a ^ p = a ^ ((p : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  ring

/-- The level-`k` bound of the Borel–Cantelli sum: with `θ_k = 2^k / k^m`, `γ = 2m + 2`,
`x_k = √(2γ log k)`, `(4^k + 1) (θ_k^{-2} · 2e^{-x_k²/2} + 2e^{-(2√k)²/2}) ≤ 4/k² + 4 (4e^{-2})^k`. -/
theorem level_bound_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    ((4 : ℝ) ^ k + 1) * (((((2 : ℝ) ^ k / (k : ℝ) ^ m) ^ 2)⁻¹ *
        (2 * Real.exp (-Real.sqrt (2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) ^ 2 / 2))) +
        2 * Real.exp (-(2 * Real.sqrt k) ^ 2 / 2)) ≤
      4 * ((k : ℝ) ^ 2)⁻¹ + 4 * (4 * Real.exp (-2)) ^ k := by
  have hK : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hK.le]
  have e1 : Real.exp (-(2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) / 2) =
      ((k : ℝ) ^ (2 * m + 2))⁻¹ := by
    rw [show -(2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) / 2 =
        -(((2 * m + 2 : ℕ) : ℝ) * Real.log k) by ring, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log hK]
  have e2 : Real.exp (-(2 ^ 2 * (k : ℝ)) / 2) = Real.exp (-2) ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [e1, e2]
  have h4 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have t1 : (((2 : ℝ) ^ k / (k : ℝ) ^ m) ^ 2)⁻¹ * (2 * ((k : ℝ) ^ (2 * m + 2))⁻¹) =
      2 / ((4 : ℝ) ^ k * (k : ℝ) ^ 2) := by
    rw [h4]
    field_simp
    ring
  rw [t1]
  have hF : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hq : (4 : ℝ) ^ k * Real.exp (-2) ^ k = (4 * Real.exp (-2)) ^ k := (mul_pow _ _ _).symm
  calc ((4 : ℝ) ^ k + 1) * (2 / ((4 : ℝ) ^ k * (k : ℝ) ^ 2) + 2 * Real.exp (-2) ^ k)
      ≤ (2 * 4 ^ k) * (2 / ((4 : ℝ) ^ k * (k : ℝ) ^ 2) + 2 * Real.exp (-2) ^ k) := by
        gcongr
        linarith
    _ = 4 * ((k : ℝ) ^ 2)⁻¹ + 4 * (4 * Real.exp (-2)) ^ k := by
        rw [← hq]
        field_simp
        ring

theorem four_mul_exp_neg_two_lt_one : 4 * Real.exp (-2) < 1 := by
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos 2)]
  linarith

theorem summable_level_bound :
    Summable fun k : ℕ => 4 * ((k : ℝ) ^ 2)⁻¹ + 4 * (4 * Real.exp (-2)) ^ k :=
  ((Real.summable_nat_pow_inv.2 (by norm_num : 1 < 2)).mul_left 4).add
    ((summable_geometric_of_lt_one (by positivity) four_mul_exp_neg_two_lt_one).mul_left 4)

/-! ## [AL14] Theorem 2 -/

/-- The constant of [AL14] Theorem 2 produced by the proof: `3^p + 2^p (2γ)^{p/2}` with
`γ = 2(⌈b⌉₊ + p) + 2`. -/
def thm2Const (p : ℕ) (b : ℝ) : ℝ :=
  3 ^ p + 2 ^ p * (2 * ((2 * (⌈b⌉₊ + p) + 2 : ℕ) : ℝ)) ^ ((p : ℝ) / 2)

theorem thm2Const_pos (p : ℕ) (b : ℝ) : 0 < thm2Const p b := by
  unfold thm2Const
  positivity

/-- **[AL14] Theorem 2 for a Brownian motion with continuous measurable paths and `B 0 = 0`.** -/
theorem ae_eventually_derivGridMaxStar_le_of_forall_continuous {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (B · ω)) (h0 : ∀ ω, B 0 ω = 0)
    (hB : IsBrownianReal B P) (p : ℕ) (b : ℝ) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      derivGridMaxStar p (fun r => B r.toNNReal ω) k ≤ thm2Const p b *
        ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) +
          Real.log k ^ ((p : ℝ) / 2) * derivGridMax (fun r => B r.toNNReal ω) k) := by
  -- the bad events of level `k ≥ 2`
  set m := ⌈b⌉₊ + p with hm
  let S : ℕ → Set Ω := fun k => if 2 ≤ k then
    ⋃ j ∈ Finset.range (4 ^ k + 1),
      ({ω | (2 : ℝ) ^ k / (k : ℝ) ^ m <
          ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime k j)) ((alHeight k : ℂ) * I)‖ ∧
          1 + Real.sqrt (2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) <
            incDelta (fun r => B r.toNNReal ω) k j} ∪
        {ω | 1 + 2 * Real.sqrt k < incDelta (fun r => B r.toNNReal ω) k j})
    else ∅
  have hS : ∀ k, P (S k) ≤
      ENNReal.ofReal (4 * ((k : ℝ) ^ 2)⁻¹ + 4 * (4 * Real.exp (-2)) ^ k) := by
    intro k
    by_cases hk : 2 ≤ k
    · simp only [S, hk, ↓reduceIte]
      have hK : (0 : ℝ) < k := Nat.cast_pos.2 (by omega)
      have hθ : (0 : ℝ) < 2 ^ k / (k : ℝ) ^ m := by positivity
      have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
      have hx : 0 < Real.sqrt (2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) :=
        Real.sqrt_pos.2 (by positivity)
      have hx' : 0 < 2 * Real.sqrt k := by positivity
      have hk8 := sqrt_eight_mul_alHeight_ne_one hk
      calc _ ≤ ∑ j ∈ Finset.range (4 ^ k + 1), P
            ({ω | (2 : ℝ) ^ k / (k : ℝ) ^ m <
              ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime k j)) ((alHeight k : ℂ) * I)‖ ∧
              1 + Real.sqrt (2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) <
                incDelta (fun r => B r.toNNReal ω) k j} ∪
              {ω | 1 + 2 * Real.sqrt k < incDelta (fun r => B r.toNNReal ω) k j}) :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ _j ∈ Finset.range (4 ^ k + 1),
            (ENNReal.ofReal ((((2 : ℝ) ^ k / (k : ℝ) ^ m) ^ 2)⁻¹) *
              ENNReal.ofReal (2 * Real.exp
                (-Real.sqrt (2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) ^ 2 / 2)) +
              ENNReal.ofReal (2 * Real.exp (-(2 * Real.sqrt k) ^ 2 / 2))) :=
            Finset.sum_le_sum fun j _ => (measure_union_le _ _).trans (add_le_add
              (measure_lt_norm_deriv_barInv_and_lt_incDelta_le_of_forall_continuous hBm hc h0 hB k j hk8 hθ
                hx)
              (measure_incDelta_gt_le_of_forall_continuous hBm hc hB k j hx'))
        _ = ENNReal.ofReal (((4 : ℝ) ^ k + 1) * (((((2 : ℝ) ^ k / (k : ℝ) ^ m) ^ 2)⁻¹ *
              (2 * Real.exp (-Real.sqrt (2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) ^ 2 / 2))) +
              2 * Real.exp (-(2 * Real.sqrt k) ^ 2 / 2))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
                (by positivity), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            push_cast
            rfl
        _ ≤ _ := ENNReal.ofReal_le_ofReal (level_bound_le hk m)
    · simp only [S, hk, ↓reduceIte, measure_empty]
      exact zero_le
  have htsum : ∑' k, P (S k) ≠ ∞ := by
    have h := (ENNReal.tsum_le_tsum hS).trans_eq
      (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_level_bound).symm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  filter_upwards [ae_eventually_notMem htsum] with ω hω
  filter_upwards [hω, eventually_ge_atTop 2] with k hk hk2
  -- the deterministic case split of [AL14] §3.1
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hK0 : (0 : ℝ) < k := by linarith
  have hK1 : (1 : ℝ) ≤ k := by linarith
  simp only [S, hk2, ↓reduceIte] at hk
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hK1
  have hlog2 : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hK
  have hγ2 : (2 : ℝ) ≤ ((2 * m + 2 : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hx1 : 1 ≤ Real.sqrt (2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) :=
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [Real.log_two_gt_d9])
  have hsq : Real.sqrt k ≤ k :=
    calc Real.sqrt k ≤ Real.sqrt ((k : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = k := Real.sqrt_sq hK0.le
  have hA0 : 0 ≤ (2 : ℝ) ^ k * (k : ℝ) ^ (-b) := by positivity
  have hL0 : 0 ≤ Real.log k ^ ((p : ℝ) / 2) := Real.rpow_nonneg hlog _
  have hD0 : 0 ≤ derivGridMax (fun r => B r.toNNReal ω) k :=
    (norm_nonneg _).trans (Finset.le_sup' (fun j => ‖deriv (barInv (fun r => B r.toNNReal ω)
      (alTime k j)) ((alHeight k : ℂ) * I)‖) (Finset.mem_range.2 (Nat.succ_pos (4 ^ k))))
  have hC3 : (3 : ℝ) ^ p ≤ thm2Const p b := le_add_of_nonneg_right (by positivity)
  have hC2 : (2 : ℝ) ^ p * (2 * ((2 * m + 2 : ℕ) : ℝ)) ^ ((p : ℝ) / 2) ≤ thm2Const p b :=
    le_add_of_nonneg_left (by positivity)
  refine Finset.sup'_le _ _ fun j hj => ?_
  have hj' := fun h => hk (mem_iUnion₂.2 ⟨j, hj, h⟩)
  have hΔ1 : 1 ≤ incDelta (fun r => B r.toNNReal ω) k j := one_le_incDelta _ k j
  have hE2 : incDelta (fun r => B r.toNNReal ω) k j ≤ 1 + 2 * Real.sqrt k :=
    not_lt.1 fun h => hj' (Or.inr h)
  have hfD : ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime k j)) ((alHeight k : ℂ) * I)‖ ≤
      derivGridMax (fun r => B r.toNNReal ω) k :=
    Finset.le_sup' (fun j => ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime k j))
      ((alHeight k : ℂ) * I)‖) hj
  by_cases hf : ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime k j)) ((alHeight k : ℂ) * I)‖ ≤
      (2 : ℝ) ^ k / (k : ℝ) ^ m
  · -- small derivative: `Δ ≤ 3k` and `|F̄'| ≤ 2^k k^{-(b'+p)}`
    have hΔk : incDelta (fun r => B r.toNNReal ω) k j ≤ 3 * k := by linarith
    have hb : (2 : ℝ) ^ k / (k : ℝ) ^ ⌈b⌉₊ ≤ (2 : ℝ) ^ k * (k : ℝ) ^ (-b) := by
      have hr : (k : ℝ) ^ (-(⌈b⌉₊ : ℝ)) ≤ (k : ℝ) ^ (-b) :=
        Real.rpow_le_rpow_of_exponent_le hK1 (neg_le_neg (Nat.le_ceil b))
      rw [Real.rpow_neg hK0.le, Real.rpow_natCast] at hr
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hr (by positivity)
    calc incDelta (fun r => B r.toNNReal ω) k j ^ p *
          ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime k j)) ((alHeight k : ℂ) * I)‖
        ≤ (3 * k) ^ p * ((2 : ℝ) ^ k / (k : ℝ) ^ m) :=
          mul_le_mul (pow_le_pow_left₀ (by linarith) hΔk p) hf (norm_nonneg _) (by positivity)
      _ = 3 ^ p * ((2 : ℝ) ^ k / (k : ℝ) ^ ⌈b⌉₊) := by
          rw [hm, pow_add, mul_pow]
          field_simp
      _ ≤ 3 ^ p * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b)) := by gcongr
      _ ≤ thm2Const p b * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) +
            Real.log k ^ ((p : ℝ) / 2) * derivGridMax (fun r => B r.toNNReal ω) k) :=
          mul_le_mul hC3 (le_add_of_nonneg_right (mul_nonneg hL0 hD0)) hA0
            (thm2Const_pos p b).le
  · -- large derivative: off the bad event, `Δ ≤ 1 + √(2γ log k) ≤ 2√(2γ log k)`
    rw [not_le] at hf
    have hE1 : incDelta (fun r => B r.toNNReal ω) k j ≤
        1 + Real.sqrt (2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) :=
      not_lt.1 fun h => hj' (Or.inl ⟨hf, h⟩)
    have hpow : Real.sqrt (2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k) ^ p =
        (2 * ((2 * m + 2 : ℕ) : ℝ)) ^ ((p : ℝ) / 2) * Real.log k ^ ((p : ℝ) / 2) := by
      rw [sqrt_pow_eq_rpow (by positivity), Real.mul_rpow (by positivity) hlog]
    calc incDelta (fun r => B r.toNNReal ω) k j ^ p *
          ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime k j)) ((alHeight k : ℂ) * I)‖
        ≤ (2 * Real.sqrt (2 * ((2 * m + 2 : ℕ) : ℝ) * Real.log k)) ^ p *
            derivGridMax (fun r => B r.toNNReal ω) k :=
          mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) p) hfD (norm_nonneg _)
            (by positivity)
      _ = (2 ^ p * (2 * ((2 * m + 2 : ℕ) : ℝ)) ^ ((p : ℝ) / 2)) *
            (Real.log k ^ ((p : ℝ) / 2) * derivGridMax (fun r => B r.toNNReal ω) k) := by
          rw [mul_pow, hpow]
          ring
      _ ≤ thm2Const p b * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) +
            Real.log k ^ ((p : ℝ) / 2) * derivGridMax (fun r => B r.toNNReal ω) k) :=
          mul_le_mul hC2 (le_add_of_nonneg_left hA0) (mul_nonneg hL0 hD0)
            (thm2Const_pos p b).le

/-- **[AL14] Theorem 2** (the SLE₈ note's (2.4), with exponent `p` on `Δ`). Let `B` be a standard
Brownian motion and `F̄_t = barInv B t` ([AL14]'s `f_t`, `∂_t ḡ = (1/4)/(ḡ − B_t)`). For every
`p : ℕ` and `b : ℝ` there is a deterministic `C > 0` such that almost surely, for all sufficiently
large `k`,
`D_k^* ≤ C (2^k k^{-b} + (log k)^{p/2} D_k)`,
with `D_k^* = max_{j ≤ 4^k} Δ_{j,k}^p |F̄'_{j y_k²}(i y_k)|` (`derivGridMaxStar p`) and
`D_k = max_{j ≤ 4^k} |F̄'_{j y_k²}(i y_k)|` (`derivGridMax`). -/
theorem exists_ae_eventually_derivGridMaxStar_le {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (p : ℕ) (b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      derivGridMaxStar p (fun r => B r.toNNReal ω) k ≤
        C * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) +
          Real.log k ^ ((p : ℝ) / 2) * derivGridMax (fun r => B r.toNNReal ω) k) := by
  obtain ⟨B'', hBm, hBc, hB0, hB'', hae⟩ := RS.exists_good_version0 hB
  refine ⟨thm2Const p b, thm2Const_pos p b, ?_⟩
  filter_upwards [ae_eventually_derivGridMaxStar_le_of_forall_continuous hBm hBc hB0 hB'' p b, hae]
    with ω hω he
  have hU : (fun r : ℝ => B r.toNNReal ω) = fun r => B'' r.toNNReal ω :=
    funext fun r => (he _).symm
  rw [hU]
  exact hω

/-- **[AL14] Theorem 2 as printed** (the SLE₈ note's (2.4) verbatim, `p = 4`): for every `b` there is
a deterministic `C_b > 0` with, almost surely for all large `k`,
`D_k^* ≤ C_b (2^k k^{-b} + (log k)² D_k)`. -/
theorem exists_ae_eventually_derivGridMaxStar_four_le {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      derivGridMaxStar 4 (fun r => B r.toNNReal ω) k ≤
        C * ((2 : ℝ) ^ k * (k : ℝ) ^ (-b) +
          Real.log k ^ 2 * derivGridMax (fun r => B r.toNNReal ω) k) := by
  obtain ⟨C, hC, h⟩ := exists_ae_eventually_derivGridMaxStar_le hB 4 b
  refine ⟨C, hC, h.mono fun ω hω => hω.mono fun k hk => ?_⟩
  have e : Real.log k ^ (((4 : ℕ) : ℝ) / 2) = Real.log k ^ 2 := by
    rw [show (((4 : ℕ) : ℝ) / 2) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rwa [e] at hk

/-! ## Versions for an arbitrary Brownian motion (through a continuous version) -/

/-- Events defined through the path `r ↦ B_r` have the same probability for two processes that agree
almost surely at all times. -/
theorem measure_setOf_path_eq {B B' : ℝ≥0 → Ω → ℝ} (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω)
    (Q : (ℝ → ℝ) → Prop) :
    P {ω | Q fun r => B r.toNNReal ω} = P {ω | Q fun r => B' r.toNNReal ω} := by
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [hae] with ω hω
  have e : (fun r : ℝ => B r.toNNReal ω) = fun r => B' r.toNNReal ω := funext fun r => (hω _).symm
  show Q _ ↔ Q _
  rw [e]

/-- **[AL14] (6)**: for a Brownian motion `B`, `P(Δ_{j,k} > 1 + x) ≤ 2 e^{-x²/2}` for `x > 0`. -/
theorem measure_incDelta_gt_le {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (k j : ℕ) {x : ℝ}
    (hx : 0 < x) :
    P {ω | 1 + x < incDelta (fun r => B r.toNNReal ω) k j} ≤
      ENNReal.ofReal (2 * Real.exp (-x ^ 2 / 2)) := by
  obtain ⟨B'', hBm, hBc, -, hB'', hae⟩ := RS.exists_good_version0 hB
  exact (measure_setOf_path_eq hae fun U => 1 + x < incDelta U k j).trans_le
    (measure_incDelta_gt_le_of_forall_continuous hBm hBc hB'' k j hx)

/-- **The independence step of [AL14] §3.1** for a Brownian motion `B`: at a grid time
`t = j y_k²` with `√8 y_k ≠ 1` and `θ, x > 0`,
`P(|F̄_t'(i y_k)| > θ, Δ_{j,k} > 1 + x) ≤ θ^{-2} · 2 e^{-x²/2}`. -/
theorem measure_lt_norm_deriv_barInv_and_lt_incDelta_le {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (k j : ℕ) (hk : Real.sqrt 8 * alHeight k ≠ 1) {θ x : ℝ}
    (hθ : 0 < θ) (hx : 0 < x) :
    P {ω | θ < ‖deriv (barInv (fun r => B r.toNNReal ω) (alTime k j)) ((alHeight k : ℂ) * I)‖ ∧
        1 + x < incDelta (fun r => B r.toNNReal ω) k j} ≤
      ENNReal.ofReal ((θ ^ 2)⁻¹) * ENNReal.ofReal (2 * Real.exp (-x ^ 2 / 2)) := by
  obtain ⟨B'', hBm, hBc, hB0, hB'', hae⟩ := RS.exists_good_version0 hB
  exact (measure_setOf_path_eq hae fun U =>
      θ < ‖deriv (barInv U (alTime k j)) ((alHeight k : ℂ) * I)‖ ∧ 1 + x < incDelta U k j).trans_le
    (measure_lt_norm_deriv_barInv_and_lt_incDelta_le_of_forall_continuous hBm hBc hB0 hB'' k j hk
      hθ hx)

end InteractingSLE.SLE8.AL14
