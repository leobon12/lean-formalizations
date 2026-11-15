import InteractingSLE.Foundations.Loewner.Hull
import QuantumZipper.Proofs.Loewner.CoreArc3b
import QuantumZipper.Proofs.Loewner.CaraRZ
import QuantumZipper.Proofs.Thm18.ASepGCFwd
import QuantumZipper.Proofs.RS.GenerationBasic
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Thm11.ForwardClock

/-!
# The Loewner chain is a capacity-parametrized family of compact `ℍ`-hulls

Design `planning/INFRA-GEO.md` §3–§4, packet GEO-LOEW. For a continuous driver `W`, QuantumZipper's
forward Loewner objects (`QuantumZipper.fwdHull W t = K_t`, the centered map
`QuantumZipper.fwdMap W t = g_t − W_t`) are connected to the hull API of `Loewner/Hull.lean`.
Reference: G. F. Lawler, *Conformally invariant processes in the plane*, AMS 2005 ([Law05]),
§4.1 (Loewner chains in `ℍ`, the expansion `g_t(z) = z + 2t/z + O(|z|⁻²)`).

## Main results

* `isHPHull_fwdHull`: `K_t` is a compact `ℍ`-hull (no normalization of `W 0` needed);
* `isMapOut_fwdMap`: `g_t = f_t + W_t` is the mapping-out function of `K_t`;
* `tendsto_mul_fwdMap_sub`: the hydrodynamic expansion `z (g_t(z) − z) → 2t` at `∞`;
* `hcap_fwdHull`: `hcap(K_t) = 2t` (Specification p. 3; SLE₈ note (1.1)ff);
* `exists_isConformalBijection_ball_fwdHull`: conformal radius along the chain in the source's
  form (Specification p. ~55, "twice `Υ_t` is the conformal radius of the active domain"): a
  conformal `φ : 𝔻 → ℍ \ K_t` with `φ 0 = z` and `|φ'(0)| = 2 Im f_t(z)/|f_t'(z)|`;
  `continuousOn_im_fwdMap_div_norm_deriv`, `antitoneOn_im_fwdMap_div_norm_deriv`: this quantity is
  continuous and nonincreasing in `t` before `z` is swallowed.

Quantitative forms: `norm_fwdMap_add_sub_le` (`‖g_t z − z‖ ≤ 4t/‖z‖`) and
`norm_mul_fwdMap_add_sub_sub_le` (`‖z (g_t z − z) − 2t‖ ≤ 4Dt/‖z‖`) for `‖z‖ > 2D`, where
`D = 24 M + 8 √t` bounds the displacement `‖f_s z − z‖` (QuantumZipper's
`CoreArc.norm_fwdMap_sub_le_uniform`) and `M` bounds `|W|` on `[0, t]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

variable {W : ℝ → ℝ}

/-! ### Basic facts about the chain -/

/-- A continuous driver is bounded on `[0, T]` (by a nonnegative constant). -/
theorem exists_abs_le_of_continuous (hW : Continuous W) (T : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ r ∈ Icc (0 : ℝ) T, |W r| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  refine ⟨max C 0, le_max_right _ _, fun r hr => ?_⟩
  have := hC r hr
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- `K_t` is bounded ([Law05] Lemma 4.12 via QuantumZipper's `CaraR.fwdHull_subset_closedBall`). -/
theorem isBounded_fwdHull (hW : Continuous W) (t : ℝ) :
    Bornology.IsBounded (QuantumZipper.fwdHull W t) := by
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hW (max t 0 + 1)
  refine (isBounded_closedBall (x := (0 : ℂ)) (r := M + 3 * Real.sqrt (max t 0 + 1))).subset ?_
  refine (QuantumZipper.fwdHull_mono.1 ?_).trans
    (QuantumZipper.CaraR.fwdHull_subset_closedBall hW (by positivity) hM)
  linarith [le_max_left t 0]

/-- The translated inverse map `w ↦ F_t^{W − W 0}(w) + W 0` is a conformal bijection of `ℍ` onto
`ℍ \ K_t`, for any continuous driver (QuantumZipper proves the case `W 0 = 0`; the general case is
a real translation, `ASep.GC.mem_fwdHull_sub_const`). -/
theorem isConformalBijection_fwdMapInv_add (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsConformalBijection
      (fun w => QuantumZipper.fwdMapInv (fun s => W s - W 0) t w + (W 0 : ℂ)) H
      (H \ QuantumZipper.fwdHull W t) := by
  set c : ℝ := W 0 with hc
  set W' : ℝ → ℝ := fun s => W s - c with hW'def
  have hW' : Continuous W' := hW.sub continuous_const
  have hW'0 : W' 0 = 0 := by simp [hW'def, hc]
  have hmem : ∀ z : ℂ, z ∈ H \ QuantumZipper.fwdHull W t ↔
      z - c ∈ H \ QuantumZipper.fwdHull W' t := by
    intro z
    rw [Set.mem_sdiff, Set.mem_sdiff, QuantumZipper.ASep.GC.mem_fwdHull_sub_const W c z t]
    have : (z - c).im = z.im := by simp
    exact and_congr_left' (by simp only [QuantumZipper.H, mem_ofPred_eq, this])
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (QuantumZipper.RS.differentiableOn_fwdMapInv hW' hW'0 ht).add_const _
  · intro w hw
    rw [hmem]
    have := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW' hW'0 ht hw
    simpa using this
  · intro w₁ hw₁ w₂ hw₂ h
    exact QuantumZipper.RS.injOn_fwdMapInv_H hW' hW'0 ht hw₁ hw₂ (add_right_cancel h)
  · intro z hz
    rw [hmem, ← QuantumZipper.RS.image_fwdMapInv_H hW' hW'0 ht] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    exact ⟨w, hw, by simp only [hwz, sub_add_cancel]⟩

/-- **`K_t` is a compact `ℍ`-hull** (design statement; REUSE-GEOM gap 7): `K_t ⊆ ℍ`, bounded,
relatively closed, and `ℍ \ K_t` is simply connected (it is conformally equivalent to `ℍ`). -/
theorem isHPHull_fwdHull {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsHPHull (QuantumZipper.fwdHull W t) := by
  have hH : IsSimplyConnected H := by
    have : ContractibleSpace H :=
      (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).contractibleSpace
        ⟨I, show (0 : ℝ) < I.im by simp⟩
    exact SimplyConnectedSpace.ofContractible _
  exact ⟨QuantumZipper.fwdHull_mono.2 t, isBounded_fwdHull hW t,
    QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht,
    isSimplyConnected_of_isConformalBijection QuantumZipper.isOpen_H
      (isConformalBijection_fwdMapInv_add hW ht) hH⟩

/-! ### The integral representation and the expansion at `∞` -/

/-- `g_s(z) = z + ∫₀ˢ 2/f_r(z) dr` for `z ∈ ℍ \ K_t` and `s ∈ [0, t]` (integrated (1.6)). -/
theorem fwdMap_add_eq_integral (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H \ QuantumZipper.fwdHull W t) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t) :
    QuantumZipper.fwdMap W s z + W s =
      z + ∫ r in (0 : ℝ)..s, 2 / QuantumZipper.fwdMap W r z := by
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht hz.1 hz.2
  have hz0 : 0 < z.im := hz.1
  rw [QuantumZipper.fwdMap_eq hW hz0 hu hs, (hu.2 s hs).2]
  have hint : ∫ r in (0 : ℝ)..s, 2 / u r = ∫ r in (0 : ℝ)..s, 2 / QuantumZipper.fwdMap W r z := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs.1] at hr
    simp only [QuantumZipper.fwdMap_eq hW hz0 hu ⟨hr.1, hr.2.trans hs.2⟩]
  rw [hint]
  ring

/-- `f_0(z) = z` when `W 0 = 0`. -/
theorem fwdMap_zero_eq (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H \ QuantumZipper.fwdHull W t) : QuantumZipper.fwdMap W 0 z = z := by
  have := fwdMap_add_eq_integral hW ht hz ⟨le_rfl, ht⟩
  rwa [intervalIntegral.integral_same, add_zero, hW0, Complex.ofReal_zero, add_zero] at this

/-- **Uniform displacement.** If `|W| ≤ M` on `[0, t]` and `W 0 = 0`, then
`‖f_s(z) − z‖ ≤ 24 M + 8 √t` for all `s ∈ [0, t]` and `z ∈ ℍ \ K_t` (QuantumZipper's
`CoreArc.norm_fwdMap_sub_le_uniform` at each positive time). -/
theorem norm_fwdMap_sub_self_le (hW : Continuous W) (hW0 : W 0 = 0) {t M : ℝ} (ht : 0 ≤ t)
    (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) {z : ℂ} (hz : z ∈ H \ QuantumZipper.fwdHull W t)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t) :
    ‖QuantumZipper.fwdMap W s z - z‖ ≤ 24 * M + 8 * Real.sqrt t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
  rcases hs.1.eq_or_lt with hs0 | hs0
  · subst hs0
    rw [fwdMap_zero_eq hW hW0 ht hz, sub_self, norm_zero]
    positivity
  · have hzs : z ∈ H \ QuantumZipper.fwdHull W s :=
      ⟨hz.1, fun h => hz.2 (QuantumZipper.fwdHull_mono.1 hs.2 h)⟩
    refine (QuantumZipper.CoreArc.norm_fwdMap_sub_le_uniform hW hW0 hs0
      (fun r hr => hM r ⟨hr.1, hr.2.trans hs.2⟩) hzs).trans ?_
    gcongr
    exact hs.2

/-- Lower bound `‖f_s(z)‖ ≥ ‖z‖/2` for `s ∈ [0, t]`, once `‖z‖ ≥ 2D`. -/
theorem norm_fwdMap_ge_half (hW : Continuous W) (hW0 : W 0 = 0) {t M : ℝ} (ht : 0 ≤ t)
    (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) {z : ℂ} (hz : z ∈ H \ QuantumZipper.fwdHull W t)
    (hzD : 2 * (24 * M + 8 * Real.sqrt t) ≤ ‖z‖) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t) :
    ‖z‖ / 2 ≤ ‖QuantumZipper.fwdMap W s z‖ := by
  have h1 := norm_fwdMap_sub_self_le hW hW0 ht hM hz hs
  have h2 := norm_sub_norm_le z (QuantumZipper.fwdMap W s z)
  rw [norm_sub_rev] at h1
  linarith

/-- `‖g_t(z) − z‖ ≤ 4t/‖z‖` for `z ∈ ℍ \ K_t` with `‖z‖ > 2D`. -/
theorem norm_fwdMap_add_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {t M : ℝ} (ht : 0 ≤ t)
    (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) {z : ℂ} (hz : z ∈ H \ QuantumZipper.fwdHull W t)
    (hzD : 2 * (24 * M + 8 * Real.sqrt t) < ‖z‖) :
    ‖QuantumZipper.fwdMap W t z + W t - z‖ ≤ 4 * t / ‖z‖ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
  have hz0 : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hzD
  rw [fwdMap_add_eq_integral hW ht hz ⟨ht, le_rfl⟩, add_sub_cancel_left]
  have hb : ∀ r ∈ Set.uIoc (0 : ℝ) t, ‖2 / QuantumZipper.fwdMap W r z‖ ≤ 4 / ‖z‖ := by
    intro r hr
    rw [uIoc_of_le ht] at hr
    have hlow := norm_fwdMap_ge_half hW hW0 ht hM hz hzD.le ⟨hr.1.le, hr.2⟩
    rw [norm_div, Complex.norm_ofNat, div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hlow) hz0]
    linarith
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_nonneg ht]
  ring

/-- `‖z (g_t(z) − z) − 2t‖ ≤ 4Dt/‖z‖` for `z ∈ ℍ \ K_t` with `‖z‖ > 2D`, `D = 24 M + 8 √t`. -/
theorem norm_mul_fwdMap_add_sub_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {t M : ℝ} (ht : 0 ≤ t)
    (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) {z : ℂ} (hz : z ∈ H \ QuantumZipper.fwdHull W t)
    (hzD : 2 * (24 * M + 8 * Real.sqrt t) < ‖z‖) :
    ‖z * (QuantumZipper.fwdMap W t z + W t - z) - ((2 * t : ℝ) : ℂ)‖ ≤
      4 * (24 * M + 8 * Real.sqrt t) * t / ‖z‖ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
  have hz0 : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hzD
  set D := 24 * M + 8 * Real.sqrt t with hD
  have hlow : ∀ r ∈ Icc (0 : ℝ) t, ‖z‖ / 2 ≤ ‖QuantumZipper.fwdMap W r z‖ :=
    fun r hr => norm_fwdMap_ge_half hW hW0 ht hM hz hzD.le hr
  have hne : ∀ r ∈ Icc (0 : ℝ) t, QuantumZipper.fwdMap W r z ≠ 0 := fun r hr h => by
    have := hlow r hr
    rw [h, norm_zero] at this
    linarith
  have hcont : ContinuousOn (fun r => QuantumZipper.fwdMap W r z) (Icc 0 t) :=
    QuantumZipper.FwdHolo.continuousOn_fwdMap_time hW ht hz
  have hii : IntervalIntegrable (fun r => z * (2 / QuantumZipper.fwdMap W r z)) MeasureTheory.volume
      0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht]
    exact continuousOn_const.mul (continuousOn_const.div hcont hne)
  have hrepr : z * (QuantumZipper.fwdMap W t z + W t - z) - ((2 * t : ℝ) : ℂ) =
      ∫ r in (0 : ℝ)..t, (z * (2 / QuantumZipper.fwdMap W r z) - 2) := by
    rw [fwdMap_add_eq_integral hW ht hz ⟨ht, le_rfl⟩, add_sub_cancel_left,
      intervalIntegral.integral_sub hii intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, Complex.real_smul]
    push_cast
    ring
  rw [hrepr]
  have hb : ∀ r ∈ Set.uIoc (0 : ℝ) t, ‖z * (2 / QuantumZipper.fwdMap W r z) - 2‖ ≤ 4 * D / ‖z‖ := by
    intro r hr
    rw [uIoc_of_le ht] at hr
    have hr' : r ∈ Icc (0 : ℝ) t := ⟨hr.1.le, hr.2⟩
    have hf := hne r hr'
    have hfl := hlow r hr'
    have hfpos : 0 < ‖QuantumZipper.fwdMap W r z‖ := lt_of_lt_of_le (by positivity) hfl
    have heq : z * (2 / QuantumZipper.fwdMap W r z) - 2 =
        2 * (z - QuantumZipper.fwdMap W r z) / QuantumZipper.fwdMap W r z := by
      field_simp
    rw [heq, norm_div, norm_mul, Complex.norm_ofNat, norm_sub_rev,
      div_le_div_iff₀ hfpos hz0]
    have hdisp := norm_fwdMap_sub_self_le hW hW0 ht hM hz hr'
    have hD0 : 0 ≤ D := by positivity
    nlinarith [norm_nonneg (QuantumZipper.fwdMap W r z - z)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  rw [sub_zero, abs_of_nonneg ht]
  ring

/-- `‖z‖ ↦ C/‖z‖` tends to `0` at `∞` (restricted to any set). -/
theorem tendsto_const_div_norm_cobounded_inf (C : ℝ) (S : Set ℂ) :
    Tendsto (fun z : ℂ => C / ‖z‖) (Bornology.cobounded ℂ ⊓ 𝓟 S) (𝓝 0) :=
  (tendsto_const_nhds.div_atTop tendsto_norm_cobounded_atTop).mono_left inf_le_left

/-- Eventually (at `∞`, inside `S`), `R < ‖z‖` and `z ∈ S`. -/
theorem eventually_lt_norm_and_mem (R : ℝ) (S : Set ℂ) :
    ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 S, R < ‖z‖ ∧ z ∈ S :=
  ((tendsto_norm_cobounded_atTop.eventually_gt_atTop R).filter_mono inf_le_left).and
    (mem_inf_of_right (mem_principal_self S))

/-- `g_t(z) − z → 0` at `∞`. -/
theorem tendsto_fwdMap_add_sub (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun z => QuantumZipper.fwdMap W t z + W t - z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ QuantumZipper.fwdHull W t)) (𝓝 0) := by
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hW t
  refine squeeze_zero_norm' ?_ (tendsto_const_div_norm_cobounded_inf (4 * t) _)
  filter_upwards [eventually_lt_norm_and_mem (2 * (24 * M + 8 * Real.sqrt t))
    (H \ QuantumZipper.fwdHull W t)] with z hz
  exact norm_fwdMap_add_sub_le hW hW0 ht hM hz.2 hz.1

/-- **Hydrodynamic expansion** `z (g_t(z) − z) → 2t` at `∞` ([Law05] §4.1:
`g_t(z) = z + 2t/z + O(|z|⁻²)`). -/
theorem tendsto_mul_fwdMap_sub (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun z => z * (QuantumZipper.fwdMap W t z + W t - z))
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ QuantumZipper.fwdHull W t)) (𝓝 ((2 * t : ℝ) : ℂ)) := by
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hW t
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_
    (tendsto_const_div_norm_cobounded_inf (4 * (24 * M + 8 * Real.sqrt t) * t) _)
  filter_upwards [eventually_lt_norm_and_mem (2 * (24 * M + 8 * Real.sqrt t))
    (H \ QuantumZipper.fwdHull W t)] with z hz
  rw [norm_norm]
  exact norm_mul_fwdMap_add_sub_sub_le hW hW0 ht hM hz.2 hz.1

/-! ### Mapping-out function and capacity -/

/-- `g_t = f_t + W_t` is a conformal bijection of `ℍ \ K_t` onto `ℍ`. -/
theorem isConformalBijection_fwdMap_add (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) :
    IsConformalBijection (fun z => QuantumZipper.fwdMap W t z + W t)
      (H \ QuantumZipper.fwdHull W t) H := by
  refine ⟨(QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).add_const _, ?_, ?_, ?_⟩
  · intro z hz
    have := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz
    simpa [QuantumZipper.H] using this
  · intro z₁ hz₁ z₂ hz₂ h
    exact QuantumZipper.FwdHolo.injOn_fwdMap hW ht hz₁ hz₂ (add_right_cancel h)
  · intro w hw
    have hw' : w - W t ∈ H := by simpa [QuantumZipper.H] using hw
    refine ⟨QuantumZipper.fwdMapInv W t (w - W t),
      QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hw', ?_⟩
    simp only [QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht hw', sub_add_cancel]

/-- **`g_t = f_t + W_t` maps out `K_t`** (design statement; Specification (1.6)–(1.7)). -/
theorem isMapOut_fwdMap {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsMapOut (QuantumZipper.fwdHull W t) (fun z => QuantumZipper.fwdMap W t z + W t) :=
  ⟨isConformalBijection_fwdMap_add hW hW0 ht, tendsto_fwdMap_add_sub hW hW0 ht⟩

/-- **Capacity parametrization** `hcap(K_t) = 2t` (design statement; Specification p. 3;
SLE₈ note (1.1)ff). -/
theorem hcap_fwdHull {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    HPHull.hcap ⟨QuantumZipper.fwdHull W t, isHPHull_fwdHull hW ht⟩ = 2 * t :=
  HPHull.hcap_eq_of_tendsto _ (isMapOut_fwdMap hW hW0 ht) (tendsto_mul_fwdMap_sub hW hW0 ht)

/-! ### Conformal radius along the chain -/

/-- The Cayley inverse `w ↦ i(1 + w)/(1 − w)` is a conformal bijection of `𝔻` onto `ℍ`. -/
theorem isConformalBijection_cayleyInv :
    IsConformalBijection QuantumZipper.CA.cayleyInv (ball (0 : ℂ) 1) H := by
  have hne : ∀ w ∈ ball (0 : ℂ) 1, w ≠ 1 := fun w hw h => by
    subst h
    simp at hw
  refine ⟨fun w hw => (QuantumZipper.CA.differentiableAt_cayleyInv
    (hne w hw)).differentiableWithinAt, fun w hw => QuantumZipper.CA.cayleyInv_mem_H hw,
    fun w₁ h₁ w₂ h₂ h => ?_, fun z hz => ?_⟩
  · rw [← QuantumZipper.CA.cayley_cayleyInv (hne w₁ h₁), h,
      QuantumZipper.CA.cayley_cayleyInv (hne w₂ h₂)]
  · exact ⟨QuantumZipper.CA.cayley z, QuantumZipper.CA.cayley_mem_ball hz,
      QuantumZipper.CA.cayleyInv_cayley
        (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt hz))⟩

/-- The disc chart of `ℍ` centred at `w₀`: `ζ ↦ Re w₀ + Im w₀ · i(1 + ζ)/(1 − ζ)`. -/
def diskChartH (w₀ : ℂ) (ζ : ℂ) : ℂ :=
  (w₀.im : ℂ) * QuantumZipper.CA.cayleyInv ζ + (w₀.re : ℂ)

theorem diskChartH_zero (w₀ : ℂ) : diskChartH w₀ 0 = w₀ := by
  apply Complex.ext <;> simp [diskChartH, QuantumZipper.CA.cayleyInv]

theorem isConformalBijection_diskChartH {w₀ : ℂ} (hw₀ : w₀ ∈ H) :
    IsConformalBijection (diskChartH w₀) (ball (0 : ℂ) 1) H := by
  have hb : 0 < w₀.im := hw₀
  have haff : IsConformalBijection (fun z : ℂ => (w₀.im : ℂ) * z + (w₀.re : ℂ)) H H :=
    ⟨((differentiable_id.const_mul _).add_const _).differentiableOn,
      QuantumZipper.CA.bijOn_affine_H hb⟩
  exact isConformalBijection_comp haff isConformalBijection_cayleyInv

theorem hasDerivAt_diskChartH (w₀ : ℂ) :
    HasDerivAt (diskChartH w₀) (2 * I * (w₀.im : ℂ)) 0 := by
  have h1 : HasDerivAt (fun w : ℂ => I * (1 + w)) I 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_add 1).const_mul I
  have h2 : HasDerivAt (fun w : ℂ => 1 - w) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
  have h3 : HasDerivAt QuantumZipper.CA.cayleyInv (2 * I) 0 :=
    (h1.div h2 (by norm_num)).congr_deriv (by simp; ring)
  exact ((h3.const_mul (w₀.im : ℂ)).add_const (w₀.re : ℂ)).congr_deriv (by ring)

/-- `F_t = fwdMapInv W t` is a conformal bijection of `ℍ` onto `ℍ \ K_t` (`W 0 = 0`). -/
theorem isConformalBijection_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsConformalBijection (QuantumZipper.fwdMapInv W t) H (H \ QuantumZipper.fwdHull W t) := by
  have h := isConformalBijection_fwdMapInv_add hW ht
  simp only [hW0, sub_zero, Complex.ofReal_zero, add_zero] at h
  exact h

/-- `F_t'(f_t(z)) · f_t'(z) = 1` for `z ∈ ℍ \ K_t`. -/
theorem deriv_fwdMapInv_mul_deriv_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ QuantumZipper.fwdHull W t) :
    deriv (QuantumZipper.fwdMapInv W t) (QuantumZipper.fwdMap W t z) *
      deriv (QuantumZipper.fwdMap W t) z = 1 := by
  have hf := QuantumZipper.FwdHolo.hasDerivAt_fwdMap hW ht hz
  have hw₀ : QuantumZipper.fwdMap W t z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz
  have hF : DifferentiableAt ℂ (QuantumZipper.fwdMapInv W t) (QuantumZipper.fwdMap W t z) :=
    ((isConformalBijection_fwdMapInv hW hW0 ht).1 _ hw₀).differentiableAt
      (QuantumZipper.isOpen_H.mem_nhds hw₀)
  have heq : QuantumZipper.fwdMapInv W t ∘ QuantumZipper.fwdMap W t =ᶠ[𝓝 z] id := by
    filter_upwards [(QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht).mem_nhds hz] with y hy
    exact QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht hy
  have h1 := hF.hasDerivAt.comp z hf
  have h2 : HasDerivAt (QuantumZipper.fwdMapInv W t ∘ QuantumZipper.fwdMap W t) 1 z :=
    (hasDerivAt_id z).congr_of_eventuallyEq heq
  rw [hf.deriv]
  exact h1.unique h2

/-- **Conformal radius along the chain**, in the source's form (Specification p. ~55: twice
`Υ_t = Im f_t(z)/|f_t'(z)|` is the conformal radius of the active domain `ℍ \ K_t` viewed from `z`;
p. ~170: the conformal radius is `|φ'(0)|` for a conformal `φ : 𝔻 → D` with `φ 0 = z`). -/
theorem exists_isConformalBijection_ball_fwdHull (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ QuantumZipper.fwdHull W t) :
    ∃ φ : ℂ → ℂ, IsConformalBijection φ (ball (0 : ℂ) 1) (H \ QuantumZipper.fwdHull W t) ∧
      φ 0 = z ∧
      ‖deriv φ 0‖ = 2 * (QuantumZipper.fwdMap W t z).im / ‖deriv (QuantumZipper.fwdMap W t) z‖ := by
  set w₀ := QuantumZipper.fwdMap W t z with hw₀def
  have hw₀ : w₀ ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz
  have hb : 0 < w₀.im := hw₀
  have hFc := isConformalBijection_fwdMapInv hW hW0 ht
  refine ⟨QuantumZipper.fwdMapInv W t ∘ diskChartH w₀,
    isConformalBijection_comp hFc (isConformalBijection_diskChartH hw₀), ?_, ?_⟩
  · simp only [Function.comp_apply, diskChartH_zero, hw₀def]
    exact QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht hz
  · have hF : HasDerivAt (QuantumZipper.fwdMapInv W t)
        (deriv (QuantumZipper.fwdMapInv W t) w₀) (diskChartH w₀ 0) := by
      rw [diskChartH_zero]
      exact ((hFc.1 _ hw₀).differentiableAt (QuantumZipper.isOpen_H.mem_nhds hw₀)).hasDerivAt
    have hprod := deriv_fwdMapInv_mul_deriv_fwdMap hW hW0 ht hz
    rw [← hw₀def] at hprod
    have hf0 : deriv (QuantumZipper.fwdMap W t) z ≠ 0 := right_ne_zero_of_mul_eq_one hprod
    have hnorm : ‖deriv (QuantumZipper.fwdMapInv W t) w₀‖ =
        1 / ‖deriv (QuantumZipper.fwdMap W t) z‖ := by
      rw [eq_div_iff (norm_ne_zero_iff.2 hf0), ← norm_mul, hprod, norm_one]
    rw [(hF.comp 0 (hasDerivAt_diskChartH w₀)).deriv, norm_mul, hnorm, norm_mul, norm_mul,
      Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
    ring

/-- `Im f_t(z)/|f_t'(z)| = exp C_t(z)` with QuantumZipper's log conformal radius `fwdLogCR`. -/
theorem im_fwdMap_div_norm_deriv_eq_exp (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H \ QuantumZipper.fwdHull W t) :
    (QuantumZipper.fwdMap W t z).im / ‖deriv (QuantumZipper.fwdMap W t) z‖ =
      Real.exp (QuantumZipper.FwdClock.fwdLogCR W t z) := by
  have hpos : 0 < (QuantumZipper.fwdMap W t z).im := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz
  rw [QuantumZipper.FwdClock.norm_deriv_fwdMap hW ht hz, QuantumZipper.FwdClock.fwdLogCR,
    Real.exp_sub, Real.exp_log hpos]

/-- The conformal-radius quantity `Im f_t(z)/|f_t'(z)|` is continuous in `t ∈ [0, T]` for
`z ∈ ℍ \ K_T` (Specification p. ~194: "the conformal radius in the component containing an unhit
point is continuous in `t`"). -/
theorem continuousOn_im_fwdMap_div_norm_deriv (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H \ QuantumZipper.fwdHull W T) :
    ContinuousOn (fun t => (QuantumZipper.fwdMap W t z).im /
      ‖deriv (QuantumZipper.fwdMap W t) z‖) (Icc 0 T) := by
  have hsol := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hT hz.1 hz.2
  have hC : ContinuousOn (fun t => QuantumZipper.FwdClock.fwdLogCR W t z) (Icc 0 T) :=
    fun t ht =>
      (QuantumZipper.FwdClock.hasDerivWithinAt_fwdLogCR hW hz.1 hsol ht).continuousWithinAt
  refine (Real.continuous_exp.comp_continuousOn hC).congr fun t ht => ?_
  exact im_fwdMap_div_norm_deriv_eq_exp hW ht.1
    ⟨hz.1, fun h => hz.2 (QuantumZipper.fwdHull_mono.1 ht.2 h)⟩

/-- The conformal-radius quantity `Im f_t(z)/|f_t'(z)|` is nonincreasing in `t ∈ [0, T]` for
`z ∈ ℍ \ K_T` (its logarithm has derivative `−4 (Im f_t)²/|f_t|⁴ ≤ 0`). -/
theorem antitoneOn_im_fwdMap_div_norm_deriv (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H \ QuantumZipper.fwdHull W T) :
    AntitoneOn (fun t => (QuantumZipper.fwdMap W t z).im /
      ‖deriv (QuantumZipper.fwdMap W t) z‖) (Icc 0 T) := by
  have hsol := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hT hz.1 hz.2
  have hA : AntitoneOn (fun t => QuantumZipper.FwdClock.fwdLogCR W t z) (Icc 0 T) :=
    QuantumZipper.FwdClock.antitoneOn_Icc_of_hasDerivWithinAt
      (fun t ht => QuantumZipper.FwdClock.hasDerivWithinAt_fwdLogCR hW hz.1 hsol ht)
      (fun t _ => by
        have : 0 ≤ 4 * (QuantumZipper.fwdMap W t z).im ^ 2 / ‖QuantumZipper.fwdMap W t z‖ ^ 4 := by
          positivity
        rw [neg_mul, neg_div]
        linarith)
  have hmem : ∀ t ∈ Icc (0 : ℝ) T, z ∈ H \ QuantumZipper.fwdHull W t := fun t ht =>
    ⟨hz.1, fun h => hz.2 (QuantumZipper.fwdHull_mono.1 ht.2 h)⟩
  intro a ha b hb hab
  simp only
  rw [im_fwdMap_div_norm_deriv_eq_exp hW ha.1 (hmem a ha),
    im_fwdMap_div_norm_deriv_eq_exp hW hb.1 (hmem b hb)]
  exact Real.exp_le_exp.2 (hA ha hb hab)

end InteractingSLE
