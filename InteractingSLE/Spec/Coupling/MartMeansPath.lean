/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.Assembly11Meas
import InteractingSLE.GFF.LocalSets.PointVariance

/-!
# The coupling mean along one path: harmonicity, mean values on safe balls, localizing times

Packet PROVE-CPL-MART (the forward step "coupling specification ⇒ coupling means are local martingales",
`planning/handoffs/PROVE-LEMMA71.md` item 3: "the mean-value property of the harmonic `𝔥_t` on discs off `K_t`, and
localization at the times when `K_t` reaches a disc"). Everything here is deterministic or concerns one stopping time.

* `harmonicOnNhd_meanCan_clamp`: the explicit mean `𝔥_s = meanCan … s` (`Assembly11Path`) is harmonic on `ℍ \ K_s`;
  it is `Im` of the holomorphic bracket of (2.5), `(1/√κ)(π(1 + ∑ ρᴿ) i − 2 log f − ∑ ρ log(f − v)) − χ log f_s'`.
* `IsSafeAt.integral_meanCan_mul_bumpFun`: on a closed ball `B̄(z, ε)` that is safe at `r`, for `s ≤ r` and `ε' < ε`,
  `∫ 𝔥_s · bump_{z,ε'} = 𝔥_s(z) ε'² ∫ e(1 − |y|²)` (mean value property).
* `locTime z n w`: the safe exit time of the ball `B̄(z, Im z/(n+2))` at level `(Im z/2)/(n+1)`, horizon `n`; for a
  continuous driver with `w 0 = 0` the ball is safe at `locTime` (`isSafeAt_locTime`), `locTime ≤ s(z)`
  (`locTime_le_swallowTime`), and every time before the swallowing time `s(z)` lies below `locTime z n w` for all large
  `n` (`eventually_lt_locTime`).
* `isStoppingTime_locTime`: for a right-continuous filtration in which the driver is adapted and has continuous paths,
  `ω ↦ locTime z n (W · ω)` is a stopping time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper Complex Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

namespace MartMeans

open Ito

variable {nL nR : ℕ}

/-! ### Harmonicity of the explicit mean -/

/-- The holomorphic bracket whose imaginary part is the explicit mean (2.5) at a fixed time, for the driver `W` and
centred positions `a`, `b`. -/
def meanBracket (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (a : Fin nL → ℝ) (b : Fin nR → ℝ)
    (W : ℝ → ℝ) (s : ℝ) (y : ℂ) : ℂ :=
  ((1 / Real.sqrt κ : ℝ) : ℂ) * ((Real.pi * (1 + ∑ i, ρR i) : ℝ) * I - 2 * log (fwdMap W s y)
      - (∑ i, (ρL i : ℂ) * log (fwdMap W s y - a i)) - ∑ i, (ρR i : ℂ) * log (fwdMap W s y - b i))
    - (chiC κ : ℂ) * logDerivFwd W s y

theorem im_meanBracket (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (a : Fin nL → ℝ) (b : Fin nR → ℝ)
    (W : ℝ → ℝ) (s : ℝ) (y : ℂ) :
    (meanBracket κ ρL ρR a b W s y).im =
      meanHarmonic κ ρL ρR a b (fwdMap W s y) - chiC κ * (logDerivFwd W s y).im := by
  simp only [meanBracket, meanHarmonic, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.im_sum, Complex.re_sum, Complex.sub_re,
    Complex.mul_re, Complex.log_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, sub_zero,
    add_zero, mul_one]

/-- **The explicit mean is harmonic off the hull**: for a continuous driver `W` and fixed centred positions,
`y ↦ meanHarmonic(f_s y) − χ arg f_s'(y)` is harmonic on `ℍ \ K_s`. -/
theorem harmonicOnNhd_meanHarmonic_fwdMap (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (a : Fin nL → ℝ)
    (b : Fin nR → ℝ) {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) :
    InnerProductSpace.HarmonicOnNhd
      (fun y => meanHarmonic κ ρL ρR a b (fwdMap W s y) - chiC κ * (logDerivFwd W s y).im)
      (H \ fwdHull W s) := by
  intro y hy
  have hU : IsOpen (H \ fwdHull W s) := FwdHolo.isOpen_compl_fwdHull hW hs
  have hfa : AnalyticAt ℂ (fwdMap W s) y :=
    (FwdHolo.differentiableOn_fwdMap hW hs).analyticAt (hU.mem_nhds hy)
  have hLa : AnalyticAt ℂ (logDerivFwd W s) y :=
    (isDerivLog_fwdMap hW hs).1.analyticAt (hU.mem_nhds hy)
  have hfH : 0 < (fwdMap W s y).im := FwdHolo.mapsTo_fwdMap hW hs hy
  have hslit : ∀ c : ℝ, fwdMap W s y - c ∈ slitPlane := fun c =>
    mem_slitPlane_of_im_pos (by simpa using hfH)
  have hslit0 : fwdMap W s y ∈ slitPlane := mem_slitPlane_of_im_pos hfH
  have hΦ : AnalyticAt ℂ (meanBracket κ ρL ρR a b W s) y := by
    unfold meanBracket
    refine (analyticAt_const.mul (((analyticAt_const.sub (analyticAt_const.mul (hfa.clog hslit0))).sub
      ?_).sub ?_)).sub (analyticAt_const.mul hLa)
    · exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul
        ((hfa.sub analyticAt_const).clog (hslit (a i)))
    · exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul
        ((hfa.sub analyticAt_const).clog (hslit (b i)))
  have h := hΦ.harmonicAt_im
  have e : (fun z => (meanBracket κ ρL ρR a b W s z).im) =
      fun y => meanHarmonic κ ρL ρR a b (fwdMap W s y) - chiC κ * (logDerivFwd W s y).im :=
    funext (im_meanBracket κ ρL ρR a b W s)
  rwa [e] at h

/-! ### Mean values on safe balls -/

section Safe

variable {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
  {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {δ N : ℝ} {σ₀ r s : ℝ≥0} {z : ℂ} {ε ε' : ℝ}

/-- **Mean value property on a safe ball.** If the closed ball `B̄(z, ε) ⊆ ℍ` is safe at `r` and `s ≤ r`, then for
`0 < ε' ≤ ε`, `∫ 𝔥_s · bump_{z,ε'} = 𝔥_s(z) ε'² ∫ e(1 − |y|²)`. -/
theorem _root_.InteractingSLE.Coupling.IsSafeAt.integral_meanCan_mul_bumpFun (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hKH : closedBall z ε ⊆ H) (h : IsSafeAt (closedBall z ε) δ N σ₀ ζ w r) (hs : s ≤ r) (hε' : 0 < ε')
    (hεε : ε' ≤ ε) :
    ∫ y, meanCan κ ρL ρR w vL vR s y * GFF.bumpFun z ε' y =
      meanCan κ ρL ρR w vL vR s z * (ε' ^ 2 * GFF.bumpMass) := by
  have hWc : Continuous (clampDrv (rpath w) r) := h.continuous_clampDrv hw
  have hsI : (s : ℝ) ∈ Icc 0 (r : ℝ) := ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  have hV : closedBall z ε ⊆ H \ fwdHull (clampDrv (rpath w) r) s := fun y hy =>
    (h.isProtected hw hKH).mem_of_le hsI hy
  have e : meanCan κ ρL ρR w vL vR s = fun y =>
      meanHarmonic κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s)
        (fwdMap (clampDrv (rpath w) r) s y) - chiC κ * (logDerivFwd (clampDrv (rpath w) r) s y).im := by
    funext y
    rw [meanCan, fwdMap_clampDrv_of_le hsI.2, logDerivFwd_clampDrv_of_le hsI.1 hsI.2]
  rw [e]
  exact GFF.integral_mul_bumpFun_of_harmonic (FwdHolo.isOpen_compl_fwdHull hWc s.coe_nonneg)
    (harmonicOnNhd_meanHarmonic_fwdMap κ ρL ρR _ _ hWc s.coe_nonneg) hε'
    ((closedBall_subset_closedBall hεε).trans hV)

/-- The safe exit time is antitone in the set. -/
theorem safeExitTime_anti_set {K K' : Set ℂ} (hK : K' ⊆ K) :
    safeExitTime K δ N σ₀ ζ w ≤ safeExitTime K' δ N σ₀ ζ w :=
  csInf_le_csInf (OrderBot.bddBelow _) nonempty_not_isSafeAt fun _ ht hsafe => ht (hsafe.subset hK)

end Safe

/-! ### The localizing times of one point -/

section Loc

variable {w : ℝ≥0 → ℝ} {z : ℂ}

/-- The radius `Im z/(n+2)` of the `n`-th localizing ball around `z`. -/
def locRad (z : ℂ) (n : ℕ) : ℝ := z.im / ((n : ℝ) + 2)

/-- The level `(Im z/2)/(n+1)` of the `n`-th localizing time. -/
def locLevel (z : ℂ) (n : ℕ) : ℝ := z.im / 2 / ((n : ℝ) + 1)

/-- **The `n`-th localizing time of `z`**: the safe exit time of the ball `B̄(z, Im z/(n+2))` at level
`(Im z/2)/(n+1)`, below the horizon `n`. -/
def locTime (z : ℂ) (n : ℕ) (w : ℝ≥0 → ℝ) : ℝ≥0 :=
  safeExitTime (closedBall z (locRad z n)) (locLevel z n) n (n : ℝ≥0) ⊤ w

theorem locRad_pos (hz : 0 < z.im) (n : ℕ) : 0 < locRad z n := by
  unfold locRad; positivity

theorem locLevel_pos (hz : 0 < z.im) (n : ℕ) : 0 < locLevel z n := by
  unfold locLevel; positivity

theorem locRad_le (hz : 0 < z.im) (n : ℕ) : locRad z n ≤ z.im / 2 := by
  unfold locRad
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

/-- Points of the localizing ball are at height at least `Im z/2`. -/
theorem half_le_im_of_mem_closedBall_locRad (hz : 0 < z.im) {n : ℕ} {y : ℂ}
    (hy : y ∈ closedBall z (locRad z n)) : z.im / 2 ≤ y.im := by
  have h1 : |y.im - z.im| ≤ locRad z n := by
    rw [mem_closedBall, dist_eq_norm] at hy
    calc |y.im - z.im| = |(y - z).im| := by rw [Complex.sub_im]
      _ ≤ ‖y - z‖ := Complex.abs_im_le_norm _
      _ ≤ locRad z n := hy
  have h2 := locRad_le hz n
  have := (abs_le.1 h1).1
  linarith

theorem closedBall_locRad_subset (hz : 0 < z.im) (n : ℕ) : closedBall z (locRad z n) ⊆ H := fun y hy =>
  show 0 < y.im from lt_of_lt_of_le (by positivity) (half_le_im_of_mem_closedBall_locRad hz hy)

theorem locLevel_le (hz : 0 < z.im) (n : ℕ) : locLevel z n ≤ z.im / 2 := by
  unfold locLevel
  rw [div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith

/-- **The localizing ball is safe at the localizing time** (continuous driver started at `0`). -/
theorem isSafeAt_locTime (hw : Continuous w) (hw0 : w 0 = 0) (hz : 0 < z.im) (n : ℕ) :
    IsSafeAt (closedBall z (locRad z n)) (locLevel z n) n (n : ℝ≥0) ⊤ w (locTime z n w) :=
  isSafeAt_safeExitTime hw.continuousOn (closedBall_locRad_subset hz n) (locLevel_pos hz n)
    ENNReal.coe_lt_top (isSafeAt_zero (closedBall_locRad_subset hz n)
      (fun _ hy => (locLevel_le hz n).trans (half_le_im_of_mem_closedBall_locRad hz hy)) hw0
      (by simp) n.cast_nonneg)

/-- The localizing time is at most the swallowing time of `z`. -/
theorem locTime_le_swallowTime (hw : Continuous w) (hw0 : w 0 = 0) (hz : 0 < z.im) (n : ℕ) :
    ((locTime z n w : ℝ≥0) : ℝ≥0∞) ≤ swallowTime (rpath w) z := by
  obtain ⟨u, hu⟩ := ((isSafeAt_locTime hw hw0 hz n).2.2.2 z
    (mem_closedBall_self (locRad_pos hz n).le)).1
  exact le_sSup ⟨_, ⟨(locTime z n w).coe_nonneg, u, hu⟩, ENNReal.ofReal_coe_nnreal⟩

/-- **Exhaustion**: every time before the swallowing time of `z` lies below all large localizing times. -/
theorem eventually_lt_locTime (hw : Continuous w) (hz : 0 < z.im) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < swallowTime (rpath w) z) : ∀ᶠ n in atTop, r < locTime z n w := by
  have hW : Continuous (rpath w) := hw.comp continuous_real_toNNReal
  obtain ⟨x, ⟨T, ⟨hT0, u, hu⟩, rfl⟩, hrx⟩ := lt_sSup_iff.1 hr
  have hrT : (r : ℝ) < T := by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg] at hrx
    exact hrx
  set t' : ℝ≥0 := ⟨((r : ℝ) + T) / 2, by have := r.coe_nonneg; linarith⟩ with ht'
  have hrt' : r < t' := by
    rw [← NNReal.coe_lt_coe]; show (r : ℝ) < ((r : ℝ) + T) / 2; linarith
  have ht'T : (t' : ℝ) < T := by show ((r : ℝ) + T) / 2 < T; linarith
  have hzt' : z ∈ H \ fwdHull (rpath w) t' :=
    (FwdHolo.mem_compl_fwdHull_iff t'.coe_nonneg).2 ⟨hz, T, ht'T, u, hu⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (FwdHolo.isOpen_compl_fwdHull hW t'.coe_nonneg) z hzt'
  set ε₁ := min (ε / 2) (z.im / 2) with hε₁
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hKball : closedBall z ε₁ ⊆ ball z ε :=
    closedBall_subset_ball ((min_le_left _ _).trans_lt (by linarith))
  have hKH : closedBall z ε₁ ⊆ H := fun y hy => (hball (hKball hy)).1
  have halive : ∀ y ∈ closedBall z ε₁, ∃ u, IsForwardSol (rpath w) y t' u := fun y hy =>
    exists_isForwardSol_of_mem t'.coe_nonneg (hball (hKball hy))
  have hev := eventually_le_safeExitTime hw.continuousOn (isCompact_closedBall z ε₁) hKH (z.im / 2)
    (le_refl t') ENNReal.coe_lt_top halive
  have hrad : ∀ᶠ n : ℕ in atTop, locRad z n ≤ ε₁ := by
    have h0 : Tendsto (fun n : ℕ => locRad z n) atTop (𝓝 0) := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
      simpa [locRad] using this.const_div_atTop z.im
    exact h0.eventually (ge_mem_nhds hε₁)
  have hN : ∀ᶠ n : ℕ in atTop, t' ≤ (n : ℝ≥0) := by
    obtain ⟨k, hk⟩ := exists_nat_ge t'
    filter_upwards [eventually_ge_atTop k] with n hn
    exact hk.trans (by exact_mod_cast hn)
  filter_upwards [hev, hrad, hN] with n h1 h2 h3
  calc r < t' := hrt'
    _ ≤ safeExitTime (closedBall z ε₁) (z.im / 2 / ((n : ℝ) + 1)) n t' ⊤ w := h1
    _ ≤ safeExitTime (closedBall z ε₁) (z.im / 2 / ((n : ℝ) + 1)) n (n : ℝ≥0) ⊤ w :=
        safeExitTime_mono le_rfl le_rfl h3
    _ ≤ locTime z n w := safeExitTime_anti_set (closedBall_subset_closedBall h2)

end Loc

/-! ### The localizing times are stopping times -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- An adapted process is adapted before the lifetime `∞`. -/
theorem adaptedBefore_top_of_stronglyAdapted (hWa : StronglyAdapted 𝓖 W) :
    AdaptedBefore 𝓖 (fun _ => ⊤) W := fun t A hA => by
  have h := (hWa t).measurable hA
  convert h using 1
  ext ω
  simp

/-- **The localizing times are stopping times** of a right-continuous filtration in which the driver is adapted with
continuous paths. -/
theorem isStoppingTime_locTime [𝓖.IsRightContinuous] (hWa : StronglyAdapted 𝓖 W)
    (hWc : ∀ ω, Continuous fun t => W t ω) {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    IsStoppingTime 𝓖 fun ω => ((locTime z n (W · ω) : ℝ≥0) : WithTop ℝ≥0) := by
  set K := closedBall z (locRad z n) with hK
  have hKH : K ⊆ H := closedBall_locRad_subset hz n
  obtain ⟨D, hDK, hDc, hKD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  obtain ⟨T, hTc, hTd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hδ := locLevel_pos hz n
  have hiff : ∀ ω d, IsSafeAt K (locLevel z n) n (n : ℝ≥0) ⊤ (W · ω) d ↔
      IsSafeAt D (locLevel z n) n (n : ℝ≥0) ⊤ (W · ω) d := fun ω d =>
    ⟨fun h => h.subset hDK, fun h => h.of_dense (hWc ω).continuousOn hKH hKD hDK hδ⟩
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
  have heq : {ω | ((locTime z n (W · ω) : ℝ≥0) : WithTop ℝ≥0) < (t : WithTop ℝ≥0)} =
      ⋃ d ∈ T ∩ Iio t, {ω | ω ∈ univ ∧
        IsSafeAt D (locLevel z n) n ((fun _ : Ω => (n : ℝ≥0)) ω) ((fun _ : Ω => (⊤ : ℝ≥0∞)) ω)
          (W · ω) d}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_lt_coe, mem_iUnion, mem_inter_iff, mem_Iio, exists_prop,
      mem_compl_iff, mem_univ, true_and]
    rw [locTime, safeExitTime_lt_iff (hWc ω).continuousOn hKH hTd]
    constructor
    · rintro ⟨d, hd, hdt, hnp⟩; exact ⟨d, ⟨hd, hdt⟩, fun h => hnp ((hiff ω d).2 h)⟩
    · rintro ⟨d, ⟨hd, hdt⟩, hnp⟩; exact ⟨d, hd, hdt, fun h => hnp ((hiff ω d).1 h)⟩
  rw [heq]
  refine MeasurableSet.biUnion (hTc.mono inter_subset_left) fun d hd => ?_
  exact 𝓖.mono hd.2.le _ (measurableSet_isSafeAt (adaptedBefore_top_of_stronglyAdapted hWa)
    (fun ω _ => (hWc ω).continuousOn) MeasurableSet.univ hDc (hDK.trans hKH)
    (isStoppingTime_const 𝓖 (n : ℝ≥0)) _ _ d).compl

end Random

end MartMeans

end Coupling

end InteractingSLE
