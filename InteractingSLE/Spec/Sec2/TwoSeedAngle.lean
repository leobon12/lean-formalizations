/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedLogClock
import InteractingSLE.Spec.Sec2.TerminalEscape

/-!
# The angle process of a two-seed solution, and the pathwise correspondence

Packet PROVE-SEC2-JAC. For a two-seed solution of Definition 2.1 (one force point on each side, both
started at `0`) whose separation `ℓ = V^R - V^L` is unbounded before the lifetime (for instance when
the lifetime is infinite, `sepN_unbounded_of_top`), the angle process in the logarithmic clock
`U = logAngle w vL vR ζ` (`TwoSeedLogClock.lean`) is a continuous path `ℝ → [0, 1]`
(`continuous_logAngle`) whose boundary set `{U ∈ {0, 1}}` is Lebesgue-null
(`volume_logAngle_boundary`). With infinite lifetime its clock diverges and the solution **is** the
time-changed two-seed construction of `U` (`eq_twoSeedPaths_logAngle`): `w = wPath U`,
`vL = vLPath U`, `vR = vRPath U`.

Together with `isIntegratedSLEPath_twoSeed` (`TwoSeedPath.lean`) this is a pathwise correspondence
between two-seed solution paths with infinite lifetime and angle paths
(Specification p. 23–24, L516–L546).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}

section Angle

variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
include h

theorem exp_lt_sepN_iff {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀) {u : ℝ} :
    u < log (sepN vL vR t₀) ↔ exp u < sepN vL vR t₀ := by
  rw [← exp_lt_exp, exp_log (sepN_pos h ht₀ ht0)]

/-- The hitting time maps `(-∞, log ℓ_{t₀})` onto `(0, t₀)`. -/
theorem hitTime_image_Iio {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀) :
    hitTime vL vR ζ '' Iio (log (sepN vL vR t₀)) = Ioo 0 t₀ := by
  ext s
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' := (exp_lt_sepN_iff h ht₀ ht0).1 hu
    obtain ⟨hle, he⟩ := hitTime_spec h ht₀ hu'.le
    refine ⟨pos_iff_ne_zero.2 fun h0 => ?_, lt_of_le_of_ne hle fun heq => ?_⟩
    · rw [h0, sepN_zero h] at he
      exact (exp_pos u).ne' he.symm
    · rw [heq] at he
      exact hu'.ne he.symm
  · rintro ⟨hs0, hst⟩
    have hsζ : (s : ℝ≥0∞) < ζ := lt_trans (by exact_mod_cast hst) ht₀
    refine ⟨log (sepN vL vR s), ?_, hitTime_log_sepN h hsζ hs0⟩
    exact log_lt_log (sepN_pos h hsζ hs0) (sepN_lt_sepN h ht₀ hst le_rfl)

theorem strictMonoOn_hitTime {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀) :
    StrictMonoOn (hitTime vL vR ζ) (Iio (log (sepN vL vR t₀))) := by
  intro u₁ hu₁ u₂ hu₂ h12
  have m1 := ((exp_lt_sepN_iff h ht₀ ht0).1 hu₁).le
  have m2 := ((exp_lt_sepN_iff h ht₀ ht0).1 hu₂).le
  refine lt_of_le_of_ne (monotoneOn_hitTime h ht₀ m1 m2 h12.le) fun he => ?_
  have e1 := (hitTime_spec h ht₀ m1).2
  have e2 := (hitTime_spec h ht₀ m2).2
  rw [he, e2] at e1
  exact h12.ne (exp_injective e1).symm

/-- The angle process is continuous below `log ℓ_{t₀}`. -/
theorem continuousAt_logAngle {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀) {u : ℝ}
    (hu : u < log (sepN vL vR t₀)) : ContinuousAt (logAngle w vL vR ζ) u := by
  have hτ : ContinuousAt (hitTime vL vR ζ) u := by
    refine (strictMonoOn_hitTime h ht₀ ht0).continuousAt_of_image_mem_nhds (Iio_mem_nhds hu) ?_
    rw [hitTime_image_Iio h ht₀ ht0]
    refine isOpen_Ioo.mem_nhds ?_
    rw [← hitTime_image_Iio h ht₀ ht0]
    exact mem_image_of_mem _ hu
  have hc : ContinuousAt (fun v => gapC w vL t₀ (hitTime vL vR ζ v) / exp v) u :=
    ((continuous_gapC h ht₀).continuousAt.comp hτ).div continuous_exp.continuousAt (exp_pos u).ne'
  refine hc.congr ?_
  filter_upwards [Iio_mem_nhds hu] with v hv
  exact (logAngle_eq_gapC h ht₀ ((exp_lt_sepN_iff h ht₀ ht0).1 hv).le).symm

/-- If `ℓ` is unbounded before the lifetime, every level `e^u` is reached: there is `t₀ < ζ` with
`0 < t₀` and `u < log ℓ_{t₀}`. -/
theorem exists_lt_log_sepN (hunb : ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ M ≤ sepN vL vR t)
    (u : ℝ) : ∃ t₀ : ℝ≥0, (t₀ : ℝ≥0∞) < ζ ∧ 0 < t₀ ∧ u < log (sepN vL vR t₀) := by
  obtain ⟨t₀, ht₀, hM⟩ := hunb (exp (u + 1))
  have ht0 : 0 < t₀ := pos_iff_ne_zero.2 fun h0 => by
    rw [h0, sepN_zero h] at hM
    exact absurd hM (not_le.2 (exp_pos _))
  refine ⟨t₀, ht₀, ht0, (exp_lt_sepN_iff h ht₀ ht0).2 ?_⟩
  exact (exp_lt_exp.2 (by linarith)).trans_le hM

/-- **The angle process is a continuous path** when `ℓ` is unbounded before the lifetime. -/
theorem continuous_logAngle (hunb : ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ M ≤ sepN vL vR t) :
    Continuous (logAngle w vL vR ζ) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  obtain ⟨t₀, ht₀, ht0, hu⟩ := exists_lt_log_sepN h hunb u
  exact continuousAt_logAngle h ht₀ ht0 hu

theorem logAngle_mem_Icc' (hunb : ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ M ≤ sepN vL vR t)
    (u : ℝ) : logAngle w vL vR ζ u ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨t₀, ht₀, ht0, hu⟩ := exists_lt_log_sepN h hunb u
  exact logAngle_mem_Icc h ht₀ ((exp_lt_sepN_iff h ht₀ ht0).1 hu).le

/-- The boundary set of the angle is null below each level `log ℓ_{t₀}`: the change of variables
maps it into the null collision sets. -/
theorem volume_logAngle_boundary_inter {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (ht0 : 0 < t₀)
    (hmeas : MeasurableSet {v | logAngle w vL vR ζ v = 0 ∨ logAngle w vL vR ζ v = 1}) :
    volume ({v | logAngle w vL vR ζ v = 0 ∨ logAngle w vL vR ζ v = 1} ∩
      Iic (log (sepN vL vR t₀))) = 0 := by
  set S := {v | logAngle w vL vR ζ v = 0 ∨ logAngle w vL vR ζ v = 1}
  set F : ℝ → ℝ → ℝ := fun y a => if a = 0 ∨ a = 1 then y⁻¹ else 0 with hF
  have hFm : Measurable (Function.uncurry F) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 = 0 ∨ p.2 = 1} :=
      (measurableSet_eq_fun measurable_snd measurable_const).union
        (measurableSet_eq_fun measurable_snd measurable_const)
    exact Measurable.ite hset measurable_fst.inv measurable_const
  have key := lintegral_exp_mul_logAngle_eq h ht₀ ht0 F hFm (fun _ => 0) ?_
  · simp only [ENNReal.ofReal_zero, lintegral_zero] at key
    have heq : ∀ v, ENNReal.ofReal (exp v * F (exp v) (logAngle w vL vR ζ v)) =
        S.indicator 1 v := by
      intro v
      by_cases hv : v ∈ S
      · have hv' : logAngle w vL vR ζ v = 0 ∨ logAngle w vL vR ζ v = 1 := hv
        simp only [hF, ite_eq_left hv', mul_inv_cancel₀ (exp_pos v).ne', ENNReal.ofReal_one,
          indicator_of_mem hv, Pi.one_apply]
      · have hv' : ¬ (logAngle w vL vR ζ v = 0 ∨ logAngle w vL vR ζ v = 1) := hv
        simp only [hF, ite_eq_right hv', mul_zero, ENNReal.ofReal_zero, indicator_of_notMem hv]
    simp only [heq] at key
    rw [lintegral_indicator_one hmeas, Measure.restrict_apply hmeas] at key
    exact key
  · filter_upwards [ae_gaps_pos h ht₀] with s hs hsI
    obtain ⟨hX, hY⟩ := hs hsI
    rw [sepC_eq_add (w := w) hsI.2]
    have hne : ¬ (gapLR w vL s / (gapLR w vL s + gapRR w vR s) = 0 ∨
        gapLR w vL s / (gapLR w vL s + gapRR w vR s) = 1) := by
      rintro (h0 | h1)
      · exact (div_pos hX (by linarith)).ne' h0
      · rw [div_eq_one_iff_eq (by linarith)] at h1
        linarith
    simp only [hF]
    rw [ite_eq_right hne, mul_zero]

/-- **The boundary set of the angle is Lebesgue-null** when `ℓ` is unbounded before the lifetime
(Specification p. 23, L520, there derived from stationarity; here from the null collision sets). -/
theorem volume_logAngle_boundary (hunb : ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ M ≤ sepN vL vR t) :
    volume {v | logAngle w vL vR ζ v = 0 ∨ logAngle w vL vR ζ v = 1} = 0 := by
  have hc := continuous_logAngle h hunb
  have hmeas : MeasurableSet {v | logAngle w vL vR ζ v = 0 ∨ logAngle w vL vR ζ v = 1} :=
    (measurableSet_eq_fun hc.measurable measurable_const).union
      (measurableSet_eq_fun hc.measurable measurable_const)
  choose t ht ht0 hn using fun n : ℕ => exists_lt_log_sepN h hunb n
  have hsub : {v | logAngle w vL vR ζ v = 0 ∨ logAngle w vL vR ζ v = 1} ⊆
      ⋃ n : ℕ, ({v | logAngle w vL vR ζ v = 0 ∨ logAngle w vL vR ζ v = 1} ∩
        Iic (log (sepN vL vR (t n)))) := by
    intro v hv
    obtain ⟨n, hn'⟩ := exists_nat_ge v
    exact mem_iUnion.2 ⟨n, hv, hn'.trans (hn n).le⟩
  exact measure_mono_null hsub (measure_iUnion_null fun n =>
    volume_logAngle_boundary_inter h (ht n) (ht0 n) hmeas)

end Angle

section Infinite

variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ⊤)
include h

/-- With infinite lifetime the separation is unbounded (`8 t ≤ ℓ_t²`). -/
theorem sepN_unbounded_of_top (M : ℝ) : ∃ t : ℝ≥0, (t : ℝ≥0∞) < ⊤ ∧ M ≤ sepN vL vR t := by
  rcases le_or_gt M 0 with hM | hM
  · exact ⟨0, ENNReal.coe_lt_top, by rw [sepN_zero h]; exact hM⟩
  · set t : ℝ≥0 := ⟨M ^ 2, sq_nonneg M⟩
    have ht : (t : ℝ) = M ^ 2 := rfl
    have ht0 : 0 < t := by rw [← NNReal.coe_pos, ht]; positivity
    have h8 := eight_mul_le_sepN_sq h (t := t) ENNReal.coe_lt_top
    have hpos := (sepN_pos h ENNReal.coe_lt_top ht0).le
    rw [ht] at h8
    refine ⟨t, ENNReal.coe_lt_top, not_lt.1 fun hlt => ?_⟩
    have := mul_self_lt_mul_self hpos hlt
    nlinarith

/-- With infinite lifetime the clock of the angle process diverges. -/
theorem tendsto_clock_logAngle_of_top : Tendsto (clock (logAngle w vL vR ⊤)) atTop atTop := by
  have hunb := sepN_unbounded_of_top h
  have hc := continuous_logAngle h hunb
  have h01 := logAngle_mem_Icc' h hunb
  refine tendsto_atTop.2 fun M => ?_
  set t : ℝ≥0 := ⟨max M 0 + 1, by positivity⟩
  have htt : (t : ℝ) = max M 0 + 1 := rfl
  have ht0 : 0 < t := by
    rw [← NNReal.coe_pos, htt]
    have := le_max_right M 0
    linarith
  filter_upwards [eventually_ge_atTop (log (sepN vL vR t))] with u hu
  have := monotone_clock hc h01 hu
  rw [clock_logAngle_eq h ENNReal.coe_lt_top ht0, htt] at this
  linarith [le_max_left M 0]

/-- **A two-seed solution with infinite lifetime is the time-changed clock construction of its
angle process** (Specification p. 24, L546): `U = logAngle w vL vR ⊤` is a continuous path in
`[0, 1]` with null boundary set and divergent clock, and `w = wPath U`, `vL = vLPath U`,
`vR = vRPath U`. -/
theorem eq_twoSeedPaths_logAngle :
    Continuous (logAngle w vL vR ⊤) ∧ (∀ v, logAngle w vL vR ⊤ v ∈ Icc (0 : ℝ) 1) ∧
      volume {v | logAngle w vL vR ⊤ v = 0 ∨ logAngle w vL vR ⊤ v = 1} = 0 ∧
      Tendsto (clock (logAngle w vL vR ⊤)) atTop atTop ∧
      w = wPath (logAngle w vL vR ⊤) ∧ vL = vLPath (logAngle w vL vR ⊤) ∧
      vR = vRPath (logAngle w vL vR ⊤) := by
  have hunb := sepN_unbounded_of_top h
  have hc := continuous_logAngle h hunb
  have h01 := logAngle_mem_Icc' h hunb
  have hnull := volume_logAngle_boundary h hunb
  have htop := tendsto_clock_logAngle_of_top h
  have hinv : ∀ t : ℝ≥0, 0 < t → invClock (logAngle w vL vR ⊤) t = log (sepN vL vR t) := by
    intro t ht0
    rw [← clock_logAngle_eq h ENNReal.coe_lt_top ht0, invClock_clock hc h01 hnull htop]
  have hphys : ∀ (f : ℝ → ℝ) (g : ℝ≥0 → ℝ), g 0 = 0 →
      (∀ t : ℝ≥0, 0 < t → g t = f (log (sepN vL vR t))) →
      g = fun t : ℝ≥0 => phys (logAngle w vL vR ⊤) f t := by
    intro f g hg0 hg
    funext t
    rcases eq_zero_or_pos t with rfl | ht0
    · rw [hg0, NNReal.coe_zero, phys_of_nonpos le_rfl]
    · rw [phys_of_pos (NNReal.coe_pos.2 ht0), hinv t ht0, hg t ht0]
  refine ⟨hc, h01, hnull, htop, ?_, ?_, ?_⟩
  · refine hphys _ _ ?_ fun t ht0 => w_eq_driver_logAngle h ENNReal.coe_lt_top ht0
    obtain ⟨hw, -⟩ := h
    exact hw
  · funext i
    rw [Subsingleton.elim i 0]
    exact hphys _ _ (path_vL_zero h) fun t ht0 => vL_eq_lowerL_logAngle h ENNReal.coe_lt_top ht0
  · funext i
    rw [Subsingleton.elim i 0]
    exact hphys _ _ (path_vR_zero h) fun t ht0 => vR_eq_upperL_logAngle h ENNReal.coe_lt_top ht0

end Infinite

section General

variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
include h

/-- **The separation is unbounded before the lifetime** (Specification p. 24, L546: "If a maximal
physical lifetime were finite and `ℓ` had a finite limit, monotonicity and `V^L ≤ 0 ≤ V^R` would give
finite limits for both force coordinates. The integrated driving identity then gives a finite limit
for `W`. … contradicting maximality"). The finite-limit step is PROVE-SEC2-TERM's
`Sec2.IsForcePath.exists_tendsto_of_bdd`; with weights `> -2` no limiting two-seed state satisfies
the threshold condition. -/
theorem sepN_unbounded (hb : Continuous b) (hρL : ∀ i, -2 < ρL i) (hρR : ∀ i, -2 < ρR i)
    (M : ℝ) : ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ M ≤ sepN vL vR t := by
  rcases eq_or_ne ζ ⊤ with rfl | hζ
  · exact sepN_unbounded_of_top h M
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  obtain ⟨T, rfl⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ := ⟨ζ.toNNReal, ENNReal.coe_toNNReal hζ⟩
  rcases eq_zero_or_pos T with rfl | hT
  · exact not_thresholdCondition_fin_one hρL hρR _ _ _
      (h.isForcePath.threshold_of_eq_zero (by simp))
  have hlt : ∀ s : ℝ≥0, s < T → (s : ℝ≥0∞) < (T : ℝ≥0∞) := fun s hs => by exact_mod_cast hs
  have hLb : ∀ i, ∃ M' : ℝ, ∀ s : ℝ≥0, s < T → M' ≤ vL i s := fun i => ⟨-M, fun s hs => by
    rw [Subsingleton.elim i 0]
    have h1 := hcon s (hlt s hs)
    have h2 : (0 : ℝ) ≤ vR 0 s := h.isForcePath.xR_le_vR (hlt s hs) 0
    rw [sepN] at h1
    linarith⟩
  have hRb : ∀ j, ∃ M' : ℝ, ∀ s : ℝ≥0, s < T → vR j s ≤ M' := fun j => ⟨M, fun s hs => by
    rw [Subsingleton.elim j 0]
    have h1 := hcon s (hlt s hs)
    have h2 : vL 0 s ≤ (0 : ℝ) := h.isForcePath.vL_le_xL (hlt s hs) 0
    rw [sepN] at h1
    linarith⟩
  obtain ⟨w₀, vL₀, vR₀, -, hth⟩ := h.isForcePath.exists_tendsto_of_bdd h.driverEq hT rfl
    hb.continuousOn hLb hRb
  exact not_thresholdCondition_fin_one hρL hρR _ _ _ hth

/-- With a finite lifetime the clock of the angle process is bounded by the lifetime. -/
theorem clock_logAngle_le (hb : Continuous b) (hρL : ∀ i, -2 < ρL i) (hρR : ∀ i, -2 < ρR i)
    (u : ℝ) : ENNReal.ofReal (clock (logAngle w vL vR ζ) u) ≤ ζ := by
  have hunb := sepN_unbounded h hb hρL hρR
  obtain ⟨t₀, ht₀, ht0, hu⟩ := exists_lt_log_sepN h hunb u
  have hmono := monotone_clock (continuous_logAngle h hunb) (logAngle_mem_Icc' h hunb) hu.le
  rw [clock_logAngle_eq h ht₀ ht0] at hmono
  calc ENNReal.ofReal (clock (logAngle w vL vR ζ) u) ≤ ENNReal.ofReal (t₀ : ℝ) :=
        ENNReal.ofReal_le_ofReal hmono
    _ = (t₀ : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
    _ ≤ ζ := ht₀.le

/-- **If the clock of the angle process diverges, the lifetime is infinite.** (For the evolution:
the stationary Jacobi clock diverges almost surely, Specification p. 23, L520.) -/
theorem lifetime_eq_top_of_tendsto_clock (hb : Continuous b) (hρL : ∀ i, -2 < ρL i)
    (hρR : ∀ i, -2 < ρR i) (htop : Tendsto (clock (logAngle w vL vR ζ)) atTop atTop) : ζ = ⊤ := by
  by_contra hζ
  obtain ⟨u, hu⟩ := (htop.eventually_gt_atTop (ζ.toReal + 1)).exists
  have h1 := clock_logAngle_le h hb hρL hρR u
  have h2 : ENNReal.ofReal (clock (logAngle w vL vR ζ) u) ≤ ENNReal.ofReal ζ.toReal := by
    rwa [ENNReal.ofReal_toReal hζ]
  have h3 := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2
  linarith

/-- **Pathwise uniqueness reduction, general lifetime** (Specification p. 24, L542–L546): for a
two-seed solution with weights `> -2` and continuous driving path, the angle process `U` is a
continuous path in `[0, 1]` with null boundary set, and before the lifetime the solution is the
clock construction of `U`. -/
theorem logAngle_spec (hb : Continuous b) (hρL : ∀ i, -2 < ρL i) (hρR : ∀ i, -2 < ρR i) :
    Continuous (logAngle w vL vR ζ) ∧ (∀ v, logAngle w vL vR ζ v ∈ Icc (0 : ℝ) 1) ∧
      volume {v | logAngle w vL vR ζ v = 0 ∨ logAngle w vL vR ζ v = 1} = 0 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → 0 < t →
        clock (logAngle w vL vR ζ) (log (sepN vL vR t)) = t ∧
        vL 0 t = lowerL (logAngle w vL vR ζ) (log (sepN vL vR t)) ∧
        vR 0 t = upperL (logAngle w vL vR ζ) (log (sepN vL vR t)) ∧
        w t = driver (logAngle w vL vR ζ) (log (sepN vL vR t)) := by
  have hunb := sepN_unbounded h hb hρL hρR
  exact ⟨continuous_logAngle h hunb, logAngle_mem_Icc' h hunb, volume_logAngle_boundary h hunb,
    fun t ht ht0 => eq_twoSeed_logAngle h ht ht0⟩

end General

end TwoSeed

end Sec2

end InteractingSLE
