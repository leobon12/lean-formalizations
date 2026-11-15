/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS3ReachProofGood
import InteractingSLE.Spec.Supplement.DS3ProofReach

/-!
# Lemma DS3 in reach form, II: the hitting time of the cross-gap level `r`

Packet PROVE-T14-DS3. The restart time of the proof of Lemma DS3 (spec p. 554): instead of a small deterministic time
`t₀` the restart is made at the hitting time `τ_r` of the level `r` by the geometric cross gap
`D = V^{1,R} − V^{1,L}` (at a fixed level of the logarithmic clock of the two-seed construction). By
`DS3.four_mul_sqrt_le_crossGap` (`D_t ≥ 4√t`), `τ_r ≤ r²/16` (`tauR_le`), so `τ_r` plays the role of the source's small
deterministic time with the deterministic cross-gap bound `a = r` at the restart (`le_crossGap_tauR`).

* `gapR`, `tauR`, `TR`: `τ_r` as the hitting time of `0` by the killed family `r − D` (landed `Assembly3.killedFam`),
  and its value capped at `1`;
* pathwise: `crossGap_lt_of_lt_tauR`, `tauR_le` (`τ_r ≤ r²/16`), `le_crossGap_tauR` (`D_{τ_r} ≥ r` when `τ_r < ζ`),
  `crossGap_le_of_le_tauR`, and **`dist_state_le_crossGap`**: before the lifetime, with both seeds at `0`, the whole
  state is within `D_t` of the initial state (every other mark moves less than the nearest one on its side);
* measurability: `isStoppingTime_TR`, and `measurableSet_tauR_lt` (the event `{τ_r < ζ}` off a null set belongs to
  `𝓖_{T_r}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DS3Reach

open Sec2 Sec2.Assembly2 Sec2.Assembly3

variable {Ω : Type*} {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR)

/-- `r − D` as a one-element family, `D = V^{1,R} − V^{1,L}`. -/
def gapR (r : ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Unit → ℝ≥0 → Ω → ℝ :=
  fun _ t ω => r - (VR ⟨0, hnR⟩ t ω - VL ⟨0, hnL⟩ t ω)

/-- The hitting time `τ_r` of the level `r` by the cross gap (the lifetime if it is not reached). -/
def tauR (r : ℝ) (ζ : Ω → ℝ≥0∞) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  hitTime (killedFam ζ (gapR hnL hnR r VL VR)) 0 ω

/-- `τ_r` capped at `1`. -/
def TR (r : ℝ) (ζ : Ω → ℝ≥0∞) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  (min (tauR hnL hnR r ζ VL VR ω) 1).toNNReal

theorem coe_TR (r : ℝ) (ζ : Ω → ℝ≥0∞) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (TR hnL hnR r ζ VL VR ω : ℝ≥0∞) = min (tauR hnL hnR r ζ VL VR ω) 1 :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))

/-! ### Pathwise facts -/

section Path

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
  {r : ℝ}

/-- The cross gap at a time. -/
abbrev cg (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  VR ⟨0, hnR⟩ t ω - VL ⟨0, hnL⟩ t ω

theorem continuousOn_gapR (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (ζ ω)) (k : Unit) :
    ContinuousOn (gapR hnL hnR r VL VR k · ω) {t | (t : ℝ≥0∞) < ζ ω} :=
  continuousOn_const.sub ((hp.continuousOn_vR _).sub (hp.continuousOn_vL _))

theorem isClosed_hitSet (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (ζ ω)) :
    IsClosed {t : ℝ≥0 | ∃ k, killedFam ζ (gapR hnL hnR r VL VR) k t ω ≤ 0} :=
  isClosed_killedFam le_rfl (continuousOn_gapR hnL hnR hp)

theorem crossGap_lt_of_lt_tauR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < tauR hnL hnR r ζ VL VR ω) :
    (t : ℝ≥0∞) < ζ ω ∧ cg hnL hnR VL VR t ω < r := by
  obtain ⟨h1, h2⟩ := lt_of_lt_hitTime_killedFam (Y := gapR hnL hnR r VL VR) le_rfl ht
  have := h2 ()
  simp only [gapR] at this
  exact ⟨h1, by linarith⟩

/-- **`τ_r ≤ r²/16`** (from `D_t ≥ 4√t`). -/
theorem tauR_le (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (ζ ω)) (hr : 0 ≤ r) :
    tauR hnL hnR r ζ VL VR ω ≤ ((r ^ 2 / 16).toNNReal : ℝ≥0∞) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hcon
  obtain ⟨htζ, htr⟩ := crossGap_lt_of_lt_tauR hnL hnR h2
  have h4 := DS3.four_mul_sqrt_le_crossGap hnL hnR hp htζ
  have hlt : r ^ 2 / 16 < (t : ℝ) := by
    have := (Real.toNNReal_lt_iff_lt_coe (r := r ^ 2 / 16) (by positivity)).1 (by exact_mod_cast h1)
    exact this
  have hsq : r < 4 * Real.sqrt t := by
    have : Real.sqrt (r ^ 2 / 16) < Real.sqrt t := Real.sqrt_lt_sqrt (by positivity) hlt
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 16), Real.sqrt_sq hr,
      show Real.sqrt 16 = 4 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    linarith
  simp only [DS3.crossGap] at h4
  linarith

/-- At `τ_r < ζ` the cross gap has reached `r`. -/
theorem le_crossGap_tauR (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (ζ ω)) (hlt : tauR hnL hnR r ζ VL VR ω < ζ ω) :
    r ≤ cg hnL hnR VL VR (tauR hnL hnR r ζ VL VR ω).toNNReal ω := by
  have hne : tauR hnL hnR r ζ VL VR ω ≠ ⊤ := ne_top_of_lt hlt
  set s := (tauR hnL hnR r ζ VL VR ω).toNNReal with hs
  have hsτ : (s : ℝ≥0∞) = tauR hnL hnR r ζ VL VR ω := ENNReal.coe_toNNReal hne
  obtain ⟨t, hts, k, hk⟩ := (hitTime_le_iff_of_isClosed (isClosed_hitSet hnL hnR hp) (s := s)).1
    (le_of_eq hsτ.symm)
  have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [hsτ]; exact hlt
  have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hts) hsζ
  simp only [killedFam, Girsanov.killed_of_lt htζ, gapR] at hk
  have h1 := hp.vL_le_of_le hts hsζ ⟨0, hnL⟩
  have h2 := hp.le_vR_of_le hts hsζ ⟨0, hnR⟩
  simp only [cg]
  linarith

/-- Up to `τ_r` the cross gap is at most `r` (with both seeds at `0`). -/
theorem crossGap_le_of_le_tauR (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (ζ ω)) (hL0 : xL ⟨0, hnL⟩ = 0) (hR0 : xR ⟨0, hnR⟩ = 0) (hr : 0 ≤ r) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ tauR hnL hnR r ζ VL VR ω) (htζ : (t : ℝ≥0∞) < ζ ω) :
    cg hnL hnR VL VR t ω ≤ r := by
  rcases lt_or_eq_of_le ht with h | h
  · exact (crossGap_lt_of_lt_tauR hnL hnR h).2.le
  rcases eq_or_ne t 0 with h0 | h0
  · simp only [cg, h0, hp.vL_zero, hp.vR_zero, hL0, hR0, sub_zero]; exact hr
  · have hne : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 h0⟩
    have hcont : ContinuousWithinAt (fun s => cg hnL hnR VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω} t :=
      ((hp.continuousOn_vR _).sub (hp.continuousOn_vL _)) t htζ
    have hU : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} ∈ 𝓝 t :=
      (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds htζ
    have hlim : Tendsto (fun s => cg hnL hnR VL VR s ω) (𝓝[<] t) (𝓝 (cg hnL hnR VL VR t ω)) :=
      ((hcont.continuousAt hU).tendsto).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun s hs => ?_)
    have : (s : ℝ≥0∞) < tauR hnL hnR r ζ VL VR ω := by
      rw [← h]; exact_mod_cast (show s < t from hs)
    exact (crossGap_lt_of_lt_tauR hnL hnR this).2.le

/-- A left mark moves at most as far as a nearer one. -/
theorem sub_vL_le (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (ζ ω)) {t : ℝ≥0} (htζ : (t : ℝ≥0∞) < ζ ω) (i : Fin nL) :
    xL i - VL i t ω ≤ xL ⟨0, hnL⟩ - VL ⟨0, hnL⟩ t ω := by
  have ei := hp.vL_eq htζ i
  have e0 := hp.vL_eq htζ ⟨0, hnL⟩
  have hi := hp.intervalIntegrable_forceL htζ i
  have h0 := hp.intervalIntegrable_forceL htζ ⟨0, hnL⟩
  have key : ∫ s in (0 : ℝ)..t, 2 / (VL ⟨0, hnL⟩ s.toNNReal ω - W s.toNNReal ω) ≤
      ∫ s in (0 : ℝ)..t, 2 / (VL i s.toNNReal ω - W s.toNNReal ω) := by
    refine intervalIntegral.integral_mono_ae_restrict (NNReal.coe_nonneg t) h0 hi ?_
    have hnull := hp.volume_collisionL ⟨0, hnL⟩
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun s hs hsI => ?_
    simp only [mem_ofPred_eq, not_and] at hs
    have hsζ : (s.toNNReal : ℝ≥0∞) < ζ ω := Sec2.toNNReal_lt_of_mem_Icc htζ hsI
    have hne := hs hsI.1 hsζ
    have hord := hp.antitone_vL hsζ (Fin.le_def.2 (Nat.zero_le (i : ℕ)) : (⟨0, hnL⟩ : Fin nL) ≤ i)
    have hw0 := hp.vL_le_w hsζ ⟨0, hnL⟩
    have hpos : 0 < W s.toNNReal ω - VL ⟨0, hnL⟩ s.toNNReal ω :=
      lt_of_le_of_ne (by linarith) (fun h => hne (by linarith))
    have hle : W s.toNNReal ω - VL ⟨0, hnL⟩ s.toNNReal ω ≤ W s.toNNReal ω - VL i s.toNNReal ω := by
      simp only at hord; linarith
    rw [show VL ⟨0, hnL⟩ s.toNNReal ω - W s.toNNReal ω = -(W s.toNNReal ω - VL ⟨0, hnL⟩ s.toNNReal ω)
        by ring, show VL i s.toNNReal ω - W s.toNNReal ω = -(W s.toNNReal ω - VL i s.toNNReal ω) by ring,
      div_neg, div_neg, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by norm_num) hpos hle
  rw [ei, e0]
  linarith

theorem vR_sub_le (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (ζ ω)) {t : ℝ≥0} (htζ : (t : ℝ≥0∞) < ζ ω) (j : Fin nR) :
    VR j t ω - xR j ≤ VR ⟨0, hnR⟩ t ω - xR ⟨0, hnR⟩ := by
  have ej := hp.vR_eq htζ j
  have e0 := hp.vR_eq htζ ⟨0, hnR⟩
  have hj := hp.intervalIntegrable_forceR htζ j
  have h0 := hp.intervalIntegrable_forceR htζ ⟨0, hnR⟩
  have key : ∫ s in (0 : ℝ)..t, 2 / (VR j s.toNNReal ω - W s.toNNReal ω) ≤
      ∫ s in (0 : ℝ)..t, 2 / (VR ⟨0, hnR⟩ s.toNNReal ω - W s.toNNReal ω) := by
    refine intervalIntegral.integral_mono_ae_restrict (NNReal.coe_nonneg t) hj h0 ?_
    have hnull := hp.volume_collisionR ⟨0, hnR⟩
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun s hs hsI => ?_
    simp only [mem_ofPred_eq, not_and] at hs
    have hsζ : (s.toNNReal : ℝ≥0∞) < ζ ω := Sec2.toNNReal_lt_of_mem_Icc htζ hsI
    have hne := hs hsI.1 hsζ
    have hord := hp.monotone_vR hsζ (Fin.le_def.2 (Nat.zero_le (j : ℕ)) : (⟨0, hnR⟩ : Fin nR) ≤ j)
    have hw0 := hp.w_le_vR hsζ ⟨0, hnR⟩
    have hpos : 0 < VR ⟨0, hnR⟩ s.toNNReal ω - W s.toNNReal ω :=
      lt_of_le_of_ne (by linarith) (fun h => hne (by linarith))
    have hle : VR ⟨0, hnR⟩ s.toNNReal ω - W s.toNNReal ω ≤ VR j s.toNNReal ω - W s.toNNReal ω := by
      simp only at hord; linarith
    exact div_le_div_of_nonneg_left (by norm_num) hpos hle
  rw [ej, e0]
  linarith

/-- **Before the lifetime, with both seeds at `0`, the state is within `D_t` of the initial state.** -/
theorem dist_state_le_crossGap (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) (ζ ω)) (hL0 : xL ⟨0, hnL⟩ = 0) (hR0 : xR ⟨0, hnR⟩ = 0) {t : ℝ≥0}
    (htζ : (t : ℝ≥0∞) < ζ ω) :
    dist (Coupling.stateAt W VL VR t ω) ((0 : ℝ), xL, xR) ≤ cg hnL hnR VL VR t ω := by
  have hL := hp.vL_le_of_le (zero_le (a := t)) htζ ⟨0, hnL⟩
  have hR := hp.le_vR_of_le (zero_le (a := t)) htζ ⟨0, hnR⟩
  simp only [hp.vL_zero, hp.vR_zero, hL0, hR0] at hL hR
  have hwL := hp.vL_le_w htζ ⟨0, hnL⟩
  have hwR := hp.w_le_vR htζ ⟨0, hnR⟩
  have hD0 : 0 ≤ cg hnL hnR VL VR t ω := by simp only [cg]; linarith
  rw [Prod.dist_eq, Prod.dist_eq]
  refine max_le ?_ (max_le ?_ ?_)
  · simp only [Coupling.stateAt, Real.dist_eq, sub_zero, cg]
    rw [abs_le]; constructor <;> linarith
  · refine (dist_pi_le_iff hD0).2 fun i => ?_
    have h1 := sub_vL_le hnL hp htζ i
    have h2 := hp.vL_le_of_le (zero_le (a := t)) htζ i
    simp only [hp.vL_zero, hL0] at h1 h2
    simp only [Coupling.stateAt, Real.dist_eq, cg]
    rw [abs_le]; constructor <;> linarith
  · refine (dist_pi_le_iff hD0).2 fun j => ?_
    have h1 := vR_sub_le hnR hp htζ j
    have h2 := hp.le_vR_of_le (zero_le (a := t)) htζ j
    simp only [hp.vR_zero, hR0] at h1 h2
    simp only [Coupling.stateAt, Real.dist_eq, cg]
    rw [abs_le]; constructor <;> linarith

end Path

/-! ### Measurability -/

section Meas

variable {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {r : ℝ}

theorem adaptedBefore_gapR (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓖 ζ (VR j))
    (k : Unit) : AdaptedBefore 𝓖 ζ (gapR hnL hnR r VL VR k) := by
  intro t A hA
  have hm : Measurable[𝓖 t] fun ω => r - (Girsanov.killed ζ (VR ⟨0, hnR⟩) t ω -
      Girsanov.killed ζ (VL ⟨0, hnL⟩) t ω) :=
    measurable_const.sub ((Girsanov.measurable_killed (hVR _) t).sub (Girsanov.measurable_killed (hVL _) t))
  have hlife : MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using hVL ⟨0, hnL⟩ t univ MeasurableSet.univ
  have heq : {ω | (t : ℝ≥0∞) < ζ ω ∧ gapR hnL hnR r VL VR k t ω ∈ A} = {ω | (t : ℝ≥0∞) < ζ ω} ∩
      (fun ω => r - (Girsanov.killed ζ (VR ⟨0, hnR⟩) t ω - Girsanov.killed ζ (VL ⟨0, hnL⟩) t ω)) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, gapR]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [Girsanov.killed_of_lt h1, Girsanov.killed_of_lt h1]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [Girsanov.killed_of_lt h1, Girsanov.killed_of_lt h1] at h2⟩
  rw [heq]
  exact hlife.inter (hm hA)

/-- **`T_r` is a stopping time.** -/
theorem isStoppingTime_TR (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓖 ζ (VR j))
    (hVLc : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ j ω, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    IsStoppingTime 𝓖 fun ω => (TR hnL hnR r ζ VL VR ω : WithTop ℝ≥0) := by
  intro s
  have hhit := measurableSet_hitTime_killedFam_le (Y := gapR hnL hnR r VL VR) (𝓕 := 𝓖) le_rfl
    (adaptedBefore_gapR hnL hnR hVL hVR) (fun k ω => continuousOn_const.sub
      ((hVRc _ ω).sub (hVLc _ ω))) s
  have e : {ω | (TR hnL hnR r ζ VL VR ω : WithTop ℝ≥0) ≤ s} =
      {ω | tauR hnL hnR r ζ VL VR ω ≤ s} ∪ {_ω | (1 : ℝ≥0) ≤ s} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union]
    rw [show ((TR hnL hnR r ζ VL VR ω : WithTop ℝ≥0) ≤ s) ↔ ((TR hnL hnR r ζ VL VR ω : ℝ≥0∞) ≤ s) from
      WithTop.coe_le_coe.trans ENNReal.coe_le_coe.symm, coe_TR, min_le_iff]
    simp only [ENNReal.one_le_coe_iff]
  rw [e]
  exact hhit.union (MeasurableSet.const _)

theorem hitTime_le_of_mem {Y : Unit → ℝ≥0 → Ω → ℝ} {ω : Ω} {t : ℝ≥0} (h : killedFam ζ Y () t ω ≤ 0) :
    hitTime (killedFam ζ Y) 0 ω ≤ t :=
  iInf₂_le (f := fun (t : ℝ≥0) (_ : ∃ k, killedFam ζ Y k t ω ≤ 0) => (t : ℝ≥0∞)) t ⟨(), h⟩

/-- **The event `{τ_r < ζ}` (off a null set) is `𝓖_{T_r}`-measurable.** -/
theorem measurableSet_tauR_lt {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓖 ζ (VR j))
    (hVLc : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ j ω, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω}) {N : Set Ω}
    (hN : ∀ t, MeasurableSet[𝓖 t] N)
    (hgood : ∀ ω, ω ∉ N → IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    (hr0 : 0 ≤ r) (hr4 : r ≤ 4) :
    MeasurableSet[(isStoppingTime_TR hnL hnR (r := r) hVL hVR hVLc hVRc).measurableSpace]
      ({ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ) := by
  set hT := isStoppingTime_TR hnL hnR (r := r) hVL hVR hVLc hVRc
  -- on good paths `T_r = τ_r`
  have hTeq : ∀ ω, ω ∉ N → (TR hnL hnR r ζ VL VR ω : ℝ≥0∞) = tauR hnL hnR r ζ VL VR ω := fun ω hω => by
    rw [coe_TR, min_eq_left]
    refine (tauR_le hnL hnR (hgood ω hω) hr0).trans ?_
    rw [← ENNReal.coe_one, ENNReal.coe_le_coe, Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    nlinarith
  have hstep : ∀ s : ℝ≥0, MeasurableSet[𝓖 s]
      (({ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ) ∩ {ω | (TR hnL hnR r ζ VL VR ω : WithTop ℝ≥0) ≤ s}) := by
    intro s
    set E : Set Ω := Nᶜ ∩ ({ω | (s : ℝ≥0∞) < ζ ω ∧ gapR hnL hnR r VL VR () s ω ∈ Iic 0} ∪
      ⋃ q : ℚ, {ω | (q : ℝ).toNNReal < s ∧ ((q : ℝ).toNNReal : ℝ≥0∞) < ζ ω ∧
        gapR hnL hnR r VL VR () (q : ℝ).toNNReal ω ∈ Iic 0}) with hE
    have hEm : MeasurableSet[𝓖 s] E := by
      refine (hN s).compl.inter ((adaptedBefore_gapR hnL hnR hVL hVR () s _ measurableSet_Iic).union
        (MeasurableSet.iUnion fun q => ?_))
      by_cases hq : (q : ℝ).toNNReal < s
      · simp only [hq, true_and]
        exact 𝓖.mono hq.le _ (adaptedBefore_gapR hnL hnR hVL hVR () _ _ measurableSet_Iic)
      · simp only [hq, false_and, ofPred_false, MeasurableSet.empty]
    convert hEm using 1
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff, hE, mem_union, mem_iUnion, mem_Iic]
    by_cases hω : ω ∈ N
    · simp only [hω, not_true_eq_false, and_false, false_and]
    simp only [hω, not_false_eq_true, and_true, true_and]
    have hp := hgood ω hω
    rw [show ((TR hnL hnR r ζ VL VR ω : WithTop ℝ≥0) ≤ s) ↔ ((TR hnL hnR r ζ VL VR ω : ℝ≥0∞) ≤ s) from
      WithTop.coe_le_coe.trans ENNReal.coe_le_coe.symm, hTeq ω hω]
    constructor
    · rintro ⟨hlt, hle⟩
      have hne : tauR hnL hnR r ζ VL VR ω ≠ ⊤ := ne_top_of_lt hlt
      set τ := (tauR hnL hnR r ζ VL VR ω).toNNReal with hτ
      have hττ : (τ : ℝ≥0∞) = tauR hnL hnR r ζ VL VR ω := ENNReal.coe_toNNReal hne
      have hD := le_crossGap_tauR hnL hnR hp hlt
      have hτs : τ ≤ s := by rw [← ENNReal.coe_le_coe, hττ]; exact hle
      have hτζ : (τ : ℝ≥0∞) < ζ ω := by rw [hττ]; exact hlt
      rcases eq_or_lt_of_le hτs with h | h
      · left
        rw [← h]
        refine ⟨hτζ, ?_⟩
        simp only [gapR]; simp only [cg] at hD; linarith
      · right
        obtain ⟨u, hτu, huζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hτζ
        have hτu' : τ < u := by exact_mod_cast hτu
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (τ : ℝ) < min (s : ℝ) (u : ℝ) from
          lt_min (by exact_mod_cast h) (by exact_mod_cast hτu'))
        have hq0 : 0 ≤ (q : ℝ) := (NNReal.coe_nonneg τ).trans hq1.le
        have hqs : (q : ℝ).toNNReal < s := by
          rw [Real.toNNReal_lt_iff_lt_coe hq0]; exact lt_of_lt_of_le hq2 (min_le_left _ _)
        have hqu : (q : ℝ).toNNReal < u := by
          rw [Real.toNNReal_lt_iff_lt_coe hq0]; exact lt_of_lt_of_le hq2 (min_le_right _ _)
        have hqζ : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω :=
          lt_trans (by exact_mod_cast hqu) huζ
        have hτq : τ ≤ (q : ℝ).toNNReal := by
          rw [Real.le_toNNReal_iff_coe_le hq0]; exact hq1.le
        have h1 := hp.vL_le_of_le hτq hqζ ⟨0, hnL⟩
        have h2 := hp.le_vR_of_le hτq hqζ ⟨0, hnR⟩
        refine ⟨q, hqs, hqζ, ?_⟩
        simp only [gapR]; simp only [cg] at hD; linarith
    · rintro (⟨hsζ, hg⟩ | ⟨q, hqs, hqζ, hg⟩)
      · have hle : tauR hnL hnR r ζ VL VR ω ≤ s :=
          hitTime_le_of_mem (by simp only [killedFam, Girsanov.killed_of_lt hsζ]; exact hg)
        exact ⟨lt_of_le_of_lt hle hsζ, hle⟩
      · have hle : tauR hnL hnR r ζ VL VR ω ≤ (q : ℝ).toNNReal :=
          hitTime_le_of_mem (by simp only [killedFam, Girsanov.killed_of_lt hqζ]; exact hg)
        exact ⟨lt_of_le_of_lt hle hqζ, hle.trans (by exact_mod_cast hqs.le)⟩
  refine (hT.measurableSet _).2 ⟨?_, hstep⟩
  -- `T_r ≤ 1` everywhere
  have h1 : ({ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ) =
      ({ω | tauR hnL hnR r ζ VL VR ω < ζ ω} ∩ Nᶜ) ∩ {ω | (TR hnL hnR r ζ VL VR ω : WithTop ℝ≥0) ≤ (1 : ℝ≥0)} := by
    refine (inter_eq_left.2 fun ω _ => ?_).symm
    show (TR hnL hnR r ζ VL VR ω : WithTop ℝ≥0) ≤ (1 : ℝ≥0)
    rw [WithTop.coe_le_coe, ← ENNReal.coe_le_coe, coe_TR, ENNReal.coe_one]
    exact min_le_right _ _
  rw [h1]
  exact le_iSup (fun t => (𝓖 t : MeasurableSpace Ω)) 1 _ (hstep 1)

end Meas

end DS3Reach

end Supp12

end InteractingSLE
