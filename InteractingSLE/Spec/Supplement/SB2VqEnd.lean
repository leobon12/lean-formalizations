/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VoCol
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Sec2.TerminalEscape
import InteractingSLE.Spec.Sec7.Lemma71BStop
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.ZhanGT4.A1CommonExit

/-!
# D10, plan step 1: at a finite lifetime the flow is at a bad point (the convergent case)

Packet PROVE-AUX61-NOJUMP (ruling R120, D10 = B1, option (a)). The stops of SB2(1)'s successor version are first
entrances of the physical tip near the bad real set. They lie strictly below the lifetime because a finite lifetime
ends at a bad real point. This file proves that for one path, in the convergent alternative of Aux. lemma 3
(`IsIntegratedSLEPath.tendsto_or_criticalEscape`).

* `wR`, `wL`, `IsBadPoint`: the right cumulative weight up to a real point `y ≥ 0`, the left one from `y ≤ 0`, and a
  bad point (real, with one of them `≤ −2`).
* **`tip_bad_of_tendsto`** (deterministic): for an integrated SLE path with finite positive lifetime `T`, a
  generating trace on `[0, T]`, and a state converging at `T` to a state satisfying the threshold condition, the
  tip `γ T` is a bad point. The steps:
  * extend the driver by its limit (`Vk.frz`, continuous);
  * identify the force coordinates with the geometric images before `T` (`SideHeightGeom.vR_eq_rightImg_frozenDrive`
    and the left version), and pass to `T` by continuity of the images (`continuousOn_rightImg`);
  * apply the collision lemmas at `T`: a collision puts the tip on `ℝ` right of the mark
    (`FlowStopIdentLL.real_tip_of_rightImg_eq`), and then the colliding marks are those at or left of the tip
    (`FlowStopIdentLL.rightImg_eq_iff_of_zero_collision`); left side by reflection (`Vo.isLoewnerTraceLT_reflect`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Finset
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Vq

open MartChar.RealFlow

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The right cumulative weight up to the real point `y`. -/
def wR (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (y : ℝ) : ℝ := ∑ j ∈ univ.filter (fun j => xR j ≤ y), ρR j

/-- The left cumulative weight from the real point `y`. -/
def wL (xL : Fin nL → ℝ) (ρL : Fin nL → ℝ) (y : ℝ) : ℝ := ∑ i ∈ univ.filter (fun i => y ≤ xL i), ρL i

/-- **A bad point** of the force word: a real point whose outward cumulative weight is `≤ −2`. -/
def IsBadPoint (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (z : ℂ) : Prop :=
  z.im = 0 ∧ ((0 ≤ z.re ∧ wR xR ρR z.re ≤ -2) ∨ (z.re ≤ 0 ∧ wL xL ρL z.re ≤ -2))

/-- The colliding right marks at a real tip `y`, once the zero mark collides, are those `≤ y`. -/
theorem filter_eq_of_zero_collision {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hB : HasBdryLimits (fwdMapInv U T)) {p : ℂ} (htip : extendFrom H (fwdMapInv U T) 0 = p)
    (hzero : rightImg U 0 T = U T) (xR : Fin nR → ℝ) :
    univ.filter (fun j => rightImg U (xR j) T = U T) = univ.filter (fun j => xR j ≤ p.re) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Restart.FlowStopIdentLL.rightImg_eq_iff_of_zero_collision hU hU0 hT hB htip hzero (xR j)

/-- **A right collision at a horizon puts the tip at a bad right point.** -/
theorem right_bad_of_collision {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hB : HasBdryLimits (fwdMapInv U T)) {p : ℂ} (htip : extendFrom H (fwdMapInv U T) 0 = p)
    (hxR : ∀ j, 0 ≤ xR j)
    (hthr : ∑ j ∈ univ.filter (fun j => rightImg U (xR j) T = U T), ρR j ≤ -2) :
    p.im = 0 ∧ 0 ≤ p.re ∧ wR xR ρR p.re ≤ -2 := by
  obtain ⟨j₀, hj₀⟩ : (univ.filter (fun j => rightImg U (xR j) T = U T)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, sum_empty] at hthr
    linarith
  have hcoll : rightImg U (xR j₀) T = U T := (Finset.mem_filter.1 hj₀).2
  obtain ⟨him, hle⟩ := Restart.FlowStopIdentLL.real_tip_of_rightImg_eq hU hU0 hT hB htip hcoll
  have hzero : rightImg U 0 T = U T :=
    le_antisymm ((rightImg_mono_index hU hT (hxR j₀)).trans hcoll.le) (le_rightImg hU 0 hT)
  rw [filter_eq_of_zero_collision hU hU0 hT hB htip hzero xR] at hthr
  exact ⟨him, (hxR j₀).trans hle, hthr⟩

/-- **Right images of the extended driver at the horizon.** If the right force coordinate of an integrated SLE path
converges at the finite lifetime `T`, and `U` is continuous and equal to the driver before `T`, then the geometric image
of the mark at `T` is the limit. -/
theorem rightImg_eq_lim {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {β : ℝ≥0 → ℝ} {T : ℝ≥0}
    (hT : 0 < T) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR β T) {U : ℝ → ℝ} (hU : Continuous U)
    (hUw : ∀ t : ℝ≥0, t < T → U t = w t) (j : Fin nR) {v₀ : ℝ} (hv : Tendsto (vR j) (𝓝[<] T) (𝓝 v₀)) :
    rightImg U (xR j) T = v₀ := by
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have heq : ∀ t : ℝ≥0, t < T → vR j t = rightImg U (xR j) t := fun t ht => by
    rw [Sec7.SideHeight.vR_eq_rightImg_frozenDrive hp (t₂ := t)
      (by rw [ENNReal.ofReal_coe_nnreal]; exact ENNReal.coe_lt_coe.2 ht) le_rfl j]
    refine Sec7.Lemma71B.rightImg_congr hU t.2 (fun s hs => ?_) (xR j)
    have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
    have h1 : w (min s (t : ℝ)).toNNReal = w s.toNNReal :=
      congrArg (fun r : ℝ => w r.toNNReal) (min_eq_left hs.2)
    have h2 : U s = w s.toNNReal := by
      have := hUw _ (lt_of_le_of_lt hst ht)
      rwa [Real.coe_toNNReal _ hs.1] at this
    exact h1.trans h2.symm
  have hc : Tendsto (fun t : ℝ≥0 => rightImg U (xR j) t) (𝓝[<] T) (𝓝 (rightImg U (xR j) T)) := by
    have hcw := continuousOn_rightImg hU (xR j) (T : ℝ) T.2
    refine hcw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun t => t.2⟩)
    exact (NNReal.continuous_coe.tendsto T).mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique (hc.congr' ?_) hv
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (heq t ht).symm

/-- **Left images of the extended driver at the horizon**, by reflection. -/
theorem neg_rightImg_neg_eq_lim {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {β : ℝ≥0 → ℝ}
    {T : ℝ≥0} (hT : 0 < T) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR β T) {U : ℝ → ℝ} (hU : Continuous U)
    (hUw : ∀ t : ℝ≥0, t < T → U t = w t) (i : Fin nL) {v₀ : ℝ} (hv : Tendsto (vL i) (𝓝[<] T) (𝓝 v₀)) :
    rightImg (-U) (-xL i) T = -v₀ := by
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have heq : ∀ t : ℝ≥0, t < T → vL i t = -rightImg (-U) (-xL i) t := fun t ht => by
    rw [Sec7.SideHeight.vL_eq_neg_rightImg_frozenDrive hp (t₂ := t)
      (by rw [ENNReal.ofReal_coe_nnreal]; exact ENNReal.coe_lt_coe.2 ht) le_rfl i]
    congr 1
    refine Sec7.Lemma71B.rightImg_congr hU.neg t.2 (fun s hs => ?_) (-xL i)
    have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
    have h1 : w (min s (t : ℝ)).toNNReal = w s.toNNReal :=
      congrArg (fun r : ℝ => w r.toNNReal) (min_eq_left hs.2)
    have h2 : U s = w s.toNNReal := by
      have := hUw _ (lt_of_le_of_lt hst ht)
      rwa [Real.coe_toNNReal _ hs.1] at this
    exact congrArg Neg.neg (h1.trans h2.symm)
  have hc : Tendsto (fun t : ℝ≥0 => -rightImg (-U) (-xL i) t) (𝓝[<] T) (𝓝 (-rightImg (-U) (-xL i) T)) := by
    have hcw := continuousOn_rightImg hU.neg (-xL i) (T : ℝ) T.2
    refine (hcw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun t => t.2⟩)).neg
    exact (NNReal.continuous_coe.tendsto T).mono_left nhdsWithin_le_nhds
  have h := tendsto_nhds_unique (hc.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heq t ht).symm)) hv
  linarith

/-- **D10 step 1, convergent case: a finite lifetime with a converging state ends at a bad point.** -/
theorem tip_bad_of_tendsto {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {β : ℝ≥0 → ℝ}
    {γ : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR β T)
    (hgen : IsGeneratingTrace w T γ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) : IsBadPoint xL xR ρL ρR (γ T) := by
  have hp' := hp
  obtain ⟨hw0, hvL0, hvR0, hwc, -, -, -, hvLw, hwvR, -, -, -, -, -, -, -, -, -, -, -⟩ := hp'
  have hT0 : ((0 : ℝ≥0) : ℝ≥0∞) < (T : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hT
  have hxR : ∀ j, 0 ≤ xR j := fun j => by rw [← hvR0 j, ← hw0]; exact hwvR 0 hT0 j
  have hxL : ∀ i, xL i ≤ 0 := fun i => by rw [← hvL0 i, ← hw0]; exact hvLw 0 hT0 i
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvR : ∀ j, Tendsto (vR j) (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
    (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim
  have hvL : ∀ i, Tendsto (vL i) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    (((continuous_apply i).comp (continuous_fst.comp continuous_snd)).tendsto _).comp hlim
  -- the driver extended by its limit
  set U' : ℝ≥0 → ℝ := Vk.frz w (T : ℝ≥0∞) with hU'def
  have hU' : Continuous U' := Vk.continuous_frz hT0 hwc fun _ => ⟨w₀, by rw [ENNReal.toNNReal_coe]; exact hw⟩
  set U : ℝ → ℝ := fun r => U' r.toNNReal with hUdef
  have hU : Continuous U := hU'.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by
    show U' (0 : ℝ).toNNReal = 0
    rw [Real.toNNReal_zero, hU'def, Vk.frz_of_lt hT0]
    exact hw0
  have hUT : U T = w₀ := by
    show U' (T : ℝ).toNNReal = w₀
    rw [Real.toNNReal_coe, hU'def, Vk.frz_of_le le_rfl, ENNReal.toNNReal_coe]
    exact hw.limUnder_eq
  have hUw : ∀ t : ℝ≥0, t < T → U t = w t := fun t ht => by
    show U' (t : ℝ).toNNReal = w t
    rw [Real.toNNReal_coe, hU'def, Vk.frz_of_lt (ENNReal.coe_lt_coe.2 ht)]
  -- the closed trace and its tip
  have hgen' : IsGeneratingTrace U' T γ :=
    Sec5.CrossRestart.isGeneratingTrace_congr_drive hgen fun t ht => Vk.frz_of_lt ht
  have hη := CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hgen'
  have hc : ContinuousOn (fun s : ℝ => γ s.toNNReal) (Icc 0 (T : ℝ)) :=
    hgen'.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
      ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hT' : (0 : ℝ) < T := hT
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hU hU0 hT' hc
  have htip : extendFrom H (fwdMapInv U T) 0 = γ T := by
    rw [TraceClose.extendFrom_zero_eq hη hU hU0 hT' hc, Real.toNNReal_coe]
  rcases hthr with hL | hR
  · -- a left threshold, by reflection
    have hη' := Vo.isLoewnerTraceLT_reflect hη
    have hc' : ContinuousOn (fun s : ℝ => LP.reflectC (γ s.toNNReal)) (Icc 0 (T : ℝ)) :=
      LP.continuous_reflectC.comp_continuousOn hc
    have hnU : Continuous (-U) := hU.neg
    have hnU0 : (-U) 0 = 0 := by simp [hU0]
    have hB' := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη' hnU hnU0 hT' hc'
    have htip' : extendFrom H (fwdMapInv (-U) T) 0 = LP.reflectC (γ T) := by
      rw [TraceClose.extendFrom_zero_eq hη' hnU hnU0 hT' hc', Real.toNNReal_coe]
    have hfilt : univ.filter (fun i => vL₀ i = w₀) =
        univ.filter (fun i => rightImg (-U) (-xL i) T = (-U) T) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply,
        neg_rightImg_neg_eq_lim hT hp hU hUw i (hvL i), hUT]
      constructor <;> intro h <;> linarith
    rw [hfilt] at hL
    obtain ⟨him, hre, hw'⟩ := right_bad_of_collision (xR := fun i => -xL i) hnU hnU0 T.2 hB' htip'
      (fun i => neg_nonneg.2 (hxL i)) hL
    have hre' : (LP.reflectC (γ T)).re = -(γ T).re := by simp [LP.reflectC]
    have him' : (LP.reflectC (γ T)).im = (γ T).im := by simp [LP.reflectC]
    refine ⟨him' ▸ him, Or.inr ⟨by linarith [hre' ▸ hre], ?_⟩⟩
    have hwL : wR (fun i => -xL i) ρL (LP.reflectC (γ T)).re = wL xL ρL (γ T).re := by
      unfold wR wL
      rw [hre']
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_le_neg_iff]
    rw [← hwL]
    exact hw'
  · have hfilt : univ.filter (fun j => vR₀ j = w₀) = univ.filter (fun j => rightImg U (xR j) T = U T) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, rightImg_eq_lim hT hp hU hUw j (hvR j), hUT]
    rw [hfilt] at hR
    obtain ⟨him, hre, hw'⟩ := right_bad_of_collision hU hU0 T.2 hB htip hxR hR
    exact ⟨him, Or.inl ⟨hre, hw'⟩⟩

/-- **D10 step 1 with a bounded driver**: an integrated SLE path with finite positive lifetime `T`, a generating
trace on `[0, T]`, a driving noise continuous at `T`, and a driver bounded before `T`, ends at a bad point. The force
coordinates are then bounded (`Sec2.IsForcePath.vR_le_of_w_le`, `vL_ge_of_le_w`). So the state converges
(`ZhanGT4.A1Common.exists_tendsto_state_of_path`) to a threshold state (the path's `threshold_of_tendsto`), and
`tip_bad_of_tendsto` applies. This rules out the critical-escape alternative of Aux. lemma 3 whenever the driver is
bounded. -/
theorem tip_bad_of_bounded {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {β : ℝ≥0 → ℝ}
    {γ : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR β T)
    (hgen : IsGeneratingTrace w T γ) (hβ : ContinuousAt β T) {M : ℝ}
    (hM : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → |w t| ≤ M) : IsBadPoint xL xR ρL ρR (γ T) := by
  have hF := hp.isForcePath
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by exact_mod_cast hT))
  have hR : ∀ t < T, ∀ j, vR j t ≤ (∑ k, |xR k|) + M + 1 + 2 * (T : ℝ) := fun t ht j => by
    have h1 := hF.vR_le_of_w_le (m := M) (fun s hs => (le_abs_self _).trans (hM s hs)) j
      (ENNReal.coe_lt_coe.2 ht)
    have h2 : xR j ≤ ∑ k, |xR k| :=
      (le_abs_self _).trans (Finset.single_le_sum (fun k _ => abs_nonneg (xR k)) (Finset.mem_univ j))
    have h3 : (t : ℝ) ≤ T := by exact_mod_cast ht.le
    have h4 : 0 ≤ ∑ k, |xR k| := Finset.sum_nonneg fun k _ => abs_nonneg (xR k)
    have h5 : max (xR j) (M + 1) ≤ (∑ k, |xR k|) + M + 1 := max_le (by linarith) (by linarith)
    linarith
  have hL : ∀ t < T, ∀ i, -((∑ k, |xL k|) + M + 1 + 2 * (T : ℝ)) ≤ vL i t := fun t ht i => by
    have h1 := hF.vL_ge_of_le_w (m := -M) (fun s hs => by
      have := hM s hs
      rw [abs_le] at this
      linarith [this.1]) i (ENNReal.coe_lt_coe.2 ht)
    have h2 : -(∑ k, |xL k|) ≤ xL i := by
      have := (neg_abs_le (xL i))
      have h' : |xL i| ≤ ∑ k, |xL k| := Finset.single_le_sum (fun k _ => abs_nonneg (xL k)) (Finset.mem_univ i)
      linarith
    have h3 : (t : ℝ) ≤ T := by exact_mod_cast ht.le
    have h4 : 0 ≤ ∑ k, |xL k| := Finset.sum_nonneg fun k _ => abs_nonneg (xL k)
    have h5 : -((∑ k, |xL k|) + M + 1) ≤ min (xL i) (-M - 1) := le_min (by linarith) (by linarith)
    linarith
  obtain ⟨w₀, vL₀, vR₀, hlim⟩ := ZhanGT4.A1Common.exists_tendsto_state_of_path hp le_rfl hβ hL hR
  have hthr := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 T hT rfl w₀ vL₀ vR₀ hlim
  exact tip_bad_of_tendsto hT hp hgen hlim hthr

end InteractingSLE.Theorem14.SB.Vq
