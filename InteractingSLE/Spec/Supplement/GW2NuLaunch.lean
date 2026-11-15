/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NuOrd
import InteractingSLE.Spec.Supplement.SB2VrRad
import InteractingSLE.Spec.Supplement.RLCG8DetApproach

/-!
# The launch chart at the candidate's death: the zero mark collides, and earlier bounces lie inside the tip

Packet PROVE-GW2-NOTHR (round 3, D35 (D-a)). In its own chart the candidate dies at a threshold of its own word
(Theorem 1.3's `ζ = T_*`, the limit state of the integrated path). Read through any continuous extension `U` of the
driver:

* **`launch_zero_collision`**: at the death, if the tip is a positive (negative) real point, the zero mark collides
  with `U` on the right (left);
* **`prior_le_of_zero_collision`**, **`prior_ge_of_zero_collision`**: then every earlier real visit of the
  (complete) trace lies weakly inside the tip. A visit beyond it kills the visited point, so the visited point's
  right image is the zero mark's (`rightImg_eq_of_not_alive_of_le`). That forces a collision beyond the tip, which
  `real_tip_of_rightImg_eq` rules out.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Nu

open MartChar.RealFlow Restart SB.Vq

/-- A complete generating trace is a generating trace up to every finite time. -/
theorem isGeneratingTrace_restrict {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (h : IsGeneratingTrace w ⊤ γ) (T : ℝ≥0) :
    IsGeneratingTrace w T γ :=
  ⟨h.1, h.2.1.mono fun t _ => show ((t : ℝ≥0∞)) ≤ ⊤ from le_top, fun t _ => h.2.2 t ENNReal.coe_lt_top⟩

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The zero mark collides at the death** (in the launch chart, read through a continuous extension `U` of the
driver): on the right if the tip is a positive real point, on the left if it is a negative real point. -/
theorem launch_zero_collision {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {β : ℝ≥0 → ℝ}
    {γ : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR β T)
    (hgen : IsGeneratingTrace w T γ) (hβ : ContinuousAt β T) {U : ℝ≥0 → ℝ} (hUc : Continuous U)
    (hUw : ∀ t : ℝ≥0, t < T → U t = w t) :
    (0 < (γ T).re → rightImg (fun r : ℝ => U r.toNNReal) 0 T = U T) ∧
      ((γ T).re < 0 → rightImg (fun r : ℝ => -U r.toNNReal) 0 T = -U T) := by
  obtain ⟨M, hM⟩ := SB.Vr.exists_abs_le_of_isGeneratingTrace hp.2.2.2.1 hp.1 hgen
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
  have hp' := hp
  obtain ⟨hw0, hvL0, hvR0, -, -, -, -, hvLw, hwvR, -, -, -, -, -, -, -, -, -, -, -⟩ := hp'
  have hT0 : ((0 : ℝ≥0) : ℝ≥0∞) < (T : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hT
  have hxR : ∀ j, 0 ≤ xR j := fun j => by rw [← hvR0 j, ← hw0]; exact hwvR 0 hT0 j
  have hxL : ∀ i, xL i ≤ 0 := fun i => by rw [← hvL0 i, ← hw0]; exact hvLw 0 hT0 i
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvR : ∀ j, Tendsto (vR j) (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
    (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim
  have hvL : ∀ i, Tendsto (vL i) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    (((continuous_apply i).comp (continuous_fst.comp continuous_snd)).tendsto _).comp hlim
  set Ur : ℝ → ℝ := fun r => U r.toNNReal with hUrdef
  have hU : Continuous Ur := hUc.comp continuous_real_toNNReal
  have hU0 : Ur 0 = 0 := by
    show U (0 : ℝ).toNNReal = 0
    rw [Real.toNNReal_zero, hUw 0 hT]
    exact hw0
  have hUT : Ur T = w₀ := by
    show U (T : ℝ).toNNReal = w₀
    rw [Real.toNNReal_coe]
    have h1 : Tendsto U (𝓝[<] T) (𝓝 (U T)) := (hUc.tendsto T).mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique h1 (hw.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hUw t ht).symm
  have hUrw : ∀ t : ℝ≥0, t < T → Ur t = w t := fun t ht => by
    show U (t : ℝ).toNNReal = w t
    rw [Real.toNNReal_coe]
    exact hUw t ht
  have hgen' : IsGeneratingTrace U T γ :=
    Sec5.CrossRestart.isGeneratingTrace_congr_drive hgen fun t ht => hUw t (ENNReal.coe_lt_coe.1 ht)
  have hη := CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hgen'
  have hc : ContinuousOn (fun s : ℝ => γ s.toNNReal) (Icc 0 (T : ℝ)) :=
    hgen'.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
      ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hT' : (0 : ℝ) < T := hT
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hU hU0 hT' hc
  have htip : extendFrom H (fwdMapInv Ur T) 0 = γ T := by
    rw [TraceClose.extendFrom_zero_eq hη hU hU0 hT' hc, Real.toNNReal_coe]
  -- the reflected chart
  have hη' := SB.Vo.isLoewnerTraceLT_reflect hη
  have hc' : ContinuousOn (fun s : ℝ => LP.reflectC (γ s.toNNReal)) (Icc 0 (T : ℝ)) :=
    LP.continuous_reflectC.comp_continuousOn hc
  have hnU : Continuous (-Ur) := hU.neg
  have hnU0 : (-Ur) 0 = 0 := by simp [hU0]
  have hB' := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη' hnU hnU0 hT' hc'
  have htip' : extendFrom H (fwdMapInv (-Ur) T) 0 = LP.reflectC (γ T) := by
    rw [TraceClose.extendFrom_zero_eq hη' hnU hnU0 hT' hc', Real.toNNReal_coe]
  have hre' : (LP.reflectC (γ T)).re = -(γ T).re := by simp [LP.reflectC]
  -- the collided sets of the two sides
  have hfiltR : univ.filter (fun j => vR₀ j = w₀) = univ.filter (fun j => rightImg Ur (xR j) T = Ur T) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, rightImg_eq_lim hT hp hU hUrw j (hvR j), hUT]
  have hfiltL : univ.filter (fun i => vL₀ i = w₀) =
      univ.filter (fun i => rightImg (-Ur) (-xL i) T = (-Ur) T) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply,
      neg_rightImg_neg_eq_lim hT hp hU hUrw i (hvL i), hUT]
    constructor <;> intro h <;> linarith
  -- a nonempty collided set collides the zero mark
  have hzR : (univ.filter (fun j => rightImg Ur (xR j) T = Ur T)).Nonempty → rightImg Ur 0 T = Ur T := by
    rintro ⟨j₀, hj₀⟩
    have hcoll : rightImg Ur (xR j₀) T = Ur T := (Finset.mem_filter.1 hj₀).2
    exact le_antisymm ((rightImg_mono_index hU T.2 (hxR j₀)).trans hcoll.le) (le_rightImg hU 0 T.2)
  have hzL : (univ.filter (fun i => rightImg (-Ur) (-xL i) T = (-Ur) T)).Nonempty →
      rightImg (-Ur) 0 T = (-Ur) T := by
    rintro ⟨i₀, hi₀⟩
    have hcoll : rightImg (-Ur) (-xL i₀) T = (-Ur) T := (Finset.mem_filter.1 hi₀).2
    exact le_antisymm ((rightImg_mono_index hnU T.2 (neg_nonneg.2 (hxL i₀))).trans hcoll.le)
      (le_rightImg hnU 0 T.2)
  have hne : ∀ {n : ℕ} {ρ : Fin n → ℝ} {S : Finset (Fin n)}, ∑ k ∈ S, ρ k ≤ -2 → S.Nonempty := by
    intro n ρ S h
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, sum_empty] at h
    linarith
  constructor
  · intro hpos
    rcases hthr with hthL | hthR
    · rw [hfiltL] at hthL
      obtain ⟨-, hre, -⟩ := right_bad_of_collision (xR := fun i => -xL i) hnU hnU0 T.2 hB' htip'
        (fun i => neg_nonneg.2 (hxL i)) hthL
      linarith
    · rw [hfiltR] at hthR
      have h := hzR (hne hthR)
      rwa [show Ur T = U T by simp [hUrdef]] at h
  · intro hneg
    rcases hthr with hthL | hthR
    · rw [hfiltL] at hthL
      have h := hzL (hne hthL)
      show rightImg (-Ur) 0 T = -U T
      rw [h]
      simp [hUrdef]
    · rw [hfiltR] at hthR
      obtain ⟨-, hre, -⟩ := right_bad_of_collision hU hU0 T.2 hB htip hxR hthR
      linarith

end Path

section Prior

variable {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}

/-- **No earlier real visit beyond a positive tip** (right side): with a complete trace, if the zero mark collides at
`T` and the tip at `T` is a positive real point, every earlier real visit is at most the tip. -/
theorem prior_le_of_zero_collision (hw : Continuous w) (hw0 : w 0 = 0) (hγc : Continuous γ)
    (hgen : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0} (hT : 0 < T)
    (hzero : rightImg (fun r : ℝ => w r.toNNReal) 0 T = w T) (hpos : 0 < (γ T).re) {t : ℝ≥0} (htT : t < T)
    (him : (γ t).im = 0) : (γ t).re ≤ (γ T).re := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  set Ur : ℝ → ℝ := fun r => w r.toNNReal with hUrdef
  have hU : Continuous Ur := hw.comp continuous_real_toNNReal
  have hU0 : Ur 0 = 0 := by simp [hUrdef, hw0]
  have hy : γ t = (((γ t).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hdead : ¬ Alive Ur (γ t).re T := fun hA =>
    RLC.G8Det.not_alive_of_real_visit hγc hw hw0 hgen htT hy ⟨_, WangWu.isForwardSol_of_alive hU hA⟩
  have hT' : (0 : ℝ) ≤ T := T.coe_nonneg
  have heq := rightImg_eq_of_not_alive_of_le hU hT' (hpos.le.trans hlt.le) hdead
  have hcoll : rightImg Ur (γ t).re T = Ur T := by
    rw [← heq, hzero]
    simp [hUrdef]
  have hη := CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace (isGeneratingTrace_restrict hgen T)
  have hc : ContinuousOn (fun s : ℝ => γ s.toNNReal) (Icc 0 (T : ℝ)) :=
    (hγc.comp continuous_real_toNNReal).continuousOn
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hU hU0 (by exact_mod_cast hT) hc
  have htip : extendFrom H (fwdMapInv Ur T) 0 = γ T := by
    rw [TraceClose.extendFrom_zero_eq hη hU hU0 (by exact_mod_cast hT) hc, Real.toNNReal_coe]
  have h := (Restart.FlowStopIdentLL.real_tip_of_rightImg_eq hU hU0 hT' hB htip hcoll).2
  linarith

/-- **No earlier real visit beyond a negative tip** (left side, by reflection). -/
theorem prior_ge_of_zero_collision (hw : Continuous w) (hw0 : w 0 = 0) (hγc : Continuous γ)
    (hgen : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0} (hT : 0 < T)
    (hzero : rightImg (fun r : ℝ => -w r.toNNReal) 0 T = -w T) (hneg : (γ T).re < 0) {t : ℝ≥0} (htT : t < T)
    (him : (γ t).im = 0) : (γ T).re ≤ (γ t).re := by
  have hgen' : IsGeneratingTrace (fun s => -w s) ⊤ (fun s => LP.reflectC (γ s)) := by
    have h := LP.isGeneratingTrace_reflect hgen
    exact h
  have hγc' : Continuous fun s => LP.reflectC (γ s) := LP.continuous_reflectC.comp hγc
  have hre : ∀ z : ℂ, (LP.reflectC z).re = -z.re ∧ (LP.reflectC z).im = z.im := fun z => by
    simp [LP.reflectC]
  have h := prior_le_of_zero_collision (w := fun s => -w s) (γ := fun s => LP.reflectC (γ s)) hw.neg
    (by simp [hw0]) hγc' hgen' hT hzero (by rw [(hre _).1]; linarith) htT (by rw [(hre _).2]; exact him)
  rw [(hre _).1, (hre _).1] at h
  linarith

end Prior

end InteractingSLE.Theorem14.GW2Nu
