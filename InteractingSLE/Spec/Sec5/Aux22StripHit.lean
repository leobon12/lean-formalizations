/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22StripAlive
import InteractingSLE.Spec.Sec5.Aux22StripRetarget
import InteractingSLE.Spec.Sec7.ContinuityProb9Prefix
import InteractingSLE.Spec.Sec7.ContinuityProb10Close
import InteractingSLE.Spec.Sec7.ContinuityProb3Coding

/-!
# Aux. lemma 22 in the strip, step 4c: the first contact with the span, along one path

Packet PROVE-SEC5-L (specification §4.1, proof of Aux. lemma 22, pp. 114–115). Along one path of an integrated
evolution whose marks are all off the source (`xL < 0 < xR`), retargeted at the right mark `x_k`
(`k = LP.retargetIdx j m`, `ψ(z) = z/(x_k − z)`): if a trace `η_G` of the new driver on `[0, u]`, `u < S`, never visits
`ℝ \ {0}` before `S` and converges to `y ≠ −1` as `u ↑ S`, then the original trace `η` reaches `ψ⁻¹(y)` at a finite time
`t ≤ ζ` and never visits `ℝ \ {0}` before `t` (**`exists_hit_of_retarget`**).

Two cases.
* `S` at most the new horizon: `exists_hit_of_le` (`Aux22StripPull.lean`).
* `S` beyond the new horizon is impossible. Then the new trace is continuous on the closed `[0, T̃]` and off `−1`, the
  pull-back (PROVE-SEC7-C10's R6, `PullData.isGeneratingTrace_of_lt_top`, `…_top`) is the original trace on `[0, τ]`,
  `τ` finite (a transient pull-back of a bounded trace is impossible), and `η([0, τ])` meets `ℝ` only in `0`.
  Every mark is then alive on `[0, τ]` (`exists_isForwardSol_of_trace_avoid`; at `τ = ζ` with the hull at `ζ` from the
  trace closure, `Sec7.traceClosureStatement`), so no force path meets the driver at `τ`
  (`not_isForwardSol_of_tendsto_gap`). But at `τ` either the target meets the driver (`τ < ζ`, definition of
  `sepTime`), or a threshold group does (`τ = ζ`, the left limit at a finite lifetime).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol H fwdMap fwdHull)

namespace InteractingSLE

namespace Sec5

namespace Aux22Strip

open Zhan.Retarget

/-- A threshold condition at a point forces some mark to sit at the driver. -/
theorem exists_eq_of_thresholdCondition {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w₀ : ℝ}
    {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ} (h : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    (∃ i, vL₀ i = w₀) ∨ ∃ i, vR₀ i = w₀ := by
  rcases h with h | h
  · left
    by_contra hno
    push Not at hno
    rw [Finset.filter_false_of_mem fun i _ => hno i, Finset.sum_empty] at h
    norm_num at h
  · right
    by_contra hno
    push Not at hno
    rw [Finset.filter_false_of_mem fun i _ => hno i, Finset.sum_empty] at h
    norm_num at h

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The first contact with the span, along one path.** -/
theorem exists_hit_of_retarget (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hxL : ∀ i, xL i < 0) (hxR : ∀ i, 0 < xR i)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin (j + 1 + m) → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) {S : ℝ≥0} (hS0 : 0 < S) {ηG : ℝ≥0 → ℂ} (hG0 : ηG 0 = 0)
    {y : ℝ} (hy : y ≠ -1)
    (hgen : ∀ u : ℝ≥0, u < S → (u : ℝ≥0∞) < retargetHorizon xR w vR ζ →
      IsGeneratingTrace (newW xR w vR) u ηG)
    (hcontG : ∀ u : ℝ≥0, u < S → ContinuousAt ηG u)
    (havoid : ∀ u : ℝ≥0, u < S → ∀ z : ℝ, z ≠ 0 → ηG u ≠ z) (hconv : Tendsto ηG (𝓝[<] S) (𝓝 (y : ℂ))) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ (∀ s : ℝ≥0, s < t → ∀ z : ℝ, z ≠ 0 → η s ≠ z) ∧
      η t = Sec7.targetChangeInv (LP.retargetPos xR) y := by
  set k := LP.retargetIdx j m with hk
  set xk := LP.retargetPos xR with hxk
  set τ := sepTime w (vR k) ζ with hτdef
  have hτζ : τ ≤ ζ := sepTime_le w _ ζ
  have hrd := retargetData_of_isSLEPathUpTo (hp.isSLEPathUpTo hτζ) hD hj fun t ht => lt_of_lt_sepTime ht
  have hd : PullData w (vR k) xk τ := ⟨hrd.pos, hp.1, hrd.sep, hrd.target⟩
  obtain ⟨hw0, -, hvR0, hwc, hvLc, hvRc, -, -, hwle, -, -, -, -, hvLeq, hvReq, -, -, -, hthr0, -⟩ := hp
  by_cases hcase : (S : ℝ≥0∞) ≤ newHorizon xk w (vR k) τ
  · obtain ⟨t, htτ, havt, hηt⟩ := exists_hit_of_le hd hwc hτζ hη hS0 hy hgen havoid hconv hcase
    exact ⟨t, htτ.trans hτζ, havt, hηt⟩
  exfalso
  push Not at hcase
  have hτn : newHorizon xk w (vR k) τ ≠ ⊤ := ne_top_of_lt hcase
  set ρs : ℝ≥0 := (newHorizon xk w (vR k) τ).toNNReal with hρs
  have hρs' : (ρs : ℝ≥0∞) = newHorizon xk w (vR k) τ := ENNReal.coe_toNNReal hτn
  have hρsS : ρs < S := by rw [← ENNReal.coe_lt_coe, hρs']; exact hcase
  -- the new trace on the closed `[0, T̃]`
  have hηG' : IsGeneratingTrace (newDrv xk w (vR k)) (newHorizon xk w (vR k) τ) ηG := by
    refine ⟨hG0, fun u hu => (hcontG u ?_).continuousWithinAt, fun u hu => ?_⟩
    · have hu' : (u : ℝ≥0∞) ≤ ρs := by rw [hρs']; exact hu
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.1 hu') hρsS
    · obtain ⟨u', huu', hu'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hu
      have hu'S : u' < S := by
        refine lt_of_le_of_lt ?_ hρsS
        rw [← ENNReal.coe_le_coe, hρs']; exact hu'.le
      exact (hgen u' hu'S hu').2.2 u huu'
  -- the new trace stays away from `−1` on `[0, T̃]`
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ u : ℝ≥0, u ≤ ρs → c ≤ ‖ηG u + 1‖ := by
    have hcpt : IsCompact (Icc (0 : ℝ≥0) ρs) := isCompact_Icc
    have hfc : ContinuousOn (fun u => ‖ηG u + 1‖) (Icc 0 ρs) := fun u hu =>
      ((hcontG u (lt_of_le_of_lt hu.2 hρsS)).add continuousAt_const).norm.continuousWithinAt
    obtain ⟨u₀, hu₀, hmin⟩ := hcpt.exists_isMinOn ⟨0, le_rfl, zero_le⟩ hfc
    have hne : ηG u₀ + 1 ≠ 0 := fun h => havoid u₀ (lt_of_le_of_lt hu₀.2 hρsS) (-1) (by norm_num)
      (by rw [eq_neg_of_add_eq_zero_left h]; push_cast; ring)
    exact ⟨_, norm_pos_iff.2 hne, fun u hu => hmin ⟨zero_le, hu⟩⟩
  have hclkρ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → (clk (rate xk w (vR k)) t).toNNReal ≤ ρs := fun t ht => by
    have := (hd.clk_lt ht).le
    rw [← hρs'] at this
    exact_mod_cast this
  rcases eq_or_ne τ ⊤ with hτtop | hτtop
  · -- `τ = ∞`: the pulled-back trace is transient, yet bounded
    rw [hτtop] at hd hηG' hclkρ
    rw [hτtop] at hτn
    have htr := (hd.isGeneratingTrace_top hηG' fun h => absurd h hτn).2
    have hbd : ∀ t : ℝ≥0, ‖pullTrace xk w (vR k) ηG t‖ ≤ xk * (1 + 1 / c) := fun t =>
      norm_targetChangeInv_le hd.pos hc (hcle _ (hclkρ t ENNReal.coe_lt_top))
    obtain ⟨t, ht⟩ := (tendsto_atTop.1 htr (xk * (1 + 1 / c) + 1)).exists
    linarith [hbd t]
  -- `τ < ∞`: the original trace is the pull-back on `[0, τ]`
  set T : ℝ≥0 := τ.toNNReal with hTdef
  have hT' : (T : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hτtop
  have hlimw : ∀ T₀ : ℝ≥0, 0 < T₀ → (T₀ : ℝ≥0∞) = ζ → ∃ w₀ : ℝ, Tendsto w (𝓝[<] T₀) (𝓝 w₀) :=
    fun T₀ h0 hT₀ => by
      obtain ⟨w₀, vL₀, vR₀, hl, -⟩ := hlim T₀ h0 hT₀
      exact ⟨w₀, (continuous_fst.tendsto _).comp hl⟩
  obtain ⟨M, hM⟩ := Sec7.exists_bound_before hwc hτζ hτtop hlimw
  obtain ⟨R, hR⟩ := hd.exists_hull_bound hτtop hM
  have hP := hd.isGeneratingTrace_of_lt_top hηG' hτn hR
  have hηP : ∀ t : ℝ≥0, t ≤ T → η t = (if (t : ℝ≥0∞) < τ then pullTrace xk w (vR k) ηG t
      else Sec7.targetChangeInv xk (ηG (newHorizon xk w (vR k) τ).toNNReal)) := fun t ht =>
    IsGeneratingTrace.eq_of_le (hη.mono_horizon hτζ) hP
      (hwc.mono fun s (hs : (s : ℝ≥0∞) < τ) => lt_of_lt_of_le hs hτζ) hw0
      (by rw [← hT']; exact ENNReal.coe_le_coe.2 ht)
  have hav : ∀ t : ℝ≥0, t ≤ T → ∀ z : ℝ, z ≠ 0 → η t ≠ z := by
    intro t ht z hz
    rw [hηP t ht]
    split_ifs with h
    · exact targetChangeInv_ne_ofReal (havoid _ (lt_of_le_of_lt (hclkρ t h) hρsS)) hz
    · exact targetChangeInv_ne_ofReal (havoid _ hρsS) hz
  have hTζ : (T : ℝ≥0∞) ≤ ζ := hT'.le.trans hτζ
  have hηc : ContinuousOn η (Icc 0 T) :=
    hη.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hTζ
  rcases hτζ.lt_or_eq with hτζ' | hτζ'
  · -- `τ < ζ`: the target meets the driver at `τ`
    have hTζ' : (T : ℝ≥0∞) < ζ := hT' ▸ hτζ'
    have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
    have hwat : ContinuousAt w T := hwc.continuousAt (hopen.mem_nhds hTζ')
    have hvat : ContinuousAt (vR k) T := (hvRc k).continuousAt (hopen.mem_nhds hTζ')
    have hmeet : vR k T = w T := by
      refine le_antisymm ?_ (hwle T hTζ' k)
      by_contra hlt
      rw [not_le] at hlt
      have hev : ∀ᶠ s in 𝓝 T, w s < vR k s := hwat.eventually_lt hvat hlt
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hev.and (hopen.mem_nhds hTζ'))
      set ε' : ℝ≥0 := (ε / 2).toNNReal with hε'
      have hε'pos : 0 < ε' := Real.toNNReal_pos.2 (half_pos hε)
      have hge : ((T + ε' : ℝ≥0) : ℝ≥0∞) ≤ τ := by
        rw [hτdef, sepTime]
        refine le_min ?_ (le_iInf₂ fun s hs => ?_)
        · have h1 := (hball (show dist (T + ε') T < ε by
            rw [NNReal.dist_eq, NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg (NNReal.coe_nonneg _),
              Real.coe_toNNReal _ (half_pos hε).le]; linarith)).2
          exact h1.le
        · by_contra hlt'
          rw [not_le] at hlt'
          have hsT : s < T + ε' := ENNReal.coe_lt_coe.1 hlt'
          rcases lt_or_ge s T with h | h
          · have hsτ : (s : ℝ≥0∞) < sepTime w (vR k) ζ := by
              rw [← hτdef, ← hT']; exact ENNReal.coe_lt_coe.2 h
            have := lt_of_lt_sepTime hsτ
            linarith [hs.2]
          · have hd' : dist s T < ε := by
              rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h))]
              have := NNReal.coe_lt_coe.2 hsT
              rw [NNReal.coe_add, Real.coe_toNNReal _ (half_pos hε).le] at this
              linarith
            linarith [(hball hd').1, hs.2]
      rw [← hT'] at hge
      exact absurd (ENNReal.coe_le_coe.1 hge) (not_le.2 (lt_add_of_pos_right _ hε'pos))
    have hT0 : 0 < T := by
      rcases eq_zero_or_pos T with h | h
      · rw [h, hvR0 k, hw0] at hmeet
        exact absurd hmeet (hxR k).ne'
      · exact h
    -- the driver frozen beyond `T`, and the hull at `T`
    obtain ⟨t₂, hTt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTζ'
    have hTt₂' : T < t₂ := ENNReal.coe_lt_coe.1 hTt₂
    have hw2 : ContinuousOn w (Iic t₂) := hwc.mono fun s hs => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ht₂ζ
    set W' : ℝ → ℝ := fun s => freezeAt w t₂ s.toNNReal with hW'
    have hW'c : Continuous W' := continuous_freezeAt hw2
    have hW'0 : W' 0 = 0 := by simp only [hW', Real.toNNReal_zero]; rw [freezeAt_of_le zero_le, hw0]
    have hW'w : ∀ r ∈ Icc (0 : ℝ) t₂, (fun s : ℝ => w s.toNNReal) r = W' r := fun r hr => by
      have hr' : r.toNNReal ≤ t₂ := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2
      exact (freezeAt_of_le hr').symm
    have hfill : IsFilling (fwdHull W' T) (η '' Icc 0 T) := by
      rw [← fwdHull_eq_of_eqOn T.coe_nonneg (NNReal.coe_lt_coe.2 hTt₂') hW'w]
      exact hη.2.2 T hTζ'
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_trace_avoid hW'c hW'0 hηc hfill hav (hxR k).ne'
    refine not_isForwardSol_of_tendsto_gap hW'c hT0 (fun t ht => (hW'w t ⟨t.coe_nonneg,
      NNReal.coe_le_coe.2 (ht.trans hTt₂').le⟩).symm.trans (by simp)) ?_ ?_ (fun t ht => hvReq t ?_ k) ?_ hu
    · exact hwc.mono fun s (hs : s < T) => (ENNReal.coe_lt_coe.2 hs).trans hTζ'
    · exact (hvRc k).mono fun s (hs : s < T) => (ENNReal.coe_lt_coe.2 hs).trans hTζ'
    · exact (ENNReal.coe_lt_coe.2 ht).trans hTζ'
    · have h1 : Tendsto (fun t => vR k t - w t) (𝓝 T) (𝓝 (vR k T - w T)) := (hvat.sub hwat).tendsto
      rw [hmeet, sub_self] at h1
      exact h1.mono_left nhdsWithin_le_nhds
  · -- `τ = ζ`: a threshold group meets the driver at `ζ`
    have hTζ'' : (T : ℝ≥0∞) = ζ := hT'.trans hτζ'
    have hT0 : 0 < T := by
      rcases eq_zero_or_pos T with h | h
      · have hζ0 : ζ = 0 := by rw [← hTζ'', h, ENNReal.coe_zero]
        rcases exists_eq_of_thresholdCondition (hthr0 hζ0) with ⟨i, hi⟩ | ⟨i, hi⟩
        · exact absurd hi (hxL i).ne
        · exact absurd hi (hxR i).ne'
      · exact h
    obtain ⟨w₀, vL₀, vR₀, hl, hthr⟩ := hlim T hT0 hTζ''
    have hlw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hl
    have hwT : ContinuousOn w {s | s < T} := hwc.mono fun s (hs : s < T) => hTζ'' ▸ ENNReal.coe_lt_coe.2 hs
    set w'' : ℝ≥0 → ℝ := Sec7.RandRestart.extendAt w T w₀ with hw''
    have hw''c : Continuous w'' := Sec7.RandRestart.continuous_extendAt hwT hlw
    have hw''w : ∀ s : ℝ≥0, s < T → w'' s = w s := fun s hs => by simp [hw'', Sec7.RandRestart.extendAt, hs]
    set W' : ℝ → ℝ := fun s => w'' s.toNNReal with hW'
    have hW'c : Continuous W' := hw''c.comp continuous_real_toNNReal
    have hW'0 : W' 0 = 0 := by simp only [hW', Real.toNNReal_zero]; rw [hw''w 0 hT0, hw0]
    have hgen' : IsGeneratingTrace w'' T η :=
      Sec7.IsGeneratingTrace.congr_lt (hTζ'' ▸ hη) fun t ht => hw''w t (ENNReal.coe_lt_coe.1 ht)
    have hIcc := Sec7.traceClosureStatement w'' T ⊤ ENNReal.coe_lt_top
      (hw''c.continuousOn) (by rw [hw''w 0 hT0, hw0]) η hgen'
    have hfill : IsFilling (fwdHull W' T) (η '' Icc 0 T) := hIcc.2.1
    have hWw : ∀ t : ℝ≥0, t < T → W' t = w t := fun t ht => by simp only [hW', Real.toNNReal_coe]; exact hw''w t ht
    have hwI : ContinuousOn w (Iio T) := hwT
    rcases exists_eq_of_thresholdCondition hthr with ⟨i, hi⟩ | ⟨i, hi⟩
    · obtain ⟨u, hu⟩ := exists_isForwardSol_of_trace_avoid hW'c hW'0 hηc hfill hav (hxL i).ne
      refine not_isForwardSol_of_tendsto_gap hW'c hT0 hWw hwI ?_ (fun t ht => hvLeq t ?_ i) ?_ hu
      · exact (hvLc i).mono fun s (hs : s < T) => hTζ'' ▸ ENNReal.coe_lt_coe.2 hs
      · exact hTζ'' ▸ ENNReal.coe_lt_coe.2 ht
      · have h1 : Tendsto (fun t => vL i t) (𝓝[<] T) (𝓝 (vL₀ i)) :=
          ((continuous_apply i).tendsto _).comp ((continuous_fst.tendsto _).comp
            ((continuous_snd.tendsto _).comp hl))
        have h2 := h1.sub hlw
        rwa [hi, sub_self] at h2
    · obtain ⟨u, hu⟩ := exists_isForwardSol_of_trace_avoid hW'c hW'0 hηc hfill hav (hxR i).ne'
      refine not_isForwardSol_of_tendsto_gap hW'c hT0 hWw hwI ?_ (fun t ht => hvReq t ?_ i) ?_ hu
      · exact (hvRc i).mono fun s (hs : s < T) => hTζ'' ▸ ENNReal.coe_lt_coe.2 hs
      · exact hTζ'' ▸ ENNReal.coe_lt_coe.2 ht
      · have h1 : Tendsto (fun t => vR i t) (𝓝[<] T) (𝓝 (vR₀ i)) :=
          ((continuous_apply i).tendsto _).comp ((continuous_snd.tendsto _).comp
            ((continuous_snd.tendsto _).comp hl))
        have h2 := h1.sub hlw
        rwa [hi, sub_self] at h2

end Aux22Strip

end Sec5

end InteractingSLE
