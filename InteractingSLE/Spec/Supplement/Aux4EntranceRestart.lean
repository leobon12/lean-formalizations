/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS3ReachProof
import InteractingSLE.Spec.Supplement.Aux4EntranceIdent
import InteractingSLE.Spec.Supplement.Aux4EntranceCover

/-!
# Aux. lemma 4, VIII: the restart state is the level functional of the two-seed angle

Packet PROVE-T14-DS3. Pathwise core of the entrance law at the restart: on a sample point where the two-seed cover
(`Aux4.exists_twoSeed_cover_path`) agrees with the evolution up to the localization time `entT`, the hitting time `τ_r`
of the cross-gap level `r` comes before `entT` (`tauR_lt_entT`: up to `τ_r` the state stays within `r` of the initial
state, so the separated marks stay at distance `> η/2` from the driver), and the restart state at `τ_r` is the
functional `Aux4.restartMap` of the entrance path `vPath U` of the angle `U` of the cover
(`restartState_eq_restartMap`): the driver and the seeds by the clock construction (`Sec2.TwoSeed.eq_twoSeed_logAngle`
and `Aux4.low_vPath`, …), the separated marks by `Aux4.mark_eq_of_flow`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace Aux4

open Sec2 Sec2.Assembly2 Sec2.Assembly3 Sec2.TwoSeed DS3Reach

variable {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) {Ω : Type*} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} {η r : ℝ}

/-- **`τ_r` comes before the localization time** (for `r ≤ η/4`). -/
theorem tauR_lt_entT (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    (hL0 : xL ⟨0, hnL⟩ = 0) (hR0 : xR ⟨0, hnR⟩ = 0) (hLη : ∀ i, xL i ≠ 0 → xL i ≤ -η)
    (hRη : ∀ j, xR j ≠ 0 → η ≤ xR j) (hr0 : 0 < r) (hrη : r ≤ η / 4) (hr1 : r ≤ 1)
    (hlt : entT (η / 2) xL xR ζ W VL VR ω < ζ ω) :
    tauR hnL hnR r ζ VL VR ω < entT (η / 2) xL xR ζ W VL VR ω := by
  have hη : 0 < η := by linarith
  have : Nonempty (Fin nL ⊕ Fin nR) := ⟨Sum.inl ⟨0, hnL⟩⟩
  have hτle := tauR_le hnL hnR hp hr0.le
  have hτ1 : tauR hnL hnR r ζ VL VR ω < 1 := by
    refine lt_of_le_of_lt hτle ?_
    rw [← ENNReal.coe_one, ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe (by positivity), NNReal.coe_one]
    nlinarith
  by_contra hcon
  push Not at hcon
  -- the localization time is attained by the gap family
  have hentle : entT (η / 2) xL xR ζ W VL VR ω ≤ hitTime (killedFam ζ (gapFam (η / 2) xL xR W VL VR))
      (η / 2) ω := min_le_left _ _
  rcases min_cases (hitTime (killedFam ζ (gapFam (η / 2) xL xR W VL VR)) (η / 2) ω) 1 with ⟨he, -⟩ | ⟨he, -⟩
  swap
  · have : (1 : ℝ≥0∞) ≤ tauR hnL hnR r ζ VL VR ω := by rw [← he]; exact hcon
    exact absurd hτ1 (not_lt.2 this)
  have hentζ : hitTime (killedFam ζ (gapFam (η / 2) xL xR W VL VR)) (η / 2) ω < ζ ω := by
    rw [← he]; exact hlt
  set s := (hitTime (killedFam ζ (gapFam (η / 2) xL xR W VL VR)) (η / 2) ω).toNNReal
  have hsne : hitTime (killedFam ζ (gapFam (η / 2) xL xR W VL VR)) (η / 2) ω ≠ ⊤ := ne_top_of_lt hentζ
  have hcont : ∀ k, ContinuousOn (gapFam (η / 2) xL xR W VL VR k · ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    rintro (i | j)
    · simp only [gapFam, Sum.elim_inl]
      split_ifs
      · exact continuousOn_const
      · exact hp.continuousOn_w.sub (hp.continuousOn_vL i)
    · simp only [gapFam, Sum.elim_inr]
      split_ifs
      · exact continuousOn_const
      · exact (hp.continuousOn_vR j).sub hp.continuousOn_w
  obtain ⟨t, hts, k, hk⟩ := (hitTime_le_iff_of_isClosed (isClosed_killedFam (by linarith) hcont) (s := s)).1
    (le_of_eq (ENNReal.coe_toNNReal hsne).symm)
  have ht1 : (t : ℝ≥0∞) ≤ hitTime (killedFam ζ (gapFam (η / 2) xL xR W VL VR)) (η / 2) ω := by
    rw [← ENNReal.coe_toNNReal hsne]; exact_mod_cast hts
  have ht2 : hitTime (killedFam ζ (gapFam (η / 2) xL xR W VL VR)) (η / 2) ω ≤
      tauR hnL hnR r ζ VL VR ω := by rw [← he]; exact hcon
  have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt ht1 hentζ
  have htτ : (t : ℝ≥0∞) ≤ tauR hnL hnR r ζ VL VR ω := ht1.trans ht2
  simp only [killedFam, Girsanov.killed_of_lt htζ] at hk
  -- the state estimate
  have hD := crossGap_le_of_le_tauR hnL hnR hp hL0 hR0 hr0.le htτ htζ
  have hdist := (dist_state_le_crossGap hnL hnR hp hL0 hR0 htζ).trans hD
  rw [Prod.dist_eq, Prod.dist_eq] at hdist
  have hW : |W t ω| ≤ r := by
    have := (le_max_left _ _).trans hdist
    simpa [Coupling.stateAt, Real.dist_eq] using this
  rw [abs_le] at hW
  rcases k with i | j
  · simp only [gapFam, Sum.elim_inl] at hk
    split_ifs at hk with hi
    · linarith
    · have h1 := hp.vL_le_of_le (zero_le (a := t)) htζ i
      simp only [hp.vL_zero] at h1
      linarith [hLη i hi]
  · simp only [gapFam, Sum.elim_inr] at hk
    split_ifs at hk with hj
    · linarith
    · have h1 := hp.le_vR_of_le (zero_le (a := t)) htζ j
      simp only [hp.vR_zero] at h1
      linarith [hRη j hj]

theorem FL_eq_inv {δ x : ℝ} (_hδ : 0 < δ) (hx : x ≤ -δ) : FL δ x = 1 / x := by
  rw [FL, max_eq_left (by linarith), neg_div, div_neg, neg_neg]

theorem FR_eq_inv {δ x : ℝ} (_hδ : 0 < δ) (hx : δ ≤ x) : FR δ x = 1 / x := by
  rw [FR, max_eq_left hx]

/-- **The restart state is the level functional of the cover's angle** (pathwise). -/
theorem restartState_eq_restartMap
    (hp : IsForcePath xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    {sL sR : ℝ} {b' : ℝ≥0 → ℝ}
    (hpQ : IsSLEPathUpTo κ xL xR (seedW xL ρL) (seedW xR ρR) (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) b' (entT (η / 2) xL xR ζ W VL VR ω))
    {Gw : ℝ≥0 → ℝ} {Gl Gr : Fin 1 → ℝ≥0 → ℝ} {bG : ℝ≥0 → ℝ}
    (hpG : IsIntegratedSLEPath κ (fun _ : Fin 1 => 0) (fun _ => 0) (fun _ => sL) (fun _ => sR) Gw Gl Gr bG ⊤)
    (hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ entT (η / 2) xL xR ζ W VL VR ω →
      Gw t = W t ω ∧ Gl 0 t = VL ⟨0, hnL⟩ t ω ∧ Gr 0 t = VR ⟨0, hnR⟩ t ω)
    (hlt : entT (η / 2) xL xR ζ W VL VR ω < ζ ω)
    {U : ℝ → ℝ} (hUc : Continuous U) (hU01 : ∀ v, U v ∈ Icc (0 : ℝ) 1)
    (hUeq : ∀ u, U u = logAngle Gw Gl Gr ⊤ u)
    (hL0 : xL ⟨0, hnL⟩ = 0) (hR0 : xR ⟨0, hnR⟩ = 0) (hLη : ∀ i, xL i ≠ 0 → xL i ≤ -η)
    (hRη : ∀ j, xR j ≠ 0 → η ≤ xR j) (hr0 : 0 < r) (hrη : r ≤ η / 4) (hr1 : r ≤ 1) :
    tauR hnL hnR r ζ VL VR ω < ζ ω ∧
      restartState hnL hnR r ζ W VL VR ω = restartMap (R := r.toNNReal) (η / 2) xL xR (vPath U hUc) := by
  have hη : 0 < η := by linarith
  have hδ : 0 < η / 2 := by linarith
  set R : ℝ≥0 := r.toNNReal with hRdef
  have hRr : (R : ℝ) = r := Real.coe_toNNReal _ hr0.le
  have hτent := tauR_lt_entT hnL hnR hp hL0 hR0 hLη hRη hr0 hrη hr1 hlt
  have hτζ : tauR hnL hnR r ζ VL VR ω < ζ ω := hτent.trans hlt
  have hτe := coe_TR_eq hnL hnR hp hr0.le (by linarith)
  set T := TR hnL hnR r ζ VL VR ω with hTdef
  have hTent : (T : ℝ≥0∞) < entT (η / 2) xL xR ζ W VL VR ω := by rw [hτe]; exact hτent
  have hTζ : (T : ℝ≥0∞) < ζ ω := by rw [hτe]; exact hτζ
  have hT0 : 0 < T := by
    have hpos : 0 < tauR hnL hnR r ζ VL VR ω := by
      refine hitTime_killedFam_pos le_rfl (continuousOn_gapR hnL hnR hp) (lt_of_le_of_lt zero_le hτζ)
        fun k => ?_
      simp only [gapR, hp.vL_zero, hp.vR_zero, hL0, hR0, sub_zero]; exact hr0
    rw [← hτe] at hpos
    exact_mod_cast hpos
  -- the cross gap at `T` is `r`
  have hτT : (tauR hnL hnR r ζ VL VR ω).toNNReal = T := by rw [← hτe, ENNReal.toNNReal_coe]
  have hDge := le_crossGap_tauR hnL hnR hp hτζ
  rw [hτT] at hDge
  have hDle := crossGap_le_of_le_tauR hnL hnR hp hL0 hR0 hr0.le (le_of_eq hτe) hTζ
  have hag := hagree T hTent.le
  have hsep : sepN Gl Gr T = r := by
    simp only [sepN, hag.2.1, hag.2.2]; simp only [cg] at hDge hDle; linarith
  -- the two-seed identities at `T`
  have hUfun : U = logAngle Gw Gl Gr ⊤ := funext hUeq
  obtain ⟨-, hl, hu, hw⟩ := eq_twoSeed_logAngle hpG (t := T) ENNReal.coe_lt_top hT0
  rw [hsep, ← hUfun] at hl hu hw
  have hrmem : r ∈ Ioc (0 : ℝ) R := ⟨hr0, by rw [hRr]⟩
  have hlow : low (vPath (R := R) U hUc) R = Gl 0 T := by rw [hRr, hl, low_vPath hUc hU01 hrmem]
  have hupp : upp (vPath (R := R) U hUc) R = Gr 0 T := by rw [hRr, hu, upp_vPath hUc hU01 hrmem]
  have hdrv : drv (vPath (R := R) U hUc) R = W T ω := by
    rw [hRr, ← hag.1, hw, drv_vPath hUc hU01 hrmem]
  -- the state estimate up to `T`
  have hWlow : ∀ t ≤ T, -r ≤ W t ω ∧ W t ω ≤ r := fun t ht => by
    have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast ht) hTζ
    have hD := crossGap_le_of_le_tauR hnL hnR hp hL0 hR0 hr0.le
      (by rw [← hτe]; exact_mod_cast ht) htζ
    have hdist := (dist_state_le_crossGap hnL hnR hp hL0 hR0 htζ).trans hD
    rw [Prod.dist_eq] at hdist
    have := (le_max_left _ _).trans hdist
    simp only [Coupling.stateAt, Real.dist_eq, sub_zero] at this
    exact abs_le.1 this
  have hk : (R : ℝ) ^ 2 / (4 * (η / 2) ^ 2) < 1 := by
    rw [hRr, div_lt_one (by positivity)]; nlinarith
  refine ⟨hτζ, ?_⟩
  simp only [restartState, restartMap]
  refine Prod.ext hdrv.symm (Prod.ext (funext fun i => ?_) (funext fun j => ?_))
  · simp only
    rw [hdrv]
    congr 1
    by_cases hi : xL i = 0
    · simp only [hi, ↓reduceIte]
      rw [hlow, hag.2.1]
      exact hpQ.vL_eq_of_xL_eq (by rw [hi, hL0]) hTent
    · simp only [hi, ↓reduceIte]
      refine mark_eq_of_flow hpG hUc hU01 hUeq (t₁ := T) ENNReal.coe_lt_top (by rw [hRr, hsep])
        (isCut_FL hδ) hk (Or.inl fun x => ?_) (Y := fun t => VL i t ω) (x₀ := xL i) ?_ ?_
      · rw [FL]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (le_max_of_le_right hδ.le)
      · exact (hp.continuousOn_vL i).comp continuous_real_toNNReal.continuousOn fun s hs =>
          lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) hTζ
      · intro t ht
        have htent : (t : ℝ≥0∞) < entT (η / 2) xL xR ζ W VL VR ω :=
          lt_of_le_of_lt (by exact_mod_cast ht) hTent
        rw [hpQ.vL_eq htent i]
        congr 1
        refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
        rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
        have hst : s.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe.2 hs.2).trans ht
        have hsζ : (s.toNNReal : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hst) hTζ
        have hGw := (hagree s.toNNReal (le_trans (by exact_mod_cast hst) hTent.le)).1
        have h1 := hp.vL_le_of_le (zero_le (a := s.toNNReal)) hsζ i
        simp only [hp.vL_zero] at h1
        have hgap : VL i s.toNNReal ω - W s.toNNReal ω ≤ -(η / 2) := by
          linarith [hLη i hi, (hWlow _ hst).1]
        rw [hGw, FL_eq_inv hδ hgap]; ring
  · simp only
    rw [hdrv]
    congr 1
    by_cases hj : xR j = 0
    · simp only [hj, ↓reduceIte]
      rw [hupp, hag.2.2]
      exact hpQ.vR_eq_of_xR_eq (by rw [hj, hR0]) hTent
    · simp only [hj, ↓reduceIte]
      refine mark_eq_of_flow hpG hUc hU01 hUeq (t₁ := T) ENNReal.coe_lt_top (by rw [hRr, hsep])
        (isCut_FR hδ) hk (Or.inr fun x => ?_) (Y := fun t => VR j t ω) (x₀ := xR j) ?_ ?_
      · rw [FR]; exact div_nonneg zero_le_one (le_max_of_le_right hδ.le)
      · exact (hp.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn fun s hs =>
          lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) hTζ
      · intro t ht
        have htent : (t : ℝ≥0∞) < entT (η / 2) xL xR ζ W VL VR ω :=
          lt_of_le_of_lt (by exact_mod_cast ht) hTent
        rw [hpQ.vR_eq htent j]
        congr 1
        refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
        rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
        have hst : s.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe.2 hs.2).trans ht
        have hsζ : (s.toNNReal : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hst) hTζ
        have hGw := (hagree s.toNNReal (le_trans (by exact_mod_cast hst) hTent.le)).1
        have h1 := hp.le_vR_of_le (zero_le (a := s.toNNReal)) hsζ j
        simp only [hp.vR_zero] at h1
        have hgap : η / 2 ≤ VR j s.toNNReal ω - W s.toNNReal ω := by
          linarith [hRη j hj, (hWlow _ hst).2]
        rw [hGw, FR_eq_inv hδ hgap]; ring

end Aux4

end Supp12

end InteractingSLE
