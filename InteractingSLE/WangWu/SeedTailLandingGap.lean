/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailLandingClosure

/-!
# The right gap closes at a killed arc's positive real landing

PROVE-WW-B27. First close the local capacity driver by the compact-arc driving
criterion. A positive terminal right gap would keep the positive landing point
alive through the horizon, contradicting the landed horizon tip theorem.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.SeedTail

open ImgWord MartChar.RealFlow

/-- Horizon version of the real-visit collision argument: a continuous driver
with a positive-real terminal tip cannot have a positive terminal right gap. -/
theorem rightImg_zero_eq_of_real_terminal {U : ℝ → ℝ} {η : ℝ → ℂ} {T x : ℝ}
    (hU : Continuous U) (hU0 : U 0 = 0) (hT : 0 < T) (hx : 0 < x)
    (hη : IsLoewnerTraceLT U T η) (hc : ContinuousOn η (Icc 0 T)) (hend : η T = x)
    (hsep : ∀ t ∈ Ioo 0 T, U t < rightImg U 0 t) : rightImg U 0 T = U T := by
  by_contra hne
  have hpos : 0 < rightImg U 0 T - U T :=
    sub_pos.2 (lt_of_le_of_ne (le_rightImg hU 0 hT.le) (Ne.symm hne))
  have hgap : ∀ t ∈ Icc (0 : ℝ) T, 0 < rightImg U x t - U t := by
    intro t ht
    rcases ht.1.eq_or_lt with he | ht0
    · subst t
      rw [rightImg_zero hU hU0 hx.le, hU0, sub_zero]
      exact hx
    · have hmono := rightImg_mono_index hU ht.1 hx.le
      rcases ht.2.lt_or_eq with htt | he
      · exact lt_of_lt_of_le (sub_pos.2 (hsep t ⟨ht0, htt⟩)) (sub_le_sub_right hmono _)
      · subst t
        exact hpos.trans_le (sub_le_sub_right hmono _)
  have hgc : ContinuousOn (fun t => rightImg U x t - U t) (Icc 0 T) :=
    ((continuousOn_rightImg hU x).mono Icc_subset_Ici_self).sub hU.continuousOn
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le) hgc
  have hA0 : Alive U x 0 := alive_zero_iff.2 (by rw [hU0, sub_zero]; exact hx)
  have hAT : Alive U x T := hA0.of_forall_le_cflow hU le_rfl (hgap a ha) fun t ht hal => by
    have h := hmin ht
    change rightImg U x a - U a ≤ rightImg U x t - U t at h
    rw [rightImg_eq_gImg hU ht.1 hal, gImg] at h
    linarith only [h]
  have htip := TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT hη hU hU0 hT hc
  rw [hend] at htip
  exact Supp8.GB6.not_isForwardSol_of_tip hU hU0 hT.le htip (isForwardSol_of_alive hU hAT)

/-- The geometric right gap of every killed simple arc closes at a positive
real terminal landing. No continuous-driver extension is a hypothesis. -/
theorem positiveLandingGapStatement : PositiveLandingGapStatement := by
  intro γ P hγ τ hτ0 hτ x hx hlim
  obtain ⟨U, hU, hU0, hEq, hη⟩ := exists_closed_driver hγ hτ0 hτ hx hlim
  have hτR : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ0
  have himg : ∀ t ∈ Ico (0 : ℝ) τ, rightImg (kPath γ P) 0 t = rightImg U 0 t := by
    intro t ht
    exact Supp8.GB6.rightImg_congr hU ht.1 fun r hr => hEq ⟨hr.1, hr.2.trans_lt ht.2⟩
  have hsep : ∀ t ∈ Ioo (0 : ℝ) τ, U t < rightImg U 0 t := by
    intro t ht
    have htL : (t.toNNReal : WithTop ℝ≥0) < kLife γ P := by
      rw [← hτ, WithTop.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe ht.1.le]
      exact ht.2
    have hp := hγ.kW_lt_kVRr (xR := fun _ : Fin 1 => 0) (fun _ => le_rfl)
      (Real.toNNReal_pos.2 ht.1) htL 0
    simpa only [kVRr, kImg, ← kPath_coe, Real.coe_toNNReal _ ht.1.le,
      hEq ⟨ht.1.le, ht.2⟩, himg t ⟨ht.1.le, ht.2⟩] using hp
  have hc := (closedKTrace_spec hγ hτ0 hτ hx hlim).1
  have hend := rightImg_zero_eq_of_real_terminal hU hU0 hτR hx hη hc
    (closedKTrace_end γ P τ x) hsep
  have hcont : Continuous (fun t : ℝ≥0 => rightImg U 0 t - U t) :=
    ((continuousOn_rightImg hU 0).comp_continuous NNReal.continuous_coe fun t => t.coe_nonneg).sub
      (hU.comp NNReal.continuous_coe)
  have hzero : Tendsto (fun t : ℝ≥0 => rightImg U 0 t - U t) (𝓝[<] τ) (𝓝 0) := by
    simpa only [hend, sub_self] using (hcont.tendsto τ).mono_left nhdsWithin_le_nhds
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t : ℝ) < τ := NNReal.coe_lt_coe.2 ht
  rw [kImg, himg t ⟨t.coe_nonneg, ht'⟩, ← kPath_coe, hEq ⟨t.coe_nonneg, ht'⟩]

end InteractingSLE.WangWu.SeedTail
