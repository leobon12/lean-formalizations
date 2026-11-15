/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailFinishCodes

/-!
# Right-gap noncollision at the killing time

PROVE-WW-B27 continuation. Restart at a positive rational time as a full canonical
solution. Its infinite lifetime and positive first right gap follow from the landed
one-sided repulsion theorem. Transfer its Borel gap event back to the killed word.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedTail

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Restart Sec7.RandRestart Sec5.Prop49Exit
open QuantumZipper.StrongMarkov ImgDrv

/-- The full canonical law of every separated start has the right-gap event. -/
theorem codeLaw_compl_rightGapCode_eq_zero {rL rR δ : ℝ}
    (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hd : 0 ≤ δ) (hd1 : δ < 1)
    (s : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hsep : SepStart s) (hword : IsOrderedForceWord s.1 s.2) :
    codeLaw 4 ![rL, -rL - δ] ![rR, -rR + δ] rightGapCodeᶜ s = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled (a := 4) (ρL := ![rL, -rL - δ])
      (ρR := ![rR, -rR + δ]) (by norm_num) hword
  have hg := shifted_groupEndSums hL hR hd hd1 s.1 s.2
  have hζ := Sec5.CfBarrier.ae_lifetime_eq_top_of_gt (by norm_num : (-2 : ℝ) < -1) hword hg.1
    (Sec5.CfBarrier.hasGroupEndSums_mono (by norm_num : (-1 : ℝ) ≤ 0) hg.2) hE
  have hgap := hE.ae_w_lt_vR (by norm_num : (0 : ℝ) < 4) hword
    (by simpa only [show (4 : ℝ) / 2 - 2 = 0 by norm_num] using hg.2) hζ (by decide : 0 < 2)
  obtain ⟨B', hm, hc, -, hbm, hae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  have hpm : Measurable fun ω (t : ℝ≥0) => B' t ω := measurable_pi_iff.2 hm
  rw [codeLaw, ← map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm,
    Measure.map_apply hpm ((measurableSet_restartSetS measurableSet_rightGapCode.compl).preimage
      measurable_prodMk_left)]
  apply measure_eq_zero_iff_ae_notMem.2
  filter_upwards [ae_codeOf_mem (by norm_num : (0 : ℝ) < 4) hE hc hae, hζ, hgap] with ω hcode hζω hgapω
  let x := codeOf s.1 s.2 B' W VL VR ζ ω
  have hx : x ∈ CRel 4 s.1 s.2 ![rL, -rL - δ] ![rR, -rR + δ] := hcode.1
  have hxζ : cζ x = ⊤ := hζω
  have hxt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζω]; exact ENNReal.coe_lt_top
  have hS : x ∈ rightGapCode := by
    refine ⟨hxζ, gapBounds_of_pos ?_ ?_ ?_⟩
    · exact continuousOn_univ.1 (hx.1.1.continuousOn_w.mono fun t _ => by rw [hxζ]; exact ENNReal.coe_lt_top)
    · exact continuousOn_univ.1 ((hx.1.1.continuousOn_vR 0).mono
        fun t _ => by rw [hxζ]; exact ENNReal.coe_lt_top)
    · intro t ht
      rw [(hcode.2 t (hxt t)).1, (hcode.2 t (hxt t)).2.2.1 0]
      exact hgapω t ht
  change ¬ ((s.1, s.2), enc (B' · ω)) ∈ lawSetS 4 ![rL, -rL - δ] ![rR, -rR + δ] rightGapCodeᶜ
  have he : x.1 = enc (B' · ω) := rfl
  rw [← he, mem_lawSetS_iff hsep hx]
  exact not_not.2 hS

/-- Right gaps of the shifted killed word do not vanish at its killing time. -/
theorem killedRightBarrierStatement : KilledRightBarrierStatement.{u} := by
  intro rL rR δ hL hR hd hd1 Ω mΩ P _ 𝓖 W VL VR B T hB hBc hK hWa hVLa hVRa hTq hT0 hE
  have hthr : ∀ᵐ ω ∂P, ¬ ForceWord.ThresholdCondition ![rL, -rL - δ] ![rR, -rR + δ]
      (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω) := Eventually.of_forall fun ω => by
    have ht : (0 : ℝ≥0∞) < T ω := hT0 ω
    have hg := shifted_groupEndSums hL hR hd.le hd1 (fun i => VL i 0 ω) (fun j => VR j 0 ω)
    exact Sec4.not_thresholdCondition_of_hasGroupEndSums (by norm_num : (-2 : ℝ) < -1)
      (hK.idxL ω 0 ht) (hK.idxR ω 0 ht) hg.1
      (Sec5.CfBarrier.hasGroupEndSums_mono (by norm_num : (-1 : ℝ) ≤ 0) hg.2)
      (hK.idxL ω 0 ht) (hK.idxR ω 0 ht) (fun i => hK.ordL ω 0 i ht)
      (fun j => hK.ordR ω 0 j ht) (fun _ _ he => he) (fun _ _ he => he)
  have hres := ae_restart_code (by norm_num : (0 : ℝ) < 4) hB hBc hWa hVLa hVRa hTq hT0
    measurableSet_rightGapCode (fun s hs hw => codeLaw_compl_rightGapCode_eq_zero hL hR hd.le hd1 s hs hw)
    hE hK.sepL hK.sepR hthr
  filter_upwards [hres] with ω hω
  intro τ hτ hτT j hlim
  obtain ⟨q, hq0, hqτ⟩ := exists_rat_btwn (show (0 : ℝ) < τ by exact_mod_cast hτ)
  have hq : 0 < q := by exact_mod_cast hq0
  let q' : ℝ≥0 := (q : ℝ).toNNReal
  have hqτ' : q' < τ := by
    rw [← NNReal.coe_lt_coe]
    simpa [q', Real.coe_toNNReal _ hq0.le] using hqτ
  have hqT : (q' : ℝ≥0∞) < T ω := by rw [← hτT]; exact_mod_cast hqτ'
  obtain ⟨x, hx, hS, -, hagree⟩ := hω q hq hqT
  have hwc : Continuous (cw x) := continuousOn_univ.1
    (hx.1.1.continuousOn_w.mono fun t _ => by rw [hS.1]; exact ENNReal.coe_lt_top)
  have hvc : Continuous (cvR x j) := continuousOn_univ.1
    ((hx.1.1.continuousOn_vR j).mono fun t _ => by rw [hS.1]; exact ENNReal.coe_lt_top)
  have hp0 : cw x (τ - q') < cvR x 0 (τ - q') := rightGapCode_pos hx hS _ (tsub_pos_iff_lt.2 hqτ')
  have hτx : ((τ - q' : ℝ≥0) : ℝ≥0∞) < cζ x := by rw [hS.1]; exact ENNReal.coe_lt_top
  have hp : 0 < cvR x j (τ - q') - cw x (τ - q') := sub_pos.2
    (hp0.trans_le ((hx.1.2.2.isSLEPathUpTo le_rfl).monotone_vR hτx (Fin.zero_le j)))
  have hcont : Continuous fun t : ℝ≥0 => cvR x j (t - q') - cw x (t - q') :=
    (hvc.sub hwc).comp (continuous_id.sub continuous_const)
  have hlim' : Tendsto (fun t => VR j t ω - W t ω) (𝓝[<] τ)
      (𝓝 (cvR x j (τ - q') - cw x (τ - q'))) := by
    apply hcont.continuousAt.tendsto.mono_left inf_le_left |>.congr'
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hqτ')] with t ht hqt
    have htT : ((t - q' : ℝ≥0) : ℝ≥0∞) < T ω - q' := by
      rw [← hτT, ENNReal.coe_sub]
      apply ENNReal.coe_lt_coe.2
      rw [← NNReal.coe_lt_coe, NNReal.coe_sub hqt.le, NNReal.coe_sub hqτ'.le]
      exact sub_lt_sub_right (show (t : ℝ) < τ from ht) _
    have he := hagree (t - q') htT
    rw [add_tsub_cancel_of_le hqt.le] at he
    rw [he.1, he.2.2 j]
    ring
  have : NeBot (𝓝[<] τ) := nhdsLT_neBot_of_exists_lt ⟨0, hτ⟩
  have : cvR x j (τ - q') - cw x (τ - q') = 0 := tendsto_nhds_unique hlim' hlim
  exact hp.ne' this

end InteractingSLE.WangWu.SeedTail
