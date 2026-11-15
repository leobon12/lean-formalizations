/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2TraceCompare
import InteractingSLE.Spec.Supplement.RLCFAvgSide
import InteractingSLE.Spec.Supplement.S9BSlit

/-!
# Slit completions through a closed finite trace horizon

The existing slit theorem treats stops strictly before the lifetime. The
closed-horizon trace theorems identify the final hull and tip, so the existing
inverse-chart ray construction also completes an injective terminal prefix.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.SB.End

open Supp9B Supp9

/-- A continuous driver and an injective generating trace through a finite
horizon have a slit completion through that horizon, including time zero. -/
theorem exists_slitCompletion_closed_horizon
    {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} {b : ℝ≥0}
    (hη : IsGeneratingTrace w (b : ℝ≥0∞) η) (hw : Continuous w)
    (hw0 : w 0 = 0) (hi : InjOn η (Icc 0 b)) :
    ∃ S, IsSlitCompletion η b S := by
  by_cases hb : b = 0
  · subst b
    refine ⟨verticalRay 0, isProperCompletion_verticalRay hη.1, ?_⟩
    intro t ht
    refine ⟨by simpa only [verticalRay_im] using (NNReal.coe_pos.2 ht), ?_⟩
    rintro ⟨s, hs, he⟩
    have hs0 : s = 0 := le_antisymm hs.2 zero_le
    rw [hs0, hη.1] at he
    have him := congrArg Complex.im he
    exact (ne_of_gt (NNReal.coe_pos.2 ht))
      (by simpa only [zero_im, verticalRay_im] using him.symm)
  have hbpos : (0 : ℝ) < b := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hb)
  let W : ℝ → ℝ := fun r => w r.toNNReal
  have hW : Continuous W := hw.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simpa only [W, Real.toNNReal_zero] using hw0
  have htrace := CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hη
  have hηc : ContinuousOn (fun r : ℝ => η r.toNNReal) (Icc 0 (b : ℝ)) :=
    hη.2.1.comp continuous_real_toNNReal.continuousOn fun r hr =>
      ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT htrace hW hW0 hbpos hηc
  have htip := TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT htrace hW hW0 hbpos hηc
  have hfill := TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT htrace hW hW0 hbpos hηc
  rw [image_toNNReal_Icc η hbpos.le, Real.toNNReal_coe] at hfill
  simp only [Real.toNNReal_coe] at htip
  obtain ⟨f, C, hf, hC⟩ := (GW1P.hasProperBdryExt_recenter_id 0).loewner hW hW0 hbpos.le hB
  have hf' : ∀ z ∈ Hbar, Tendsto (fwdMapInv W b) (𝓝[H] z) (𝓝 (f z)) := by
    simpa only [Chart.loewner, Chart.recenter, Chart.id, Complex.ofReal_zero, add_zero] using hf
  have hfc := GW1P.continuousOn_of_tendsto hf'
  have hfeq : EqOn f (fwdMapInv W b) H := by
    intro z hz
    have := GW1P.neBot_nhdsWithin_H (QuantumZipper.H_subset_Hbar hz)
    exact tendsto_nhds_unique (hf' z (QuantumZipper.H_subset_Hbar hz))
      (((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hbpos.le).continuousOn.continuousAt
        (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)
  have hf0 : f 0 = η b := by
    have h0H : (0 : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ (0 : ℂ).im; rfl
    have := GW1P.neBot_nhdsWithin_H h0H
    exact tendsto_nhds_unique (hf' 0 h0H) htip
  let D := H \ fwdHull W b
  have hmap : MapsTo f H D := fun z hz => by
    rw [hfeq hz]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hbpos.le hz
  have hfi : InjOn f H := by
    intro z hz v hv he
    rw [hfeq hz, hfeq hv] at he
    exact QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 hbpos.le hz hv he
  have hoff : ∀ z ∈ D, z ∉ η '' Icc 0 b := by
    intro z hz hzη
    apply hz.2
    rw [hfill]
    exact ⟨hz.1, Or.inl (subset_closure hzη)⟩
  have hηH : ∀ t ≤ b, 0 ≤ (η t).im := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hη hw.continuousOn hw0 (ENNReal.coe_le_coe.2 ht)
  have hproper := RLC.isProperCurve_rayCurve
    (hη.2.1.mono fun t ht => ENNReal.coe_le_coe.2 ht.2) hi hηH
    (D := D) (fun _ hz => hz.1) hoff hmap hfi hfc hC hf0
  refine ⟨RLC.rayCurve η b f 0,
    ⟨hproper.1, hproper.2.1, hproper.2.2.1, hproper.2.2.2,
      fun t ht => RLC.rayCurve_of_le ht⟩, ?_⟩
  intro t ht
  have hm : RLC.rayCurve η b f 0 t ∈ D := by
    rw [RLC.rayCurve_of_lt ht]
    exact hmap (RLC.ray_mem_H ht)
  exact ⟨hm.1, hoff _ hm⟩

/-- Stopping a driver at a finite closed available prefix supplies the global
continuity needed above. The original trace and its clock are preserved. -/
theorem exists_slitCompletion_of_closed_prefix
    {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {b : ℝ≥0}
    (hη : IsGeneratingTrace w ζ η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) ≤ (b : ℝ≥0∞)})
    (hw0 : w 0 = 0) (hi : InjOn η (Icc 0 b)) (hb : (b : ℝ≥0∞) ≤ ζ) :
    ∃ S, IsSlitCompletion η b S := by
  have hgen := CounterflowRange.isGeneratingTrace_stopped (hη.mono_horizon hb)
  apply exists_slitCompletion_closed_horizon hgen (CounterflowRange.continuous_stopped hw) _ hi
  simpa only [ENNReal.coe_zero, zero_min, ENNReal.toNNReal_zero] using hw0

/-- A finite left limit suffices even if the raw driver value at its terminal
time was arbitrary. Regularization changes only unavailable driver values. -/
theorem exists_slitCompletion_of_leftLimit
    {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} {b : ℝ≥0}
    (hη : IsGeneratingTrace w (b : ℝ≥0∞) η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < (b : ℝ≥0∞)})
    (hw0 : w 0 = 0) (hi : InjOn η (Icc 0 b))
    (hlim : 0 < b → ∃ L : ℝ, Tendsto w (𝓝[<] b) (𝓝 L)) :
    ∃ S, IsSlitCompletion η b S := by
  by_cases hb : b = 0
  · subst b
    have hgen : IsGeneratingTrace (fun _ => 0) 0 η :=
      Sec7.IsGeneratingTrace.congr_lt hη fun _ ht => (ENNReal.not_lt_zero ht).elim
    exact exists_slitCompletion_closed_horizon hgen continuous_const rfl hi
  let e : (ℝ≥0 → ℝ) × ℝ≥0∞ := StagedReg.regularize ⊤ (w, (b : ℝ≥0∞))
  have hr := StagedReg.isRegularDriver_regularize ⊤ (w, (b : ℝ≥0∞))
  change Exist.Staged.IsRegularDriver e at hr
  have he : e.2 = (b : ℝ≥0∞) := StagedReg.regularize_snd _ _
  unfold Exist.Staged.IsRegularDriver at hr
  rw [he] at hr
  have heq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < (b : ℝ≥0∞) → e.1 s = w s :=
    fun _ hs => StagedReg.regularize_eq_of_lt ⊤ hw0 hw hs
  obtain ⟨L, hL⟩ := hlim (pos_iff_ne_zero.2 hb)
  have hLe : Tendsto e.1 (𝓝[<] b) (𝓝 L) := by
    apply hL.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (heq s (ENNReal.coe_lt_coe.2 hs)).symm
  have hval : e.1 b = L := by
    have h := hr.2.2.2 ENNReal.coe_ne_top
      (ENNReal.coe_pos.2 (pos_iff_ne_zero.2 hb)) L
    simp only [ENNReal.toNNReal_coe] at h
    exact h hLe
  have hcont := CounterflowRange.continuousOn_le_of_tendsto hr.1 (by rw [hval]; exact hLe)
  have hgen := Sec7.IsGeneratingTrace.congr_lt hη fun s hs => heq s hs
  exact exists_slitCompletion_of_closed_prefix hgen hcont hr.2.1 hi le_rfl

end InteractingSLE.Theorem14.SB.End
