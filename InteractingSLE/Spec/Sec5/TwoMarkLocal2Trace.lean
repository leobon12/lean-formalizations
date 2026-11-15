/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkLocal2Path
import InteractingSLE.Spec.Sec5.Aux22StripPull

/-!
# Transport of a given trace through a target-separation endpoint

The original trace and a trace of the canonical transformed driver determine
each other before separation. At a finite original endpoint different from
the target, a transient transformed trace must have finite horizon, and its
endpoint is the target change of the original endpoint. This uses the given
traces, not a full force-word trace-existence theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Local2

open Zhan.Retarget

variable {a : ℝ} {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞}
  {η Γ : ℝ≥0 → ℂ}

/-- The compact separation data give continuity of the original driver. -/
theorem continuousOn_driver (hd : PullData w vk a T) :
    ContinuousOn w {t | (t : ℝ≥0∞) < T} := by
  intro t ht
  obtain ⟨S, htS, hST⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hc : ContinuousOn w (Iic S) := by
    have h := (hd.sep.isSep_of_lt hST).cont_w.comp
      (show ContinuousOn (fun s : ℝ≥0 => (s : ℝ)) (Iic S) from
        continuous_subtype_val.continuousOn)
      (fun (s : ℝ≥0) (hs : s ∈ Iic S) => ⟨s.coe_nonneg, hs⟩)
    simpa only [Function.comp_def, Real.toNNReal_coe] using h
  exact (hc.continuousAt (Iic_mem_nhds (ENNReal.coe_lt_coe.1 htS))).continuousWithinAt

/-- The given traces agree under the capacity clock before target separation. -/
theorem image_trace_before (hd : PullData w vk a T)
    (hη : IsGeneratingTrace w T η)
    (hΓ : IsGeneratingTrace (newDrv a w vk) (newHorizon a w vk T) Γ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    Γ (clk (rate a w vk) t).toNNReal = Sec7.targetChange a (η t) := by
  obtain ⟨t', htt', ht'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have hc0 := (hd.isRate ht'T).clk_nonneg ⟨t'.coe_nonneg, le_rfl⟩
  have he := Aux22Strip.eq_pullTrace_of_lt hd (continuousOn_driver hd)
    le_rfl hη (S := (clk (rate a w vk) t').toNNReal + 1)
    (fun u _ hu => hΓ.mono_horizon hu.le)
    (ENNReal.coe_lt_coe.1 htt') ht'T
    (by rw [NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal _ hc0]; linarith)
  rw [he, pullTrace]
  exact (Sec7.targetChange_targetChangeInv hd.pos.ne' (hd.ne_neg_one hΓ ht)).symm

/-- Continuity of the forward target change away from its pole. -/
theorem continuousAt_targetChange_of_ne {z : ℂ} (hz : z ≠ (a : ℂ)) :
    ContinuousAt (Sec7.targetChange a) z :=
  continuousAt_id.div (continuousAt_const.sub continuousAt_id) (sub_ne_zero.2 hz.symm)

/-- At a finite original endpoint different from the target, the transformed
horizon is finite and its terminal trace value is the image endpoint. -/
theorem image_trace_endpoint (hd : PullData w vk a T)
    (hη : IsGeneratingTrace w T η)
    (hΓ : IsGeneratingTrace (newDrv a w vk) (newHorizon a w vk T) Γ)
    (htr : newHorizon a w vk T = ⊤ → Tendsto (fun s => ‖Γ s‖) atTop atTop)
    {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) = T) (hne : η t ≠ (a : ℂ)) :
    newHorizon a w vk T ≠ ⊤ ∧
      Γ (newHorizon a w vk T).toNNReal = Sec7.targetChange a (η t) := by
  have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
  have hleft : IsLeftOf (𝓝[<] t) T := ht ▸ isLeftOf_nhdsLT t
  have hlimη : Tendsto η (𝓝[<] t) (𝓝 (η t)) :=
    (hη.2.1 t ht.le).tendsto.mono_left (nhdsWithin_mono _ fun s hs =>
      (ENNReal.coe_lt_coe.2 hs).le.trans ht.le)
  have hlimψ := (continuousAt_targetChange_of_ne hne).tendsto.comp hlimη
  have hlim : Tendsto (fun s : ℝ≥0 => Γ (clk (rate a w vk) s).toNNReal)
      (𝓝[<] t) (𝓝 (Sec7.targetChange a (η t))) := by
    apply hlimψ.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (image_trace_before hd hη hΓ ((ENNReal.coe_lt_coe.2 hs).trans_le ht.le)).symm
  have hfin : newHorizon a w vk T ≠ ⊤ := by
    intro htop
    have hinf := (htr htop).comp (hd.tendsto_clk_of_eq_top hleft htop)
    exact not_tendsto_atTop_of_tendsto_nhds hlim.norm hinf
  refine ⟨hfin, ?_⟩
  have hcoe : (((newHorizon a w vk T).toNNReal : ℝ≥0) : ℝ≥0∞) =
      newHorizon a w vk T := ENNReal.coe_toNNReal hfin
  have hlimΓ : Tendsto Γ (𝓝[≤] (newHorizon a w vk T).toNNReal)
      (𝓝 (Γ (newHorizon a w vk T).toNNReal)) :=
    (hΓ.2.1 _ hcoe.le).tendsto.mono_left (nhdsWithin_mono _ fun s hs =>
      (ENNReal.coe_le_coe.2 hs).trans hcoe.le)
  exact tendsto_nhds_unique (hlimΓ.comp (hd.tendsto_clk_of_ne_top hleft hfin)) hlim

/-- Every original visit away from the target, including a finite endpoint,
has a corresponding visit of the transformed trace through its horizon. -/
theorem exists_image_trace_time (hd : PullData w vk a T)
    (hη : IsGeneratingTrace w T η)
    (hΓ : IsGeneratingTrace (newDrv a w vk) (newHorizon a w vk T) Γ)
    (htr : newHorizon a w vk T = ⊤ → Tendsto (fun s => ‖Γ s‖) atTop atTop)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ T) (hne : η t ≠ (a : ℂ)) :
    ∃ s : ℝ≥0, (s : ℝ≥0∞) ≤ newHorizon a w vk T ∧
      Γ s = Sec7.targetChange a (η t) := by
  rcases eq_zero_or_pos t with rfl | ht0
  · exact ⟨0, bot_le, by rw [hΓ.1, hη.1, Sec7.targetChange_zero]⟩
  rcases ht.lt_or_eq with hlt | heq
  · exact ⟨_, (hd.clk_lt hlt).le, image_trace_before hd hη hΓ hlt⟩
  · have h := image_trace_endpoint hd hη hΓ htr ht0 heq hne
    exact ⟨_, (ENNReal.coe_toNNReal h.1).le, h.2⟩

/-- The outer-ray exclusion transports to the original interval, through the
separation endpoint, once the two given traces and transience are supplied. -/
theorem avoid_interval_of_image_ray (hd : PullData w vk a T)
    (hη : IsGeneratingTrace w T η)
    (hΓ : IsGeneratingTrace (newDrv a w vk) (newHorizon a w vk T) Γ)
    (htr : newHorizon a w vk T = ⊤ → Tendsto (fun s => ‖Γ s‖) atTop atTop)
    {b : ℝ} (hav : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ newHorizon a w vk T →
      ∀ y < Sec7.targetChangeReal a b, Γ s ≠ (y : ℂ)) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → ∀ y ∈ Ioo a b, η t ≠ (y : ℂ) := by
  intro t ht y hy he
  have hne : η t ≠ (a : ℂ) := by
    rw [he]
    exact_mod_cast hy.1.ne'
  obtain ⟨s, hs, he'⟩ := exists_image_trace_time hd hη hΓ htr ht hne
  apply hav s hs (Sec7.targetChangeReal a y) (TwoMark.targetChangeReal_lt_of_mem hd.pos hy)
  rw [he', he, Sec7.targetChange_ofReal]

/-- Apply the image barrier to an arbitrary local original path through its
first target separation. The original trace is only restricted, not extended. -/
theorem avoid_interval_through_sep {κ b r : ℝ} {xL ρL : Fin 0 → ℝ}
    {vL : Fin 0 → ℝ≥0 → ℝ} {vR : Fin 2 → ℝ≥0 → ℝ} {β : ℝ≥0 → ℝ}
    (ha : 0 < a) (hab : a < b)
    (hp : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ![r, -r] w vL vR β T)
    (hη : IsGeneratingTrace w T η)
    (hΓ : IsGeneratingTrace (newDrv a w (vR 0))
      (newHorizon a w (vR 0) (sepTime w (vR 0) T)) Γ)
    (htr : newHorizon a w (vR 0) (sepTime w (vR 0) T) = ⊤ →
      Tendsto (fun s => ‖Γ s‖) atTop atTop)
    (hav : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ newHorizon a w (vR 0) (sepTime w (vR 0) T) →
      ∀ y < Sec7.targetChangeReal a b, Γ s ≠ (y : ℂ)) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ sepTime w (vR 0) T →
      ∀ y ∈ Ioo a b, η t ≠ (y : ℂ) := by
  have hle := sepTime_le w (vR 0) T
  have hd := retargetData_first ha hab (hp.mono hle) (fun _ ht => lt_of_lt_sepTime ht)
  have hpd : PullData w (vR 0) a (sepTime w (vR 0) T) :=
    ⟨ha, hp.w_zero, hd.sep, hd.target⟩
  exact avoid_interval_of_image_ray hpd (hη.mono_horizon hle) hΓ htr hav

/-- **Conditional:** to cover the original stop after separation it remains
to show that an interval visit occurs no later than the first separation.
That geometric statement is the explicitly named hypothesis `hcover`. -/
theorem avoid_interval_of_sep_cover {κ b r : ℝ} {xL ρL : Fin 0 → ℝ}
    {vL : Fin 0 → ℝ≥0 → ℝ} {vR : Fin 2 → ℝ≥0 → ℝ} {β : ℝ≥0 → ℝ}
    (ha : 0 < a) (hab : a < b)
    (hp : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ![r, -r] w vL vR β T)
    (hη : IsGeneratingTrace w T η)
    (hΓ : IsGeneratingTrace (newDrv a w (vR 0))
      (newHorizon a w (vR 0) (sepTime w (vR 0) T)) Γ)
    (htr : newHorizon a w (vR 0) (sepTime w (vR 0) T) = ⊤ →
      Tendsto (fun s => ‖Γ s‖) atTop atTop)
    (hav : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ newHorizon a w (vR 0) (sepTime w (vR 0) T) →
      ∀ y < Sec7.targetChangeReal a b, Γ s ≠ (y : ℂ))
    (hcover : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → ∀ y ∈ Ioo a b,
      η t = (y : ℂ) → (t : ℝ≥0∞) ≤ sepTime w (vR 0) T) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → ∀ y ∈ Ioo a b, η t ≠ (y : ℂ) := by
  intro t ht y hy he
  exact avoid_interval_through_sep ha hab hp hη hΓ htr hav t (hcover t ht y hy he) y hy he

end InteractingSLE.Sec5.TwoMark.Local2
