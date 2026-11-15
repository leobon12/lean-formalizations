/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkImage4Trace

/-!
# Finite original endpoints away from the target

A finite original trace segment ending away from the new target has bounded
Möbius image. The capacity bound forces a finite image horizon. Cofinality
of the inverse clock then supplies the image endpoint and a generating trace
through it. No image Brownian law or pre-existing image trace is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Image4

open Zhan.Retarget

variable {a : ℝ} {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- A finite original endpoint away from the target forces a finite image horizon. -/
theorem newHorizon_ne_top_of_endpoint_ne (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) = T) (hne : η t ≠ (a : ℂ)) :
    newHorizon a w vk T ≠ ⊤ := by
  have hne' : ∀ s ∈ Icc (0 : ℝ≥0) t, η s ≠ (a : ℂ) := by
    intro s hs
    rcases hs.2.lt_or_eq with hst | rfl
    · exact trace_ne_target hd hη ((ENNReal.coe_lt_coe.2 hst).trans_eq ht)
    · exact hne
  have hcη : ContinuousOn η (Icc 0 t) :=
    hη.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans_eq ht
  have hc : ContinuousOn (fun s => Sec7.targetChange a (η s)) (Icc 0 t) :=
    hcη.div (continuousOn_const.sub hcη) fun s hs => sub_ne_zero.2 (hne' s hs).symm
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  intro htop
  have hgen := isGeneratingTrace_imageTrace_top hd hη htop
  have hbound : ∀ u : ℝ≥0, ‖imageTrace a w vk η u‖ ≤ B := by
    intro u
    have htu := invClk_lt hd.sep hd.pos (u := u) (by rw [htop]; exact ENNReal.coe_lt_top)
    exact hB _ ⟨zero_le, ENNReal.coe_le_coe.1 (htu.le.trans_eq ht.symm)⟩
  have hT0 : 0 < T := by
    by_contra h
    have h0 : T = 0 := le_antisymm (not_lt.1 h) bot_le
    rw [h0, newHorizon_zero] at htop
    exact ENNReal.zero_ne_top htop
  have hwc : ContinuousOn (newDrv a w vk) {u : ℝ≥0 | (u : ℝ≥0∞) < ⊤} := by
    rw [← htop]
    exact hd.continuousOn_newDrv
  set u : ℝ≥0 := (B ^ 2 / 2 + 1).toNNReal
  have hu : (u : ℝ) = B ^ 2 / 2 + 1 := Real.coe_toNNReal _ (by positivity)
  have hcap := Aux22Strip.two_mul_le_sq_of_isGeneratingTrace hwc (hd.newDrv_zero hT0)
    hgen (t := u) ENNReal.coe_lt_top (fun s _ => hbound s)
  rw [hu] at hcap
  linarith only [hcap]

/-- The inverse clock read as nonnegative real time inverts the forward clock. -/
theorem clk_inverseTime (hd : PullData w vk a T) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon a w vk T) :
    clk (rate a w vk) (invClk (rate a w vk) u).toNNReal = u := by
  obtain ⟨S, -, -, -, hmem, hclk⟩ := newTime_spec hd.sep hd.pos hu
  rw [Real.coe_toNNReal _ hmem.1, hclk]

/-- A cofinal image-time filter approaches a finite original endpoint from below. -/
theorem tendsto_inverseTime (hd : PullData w vk a T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) = T)
    {F : Filter ℝ≥0} (hF : ∀ᶠ u : ℝ≥0 in F, (u : ℝ≥0∞) < newHorizon a w vk T)
    (hcofinal : ∀ s : ℝ≥0, s < t → ∀ᶠ u : ℝ≥0 in F, clk (rate a w vk) s < u) :
    Tendsto (fun u : ℝ≥0 => (invClk (rate a w vk) u).toNNReal) F (𝓝[<] t) := by
  have hlt : ∀ᶠ u : ℝ≥0 in F, (invClk (rate a w vk) u).toNNReal < t := by
    filter_upwards [hF] with u hu
    exact ENNReal.coe_lt_coe.1 ((invClk_lt hd.sep hd.pos hu).trans_eq ht.symm)
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨?_, ?_⟩, hlt⟩
  · intro s hst
    filter_upwards [hF, hcofinal s hst] with u hu hsu
    by_contra h
    have hle : (invClk (rate a w vk) u).toNNReal ≤ s := not_lt.1 h
    have hsT : (s : ℝ≥0∞) < T := (ENNReal.coe_lt_coe.2 hst).trans_eq ht
    have hcmp := hd.clk_mono hle hsT
    rw [clk_inverseTime hd hu] at hcmp
    exact (not_lt_of_ge hcmp) hsu
  · intro s hts
    filter_upwards [hlt] with u hu using hu.trans hts

/-- At a finite image horizon the inverse clock approaches the original endpoint. -/
theorem tendsto_inverseTime_endpoint (hd : PullData w vk a T) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) = T) (hfin : newHorizon a w vk T ≠ ⊤) :
    Tendsto (fun u : ℝ≥0 => (invClk (rate a w vk) u).toNNReal)
      (𝓝[<] (newHorizon a w vk T).toNNReal) (𝓝[<] t) := by
  have he : ((newHorizon a w vk T).toNNReal : ℝ≥0∞) = newHorizon a w vk T :=
    ENNReal.coe_toNNReal hfin
  apply tendsto_inverseTime hd ht
  · filter_upwards [self_mem_nhdsWithin] with u hu
    rw [← he]
    exact ENNReal.coe_lt_coe.2 hu
  · intro s hst
    have hsT : (s : ℝ≥0∞) < T := (ENNReal.coe_lt_coe.2 hst).trans_eq ht
    have hC0 := (hd.isRate hsT).clk_nonneg ⟨s.coe_nonneg, le_rfl⟩
    have hcs : (clk (rate a w vk) s).toNNReal < (newHorizon a w vk T).toNNReal :=
      ENNReal.coe_lt_coe.1 ((hd.clk_lt hsT).trans_eq he.symm)
    filter_upwards [Ioo_mem_nhdsLT hcs] with u hu
    have h := NNReal.coe_lt_coe.2 hu.1
    rwa [Real.coe_toNNReal _ hC0] at h

/-- The canonical image has the expected finite endpoint without an image-trace premise. -/
theorem tendsto_imageTrace_endpoint (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) = T) (hne : η t ≠ (a : ℂ)) :
    Tendsto (imageTrace a w vk η) (𝓝[<] (newHorizon a w vk T).toNNReal)
      (𝓝 (Sec7.targetChange a (η t))) := by
  have hηlim : Tendsto η (𝓝[<] t) (𝓝 (η t)) :=
    ((hη.2.1 t ht.le).mono fun s (hs : s < t) =>
      (ENNReal.coe_lt_coe.2 hs).le.trans ht.le).tendsto
  exact (Local2.continuousAt_targetChange_of_ne hne).tendsto.comp
    (hηlim.comp (tendsto_inverseTime_endpoint hd ht (newHorizon_ne_top_of_endpoint_ne hd hη ht hne)))

/-- The canonical image extends to a generating trace through a finite original
endpoint away from the target. Its endpoint is the Möbius image of that endpoint. -/
theorem isGeneratingTrace_imageTrace_endpoint (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) = T) (hne : η t ≠ (a : ℂ)) :
    IsGeneratingTrace (newDrv a w vk) (newHorizon a w vk T)
      (fun u : ℝ≥0 => if (u : ℝ≥0∞) < newHorizon a w vk T then imageTrace a w vk η u
        else Sec7.targetChange a (η t)) := by
  refine isGeneratingTrace_piecewise (fun _ => imageTrace_zero hη) ?_
    (fun u hu => continuousAt_imageTrace hd hη hu) (fun u hu => isFilling_imageTrace hd hη hu) ?_
  · intro hH0
    have ht0 : t = 0 := by
      by_contra ht0
      have htpos : 0 < T := by
        rw [← ht]
        exact_mod_cast pos_iff_ne_zero.2 ht0
      have hC := hd.clk_lt (t := 0) (by simpa only [ENNReal.coe_zero] using htpos)
      simp only [NNReal.coe_zero, clk_zero, Real.toNNReal_zero, ENNReal.coe_zero, hH0] at hC
      exact lt_irrefl _ hC
    rw [ht0, hη.1, Sec7.targetChange, zero_div]
  · intro U hU
    have he : U = (newHorizon a w vk T).toNNReal := by
      simpa only [ENNReal.toNNReal_coe] using congrArg ENNReal.toNNReal hU
    rw [he]
    exact tendsto_imageTrace_endpoint hd hη ht hne

/-- No pre-horizon image value equals the image of an injective original endpoint. -/
theorem imageTrace_ne_endpoint (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    (hinj : InjOn η {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) = T) (hne : η t ≠ (a : ℂ))
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon a w vk T) :
    imageTrace a w vk η u ≠ Sec7.targetChange a (η t) := by
  intro he
  have htu := invClk_lt hd.sep hd.pos hu
  have hηeq := congrArg (Sec7.targetChangeInv a) he
  change Sec7.targetChangeInv a (Sec7.targetChange a (η (invClk (rate a w vk) u).toNNReal)) =
    Sec7.targetChangeInv a (Sec7.targetChange a (η t)) at hηeq
  rw [Sec7.targetChangeInv_targetChange hd.pos.ne' (trace_ne_target hd hη htu),
    Sec7.targetChangeInv_targetChange hd.pos.ne' hne] at hηeq
  have htime := hinj htu.le ht.le hηeq
  have hlt : (invClk (rate a w vk) u).toNNReal < t :=
    ENNReal.coe_lt_coe.1 (htu.trans_eq ht.symm)
  exact hlt.ne htime

/-- The endpoint extension is injective through the closed image horizon. -/
theorem injOn_imageTrace_endpoint (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    (hinj : InjOn η {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) = T) (hne : η t ≠ (a : ℂ)) :
    InjOn (fun u : ℝ≥0 => if (u : ℝ≥0∞) < newHorizon a w vk T then imageTrace a w vk η u
      else Sec7.targetChange a (η t)) {u : ℝ≥0 | (u : ℝ≥0∞) ≤ newHorizon a w vk T} := by
  intro u hu v hv he
  rcases (show (u : ℝ≥0∞) ≤ newHorizon a w vk T from hu).lt_or_eq with hul | hue
  · rcases (show (v : ℝ≥0∞) ≤ newHorizon a w vk T from hv).lt_or_eq with hvl | hve
    · simp only [hul, hvl, ↓reduceIte] at he
      exact injOn_imageTrace hd hη hinj hul hvl he
    · simp only [hul, hve, lt_self_iff_false, ↓reduceIte] at he
      exact False.elim (imageTrace_ne_endpoint hd hη hinj ht hne hul he)
  · rcases (show (v : ℝ≥0∞) ≤ newHorizon a w vk T from hv).lt_or_eq with hvl | hve
    · simp only [hue, hvl, lt_self_iff_false, ↓reduceIte] at he
      exact False.elim (imageTrace_ne_endpoint hd hη hinj ht hne hvl he.symm)
    · exact ENNReal.coe_injective (hue.trans hve.symm)

/-- With an infinite image horizon, inverse image times approach the finite original endpoint. -/
theorem tendsto_inverseTime_top (hd : PullData w vk a T) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) = T) (hH : newHorizon a w vk T = ⊤) :
    Tendsto (fun u : ℝ≥0 => (invClk (rate a w vk) u).toNNReal) atTop (𝓝[<] t) := by
  apply tendsto_inverseTime hd ht
  · exact Eventually.of_forall fun u => by rw [hH]; exact ENNReal.coe_lt_top
  · intro s _
    filter_upwards [eventually_gt_atTop (clk (rate a w vk) s).toNNReal] with u hu
    exact (Real.le_coe_toNNReal _).trans_lt (NNReal.coe_lt_coe.2 hu)

/-- For a finite original segment, its image is transient whenever its image
horizon is infinite. No transience hypothesis or Brownian law is needed. -/
theorem transient_imageTrace_of_finite_original (hd : PullData w vk a T)
    (hη : IsGeneratingTrace w T η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) = T)
    (hH : newHorizon a w vk T = ⊤) :
    Tendsto (fun u => ‖imageTrace a w vk η u‖) atTop atTop := by
  have he : η t = (a : ℂ) := by
    by_contra hne
    exact newHorizon_ne_top_of_endpoint_ne hd hη ht hne hH
  have hηlim : Tendsto η (𝓝[<] t) (𝓝 (η t)) :=
    ((hη.2.1 t ht.le).mono fun s (hs : s < t) =>
      (ENNReal.coe_lt_coe.2 hs).le.trans ht.le).tendsto
  have hlim : Tendsto (fun u : ℝ≥0 => η (invClk (rate a w vk) u).toNNReal)
      atTop (𝓝[≠] (a : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [← he]
      exact hηlim.comp (tendsto_inverseTime_top hd ht hH)
    · exact Eventually.of_forall fun u => trace_ne_target hd hη
        (invClk_lt hd.sep hd.pos (by rw [hH]; exact ENNReal.coe_lt_top))
  exact (Sec7.tendsto_norm_targetChange_nhdsNE a hd.pos.ne').comp hlim

end InteractingSLE.Sec5.TwoMark.Image4
