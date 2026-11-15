/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Conf2Data
import InteractingSLE.Spec.Sec5.Aux61RestartFinInherited

/-!
# Aux. 61 at the glued stop, II: the two-sides configuration from the glued data

Packet PROVE-AUX61-CONFIG. From the per-sample glued data `IsGluedSlit` (physical coordinates) and a comparison time
`σ ∈ (0, τ)`, **`IsGluedSlit.exists_isTwoSideConfig`** builds the configuration `Aux61TwoS.IsTwoSideConfig` of
PROVE-AUX61-TWOSIDES field by field, as its handoff prescribes (wiring (W)):

* flow side: the shifted driver `V = shiftDrive Wph r` frozen at `σ`, the shifted continuation `β₀` frozen at `σ`
  (`YuanCorollary13.extDrive`/`extTrace`, a continuous Loewner trace and a simple proper arc by
  `IsLoewnerTraceLT.isLoewnerTrace_ext` and `WangWu.isProperArc_extTrace`), the actual continuation `β′ = β₀`;
* chart: `Ω = ℍ ∩ F_r⁻¹(D)`, `Ψ = c.1 ∘ F_r`, `Ψi = physInv Wph r c = f_r ∘ c.2.1`, `LΨ = physLog Wph r Lc` with
  `Lc = log a + physicalRestartLog B` (R1's positive-scale representation); the collar and the current limit are R1's;
  `Im Ψ → 0` at the real collar points by properness of `mapOut B` (`IsMapOut.tendsto_im_nhdsWithin`); **`log_seed`**
  is PROVE-AUX61-TWOSIDES's `tendsto_im_physicalRestartLog_retained_sub_logDerivFwd`, applied to the physical trace
  frozen at `r + τ` (a proper arc);
* chart chain: the chart driver and trace frozen at the chart time `t`; the hull and the tip are the glued data's.

It also returns R1's lift identity in the form `c.2.2 ∘ c.2.1 = Im Lc ∘ c.2.1` on `ℍ` (TWOSIDES's `hlift`) and the
inverse-chart inclusion `c.2.1(ℍ) ⊆ ℍ ∖ K_r` (TWOSIDES's `hinvD`).

Deterministic; no source statement is replaced. R48/R77: nothing here uses Theorem 1.2/1.3 or the post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Sec5.Aux61Conf2

open WangWu (IsProperArc)
open Aux61Restart (stripRightRetarget stripTargetHull physicalRestartLog)
open YuanCorollary13 (extDrive extTrace)
open Aux61TwoS (IsTwoSideConfig physInv physLog)

namespace IsGluedSlit

variable {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r τ : ℝ} {c : Chart} {D : Set ℂ} {w : ℝ → ℝ} {γ : ℝ → ℂ} {Tc t : ℝ}
  (hg : IsGluedSlit Wph η r τ c D w γ Tc t)
include hg

/-! ### The chart in flow coordinates -/

theorem isHPHull_B : IsHPHull (stripTargetHull D) :=
  Aux61Restart.isHPHull_stripTargetHull hg.isOpen_D hg.simply hg.dom_subset_H hg.target

theorem mapsTo_retarget : MapsTo stripRightRetarget D (H \ stripTargetHull D) := fun z hz => by
  rw [Aux61Restart.H_diff_stripTargetHull hg.dom_subset_H]
  exact mem_image_of_mem _ hz

theorem mem_dom {z : ℂ} (hz : z ∈ D) : z ∈ c.dom := by
  rw [← SetLike.mem_coe, hg.dom_eq]
  exact hz

theorem diffOn_fwd : DifferentiableOn ℂ c.1 D := by
  rw [← hg.dom_eq]
  exact hg.conf.differentiableOn_fwd

/-- A logarithm of the derivative of R1's chart: `log a + physicalRestartLog B` (positive scale, real translation). -/
theorem isDerivLog_seedLog {a x : ℝ} (ha : 0 < a)
    (hsc : EqOn c.1 (fun z => (a : ℂ) * (ConformalImage.mapOut (stripTargetHull D) (stripRightRetarget z) - x)) D) :
    IsDerivLog c.1 (seedLog D a) D := by
  have hB := hg.isHPHull_B
  have hgd : DifferentiableOn ℂ (ConformalImage.mapOut (stripTargetHull D) ∘ stripRightRetarget) D :=
    (ConformalImage.isMapOut_mapOut hB).1.1.comp
      (Aux61Restart.isConformalBijection_stripRightRetarget.1.mono hg.dom_subset_H) hg.mapsTo_retarget
  exact Aux61Restart.isDerivLog_pos_scale_sub hg.isOpen_D hgd
    (Aux61Restart.isDerivLog_physicalRestartLog hg.isOpen_D hB hg.dom_subset_H hg.mapsTo_retarget) ha hsc

theorem fwdMapInv_mem {z : ℂ} (hz : z ∈ H) : fwdMapInv Wph r z ∈ H \ fwdHull Wph r :=
  QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hg.hW hg.hW0 hg.rpos.le hz

theorem inv_mem_D {y : ℂ} (hy : y ∈ H) : c.2.1 y ∈ D := by
  rw [← hg.dom_eq]
  exact hg.conf.inv_mem_dom hy

/-- TWOSIDES's `hinvD`: the inverse chart maps `ℍ` off the physical hull at the restart time. -/
theorem inv_mem_compl (y : ℂ) (hy : y ∈ H) : c.2.1 y ∈ H \ fwdHull Wph r := hg.dom_sub (hg.inv_mem_D hy)

/-- TWOSIDES's `hlift`, for the seed logarithm. -/
theorem lift_inv_eq (a : ℝ) (y : ℂ) (hy : y ∈ H) : c.2.2 (c.2.1 y) = (seedLog D a (c.2.1 y)).im := by
  rw [hg.lift _ (hg.inv_mem_D hy), seedLog, add_im, ofReal_im, zero_add]

theorem isOpen_flowDom : IsOpen (flowDom Wph r D) :=
  ((QuantumZipper.RS.differentiableOn_fwdMapInv hg.hW hg.hW0 hg.rpos.le).continuousOn).isOpen_inter_preimage
    QuantumZipper.isOpen_H hg.isOpen_D

theorem physInv_mem {y : ℂ} (hy : y ∈ H) : physInv Wph r c y ∈ flowDom Wph r D := by
  have hD := hg.inv_mem_D hy
  have hK := hg.dom_sub hD
  refine ⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hg.hW hg.rpos.le hK, ?_⟩
  show fwdMapInv Wph r (fwdMap Wph r (c.2.1 y)) ∈ D
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hg.hW hg.hW0 hg.rpos.le hK]
  exact hD

/-! ### The seed -/

/-- `Im Ψ → 0` at every real point of the current collar (properness of `mapOut B` through R1's scale), for the collar
radius shrunk so that its boundary images stay away from the target `1`. -/
theorem exists_collar_im :
    ∃ δ > 0, MapsTo (fwdMapInv Wph r) (ball 0 δ ∩ H) D ∧
      ∀ ξ : ℝ, |ξ| < δ → Tendsto (fun z => (flowChart Wph r c z).im) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨a, x, ha, hsc⟩ := hg.scale
  obtain ⟨δ₁, hδ₁, hcol⟩ := hg.collar
  set F := fwdMapInv Wph r with hFdef
  set R := stripRightRetarget with hRdef
  set B := stripTargetHull D with hBdef
  have hB : IsHPHull B := hg.isHPHull_B
  have hgB := ConformalImage.isMapOut_mapOut hB
  have hRD : H \ B = R '' D := Aux61Restart.H_diff_stripTargetHull hg.dom_subset_H
  have hBd := hg.trace.hasBdryLimits hg.hW hg.hW0 hg.rpos.le
  have h0H : (0 : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have htip : extendFrom H F 0 = η r := hg.trace.loewnerTip_eq hg.hW hg.hW0 hg.rpos.le
  have hηr : η r ∈ H := hg.mem_H r ⟨hg.rpos, by linarith [hg.τpos]⟩
  have hηr1 : 0 < dist (η r) 1 := dist_pos.2 fun h => by
    rw [h] at hηr
    exact lt_irrefl _ (show (0 : ℝ) < (1 : ℂ).im from hηr)
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.continuousWithinAt_iff.1 (hBd.continuousOn 0 h0H) _ hηr1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun z hz => hcol ⟨ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩,
    fun ξ hξ => ?_⟩
  have hξH : (ξ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  set q := extendFrom H F ξ with hqdef
  have hq1 : q ≠ 1 := by
    intro h
    have hd := @hδ₂sub (ξ : ℂ) hξH (by
      rw [dist_zero_right, norm_real, Real.norm_eq_abs]
      exact hξ.trans_le (min_le_right _ _))
    rw [← hqdef, h, htip, dist_comm] at hd
    exact lt_irrefl _ hd
  have hqD : q ∉ D := fun h =>
    Aux61TwoS.extendFrom_notMem_compl_fwdHull hg.hW hg.hW0 hg.trace hg.rpos.le ξ (hg.dom_sub h)
  have hqcl : q ∈ Hbar := Prop49Exit.extendFrom_mem_Hbar hg.trace hg.hW hg.hW0 hg.rpos.le ξ
  have hRq : R q ∉ H \ B := by
    rw [hRD]
    rintro ⟨o, ho, he⟩
    have hoH := hg.dom_subset_H ho
    by_cases hqH : q ∈ H
    · exact hqD (Aux61Restart.isConformalBijection_stripRightRetarget.2.injOn hqH hoH he.symm ▸ ho)
    · have hq0 : q.im = 0 := le_antisymm (not_lt.1 hqH) hqcl
      have hRq0 : (R q).im = 0 := by
        rw [hRdef, Aux61Restart.stripRightRetarget_eq, div_im, sub_im, one_im, hq0]
        simp
      have : (R o).im > 0 := Aux61Restart.isConformalBijection_stripRightRetarget.2.mapsTo hoH
      rw [he, hRq0] at this
      exact lt_irrefl _ this
  have hball : ∀ᶠ z in 𝓝[H] (ξ : ℂ), z ∈ ball (0 : ℂ) δ₁ ∩ H := by
    have hξb : (ξ : ℂ) ∈ ball (0 : ℂ) δ₁ := by
      rw [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs]
      exact hξ.trans_le (min_le_left _ _)
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hξb), self_mem_nhdsWithin] with z h1 h2
    exact ⟨h1, h2⟩
  have hRF : Tendsto (fun y => R (F y)) (𝓝[H] (ξ : ℂ)) (𝓝[H \ B] (R q)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Aux61TwoS.continuousAt_stripRightRetarget hq1).tendsto.comp (hBd.tendsto hξH),
      hball.mono fun z hz => by rw [hRD]; exact mem_image_of_mem _ (hcol hz)⟩
  have hIm := ((IsMapOut.tendsto_im_nhdsWithin hB hgB hRq).comp hRF).const_mul a
  rw [mul_zero] at hIm
  refine hIm.congr' (hball.mono fun z hz => ?_)
  have hFz := hcol hz
  simp only [Function.comp_apply, flowChart]
  rw [← hFdef, hsc hFz, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, sub_im, ofReal_im, sub_zero]

/-- **R1's lift is seed-normalized** (`log_seed`): through the physical trace frozen at `r + τ` (a proper arc) and
TWOSIDES's `tendsto_im_physicalRestartLog_retained_sub_logDerivFwd`. -/
theorem tendsto_im_physLog_seed (a : ℝ) :
    Tendsto (fun z => (physLog Wph r (seedLog D a) z).im) (𝓝[H] 0) (𝓝 0) := by
  set T' := r + τ with hT'
  have hT'pos : 0 < T' := by linarith [hg.rpos, hg.τpos]
  have hLT := WangWu.isLoewnerTraceLT_of_isLoewnerTrace hg.trace (T' + 1)
  have hη₁ := hLT.isLoewnerTrace_ext hg.hW hg.hW0 hT'pos.le (by linarith)
  have hη₁p : IsProperArc (extTrace Wph η T') :=
    WangWu.isProperArc_extTrace hLT hg.hW hg.hW0 hT'pos.le (by linarith) hg.inj hg.mem_H
  have hW₁ : Continuous (extDrive Wph T') := YuanCorollary13.continuous_extDrive hg.hW
  have hW₁0 : extDrive Wph T' 0 = 0 := YuanCorollary13.extDrive_zero hg.hW0 hT'pos.le
  have hrT : r ≤ T' := by linarith [hg.τpos]
  have heq : ∀ s ∈ Icc (0 : ℝ) r, extDrive Wph T' s = Wph s := fun s hs =>
    YuanCorollary13.extDrive_eq (hs.2.trans hrT)
  have hK : fwdHull (extDrive Wph T') r = fwdHull Wph r :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc hW₁ hg.hW hg.rpos.le heq
  have hFeq : ∀ z ∈ H, fwdMapInv (extDrive Wph T') r z = fwdMapInv Wph r z := fun z hz =>
    ZhanGT4.fwdMapInv_congr hW₁ hg.hW hW₁0 hg.hW0 hg.rpos.le heq hz
  have hLeq : ∀ z, logDerivFwd (extDrive Wph T') r z = logDerivFwd Wph r z := fun z =>
    Ito.logDerivFwd_congr_of_eqOn (T := r) (fun s hs => heq s hs) hg.rpos.le le_rfl
  obtain ⟨δ, hδ, hcol⟩ := hg.collar
  have hcol₁ : ∃ δ > 0, MapsTo (fwdMapInv (extDrive Wph T') r) (ball 0 δ ∩ H) D :=
    ⟨δ, hδ, fun z hz => by rw [hFeq z hz.2]; exact hcol hz⟩
  have hDO : D ⊆ H \ fwdHull (extDrive Wph T') r := by rw [hK]; exact hg.dom_sub
  have h := Aux61TwoS.tendsto_im_physicalRestartLog_retained_sub_logDerivFwd hW₁ hW₁0 hη₁ hη₁p hg.rpos hDO
    hg.isHPHull_B hcol₁
  refine h.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  simp only [physLog, seedLog, hFeq z hz, hLeq, add_sub_assoc, add_im, ofReal_im, zero_add]

/-! ### The configuration -/

/-- **The two-sides configuration from the glued data** (TWOSIDES's wiring (W), field by field): for a comparison time
`σ ∈ (0, τ)` there are a seed radius `δ` and a scale `a > 0` such that the frozen shifted driver and continuation, the
actual continuation `β₀`, the restart chart in flow coordinates with the seed logarithm `log a + physicalRestartLog B`,
and the chart driver and trace frozen at `t` form an `IsTwoSideConfig`; R1's lift is `Im` of the seed logarithm on the
inverse chart. -/
theorem exists_isTwoSideConfig {σ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) :
    ∃ δ a : ℝ, IsTwoSideConfig (extDrive (shiftDrive Wph r) σ)
        (extTrace (shiftDrive Wph r) (loewnerTip (shiftDrive Wph r)) σ) (loewnerTip (shiftDrive Wph r)) σ τ
        (flowDom Wph r D) (flowChart Wph r c) (physInv Wph r c) (physLog Wph r (seedLog D a)) δ
        (extDrive w t) (extTrace w γ t) t ∧
      ∀ y ∈ H, c.2.2 (c.2.1 y) = (seedLog D a (c.2.1 y)).im := by
  obtain ⟨a, x, ha, hsc⟩ := hg.scale
  obtain ⟨δ, hδ, hcol, him⟩ := hg.exists_collar_im
  have hV := hg.continuous_shift
  have hV0 : shiftDrive Wph r 0 = 0 := shiftDrive_zero Wph r
  have hLT := WangWu.isLoewnerTraceLT_of_isLoewnerTrace hg.shift_trace (σ + 1)
  have hr := hg.rpos.le
  have hFd := QuantumZipper.RS.differentiableOn_fwdMapInv hg.hW hg.hW0 hr
  refine ⟨δ, a, ?_, hg.lift_inv_eq a⟩
  exact
  { hW := YuanCorollary13.continuous_extDrive hV
    hW0 := YuanCorollary13.extDrive_zero hV0 hσ.le
    trace := hLT.isLoewnerTrace_ext hV hV0 hσ.le (by linarith)
    arc := WangWu.isProperArc_extTrace hLT hV hV0 hσ.le (by linarith)
      (hg.injOn_shift.mono (Icc_subset_Icc_right hστ.le)) fun u hu => hg.shift_mem_H ⟨hu.1, hu.2.trans hστ.le⟩
    σpos := hσ
    σ_lt_τ := hστ
    cont_eqOn := fun u hu => (YuanCorollary13.extTrace_eq hu.2).symm
    cont_contOn := hg.continuous_shiftTip.mono Icc_subset_Ici_self
    cont_injOn := hg.injOn_shift
    cont_mapsTo := fun u hu => ⟨hg.shift_mem_H hu, by
      show fwdMapInv Wph r (loewnerTip (shiftDrive Wph r) u) ∈ D
      rw [hg.fwdMapInv_shift hu]
      exact hg.cont u hu⟩
    isOpen_dom := hg.isOpen_flowDom
    dom_subset := fun z hz => hz.1
    diff := hg.diffOn_fwd.comp (hFd.mono fun z hz => hz.1) fun z hz => hz.2
    injOn := by
      intro z₁ hz₁ z₂ hz₂ he
      have h1 : fwdMapInv Wph r z₁ = fwdMapInv Wph r z₂ := by
        have e1 := hg.conf.inv_fwd (hg.mem_dom hz₁.2)
        have e2 := hg.conf.inv_fwd (hg.mem_dom hz₂.2)
        rw [← e1, ← e2]
        exact congrArg c.2.1 he
      rw [← QuantumZipper.RS.fwdMap_fwdMapInv hg.hW hg.hW0 hr hz₁.1,
        ← QuantumZipper.RS.fwdMap_fwdMapInv hg.hW hg.hW0 hr hz₂.1, h1]
    mapsTo := fun z hz => hg.conf.fwd_mem (hg.mem_dom hz.2)
    inv_contOn := by
      have h1 : ContinuousOn c.2.1 H := hg.conf.1.continuousOn
      have h2 : ContinuousOn (fwdMap Wph r) (H \ fwdHull Wph r) :=
        (QuantumZipper.FwdHolo.differentiableOn_fwdMap hg.hW hr).continuousOn
      exact h2.comp h1 fun y hy => hg.inv_mem_compl y hy
    inv_mapsTo := fun y hy => hg.physInv_mem hy
    apply_inv := fun y hy => by
      show c.1 (fwdMapInv Wph r (fwdMap Wph r (c.2.1 y))) = y
      rw [QuantumZipper.RS.fwdMapInv_fwdMap hg.hW hg.hW0 hr (hg.inv_mem_compl y hy)]
      exact hg.conf.2.2 y hy
    inv_apply := fun z hz => by
      show fwdMap Wph r (c.2.1 (c.1 (fwdMapInv Wph r z))) = z
      rw [hg.conf.inv_fwd (hg.mem_dom hz.2),
        QuantumZipper.RS.fwdMap_fwdMapInv hg.hW hg.hW0 hr hz.1]
    δpos := hδ
    collar := fun z hz => ⟨hz.1, hcol ⟨hz.2, hz.1⟩⟩
    tendsto_zero := hg.current
    tendsto_im := him
    log := by
      have hc := IsDerivLog.comp hg.isOpen_flowDom hg.isOpen_D hg.diffOn_fwd (hFd.mono fun z hz => hz.1)
        (fun z hz => hz.2) (hg.isDerivLog_seedLog ha hsc)
        ((Aux10.isDerivLog_fwdMapInv hg.hW hg.hW0 hr).mono fun z hz => hz.1)
      have he : physLog Wph r (seedLog D a) =
          fun z => seedLog D a (fwdMapInv Wph r z) + -logDerivFwd Wph r (fwdMapInv Wph r z) := by
        funext z
        rw [physLog, sub_eq_add_neg]
      rw [he]
      exact hc
    log_seed := hg.tendsto_im_physLog_seed a
    hw := YuanCorollary13.continuous_extDrive hg.hw
    hw0 := YuanCorollary13.extDrive_zero hg.hw0 hg.tpos.le
    ctrace := hg.ctrace.isLoewnerTrace_ext hg.hw hg.hw0 hg.tpos.le hg.t_lt
    carc := WangWu.isProperArc_extTrace hg.ctrace hg.hw hg.hw0 hg.tpos.le hg.t_lt hg.cinj hg.cmem_H
    tpos := hg.tpos
    hull := by
      rw [YuanCorollary13.fwdHull_eq_of_eqOn_Icc (YuanCorollary13.continuous_extDrive hg.hw) hg.hw hg.tpos.le
        (fun s hs => YuanCorollary13.extDrive_eq hs.2), hg.hull, image_image, image_image]
      refine image_congr fun u hu => ?_
      show c.1 (η (r + u)) = c.1 (fwdMapInv Wph r (loewnerTip (shiftDrive Wph r) u))
      rw [hg.fwdMapInv_shift hu]
    tip := by
      rw [YuanCorollary13.extTrace_eq le_rfl, hg.tip]
      show c.1 (η (r + τ)) = c.1 (fwdMapInv Wph r (loewnerTip (shiftDrive Wph r) τ))
      rw [hg.fwdMapInv_shift ⟨hg.τpos, le_rfl⟩] }

end IsGluedSlit

end InteractingSLE.Sec5.Aux61Conf2
