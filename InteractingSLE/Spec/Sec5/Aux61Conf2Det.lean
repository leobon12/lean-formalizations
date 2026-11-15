/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Conf2Config
import InteractingSLE.Spec.Sec5.Aux61GInstBoundary

/-!
# Aux. 61 at the glued stop, III: the slit-side boundary data, deterministic part

Packet PROVE-AUX61-CONFIG. For one sample with glued two-sides data `IsGluedSlit` and a real point `x′` of the chart's
`F_t`-boundary (`F_t = fwdMapInv w t`, `w` the chart driver, `t` the chart time):

* **`IsGluedSlit.exists_slitTime`** (the slit points): if `x′ ≠ 0` and `F̄_t(x′) ∈ ℍ`, then `F_t → c.1(η(r + s′))` at
  `x′` for some `s′ ∈ (0, τ)` (the point of the continuation strictly before its tip);
* **`IsGluedSlit.tendsto_inv_fwdMapInv`** ((D2), the boundary correspondence): then `inv ∘ F_t → η(r + s′)`;
* **`IsGluedSlit.tendsto_chartReading_sub_couplingMean`** ((D1) at the glued data): for a comparison time
  `σ ∈ (s′, τ)`, the chart reading of the physical flow line's mean at time `r + σ` minus the chart coupling mean tends
  to `0` at `x′` — the height offset is `0` (R1's lift is seed-normalized), and the boundary heights `bL`/`bR` of the
  physical word on the left/right side of `η[0, r + σ]` are the chart word's heights on the left/right side of the chart
  slit;
* **`IsGluedSlit.tendsto_chartReading_sub_meanF`**: with PROVE-AUX61-GLUEINST's
  `Aux61GInst.tendsto_meanF_sub_couplingMean`, the same with the explicit mean `meanF` (for `canonMean`:
  `uc = canonExt`) in place of the coupling mean — SLIT's `hdet` in `Aux61SlitV.tendsto_slit_of_chart`.

The height hypotheses are stated in the physical time-`(r + σ)` coordinates ("`u_ph → bL` at every real `p < 0` whose
boundary image `F̄_{r+σ}(p)` is a point of `ℍ`", i.e. on the left side of the hull) and at `x′` for the chart word.

Deterministic; conditional helpers with distinct names; no source statement is replaced. R48/R77: nothing here uses
Theorem 1.2/1.3 or the post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Sec5.Aux61Conf2

open WangWu (IsProperArc chartAL chartAR)
open Aux61Restart (stripRightRetarget stripTargetHull physicalRestartLog)
open YuanCorollary13 (extDrive extTrace)
open Aux61TwoS (IsTwoSideConfig physInv physLog)
open Restart.FlowStopIdentCMI (CMCut)
open Aux61Win (IsCutoffOn meanF)

/-- `extendFrom H` only reads the function on `ℍ`. -/
theorem extendFrom_congr_H {f g : ℂ → ℂ} (h : EqOn f g H) : extendFrom H f = extendFrom H g := by
  funext x
  simp only [extendFrom, limUnder]
  rw [Filter.map_congr (eventuallyEq_nhdsWithin_of_eqOn h)]

namespace IsGluedSlit

variable {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r τ : ℝ} {c : Chart} {D : Set ℂ} {w : ℝ → ℝ} {γ : ℝ → ℂ} {Tc t : ℝ}
  (hg : IsGluedSlit Wph η r τ c D w γ Tc t)
include hg

/-! ### The frozen chart chain -/

theorem continuous_extW : Continuous (extDrive w t) := YuanCorollary13.continuous_extDrive hg.hw

theorem extW_zero : extDrive w t 0 = 0 := YuanCorollary13.extDrive_zero hg.hw0 hg.tpos.le

omit hg in
theorem extW_eqOn : EqOn (extDrive w t) w (Icc 0 t) := fun _ hs => YuanCorollary13.extDrive_eq hs.2

theorem ext_trace : IsLoewnerTrace (extDrive w t) (extTrace w γ t) :=
  hg.ctrace.isLoewnerTrace_ext hg.hw hg.hw0 hg.tpos.le hg.t_lt

theorem ext_arc : IsProperArc (extTrace w γ t) :=
  WangWu.isProperArc_extTrace hg.ctrace hg.hw hg.hw0 hg.tpos.le hg.t_lt hg.cinj hg.cmem_H

theorem fwdMapInv_extW {y : ℂ} (hy : y ∈ H) : fwdMapInv (extDrive w t) t y = fwdMapInv w t y :=
  ZhanGT4.fwdMapInv_congr hg.continuous_extW hg.hw hg.extW_zero hg.hw0 hg.tpos.le (fun _ hs => extW_eqOn hs) hy

theorem extendFrom_extW : extendFrom H (fwdMapInv (extDrive w t) t) = extendFrom H (fwdMapInv w t) :=
  extendFrom_congr_H fun _ hy => hg.fwdMapInv_extW hy

theorem fwdHull_extW : fwdHull (extDrive w t) t = fwdHull w t :=
  YuanCorollary13.fwdHull_eq_of_eqOn_Icc hg.continuous_extW hg.hw hg.tpos.le fun _ hs => extW_eqOn hs

/-! ### The slit points -/

/-- **The slit points of the chart boundary**: a real `x′ ≠ 0` whose `F_t`-boundary value lies in `ℍ` is the image of
a point `c.1(η(r + s′))` of the continuation strictly before its tip, and `F_t` tends to it at `x′`. -/
theorem exists_slitTime {x' : ℝ} (hx'0 : x' ≠ 0) (hx'H : extendFrom H (fwdMapInv w t) x' ∈ H) :
    ∃ s' ∈ Ioo 0 τ, Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (c.1 (η (r + s')))) := by
  have hγ := hg.ext_trace
  have hBd := hγ.hasBdryLimits hg.continuous_extW hg.extW_zero hg.tpos.le
  have hx'Hb : (x' : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  rw [← hg.extendFrom_extW] at hx'H
  obtain ⟨hK, -⟩ := ZhanGT4.extendFrom_mem_fwdHull hγ hg.continuous_extW hg.extW_zero hg.tpos.le hx'H
  rw [hg.fwdHull_extW, hg.hull] at hK
  obtain ⟨_, ⟨s', hs', rfl⟩, hp⟩ := hK
  have hlim : Tendsto (fwdMapInv (extDrive w t) t) (𝓝[H] (x' : ℂ)) (𝓝 (c.1 (η (r + s')))) := by
    rw [hp]
    exact hBd.tendsto hx'Hb
  refine ⟨s', ⟨hs'.1, lt_of_le_of_ne hs'.2 fun he => hx'0 ?_⟩,
    hlim.congr' (eventually_nhdsWithin_of_forall fun y hy => hg.fwdMapInv_extW hy)⟩
  refine WangWu.eq_zero_of_extendFrom_eq_tip hγ hg.ext_arc hg.continuous_extW hg.extW_zero hg.tpos ?_
  rw [YuanCorollary13.extTrace_eq le_rfl, hg.tip, ← he, ← hp]

/-- **(D2) the boundary correspondence**: `inv ∘ F_t → η(r + s′)` at a slit point. -/
theorem tendsto_inv_fwdMapInv {x' s' : ℝ} (hs' : s' ∈ Ioc 0 τ)
    (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (c.1 (η (r + s'))))) :
    Tendsto (fun y => c.2.1 (fwdMapInv w t y)) (𝓝[H] (x' : ℂ)) (𝓝 (η (r + s'))) := by
  have hD : η (r + s') ∈ c.dom := hg.mem_dom (hg.cont s' hs')
  exact Aux61TwoS.tendsto_inv_comp_of_tendsto hg.conf hx' (hg.conf.fwd_mem hD) (hg.conf.inv_fwd hD)

/-! ### (D1) at the glued data -/

/-- A real point of the new piece's left or right side in the frozen shifted chart at time `σ` is a point of the
physical hull's side at time `r + σ`: its `F̄_{r+σ}`-image lies in `ℍ`. -/
theorem extendFrom_mem_H_phys {σ : ℝ} (hσ : 0 < σ) {p : ℝ}
    (hp : extendFrom H (fwdMapInv (extDrive (shiftDrive Wph r) σ) σ) p ∈ H) :
    extendFrom H (fwdMapInv Wph (r + σ)) p ∈ H := by
  set V := shiftDrive Wph r with hV
  have hVc : Continuous V := hg.continuous_shift
  have hV0 : V 0 = 0 := shiftDrive_zero Wph r
  have hLT := WangWu.isLoewnerTraceLT_of_isLoewnerTrace hg.shift_trace (σ + 1)
  have hβ := hLT.isLoewnerTrace_ext hVc hV0 hσ.le (by linarith)
  have hW'c : Continuous (extDrive V σ) := YuanCorollary13.continuous_extDrive hVc
  have hW'0 : extDrive V σ 0 = 0 := YuanCorollary13.extDrive_zero hV0 hσ.le
  have hBd := hβ.hasBdryLimits hW'c hW'0 hσ.le
  have hpHb : (p : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  set q := extendFrom H (fwdMapInv (extDrive V σ) σ) p with hq
  have h1 : Tendsto (fwdMapInv V σ) (𝓝[H] (p : ℂ)) (𝓝 q) :=
    (hBd.tendsto hpHb).congr' (eventually_nhdsWithin_of_forall fun y hy =>
      ZhanGT4.fwdMapInv_congr hW'c hVc hW'0 hV0 hσ.le (fun s hs => YuanCorollary13.extDrive_eq hs.2) hy)
  have hFr : ContinuousAt (fwdMapInv Wph r) q :=
    ((QuantumZipper.RS.differentiableOn_fwdMapInv hg.hW hg.hW0 hg.rpos.le).differentiableAt
      (QuantumZipper.isOpen_H.mem_nhds hp)).continuousAt
  have h2 : Tendsto (fwdMapInv Wph (r + σ)) (𝓝[H] (p : ℂ)) (𝓝 (fwdMapInv Wph r q)) :=
    (hFr.tendsto.comp h1).congr' (eventually_nhdsWithin_of_forall fun y hy =>
      (QuantumZipper.RS.fwdMapInv_add_shift hg.hW hg.hW0 hg.rpos.le hσ.le hy).symm)
  rw [extendFrom_eq (by rw [closure_H]; exact hpHb) h2]
  exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hg.hW hg.hW0 hg.rpos.le hp).1

/-- **(D1) at the glued data.** At a slit point `x′` (`F_t → c.1(η(r + s′))`, `0 < s′ < σ < τ`, `x′ ≠ 0`), the chart
reading of the physical flow line's mean at the comparison time `r + σ` minus the chart coupling mean tends to `0`,
when the physical word has the heights `bL`/`bR` on the left/right side of `η[0, r + σ]` and the chart word has the
same heights at `x′` on the corresponding side of the chart slit. -/
theorem tendsto_chartReading_sub_couplingMean (κ : ℝ) {s' σ : ℝ} (hs' : 0 < s') (hs'σ : s' < σ) (hστ : σ < τ)
    {x' : ℝ} (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (c.1 (η (r + s'))))) (hx'0 : x' ≠ 0)
    {uph uc : ℂ → ℝ} {bL bR : ℝ}
    (huL : ∀ p : ℝ, p < 0 → extendFrom H (fwdMapInv Wph (r + σ)) p ∈ H → Tendsto uph (𝓝[H] (p : ℂ)) (𝓝 bL))
    (huR : ∀ p : ℝ, 0 < p → extendFrom H (fwdMapInv Wph (r + σ)) p ∈ H → Tendsto uph (𝓝[H] (p : ℂ)) (𝓝 bR))
    (hucL : x' < 0 → Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bL)) (hucR : 0 < x' → Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bR)) :
    Tendsto (fun y => couplingMean κ Wph (r + σ) uph (c.2.1 (fwdMapInv w t y)) +
        chiC κ * c.2.2 (c.2.1 (fwdMapInv w t y)) - couplingMean κ w t uc (fwdMapInv w t y))
      (𝓝[H] (x' : ℂ)) (𝓝 0) := by
  have hσ : 0 < σ := hs'.trans hs'σ
  obtain ⟨δ, a, hc, hlift⟩ := hg.exists_isTwoSideConfig hσ hστ
  have hs'τ : s' ∈ Ioc 0 τ := ⟨hs', (hs'σ.trans hστ).le⟩
  have hx'c : Tendsto (fwdMapInv (extDrive w t) t) (𝓝[H] (x' : ℂ))
      (𝓝 (flowChart Wph r c (loewnerTip (shiftDrive Wph r) s'))) := by
    rw [flowChart, hg.fwdMapInv_shift hs'τ]
    exact hx'.congr' (eventually_nhdsWithin_of_forall fun y hy => (hg.fwdMapInv_extW hy).symm)
  have hW'eq : EqOn (extDrive (shiftDrive Wph r) σ) (fun s => Wph (r + s) - Wph r) (Icc 0 σ) :=
    fun s hs => YuanCorollary13.extDrive_eq hs.2
  have hphys : ∀ p : ℝ, extendFrom H (fwdMapInv (extDrive (shiftDrive Wph r) σ) σ) p ∈ H →
      extendFrom H (fwdMapInv Wph (r + σ)) p ∈ H := fun p hp => hg.extendFrom_mem_H_phys hσ hp
  -- the configuration's conclusion, with the chart driver frozen at `t`
  have key : Tendsto (fun y => couplingMean κ Wph (r + σ) uph (c.2.1 (fwdMapInv (extDrive w t) t y)) + 0 +
      chiC κ * c.2.2 (c.2.1 (fwdMapInv (extDrive w t) t y)) -
      couplingMean κ (extDrive w t) t uc (fwdMapInv (extDrive w t) t y)) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
    rcases lt_or_gt_of_ne hx'0 with hneg | hpos
    · have h := Aux61TwoS.tendsto_chartReading_sub_couplingMean_of_neg' κ hc hW'eq hg.hW hg.hW0 hg.rpos.le
        hg.inv_mem_compl hlift hs' hs'σ hx'c hneg (uph := uph) (uc := uc) (bph := bL) (bc := bL)
        (fun p hp1 hp2 => huL p hp2 (hphys p (GlueImg.extendFrom_mem_H_of_chartAL_lt hc.trace hc.arc hc.hW hc.hW0
          hσ hp1 (hp2.trans_le (WangWu.chartAR_nonneg hc.hW hσ.le))))) (hucL hneg) 0
      simpa only [add_zero, sub_self] using h
    · have h := Aux61TwoS.tendsto_chartReading_sub_couplingMean_of_pos' κ hc hW'eq hg.hW hg.hW0 hg.rpos.le
        hg.inv_mem_compl hlift hs' hs'σ hx'c hpos (uph := uph) (uc := uc) (bph := bR) (bc := bR)
        (fun p hp1 hp2 => huR p hp1 (hphys p (GlueImg.extendFrom_mem_H_of_chartAL_lt hc.trace hc.arc hc.hW hc.hW0
          hσ ((WangWu.chartAL_nonpos hc.hW hσ.le).trans_lt hp1) hp2))) (hucR hpos) 0
      simpa only [add_zero, sub_self] using h
  refine key.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hF := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hg.hw hg.hw0 hg.tpos.le hy
  rw [hg.fwdMapInv_extW hy, add_zero,
    Markov.couplingMean_congr_of_eqOn extW_eqOn hg.tpos.le le_rfl κ uc]

/-- **SLIT's `hdet` at the glued data**: with a cutoff `F` of the correction `q` on a neighbourhood `N` of the closed
chart hull, the chart reading of the physical flow line's mean minus the explicit mean `meanF κ uc q F w t` tends to `0`
at every slit point (PROVE-AUX61-GLUEINST's `tendsto_meanF_sub_couplingMean` for the second difference). -/
theorem tendsto_chartReading_sub_meanF (κ : ℝ) {s' σ : ℝ} (hs' : 0 < s') (hs'σ : s' < σ) (hστ : σ < τ)
    {x' : ℝ} (hx' : Tendsto (fwdMapInv w t) (𝓝[H] (x' : ℂ)) (𝓝 (c.1 (η (r + s'))))) (hx'0 : x' ≠ 0)
    {uph uc : ℂ → ℝ} {bL bR : ℝ}
    (huL : ∀ p : ℝ, p < 0 → extendFrom H (fwdMapInv Wph (r + σ)) p ∈ H → Tendsto uph (𝓝[H] (p : ℂ)) (𝓝 bL))
    (huR : ∀ p : ℝ, 0 < p → extendFrom H (fwdMapInv Wph (r + σ)) p ∈ H → Tendsto uph (𝓝[H] (p : ℂ)) (𝓝 bR))
    (hucL : x' < 0 → Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bL)) (hucR : 0 < x' → Tendsto uc (𝓝[H] (x' : ℂ)) (𝓝 bR))
    {q : ℂ → ℝ} {F : CMCut} {N : Set ℂ} {O : Set ℝ} (hF : IsCutoffOn F q N O)
    (hKN : closure (fwdHull w t) ⊆ N) :
    Tendsto (fun y => couplingMean κ Wph (r + σ) uph (c.2.1 (fwdMapInv w t y)) +
        chiC κ * c.2.2 (c.2.1 (fwdMapInv w t y)) - meanF κ uc q F w t (fwdMapInv w t y))
      (𝓝[H] (x' : ℂ)) (𝓝 0) := by
  have h1 := hg.tendsto_chartReading_sub_couplingMean κ hs' hs'σ hστ hx' hx'0 huL huR hucL hucR
  set Ψ := extendFrom H (fwdMapInv (extDrive w t) t) with hΨ
  have hBd := hg.ext_trace.hasBdryLimits hg.continuous_extW hg.extW_zero hg.tpos.le
  have hΨeq : EqOn Ψ (fwdMapInv w t) H := fun y hy => by
    rw [hΨ, WangWu.extendFrom_fwdMapInv_eq hg.continuous_extW hg.extW_zero hg.tpos.le hy, hg.fwdMapInv_extW hy]
  have hx'Hb : (x' : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hΨx : Ψ x' = c.1 (η (r + s')) := by
    rw [hΨ, hg.extendFrom_extW]
    exact extendFrom_eq (by rw [closure_H]; exact hx'Hb) hx'
  have hN : Ψ x' ∈ N := by
    rw [hΨx]
    refine hKN (subset_closure ?_)
    rw [hg.hull]
    exact ⟨_, ⟨s', ⟨hs', (hs'σ.trans hστ).le⟩, rfl⟩, rfl⟩
  have h2 := Aux61GInst.tendsto_meanF_sub_couplingMean (κ := κ) (v := uc) hF hg.hw hg.hw0 hg.tpos.le hKN hΨeq
    hBd.continuousOn x' hN
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  refine h3.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  simp only [hΨeq hy]
  ring

end IsGluedSlit

end InteractingSLE.Sec5.Aux61Conf2
