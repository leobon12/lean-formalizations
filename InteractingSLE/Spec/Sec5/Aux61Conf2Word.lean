/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Conf2Det
import InteractingSLE.Spec.Sec5.Aux61UnionKPC1
import InteractingSLE.Spec.Sec5.Aux61MeanIdSlit
import InteractingSLE.Spec.Sec7.Aux37SideGerm
import InteractingSLE.Spec.Supplement.GB6LifeBase
import InteractingSLE.Spec.Supplement.GW3Word

/-!
# Aux. 61 at the glued stop, V: the chart word's heights on the two new sides

Packet PROVE-AUX61-CONFIG. The chart field's canonical reference extension `canonExt d s q` (the bounded harmonic
extension of the data's flow-line word at the geometric images of its marks under the decoded chart driver) has the
flow line's own heights on the two sides of the chart slit:

* **`tendsto_bhe_left`** / **`tendsto_bhe_right`** (generic): a bounded harmonic extension of the force data at the
  time-`t` geometric images of left marks `≤ 0` and right marks `≥ 0` tends to `−π/√κ` on `(chartAL W t, 0)` and to
  `π/√κ` on `(0, chartAR W t)` (the left marks' images are `≤ chartAL W t` by monotonicity of the real flow, the right
  marks' images `≥ chartAR W t`, so no jump point and no active force weight lies between `x′` and `0`);
  **`tendsto_bhe_of_mem`**: the same at every real point whose `F_t`-boundary value lies in `ℍ` (for a continuous
  Loewner trace) — the form of `IsGluedSlitSample.physL/physR` for the physical word;
* **`tendsto_canonExt_left`** / **`tendsto_canonExt_right`**: the chart word `canonExt d s q` (FIBK), as an instance;
* **`IsGluedSlit.chartAL_lt_of_mem`**: a real point whose `F_t`-boundary value lies in `ℍ` is strictly between the base
  images `chartAL w t`, `chartAR w t`; hence **`IsGluedSlit.tendsto_canonExt_of_mem_left/right`**: the chart word's
  side heights at the points of the two new sides.

Deterministic; no source statement is replaced. R48/R77: nothing here uses Theorem 1.2/1.3 or the post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.Aux61Conf2

open WangWu (chartAL chartAR)
open MartChar.RealFlow (rightImg)
open Aux61Fib (FibCode FibData fibW)
open Aux61FibK (canonExt)
open YuanCorollary13 (extDrive)

universe v

/-- **The flow-line word's left height** (generic): a bounded harmonic extension of the force data at the geometric
images under a continuous driver `W` at time `t` of left marks `≤ 0` and right marks `≥ 0` tends to `−π/√κ` at every
real `x′` with `chartAL W t < x′ < 0` (no jump point there, no force weight active between `x′` and `0`). -/
theorem tendsto_bhe_left {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {W : ℝ → ℝ} {t : ℝ} {u : ℂ → ℝ} (hW : Continuous W) (ht : 0 ≤ t)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hb : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => Restart.FlowStopIdentCMI.geomL W t (xL i))
        (fun j => Restart.FlowStopIdentCMI.geomR W t (xR j)))
      (forceJumpSet (fun i => Restart.FlowStopIdentCMI.geomL W t (xL i))
        (fun j => Restart.FlowStopIdentCMI.geomR W t (xR j))) u)
    {x' : ℝ} (hL : chartAL W t < x') (h0 : x' < 0) :
    Tendsto u (𝓝[H] (x' : ℂ)) (𝓝 (-(Real.pi / Real.sqrt κ))) := by
  have hvL : ∀ i, Restart.FlowStopIdentCMI.geomL W t (xL i) ≤ chartAL W t := fun i => by
    have hm := Sec7.Aux37Side.rightImg_mono (w := fun r => -W r) hW.neg (neg_nonneg.2 (hxL i)) ht
    simp only [Restart.FlowStopIdentCMI.geomL, chartAL] at hm ⊢
    linarith
  have hvR : ∀ j, chartAR W t ≤ Restart.FlowStopIdentCMI.geomR W t (xR j) := fun j => by
    have hm := Sec7.Aux37Side.rightImg_mono hW (hxR j) ht
    simp only [Restart.FlowStopIdentCMI.geomR, chartAR] at hm ⊢
    linarith
  have hAR := WangWu.chartAR_nonneg (T := t) hW ht
  have hJ : x' ∉ forceJumpSet (fun i => Restart.FlowStopIdentCMI.geomL W t (xL i))
      (fun j => Restart.FlowStopIdentCMI.geomR W t (xR j)) := by
    rintro (h | ⟨i, hi⟩ | ⟨j, hj⟩)
    · exact h0.ne h
    · linarith [hvL i]
    · linarith [hvR j]
  have hval : forceBoundaryData κ ρL ρR (fun i => Restart.FlowStopIdentCMI.geomL W t (xL i))
      (fun j => Restart.FlowStopIdentCMI.geomR W t (xR j)) x' = -(Real.pi / Real.sqrt κ) := by
    simp only [forceBoundaryData, h0, ↓reduceIte]
    rw [Finset.filter_false_of_mem fun i _ => not_lt.2 ((hvL i).trans hL.le), Finset.sum_empty, add_zero, mul_one]
  rw [← hval]
  exact hb.2.2 x' hJ

/-- **The flow-line word's right height** (generic): `π/√κ` at every real `x′` with `0 < x′ < chartAR W t`. -/
theorem tendsto_bhe_right {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {W : ℝ → ℝ} {t : ℝ} {u : ℂ → ℝ} (hW : Continuous W) (ht : 0 ≤ t)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hb : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => Restart.FlowStopIdentCMI.geomL W t (xL i))
        (fun j => Restart.FlowStopIdentCMI.geomR W t (xR j)))
      (forceJumpSet (fun i => Restart.FlowStopIdentCMI.geomL W t (xL i))
        (fun j => Restart.FlowStopIdentCMI.geomR W t (xR j))) u)
    {x' : ℝ} (h0 : 0 < x') (hR : x' < chartAR W t) :
    Tendsto u (𝓝[H] (x' : ℂ)) (𝓝 (Real.pi / Real.sqrt κ)) := by
  have hvL : ∀ i, Restart.FlowStopIdentCMI.geomL W t (xL i) ≤ chartAL W t := fun i => by
    have hm := Sec7.Aux37Side.rightImg_mono (w := fun r => -W r) hW.neg (neg_nonneg.2 (hxL i)) ht
    simp only [Restart.FlowStopIdentCMI.geomL, chartAL] at hm ⊢
    linarith
  have hvR : ∀ j, chartAR W t ≤ Restart.FlowStopIdentCMI.geomR W t (xR j) := fun j => by
    have hm := Sec7.Aux37Side.rightImg_mono hW (hxR j) ht
    simp only [Restart.FlowStopIdentCMI.geomR, chartAR] at hm ⊢
    linarith
  have hAL := WangWu.chartAL_nonpos (T := t) hW ht
  have hJ : x' ∉ forceJumpSet (fun i => Restart.FlowStopIdentCMI.geomL W t (xL i))
      (fun j => Restart.FlowStopIdentCMI.geomR W t (xR j)) := by
    rintro (h | ⟨i, hi⟩ | ⟨j, hj⟩)
    · exact h0.ne' h
    · linarith [hvL i]
    · linarith [hvR j]
  have hval : forceBoundaryData κ ρL ρR (fun i => Restart.FlowStopIdentCMI.geomL W t (xL i))
      (fun j => Restart.FlowStopIdentCMI.geomR W t (xR j)) x' = Real.pi / Real.sqrt κ := by
    simp only [forceBoundaryData, not_lt.2 h0.le, ↓reduceIte]
    rw [Finset.filter_false_of_mem fun j _ => not_le.2 (hR.trans_le (hvR j)), Finset.sum_empty, add_zero, mul_one]
  rw [← hval]
  exact hb.2.2 x' hJ

/-- **The physical word's side heights** (`IsGluedSlitSample.physL/physR`): for a continuous Loewner trace of `W`, a
bounded harmonic extension of the force data at the time-`t` geometric images of left marks `≤ 0` and right marks
`≥ 0` tends to `−π/√κ` (resp. `π/√κ`) at every real `p < 0` (resp. `p > 0`) whose `F_t`-boundary value lies in `ℍ`. -/
theorem tendsto_bhe_of_mem {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ} {u : ℂ → ℝ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hb : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => Restart.FlowStopIdentCMI.geomL W t (xL i))
        (fun j => Restart.FlowStopIdentCMI.geomR W t (xR j)))
      (forceJumpSet (fun i => Restart.FlowStopIdentCMI.geomL W t (xL i))
        (fun j => Restart.FlowStopIdentCMI.geomR W t (xR j))) u) :
    (∀ p : ℝ, p < 0 → extendFrom H (fwdMapInv W t) p ∈ H → Tendsto u (𝓝[H] (p : ℂ)) (𝓝 (-(Real.pi / Real.sqrt κ)))) ∧
      ∀ p : ℝ, 0 < p → extendFrom H (fwdMapInv W t) p ∈ H → Tendsto u (𝓝[H] (p : ℂ)) (𝓝 (Real.pi / Real.sqrt κ)) :=
  ⟨fun _ h0 hp => tendsto_bhe_left hW ht hxL hxR hb (GlueImg.chartAL_lt_of_extendFrom_mem_H hη hW hW0 ht hp).1 h0,
    fun _ h0 hp => tendsto_bhe_right hW ht hxL hxR hb h0 (GlueImg.chartAL_lt_of_extendFrom_mem_H hη hW hW0 ht hp).2⟩

/-- **The chart word's left height**: on `(chartAL w q, 0)` the canonical reference extension tends to `−π/√κ`. -/
theorem tendsto_canonExt_left (d : FibData) (s : FibCode) (q : ℝ≥0) {x' : ℝ}
    (hL : chartAL (fun r : ℝ => FibCode.driver r.toNNReal s) q < x') (h0 : x' < 0) :
    Tendsto (canonExt.{v} d (ULift.up s) q) (𝓝[H] (x' : ℂ)) (𝓝 (-(Real.pi / Real.sqrt d.κ))) :=
  tendsto_bhe_left (Aux61MeanId.continuous_chartDriver s) q.coe_nonneg
    (Theorem14.GW3Word.flowLineXL_nonpos d.bR d.JR) (Theorem14.GW3Word.flowLineXR_nonneg d.bR d.JR)
    (Aux61UnionK.bhe_canonExt.{v} d (ULift.up s) q) hL h0

/-- **The chart word's right height**: on `(0, chartAR w q)` the canonical reference extension tends to `π/√κ`. -/
theorem tendsto_canonExt_right (d : FibData) (s : FibCode) (q : ℝ≥0) {x' : ℝ} (h0 : 0 < x')
    (hR : x' < chartAR (fun r : ℝ => FibCode.driver r.toNNReal s) q) :
    Tendsto (canonExt.{v} d (ULift.up s) q) (𝓝[H] (x' : ℂ)) (𝓝 (Real.pi / Real.sqrt d.κ)) :=
  tendsto_bhe_right (Aux61MeanId.continuous_chartDriver s) q.coe_nonneg
    (Theorem14.GW3Word.flowLineXL_nonpos d.bR d.JR) (Theorem14.GW3Word.flowLineXR_nonneg d.bR d.JR)
    (Aux61UnionK.bhe_canonExt.{v} d (ULift.up s) q) h0 hR

namespace IsGluedSlit

variable {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r τ : ℝ} {c : Chart} {D : Set ℂ} {w : ℝ → ℝ} {γ : ℝ → ℂ} {Tc t : ℝ}
  (hg : IsGluedSlit Wph η r τ c D w γ Tc t)
include hg

/-- A real point whose `F_t`-boundary value lies in `ℍ` is strictly between the base images. -/
theorem chartAL_lt_of_mem {x' : ℝ} (hx : extendFrom H (fwdMapInv w t) x' ∈ H) :
    chartAL w t < x' ∧ x' < chartAR w t := by
  rw [← hg.extendFrom_extW] at hx
  obtain ⟨h1, h2⟩ := GlueImg.chartAL_lt_of_extendFrom_mem_H hg.ext_trace hg.continuous_extW hg.extW_zero
    hg.tpos.le hx
  have heq : ∀ r ∈ Icc (0 : ℝ) t, extDrive w t r = w r := fun r hr => YuanCorollary13.extDrive_eq hr.2
  have hT : extDrive w t t = w t := YuanCorollary13.extDrive_eq le_rfl
  have hL : chartAL (extDrive w t) t = chartAL w t := by
    simp only [chartAL]
    rw [Supp8.GB6.rightImg_congr (w' := fun s => -w s) hg.hw.neg hg.tpos.le fun r hr => by rw [heq r hr], hT]
  have hR : chartAR (extDrive w t) t = chartAR w t := by
    simp only [chartAR]
    rw [Supp8.GB6.rightImg_congr hg.hw hg.tpos.le heq, hT]
  exact ⟨hL ▸ h1, hR ▸ h2⟩

end IsGluedSlit

/-- **The chart word's heights on the two new sides at a glued sample**: at a real `x′ < 0` (resp. `> 0`) whose
`F_q`-boundary value lies in `ℍ`, `canonExt d s q → −π/√κ` (resp. `π/√κ`). -/
theorem tendsto_canonExt_of_mem_left {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r τ : ℝ} {c : Chart} {D : Set ℂ} {γ : ℝ → ℂ}
    {Tc : ℝ} (d : FibData) {s : FibCode} {q : ℝ≥0}
    (hg : IsGluedSlit Wph η r τ c D (fun r : ℝ => FibCode.driver r.toNNReal s) γ Tc q) {x' : ℝ} (h0 : x' < 0)
    (hx : extendFrom H (fwdMapInv (fun r : ℝ => FibCode.driver r.toNNReal s) q) x' ∈ H) :
    Tendsto (canonExt.{v} d (ULift.up s) q) (𝓝[H] (x' : ℂ)) (𝓝 (-(Real.pi / Real.sqrt d.κ))) :=
  tendsto_canonExt_left d s q (hg.chartAL_lt_of_mem hx).1 h0

theorem tendsto_canonExt_of_mem_right {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r τ : ℝ} {c : Chart} {D : Set ℂ} {γ : ℝ → ℂ}
    {Tc : ℝ} (d : FibData) {s : FibCode} {q : ℝ≥0}
    (hg : IsGluedSlit Wph η r τ c D (fun r : ℝ => FibCode.driver r.toNNReal s) γ Tc q) {x' : ℝ} (h0 : 0 < x')
    (hx : extendFrom H (fwdMapInv (fun r : ℝ => FibCode.driver r.toNNReal s) q) x' ∈ H) :
    Tendsto (canonExt.{v} d (ULift.up s) q) (𝓝[H] (x' : ℂ)) (𝓝 (Real.pi / Real.sqrt d.κ)) :=
  tendsto_canonExt_right d s q h0 (hg.chartAL_lt_of_mem hx).2

end InteractingSLE.Sec5.Aux61Conf2
