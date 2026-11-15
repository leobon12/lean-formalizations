/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61TwoSPhys
import InteractingSLE.Spec.Sec5.Aux61TwoSSeedR1
import InteractingSLE.Foundations.Loewner.YuanCorollary13
import InteractingSLE.WangWu.ReverseContactBdryGlue
import InteractingSLE.Spec.Supplement.Aux10FullTD
import InteractingSLE.Spec.ZhanGT4.CrosscutRestart
import InteractingSLE.Spec.Sec5.Prop49QExitMainNR
import InteractingSLE.Spec.Sec5.Aux61RestartFinCanonical
import InteractingSLE.Spec.Sec7.Aux2728Pocket

/-!
# Aux. 61 at the glued stop, I: the per-sample glued two-sides data

Packet PROVE-AUX61-CONFIG (Theorem 1.2's Prop. 5.1 (E1); Astra's follow-up 4 §1.1, L113–L123, ruling R71). The
two-sides configuration `Aux61TwoS.IsTwoSideConfig` of PROVE-AUX61-TWOSIDES is stated in the coordinates of the
physical flow line mapped out at the restart time. This file records, **per sample and in physical coordinates**, the
objects the glued setting provides at the glued stop, in the form in which the landed constructions deliver them:

* the physical flow line: a continuous driver `Wph` (`Wph 0 = 0`) with a continuous Loewner trace `η`, simple and in
  `ℍ` on `(0, r + τ]` (`r > 0` the restart time, `τ > 0` the physical duration of the continuation read at the chart
  time);
* R1's restart chart `c` (`Aux61Restart.HasOriginalTargetRestartChart`): conformal, with domain the retained component
  `D ⊆ ℍ ∖ K_r` (open, simply connected, with a collar of the target `1`), the lift `Im physicalRestartLog B`
  (`B = stripTargetHull D`), the current collar `F_r(ℍ ∩ B(0, δ)) ⊆ D`, the current limit `c.1 ∘ F_r → 0` at `0` and
  the target limit `‖c.1(w + 1)‖ → ∞` as `w → 0` (exactly the clauses of `HasOriginalTargetRestartChart`);
* the continuation `η(r + u) ∈ D` for `u ∈ (0, τ]`;
* the chart path: a continuous chart driver `w` (`w 0 = 0`) with a Loewner trace `γ` continuous before `Tc`, simple and
  in `ℍ` on `(0, t]`, `0 < t < Tc`, whose hull at the chart time `t` is the chart image of the continuation, with tip
  the chart image of `η(r + τ)`.

`IsGluedSlit` is a predicate on these explicit objects (no proof step is hidden in it: each clause is a property of one
of the objects, as produced by R1, FIBDATA and the restart event). The derived objects of this file: the shifted
continuation `β₀ = loewnerTip (shiftDrive Wph r)` ([Yua22] Corollary 1.3, `F̄_r(β₀(u)) = η(r + u)`), R1's
positive-scale representation `c.1 = a (mapOut B ∘ R − x)` on `D` (`R(z) = z/(1 − z)`; R1's
`exists_original_target_chart_scale` from the exported clauses), its frozen proper
extensions at a comparison time `σ ∈ (0, τ)`, the chart trace frozen at `t`, the restart chart in flow coordinates
`Ψ = c.1 ∘ F_r` on `Ω = ℍ ∩ F_r⁻¹(D)`, and the seed logarithm `Lc = log a + physicalRestartLog B`.

Deterministic; conditional helpers with distinct names; no source statement is replaced. R48/R77: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param`, or Astra's post-contact kernel.
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

/-- **The glued two-sides data of one sample** at the glued stop (physical coordinates). `Wph`, `η`: the physical
flow line's driver and trace; `r`: the restart time; `τ`: the physical duration of the continuation up to the chart
time; `c`, `D`: R1's restart chart and its domain (the retained component); `w`, `γ`, `Tc`: the chart driver and the
chart trace (continuous before `Tc`); `t`: the chart time. -/
structure IsGluedSlit (Wph : ℝ → ℝ) (η : ℝ → ℂ) (r τ : ℝ) (c : Chart) (D : Set ℂ) (w : ℝ → ℝ) (γ : ℝ → ℂ)
    (Tc t : ℝ) : Prop where
  hW : Continuous Wph
  hW0 : Wph 0 = 0
  trace : IsLoewnerTrace Wph η
  rpos : 0 < r
  τpos : 0 < τ
  inj : InjOn η (Icc 0 (r + τ))
  mem_H : ∀ u ∈ Ioc 0 (r + τ), η u ∈ H
  conf : c.IsConformal
  dom_eq : (c.dom : Set ℂ) = D
  dom_sub : D ⊆ H \ fwdHull Wph r
  simply : IsSimplyConnected D
  target : ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ D
  infty : Tendsto (fun w : ℂ => ‖c.1 (w + 1)‖) (𝓝[H] 0) atTop
  lift : ∀ z ∈ D, c.2.2 z = (physicalRestartLog (stripTargetHull D) z).im
  collar : ∃ δ > 0, MapsTo (fwdMapInv Wph r) (ball 0 δ ∩ H) D
  current : Tendsto (fun z => c.1 (fwdMapInv Wph r z)) (𝓝[H] 0) (𝓝 0)
  cont : ∀ u ∈ Ioc 0 τ, η (r + u) ∈ D
  hw : Continuous w
  hw0 : w 0 = 0
  ctrace : IsLoewnerTraceLT w Tc γ
  tpos : 0 < t
  t_lt : t < Tc
  cinj : InjOn γ (Icc 0 t)
  cmem_H : ∀ u ∈ Ioc 0 t, γ u ∈ H
  hull : fwdHull w t = c.1 '' ((fun u => η (r + u)) '' Ioc 0 τ)
  tip : γ t = c.1 (η (r + τ))

/-- The restart chart in flow coordinates, `Ψ = c.1 ∘ F_r`. -/
def flowChart (Wph : ℝ → ℝ) (r : ℝ) (c : Chart) (z : ℂ) : ℂ := c.1 (fwdMapInv Wph r z)

/-- Its domain `Ω = ℍ ∩ F_r⁻¹(D)` (the retained component in flow coordinates). -/
def flowDom (Wph : ℝ → ℝ) (r : ℝ) (D : Set ℂ) : Set ℂ := {z | z ∈ H ∧ fwdMapInv Wph r z ∈ D}

/-- The seed logarithm `log a + physicalRestartLog B` of the derivative of R1's chart. -/
def seedLog (D : Set ℂ) (a : ℝ) (z : ℂ) : ℂ := (Real.log a : ℂ) + physicalRestartLog (stripTargetHull D) z

namespace IsGluedSlit

variable {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r τ : ℝ} {c : Chart} {D : Set ℂ} {w : ℝ → ℝ} {γ : ℝ → ℂ} {Tc t : ℝ}

section Basic

variable (hg : IsGluedSlit Wph η r τ c D w γ Tc t)
include hg

theorem dom_subset_H : D ⊆ H := fun _ hz => (hg.dom_sub hz).1

theorem isOpen_D : IsOpen D := by
  rw [← hg.dom_eq]
  exact c.dom.isOpen

theorem continuous_shift : Continuous (shiftDrive Wph r) := QuantumZipper.RS.continuous_shiftDrive hg.hW r

omit hg in
theorem shift_zero : shiftDrive Wph r 0 = 0 := shiftDrive_zero Wph r

/-- [Yua22] Corollary 1.3: the shifted continuation is a continuous Loewner trace of the shifted driver. -/
theorem shift_trace : IsLoewnerTrace (shiftDrive Wph r) (loewnerTip (shiftDrive Wph r)) :=
  (hg.trace.isLoewnerTrace_shift_and_extendFrom hg.hW hg.hW0 hg.rpos.le).1

/-- The shifted continuation lies over the future of the flow line: `F̄_r(β₀(u)) = η(r + u)`. -/
theorem extendFrom_shift {u : ℝ} (hu : 0 ≤ u) :
    extendFrom H (fwdMapInv Wph r) (loewnerTip (shiftDrive Wph r) u) = η (r + u) :=
  (hg.trace.isLoewnerTrace_shift_and_extendFrom hg.hW hg.hW0 hg.rpos.le).2 u hu

/-- The continuation's points `β₀(u)`, `0 < u ≤ τ`, are interior points of `ℍ`. -/
theorem shift_mem_H {u : ℝ} (hu : u ∈ Ioc 0 τ) : loewnerTip (shiftDrive Wph r) u ∈ H := by
  set p := loewnerTip (shiftDrive Wph r) u with hp
  have hpH : p ∈ Hbar := by
    rw [hp, ← hg.shift_trace.loewnerTip_eq hg.continuous_shift (shiftDrive_zero Wph r) hu.1.le]
    exact Prop49Exit.extendFrom_mem_Hbar hg.shift_trace hg.continuous_shift (shiftDrive_zero Wph r) hu.1.le 0
  by_contra hpn
  have hp0 : p.im = 0 := le_antisymm (not_lt.1 hpn) hpH
  have hpre : p = (p.re : ℂ) := Complex.ext (by simp) (by simp [hp0])
  have hnot := Aux61TwoS.extendFrom_notMem_compl_fwdHull hg.hW hg.hW0 hg.trace hg.rpos.le p.re
  rw [← hpre, hg.extendFrom_shift hu.1.le] at hnot
  exact hnot (hg.dom_sub (hg.cont u hu))

/-- On the continuation, `F_r(β₀(u)) = η(r + u)`. -/
theorem fwdMapInv_shift {u : ℝ} (hu : u ∈ Ioc 0 τ) :
    fwdMapInv Wph r (loewnerTip (shiftDrive Wph r) u) = η (r + u) := by
  rw [← hg.extendFrom_shift hu.1.le, WangWu.extendFrom_fwdMapInv_eq hg.hW hg.hW0 hg.rpos.le (hg.shift_mem_H hu)]

/-- The shifted continuation is injective on `[0, τ]`. -/
theorem injOn_shift : InjOn (loewnerTip (shiftDrive Wph r)) (Icc 0 τ) := by
  intro u hu v hv he
  have h := congrArg (extendFrom H (fwdMapInv Wph r)) he
  rw [hg.extendFrom_shift hu.1, hg.extendFrom_shift hv.1] at h
  have h' := hg.inj ⟨by linarith [hg.rpos, hu.1], by linarith [hu.2]⟩
    ⟨by linarith [hg.rpos, hv.1], by linarith [hv.2]⟩ h
  linarith

theorem continuous_shiftTip : ContinuousOn (loewnerTip (shiftDrive Wph r)) (Ici 0) := hg.shift_trace.2.1

/-- **R1's positive-scale representation** `c.1 = a (mapOut B ∘ R − x)` on `D`, from the exported clauses
(`Aux61Restart.exists_original_target_chart_scale`, with the own chart `F_r : ℍ → ℍ ∖ K_r`). -/
theorem scale : ∃ a x : ℝ, 0 < a ∧
    EqOn c.1 (fun z => (a : ℂ) * (ConformalImage.mapOut (stripTargetHull D) (stripRightRetarget z) - x)) D := by
  have hr := hg.rpos.le
  have hbij : SupercriticalConformalCovariance.IsConformalBijection c.1 D H := by
    rw [← hg.dom_eq]
    exact Sec7.Aux2728Pocket.isConformalBijection_fwd hg.conf
  exact Aux61Restart.exists_original_target_chart_scale (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hg.hW hr)
    (isHPHull_fwdHull hg.hW hr).2.2.2 (fun z hz => hz.1) hg.isOpen_D hg.simply hg.dom_sub
    (isConformalBijection_fwdMapInv hg.hW hg.hW0 hr) (hg.mem_H r ⟨hg.rpos, by linarith [hg.τpos]⟩)
    (hg.trace.tendsto_fwdMapInv_tip hg.hW hg.hW0 hr) hg.collar hg.target hbij hg.current hg.infty

end Basic

end IsGluedSlit

end InteractingSLE.Sec5.Aux61Conf2
