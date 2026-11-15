/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61NjGerm
import InteractingSLE.Spec.Sec5.Aux61CptAccess
import InteractingSLE.Spec.Sec5.Aux61CptLandAccess
import InteractingSLE.Spec.ZhanGT4.RealTip
import InteractingSLE.Spec.Sec7.Prop74ProofWord
import InteractingSLE.Spec.Sec5.Aux61CptLanding
import QuantumZipper.Proofs.Thm14.FromThm13

/-!
# Seed admission: the actual record passes a rational seed test

Packet PROVE-AUX61-NOJUMP (seed part of R103's per-outcome family). PROVE-AUX61-CAPTURE's seed selection
(`Aux61Cpt.seedTest`, `seedRecords`, `ae_ownCollarPointNP_of_seedRecords`) makes every point of the seed
interval an own collar point (`Aux61Nj.OwnCollarPointNP`) on records passing a rational seed test
`(δ, δ', ε, d)`. This file proves the **admission**: almost surely on the selected records of any restart
family with the source chart geometry, if the restart tip `η(r)` is off the counterflow hull, the actual
sample satisfies the four seed conditions for some rationals, on whole half-discs:

1. `d ≤ dist(F_r(z), (ℍ ∖ R(K_s))ᶜ)` on `ℍ ∩ B(0, δ)`. `F̄_r(0) = η(r)` (`ZhanGT4.extendFrom_zero_eq`) has
   positive distance from the closed obstacle, and `F_r` is continuous up to `0`.
2. `‖f_r(c⁻¹ ζ)‖ ≤ δ'` on `ℍ ∩ B(0, ε)`. The transition `f_r ∘ c⁻¹ → 0` at the seed
   (`Aux61Cmp.tendsto_transition_collar` at `b = 0`, from the geometry's `collar` and `current`, with
   `F̄_r ≠ 1` near `0` by continuity).
3. `ownVL ≤ −δ` and `ownVR ≥ δ`. The source's own force marks are all at the seed (`S.physical_forces`,
   `Sec7.flowLineX{L,R}_prop74Data`), so every own force position is the base image `g_r(0∓) − W_r`, which is
   strictly signed because `F̄_r(0) = η(r) ∈ ℍ` (`WangWu.neg_rightImg_sub_lt_of_extendFrom_mem_H`,
   `lt_rightImg_sub_of_extendFrom_mem_H`).

`ae_windowEvent_tip_notMem`: on the window event the restart tip at the window time `t` is off the
counterflow hull (the excursion's no-contact clause; the window's driver and the retained driver give the same
hull). `ae_seed_admission_window` combines the two for an index restarted at `t`.

`retObs_eq_of_good`: the record obstacle `retObs s y` (read from the record) is the sample's
`(ℍ ∖ R(K_s))ᶜ` on the good counterflow histories with a state certificate. With it, condition 1 becomes the
record test.

The conditions are stated at the sample level because CAPTURE's record-level test lives in uncommitted
modules. The conversion back to `seedTest` uses the transfer equalities of
`Aux61Cpt.ae_ownCollarPointNP_of_seedRecords`'s proof (own driver on `[0, r]`, `recPhys_eq_of_mem_H`,
`histState_stopRec_killed`) and `retObs_eq_of_good`.

Deterministic up to the landed a.s. facts of the restart family. R48: no Theorem 1.2/1.3 input; R77: no
post-contact kernel. Nothing here replaces a source statement.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Nj
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61GChoice16 Aux61Restart Aux61FibData
open Aux61ChLoc LawUnique GlueCond Aux61R1C Aux61Asm2 Aux61GInst Aux61GR1F
open WangWu Cond44Ref Aux61GWord Aux61Cmp Aux61TwoS MartChar.RealFlow
universe u

/-- **The record obstacle is the sample's obstacle** on the good counterflow histories, for a record whose
counterflow part is the stopped history and carries a state certificate. -/
theorem retObs_eq_of_good (S : SourceSetting.{u}) {p : S.Ω × HistorySpace 0 0}
    (hgood : p.2 ∈ CfRegQ.goodCfSet) (y : SourceRecord S.nL S.nR)
    (hy : y.1 = Aux61ULoc.stopRec (rationalTime S.s) p.2) (hS : Aux61R1C.StateCert (rationalTime S.s) y.1) :
    Aux61Marks.retObs (rationalTime S.s) y = (H \ cfHullQ (rationalTime S.s) p.2)ᶜ := by
  have h1 : historyHull (rationalTime S.s) (fun p : HistorySpace 0 0 × HistorySpace S.nL S.nR => p.1) y =
      cfHullQ (rationalTime S.s) p.2 := by
    change negInv '' fwdHull (CrossCond.Word49.cfDrv0 (rationalTime S.s) y.1) (rationalTime S.s) = _
    rw [Aux61SlitWAB.cfDrv0_eq_frozenDrv hS, Aux61Cpt.cfHullQ_eq_cfW S hgood,
      Aux61Cpt.cfW_eq_recDrv hgood y hy]
    rfl
  simp only [Aux61Marks.retObs, h1]

variable {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}

/-- **Seed admission** (sample form): almost surely on the selected records, if the restart tip is off the
counterflow hull, there are rationals `0 < δ' < δ`, `0 < ε`, `0 < d` such that (1) the own collar
`F_r(ℍ ∩ B(0, δ))` keeps distance `≥ d` from the obstacle `(ℍ ∖ R(K_s))ᶜ`, (2) the chart half-disc
`ℍ ∩ B(0, ε)` is carried by `f_r ∘ c⁻¹` into `B̄(0, δ')`, and (3) the own force positions lie outside
`(−δ, δ)`. -/
theorem ae_seed_admission
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) :
    ∀ᵐ p ∂S.μ, (S.marksData F).Z i p ∈ (S.marksData F).B i →
      S.path p.1 (F.start i) ∉ cfHullQ (rationalTime S.s) p.2 →
      ∃ δ δ' ε d : ℚ, 0 < δ' ∧ δ' < δ ∧ 0 < ε ∧ 0 < d ∧
        (∀ z ∈ H ∩ ball (0 : ℂ) (δ : ℝ), (d : ℝ) ≤ infDist
          (fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i) z)
          (H \ cfHullQ (rationalTime S.s) p.2)ᶜ) ∧
        (∀ ζ ∈ H ∩ ball (0 : ℂ) (ε : ℝ), ‖fwdMap (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i)
          (((S.marksData F).chart i p).2.1 ζ)‖ ≤ (δ' : ℝ)) ∧
        (∀ j, ownVL S F i p j ≤ -(δ : ℝ)) ∧ (∀ j, (δ : ℝ) ≤ ownVR S F i p j) := by
  filter_upwards [hgeometry, S.physical_path, S.physical_forces, hR.physical_stop i,
    Aux61Asm2.ae_mem_goodCfSet S] with p hg hp hfor hstop hgood hB htip
  have hsel : sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := hB
  have he : p ∈ F.event i := (hstop hsel).1
  have hc : ((S.marksData F).chart i p).IsConformal := (hR.spec i).conf p he
  have hgeo := hg he
  set W : ℝ → ℝ := fun t => S.own.W t.toNNReal p.1 with hWdef
  set η : ℝ → ℂ := fun t => S.path p.1 t.toNNReal with hηdef
  set r : ℝ := ((F.start i : ℝ≥0) : ℝ) with hrdef
  have hW : Continuous W := hp.1.continuous_rpath
  have hW0 : W 0 = 0 := by simpa only [hWdef, Real.toNNReal_zero] using hp.1.2.1
  have hr : 0 < r := NNReal.coe_pos.2 hgeo.start_pos
  have hηr : η r = S.path p.1 (F.start i) := by simp only [hηdef, hrdef, Real.toNNReal_coe]
  have htipH : η r ∈ H := hp.2.2.mem_H r hr
  have hF0 : extendFrom H (fwdMapInv W r) 0 = η r := ZhanGT4.extendFrom_zero_eq hp.2.1 hW hW0 hr.le
  have hlim0 : Tendsto (fwdMapInv W r) (𝓝[H] (0 : ℂ)) (𝓝 (η r)) := by
    have h := (hp.2.1.hasBdryLimits hW hW0 hr.le).tendsto (show (0 : ℂ) ∈ Hbar by simp [Hbar])
    rwa [hF0] at h
  -- (1) the own collar off the obstacle
  set O : Set ℂ := (H \ cfHullQ (rationalTime S.s) p.2)ᶜ with hO
  have hOc : IsClosed O := by
    rw [hO, isClosed_compl_iff, Aux61Cpt.cfHullQ_eq_cfW S hgood]
    exact GlueImg.isOpen_H_diff_negInv_fwdHull (Sec4.continuous_rpath_regPath _) (NNReal.coe_nonneg _)
  have hOne : O.Nonempty := ⟨0, fun h => by have : (0 : ℝ) < (0 : ℂ).im := h.1; simp at this⟩
  have hηO : η r ∉ O := by
    rw [hO, mem_compl_iff, not_not]
    exact ⟨htipH, by rw [hηr]; exact htip⟩
  have hD : 0 < infDist (η r) O := (hOc.notMem_iff_infDist_pos hOne).1 hηO
  set D := infDist (η r) O with hDdef
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.mem_nhdsWithin_iff.1
    (hlim0 (Metric.ball_mem_nhds (η r) (half_pos hD)))
  have htest1 : ∀ z ∈ ball (0 : ℂ) δ₁ ∩ H, D / 2 ≤ infDist (fwdMapInv W r z) O := by
    intro z hz
    have h1 : dist (fwdMapInv W r z) (η r) < D / 2 := hδ₁sub hz
    have h2 := infDist_le_infDist_add_dist (x := η r) (y := fwdMapInv W r z) (s := O)
    rw [dist_comm] at h2
    linarith
  -- (3) the own force positions
  have hxL : ∀ j, S.xL j = 0 := fun j => Sec7.flowLineXL_prop74Data S.a S.b j
  have hxR : ∀ j, S.xR j = 0 := fun j => Sec7.flowLineXR_prop74Data S.a S.b j
  have hFH : extendFrom H (fwdMapInv W r) ((0 : ℝ) : ℂ) ∈ H := by
    rw [Complex.ofReal_zero, hF0]; exact htipH
  have hgL := neg_rightImg_sub_lt_of_extendFrom_mem_H hp.2.1 hW hW0 hr.le hFH
  have hgR := lt_rightImg_sub_of_extendFrom_mem_H hp.2.1 hW hW0 hr.le hFH
  set gL : ℝ := -rightImg (fun s => -W s) 0 r - W r with hgLdef
  set gR : ℝ := rightImg W 0 r - W r with hgRdef
  have hWr : W r = S.own.W (F.start i) p.1 := by simp only [hWdef, hrdef, Real.toNNReal_coe]
  have hVL : ∀ j, ownVL S F i p j = gL := by
    intro j
    have h := (hfor (F.start i)).1 j
    simp only [Restart.FlowStopIdentCMI.geomL, hxL j, neg_zero] at h
    simp only [ownVL, h, hgLdef, hWdef, hrdef, Real.toNNReal_coe]
  have hVR : ∀ j, ownVR S F i p j = gR := by
    intro j
    have h := (hfor (F.start i)).2 j
    simp only [Restart.FlowStopIdentCMI.geomR, hxR j] at h
    simp only [ownVR, h, hgRdef, hWdef, hrdef, Real.toNNReal_coe]
  -- (2) the transition at the seed
  obtain ⟨δc, hδc, hcol⟩ := hgeo.collar
  have hFc : ContinuousWithinAt (extendFrom H (fwdMapInv W r)) Hbar 0 :=
    (hp.2.1.hasBdryLimits hW hW0 hr.le).continuousOn 0 (by simp [Hbar])
  have h1ne : (1 : ℂ) ≠ η r := fun h => by
    have : (0 : ℝ) < (1 : ℂ).im := by rw [h]; exact htipH
    simp at this
  obtain ⟨δo, hδo, hδosub⟩ := Metric.mem_nhdsWithin_iff.1
    (hFc (Metric.ball_mem_nhds _ (show 0 < dist (1 : ℂ) (η r) from dist_pos.2 h1ne)))
  set δt : ℝ := min δc δo with hδt
  have hδt0 : 0 < δt := lt_min hδc hδo
  have hcolt : MapsTo (fwdMapInv W r) (ball 0 δt ∩ H) ((S.marksData F).chart i p).dom :=
    fun z hz => hcol ⟨ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
  have hone : ∀ x : ℝ, |x| < δt → extendFrom H (fwdMapInv W r) x ≠ 1 := by
    intro x hx h1
    have hxB : ((x : ℝ) : ℂ) ∈ ball (0 : ℂ) δo := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_lt_of_le hx (min_le_right _ _)
    have hmem := hδosub ⟨hxB, show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp⟩
    rw [hF0, mem_preimage, h1, mem_ball] at hmem
    exact lt_irrefl _ hmem
  have hhull : fwdHull W r = η '' Ioc 0 r := WangWu.fwdHull_eq_image_Ioc hp.2.1 hp.2.2 hr.le
  have hsub : (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ fwdHull W r := by
    rw [hhull]
    intro z hz
    exact ⟨(hgeo.retained hz).1, fun hP' => (hgeo.retained hz).2
      (Or.inr (image_mono Ioc_subset_Icc_self hP'))⟩
  have hBh := isHPHull_stripTargetHull ((S.marksData F).chart i p).dom.isOpen
    hgeo.simply hc.dom_subset hgeo.target
  obtain ⟨a, ξ, ha, hscale⟩ := hgeo.scale hW hW0 hp.2.1 hp.2.2 hc
  have hcur : Tendsto (fun z => ((S.marksData F).chart i p).1 (fwdMapInv W r z))
      (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 ((0 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_zero]; exact hgeo.current
  have hT := tendsto_transition_collar hW hW0 hp.2.1 hr hc hsub hBh hscale hδt0 hcolt hone
    (show |(0 : ℝ)| < δt by rw [abs_zero]; exact hδt0) hcur
  rw [Complex.ofReal_zero] at hT
  -- rational parameters
  set δ₀ : ℝ := min δ₁ (min (-gL) gR) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδ₁ (lt_min (by linarith) (by linarith))
  obtain ⟨δ, hδpos, hδlt⟩ := exists_rat_btwn hδ₀pos
  obtain ⟨δ', hδ'pos, hδ'lt⟩ := exists_rat_btwn (show (0 : ℝ) < δ by exact_mod_cast hδpos)
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhdsWithin_iff.1
    ((hT.mono_right nhdsWithin_le_nhds) (Metric.ball_mem_nhds (0 : ℂ) hδ'pos))
  obtain ⟨ε, hεpos, hεlt⟩ := exists_rat_btwn hε₁
  obtain ⟨d, hdpos, hdlt⟩ := exists_rat_btwn (half_pos hD)
  refine ⟨δ, δ', ε, d, by exact_mod_cast hδ'pos, by exact_mod_cast hδ'lt, by exact_mod_cast hεpos,
    by exact_mod_cast hdpos, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hz1 : z ∈ ball (0 : ℂ) δ₁ ∩ H :=
      ⟨ball_subset_ball ((le_of_lt hδlt).trans (min_le_left _ _)) hz.2, hz.1⟩
    exact (le_of_lt hdlt).trans (htest1 z hz1)
  · intro ζ hζ
    have hζ1 : ζ ∈ ball (0 : ℂ) ε₁ ∩ H := ⟨ball_subset_ball hεlt.le hζ.2, hζ.1⟩
    have h := hε₁sub hζ1
    rw [mem_preimage, mem_ball, dist_zero_right] at h
    exact h.le
  · intro j
    rw [hVL j]
    have : (δ : ℝ) < -gL := lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  · intro j
    rw [hVR j]
    exact (lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_right _ _))).le

/-- **The restart tip is off the counterflow hull on the window event**: almost surely on the window event,
the flow line at the window's restart time `t` lies in `ℍ ∖ R(K_s)` (the excursion clause "no contact on
`[t − δ, t]`", with the window's driver and the retained driver agreeing on `[0, s]`). -/
theorem ae_windowEvent_tip_notMem (S : SourceSetting.{u}) :
    ∀ᵐ p ∂S.μ, S.windowEvent p →
      S.path p.1 (rationalTime S.t) ∈ H \ cfHullQ (rationalTime S.s) p.2 := by
  filter_upwards [Aux61Asm2.ae_mem_goodCfSet S] with p hgood hwin
  obtain ⟨hW, u₀, hE, -⟩ := hwin
  obtain ⟨-, hno, -, -, -⟩ := hE
  have hδ := hW.δ_pos
  have htmem : (S.t : ℝ) ∈ Icc ((S.t : ℝ) - (S.windowCode.2.2.2 : ℝ)) (S.t : ℝ) :=
    ⟨by linarith, le_rfl⟩
  have h := hno _ htmem
  obtain ⟨-, hw, -, -⟩ := CfRegQ.reg_of_mem_goodCfSet hgood
  have hcW : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hrs : ((rationalTime S.s : ℝ≥0) : ℝ) = (S.s : ℝ) := Aux61R1C.coe_rationalTime S.s_pos.le
  have hEq := Aux61Cpt.eqOn_cfW_cfDrv S hgood
  have hhull : fwdHull (cfW S p) (rationalTime S.s) = fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s) :=
    QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn hcW hw hs hEq
  rw [Aux61Cpt.cfHullQ_eq_cfW S hgood, hhull, hrs]
  exact h

/-- **Seed admission on the window event**: for an index restarted at the window's time `t`, almost surely
on the window event and the selected records the four seed conditions hold for some rationals. -/
theorem ae_seed_admission_window
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
      (μ := S.μ) S.κ) (i : F.ι) (hstart : F.start i = rationalTime S.t)
    (hgeometry : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) :
    ∀ᵐ p ∂S.μ, S.windowEvent p → (S.marksData F).Z i p ∈ (S.marksData F).B i →
      ∃ δ δ' ε d : ℚ, 0 < δ' ∧ δ' < δ ∧ 0 < ε ∧ 0 < d ∧
        (∀ z ∈ H ∩ ball (0 : ℂ) (δ : ℝ), (d : ℝ) ≤ infDist
          (fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i) z)
          (H \ cfHullQ (rationalTime S.s) p.2)ᶜ) ∧
        (∀ ζ ∈ H ∩ ball (0 : ℂ) (ε : ℝ), ‖fwdMap (fun t : ℝ => S.own.W t.toNNReal p.1) (F.start i)
          (((S.marksData F).chart i p).2.1 ζ)‖ ≤ (δ' : ℝ)) ∧
        (∀ j, ownVL S F i p j ≤ -(δ : ℝ)) ∧ (∀ j, (δ : ℝ) ≤ ownVR S F i p j) := by
  filter_upwards [ae_seed_admission hR i hgeometry, ae_windowEvent_tip_notMem S] with p hadm htip hwin hB
  refine hadm hB ?_
  rw [hstart]
  exact (htip hwin).2

end InteractingSLE.Sec5.Aux61Nj
