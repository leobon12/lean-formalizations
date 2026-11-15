/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptLandTest

/-!
# The landing test gives component counterflow accesses on the whole landing interval

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a). For restart choices `C` whose normalized chart is GLUEINST's canonical
record chart, if the selected records of an index pass the landing test with parameter `L = (v₀, ε₀, M, d)`, then almost
surely on the selected records every real chart point `b` with `|b − v₀| < ε₀` is a component counterflow access point
(`CfAccessC`), up to the word clauses `b ≠ 0`, `b ∉ J` and the height identity (`CollarHeight`, the clause supplied by the
per-outcome height and branch selection). `ae_cfAccessC_of_landRecords`.

The sample is linked to its record: the source chart is the record chart (`normalized_chart_eq_recordChart`), the retained
counterflow driver is the record driver on good histories (`cfW_eq_recDrv`), and on the cut events the own prefix is the
record prefix (`prefix_eq_recPrefix`).

R48/R77 respected; nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu GlueCond Cond44Ref Aux61GWord Aux61Cmp LawUnique Aux61Restart
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61R1C Aux61Asm2 Aux61SlitWX Aux61GWindow17 Aux61ULoc
universe u

variable {S : SourceSetting.{u}}

/-- On a good counterflow history the retained regularized driver is the driver read from the record. -/
theorem cfW_eq_recDrv {p : S.Ω × HistorySpace 0 0} (hgood : p.2 ∈ CfRegQ.goodCfSet)
    (y : SourceRecord S.nL S.nR) (hy : y.1 = stopRec (rationalTime S.s) p.2) :
    cfW S p = recDrv S y := by
  funext r
  simp only [cfW, recDrv, Ito.rpath, hy, regPath_cfStop_of_mem_goodCfSet hgood]
  rw [Aux61SlitWAB.frozenDrv_stopRec_of_dyCert hgood.1.2]

variable (C : RestartChoices S) (R : ReaderFacts C.toR1Restart)

/-- The good time of an index of restart choices. -/
abbrev idxTime (i : C.Idx) : GoodTime S := ⟨C.q i.1, i.2⟩

include R in
/-- **Component counterflow accesses on the landing interval from the landing test.** -/
theorem ae_cfAccessC_of_landRecords (hTip : OwnTipForwardLimit S)
    (V : WindowData C.toR1Restart C.hasChart) (hExit : PhysicalExit C.toR1Restart C.hasChart)
    (i : C.Idx) (L : LandParam)
    (hL : ∀ y ∈ (normSource C.toR1Restart C.hasChart).selected i, y ∈ landRecords S (idxTime C i) L) :
    ∀ᵐ p ∂S.μ, (S.marksData (normSource C.toR1Restart C.hasChart)).Z i p ∈
        (S.marksData (normSource C.toR1Restart C.hasChart)).B i →
      ∀ b : ℝ, |b - L.1.1| < L.1.2.1 → b ≠ 0 →
        b ∉ ((normSource C.toR1Restart C.hasChart).data i).JR →
        CollarHeight S (normSource C.toR1Restart C.hasChart) i p
          (recPhys S (idxTime C i) (sourceRecord (normSource C.toR1Restart C.hasChart) (rationalTime S.s)
            S.own.W S.own.VL S.own.VR S.life i p) b) b →
        CfAccessC S (normSource C.toR1Restart C.hasChart) i p b := by
  set F := normSource C.toR1Restart C.hasChart with hFdef
  have hR := Aux61GCaptureNext.normalized_cut_restart C.toR1Restart C.hasChart R hTip V hExit
  filter_upwards [R.ae_domain C.hasChart i, S.physical_path, hR.physical_stop i,
    Aux61Asm2.ae_mem_goodCfSet S, ae_cfW_trace S] with p hdom hp hstop hgood hcfp hB b hb hb0 hbJ hheight
  set y := sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p with hydef
  have hsel : y ∈ F.selected i := hB
  have he : p ∈ F.event i := (hstop hsel).1
  have hyL := hL y hsel
  have hq0 : (0 : ℚ) ≤ C.q i.1 := by exact_mod_cast (goodTime_pos S (idxTime C i)).le
  have hstart : ((F.start i : ℝ≥0) : ℝ) = (C.q i.1 : ℝ) := coe_rationalTime hq0
  -- the source chart is the record chart
  have hchart : (S.marksData F).chart i p = recordChart S (idxTime C i) y := by
    change Aux61SlitWX.chart C.toR1Restart C.hasChart i y = _
    rw [Aux61GWindow18.normalized_chart_eq_recordChart C i]
  -- the retained driver is the record driver
  have hdrv : cfW S p = recDrv S y := cfW_eq_recDrv hgood y rfl
  -- on the cut event the own prefix is the record prefix
  have hpre : (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ) = recPrefix S (idxTime C i) y := by
    have hEq := stoppedTrace_eqOn_of_mem_cut S (source C.toR1Restart C.hasChart) he
    rw [recPrefix, ← hstart]
    refine (image_congr fun v hv => ?_).symm
    exact hEq hv
  have hc : ((S.marksData F).chart i p).IsConformal := (hR.spec i).conf p he
  have hηc : ContinuousOn (fun t : ℝ => S.path p.1 t.toNNReal) (Icc 0 (F.start i : ℝ)) :=
    hp.2.2.cont.mono fun v hv => hv.1
  have hd : (0 : ℝ) < L.1.2.2.2 := by exact_mod_cast L.2.2
  refine cfAccessC_of_chartBall' hgood hcfp hc (hdom he.1) hηc hd (v₀ := (L.1.1 : ℝ)) (ε₀ := (L.1.2.1 : ℝ))
    (M := (L.1.2.2.1 : ℝ)) ?_ (fun r : ℝ => recPhys S (idxTime C i) y r) ?_
    ⟨(L.1.2.2.2 : ℝ), hd, fun ζ hζ => by
      rw [hchart, hdrv]; exact landTest_re S (idxTime C i) L hyL ζ hζ⟩ ?_ hb0 hbJ hheight
  · intro ζ hζ
    rw [hchart, hdrv]
    exact landTest_bound S (idxTime C i) L hyL ζ hζ
  · intro r hr
    have hr' : |r - L.1.1| < L.1.2.1 := by
      rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hr
      exact hr
    obtain ⟨hlim, hIm, hdist⟩ := landTest_phys S (idxTime C i) L hyL hr'
    refine ⟨by rw [hchart]; exact hlim, lt_of_lt_of_le hd hIm, fun u hu => ?_⟩
    rw [hpre] at hu
    exact hdist u hu
  · rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hb

end InteractingSLE.Sec5.Aux61Cpt
