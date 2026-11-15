/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptSeed
import InteractingSLE.Spec.Sec5.Aux61CptSeedTest
import InteractingSLE.Spec.Sec5.Aux61CptLandAccess

/-!
# The seed test gives pinch-free own collar points on the whole seed interval

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a). `ae_ownCollarPointNP_of_seedRecords`: for restart choices whose
normalized chart is the canonical record chart, if the selected records of an index pass the seed test with parameter
`P = (δ, δ', ε, d)` and the installed word is `−λ` left and `λ` right of `0` on `(−ε, ε)`, then almost surely on the
selected records every chart point `b` with `|b| < ε` is an own collar point in NOJUMP's pinch-free form
(`Aux61Nj.OwnCollarPointNP`). The record tests are transferred to the sample (own driver, retained obstacle, force
positions) and `exists_seedAccessNP` supplies the collar access; the own height is `∓λ` because the own force positions
lie outside the collar (`forceBoundaryData_of_gap`).

R48/R77 respected; nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu GlueCond Cond44Ref Aux61GWord Aux61Cmp LawUnique Aux61Restart Aux61Marks
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61R1C Aux61Asm2 Aux61SlitWX Aux61GWindow17 Aux61ULoc
open Restart.FlowStopIdentG
universe u

/-- **The own word on a force-free collar**: with every left force position `≤ −δ` and every right one `≥ δ`, the
boundary data at `|t| < δ` is `∓λ`. -/
theorem forceBoundaryData_of_gap {κ : ℝ} {F : Impl.ForceWord}
    {vL : Fin F.nL → ℝ} {vR : Fin F.nR → ℝ} {δ t : ℝ} (hL : ∀ j, vL j ≤ -δ) (hR : ∀ j, δ ≤ vR j)
    (ht : |t| < δ) :
    Impl.forceBoundaryData κ F vL vR t = if t < 0 then -sleLambda κ else sleLambda κ := by
  rw [abs_lt] at ht
  unfold Impl.forceBoundaryData sleLambda
  split_ifs with h
  · have h0 : ∑ i ∈ Finset.univ.filter (fun i => t < vL i), F.ρL i = 0 :=
      Finset.sum_eq_zero fun j hj => absurd (Finset.mem_filter.1 hj).2 (not_lt.2 ((hL j).trans ht.1.le))
    rw [h0, add_zero, mul_one]
  · have h0 : ∑ i ∈ Finset.univ.filter (fun i => vR i ≤ t), F.ρR i = 0 :=
      Finset.sum_eq_zero fun j hj => absurd (Finset.mem_filter.1 hj).2 (not_le.2 (ht.2.trans_le (hR j)))
    rw [h0, add_zero, mul_one]

variable {S : SourceSetting.{u}} (C : RestartChoices S) (R : ReaderFacts C.toR1Restart)

include R in
/-- **Own collar points on the seed interval from the seed test.** -/
theorem ae_ownCollarPointNP_of_seedRecords (hTip : OwnTipForwardLimit S)
    (V : WindowData C.toR1Restart C.hasChart) (hExit : PhysicalExit C.toR1Restart C.hasChart)
    (i : C.Idx) (P : SeedParam)
    (hP : ∀ y ∈ (normSource C.toR1Restart C.hasChart).selected i, y ∈ seedRecords S (idxTime C i) P)
    (hword : ∀ b : ℝ, |b| < P.1.2.2.1 → b ≠ 0 →
      b ∉ ((normSource C.toR1Restart C.hasChart).data i).JR ∧
      ((normSource C.toR1Restart C.hasChart).data i).bR b = if b < 0 then -sleLambda S.κ else sleLambda S.κ) :
    ∀ᵐ p ∂S.μ, (S.marksData (normSource C.toR1Restart C.hasChart)).Z i p ∈
        (S.marksData (normSource C.toR1Restart C.hasChart)).B i →
      ∀ b : ℝ, |b| < P.1.2.2.1 → Aux61Nj.OwnCollarPointNP S (normSource C.toR1Restart C.hasChart) i p b := by
  set F := normSource C.toR1Restart C.hasChart with hFdef
  have hR := Aux61GCaptureNext.normalized_cut_restart C.toR1Restart C.hasChart R hTip V hExit
  filter_upwards [R.ae_domain C.hasChart i, R.ae_geometry C.hasChart i, S.physical_path,
    hR.physical_stop i, Aux61Asm2.ae_mem_goodCfSet S] with p hdom hgeo hp hstop hgood hB b hb
  set y := sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p with hydef
  have hsel : y ∈ F.selected i := hB
  have he : p ∈ F.event i := (hstop hsel).1
  have hyP := hP y hsel
  set t := idxTime C i
  set W : ℝ → ℝ := fun s => S.own.W s.toNNReal p.1 with hWdef
  set η : ℝ → ℂ := fun s => S.path p.1 s.toNNReal with hηdef
  set r : ℝ := ((F.start i : ℝ≥0) : ℝ) with hrdef
  have hgeo' := hgeo he.1
  have hW : Continuous W := hp.1.continuous_rpath
  have hW0 : W 0 = 0 := by simpa only [hWdef, Real.toNNReal_zero] using hp.1.2.1
  have hr : 0 < r := NNReal.coe_pos.2 hgeo'.start_pos
  have hq0 : (0 : ℚ) ≤ C.q i.1 := by exact_mod_cast (goodTime_pos S t).le
  have hstart : r = (C.q i.1 : ℝ) := coe_rationalTime hq0
  have hchart : (S.marksData F).chart i p = recordChart S t y := by
    change Aux61SlitWX.chart C.toR1Restart C.hasChart i y = _
    rw [Aux61GWindow18.normalized_chart_eq_recordChart C i]
  have hc : ((S.marksData F).chart i p).IsConformal := (hR.spec i).conf p he
  have hhull : fwdHull W r = η '' Ioc 0 r := WangWu.fwdHull_eq_image_Ioc hp.2.1 hp.2.2 hr.le
  have hsub : (((S.marksData F).chart i p).dom : Set ℂ) ⊆ H \ fwdHull W r := by
    rw [hhull]
    intro z hz
    exact ⟨(hgeo'.retained hz).1, fun hP' => (hgeo'.retained hz).2 (Or.inr (image_mono Ioc_subset_Icc_self hP'))⟩
  have hBh := isHPHull_stripTargetHull ((S.marksData F).chart i p).dom.isOpen
    hgeo'.simply hc.dom_subset hgeo'.target
  obtain ⟨a, ξ, ha, hscale⟩ := hgeo'.scale hW hW0 hp.2.1 hp.2.2 hc
  -- the record's own driver is the sample's on `[0, r]`
  have hζ := hp.1.1
  have hcst : Continuous fun s => (S.own.W s p.1, fun j => S.own.VL j s p.1, fun j => S.own.VR j s p.1) := by
    have h1 : Continuous fun s => S.own.W s p.1 := by
      have := hp.1.2.2.1; rw [hζ] at this; simpa [continuousOn_univ] using this
    have h2 : ∀ j, Continuous fun s => S.own.VL j s p.1 := fun j => by
      have := hp.1.2.2.2.1 j; rw [hζ] at this; simpa [continuousOn_univ] using this
    have h3 : ∀ j, Continuous fun s => S.own.VR j s p.1 := fun j => by
      have := hp.1.2.2.2.2 j; rw [hζ] at this; simpa [continuousOn_univ] using this
    exact h1.prodMk ((continuous_pi h2).prodMk (continuous_pi h3))
  have hy2 : y.2 = stopRec (F.start i) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) := rfl
  have hFs : F.start i = rationalTime (C.q i.1) := rfl
  have hdrvEq : EqOn (ownDrv S t y) W (Icc 0 r) := by
    intro x hx
    have hxr : x.toNNReal ≤ F.start i := Real.toNNReal_le_iff_le_coe.2 hx.2
    simp only [ownDrv, Ito.rpath, recU, hWdef]
    rw [hy2, ← hFs, frozenDrv_stopRec_killed hζ hcst, min_eq_left hxr]
  obtain ⟨hdc, hd0, -⟩ := ownDrv_facts S t hyP.1
  have hdc' : Continuous (ownDrv S t y) := hdc.comp continuous_real_toNNReal
  have hd0' : ownDrv S t y 0 = 0 := by simpa [ownDrv, Ito.rpath] using hd0
  have hrt : ((rationalTime t.1 : ℝ≥0) : ℝ) = r := rfl
  have hinv : EqOn (fwdMapInv (ownDrv S t y) r) (fwdMapInv W r) H :=
    Sec7.fwdMapInv_eqOn_of_eqOn hdc' hd0' hW hW0 hr.le hdrvEq
  have hfwd : ∀ z, fwdMap (ownDrv S t y) r z = fwdMap W r z := fun z =>
    Ito.fwdMap_congr_of_eqOn hdrvEq
  -- the retained obstacle contains the counterflow hull
  have hobs : cfHullQ (rationalTime S.s) p.2 ⊆ retObs (rationalTime S.s) y := by
    intro z hz hz'
    have hK := cfHullQ_eq_cfW S hgood
    rw [hK, cfW_eq_recDrv hgood y rfl] at hz
    apply hz'.2
    change z ∈ negInv '' fwdHull (CrossCond.Word49.cfDrv0 (rationalTime S.s) y.1) (rationalTime S.s)
    rw [Aux61SlitWAB.cfDrv0_eq_frozenDrv hyP.1.2.1]
    exact hz
  have hd : (0 : ℝ) < P.1.2.2.2 := by exact_mod_cast P.2.2.2.2
  have hδ : (0 : ℝ) < P.1.1 := by exact_mod_cast (P.2.1.trans P.2.2.1)
  have hδ' : (P.1.2.1 : ℝ) < P.1.1 := by exact_mod_cast P.2.2.1
  -- the collar distance on the whole half-disc
  have hU : IsOpen (H ∩ ball (0 : ℂ) (P.1.1 : ℝ)) := QuantumZipper.isOpen_H.inter isOpen_ball
  have hdist : ∀ z ∈ H ∩ ball (0 : ℂ) (P.1.1 : ℝ),
      (P.1.2.2.2 : ℝ) ≤ infDist (fwdMapInv W r z) (retObs (rationalTime S.s) y) := by
    have h := le_of_forall_ratPt (g := fun z => -infDist (fwdMapInv W r z) (retObs (rationalTime S.s) y))
      (M := -(P.1.2.2.2 : ℝ)) hU inter_subset_left ?_ ?_
    · intro z hz; have := h z hz; linarith
    · intro z hz
      exact ((continuous_infDist_pt _).continuousAt.comp_continuousWithinAt
        (((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hr.le).continuousOn z hz.1).mono
          inter_subset_left)).neg
    · intro a' b' hb' hab
      have h1 := hyP.2.1 a' b' hb' hab.2
      rw [hrt, hinv hab.1] at h1
      linarith
  have hK : ∀ z ∈ H ∩ ball (0 : ℂ) (P.1.1 : ℝ), fwdMapInv W r z ∉ cfHullQ (rationalTime S.s) p.2 := by
    intro z hz hK
    have h := hdist z hz
    rw [infDist_zero_of_mem (hobs hK)] at h
    linarith
  have hone : ∀ x : ℝ, |x| < P.1.1 → extendFrom H (fwdMapInv W r) x ≠ 1 := by
    intro x hx h1
    have hxB : ((x : ℝ) : ℂ) ∈ ball (0 : ℂ) (P.1.1 : ℝ) := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact hx
    have hbar : ((x : ℝ) : ℂ) ∈ Hbar := ofReal_mem_Hbar x
    have hlim := (hp.2.1.hasBdryLimits hW hW0 hr.le).tendsto hbar
    have := GlueImg.nhdsWithin_H_neBot x
    have hge : (P.1.2.2.2 : ℝ) ≤ infDist (extendFrom H (fwdMapInv W r) x) (retObs (rationalTime S.s) y) :=
      ge_of_tendsto ((continuous_infDist_pt _).tendsto _ |>.comp hlim)
        (by filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hxB)] with z hz using hdist z hz)
    have h1mem : (1 : ℂ) ∈ retObs (rationalTime S.s) y := fun h => by
      have : (0 : ℝ) < (1 : ℂ).im := h.1
      simp at this
    rw [h1, infDist_zero_of_mem h1mem] at hge
    linarith
  have hseed : ∀ ζ ∈ H ∩ ball (0 : ℂ) (P.1.2.2.1 : ℝ),
      ‖fwdMap W r (((S.marksData F).chart i p).2.1 ζ)‖ ≤ (P.1.2.1 : ℝ) := by
    have hU' : IsOpen (H ∩ ball (0 : ℂ) (P.1.2.2.1 : ℝ)) := QuantumZipper.isOpen_H.inter isOpen_ball
    refine le_of_forall_ratPt hU' inter_subset_left ?_ ?_
    · intro ζ hζ
      have hm := hsub (hc.inv_mem_dom hζ.1)
      have h1 : ContinuousWithinAt (fwdMap W r ∘ ((S.marksData F).chart i p).2.1)
          (H ∩ ball (0 : ℂ) (P.1.2.2.1 : ℝ)) ζ :=
        ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hr.le).differentiableAt
          ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hr.le).mem_nhds hm)).continuousAt.comp_continuousWithinAt
          ((hc.1.continuousOn ζ hζ.1).mono inter_subset_left)
      exact h1.norm
    · intro a' b' hb' hab
      have h1 := hyP.2.2.1 a' b' hb' hab.2
      rw [recPhys_eq_of_mem_H S t hyP.1 hab.1, hrt, hfwd, ← hchart] at h1
      exact h1
  obtain ⟨tt, htt, hpos, hneg, hzero, hacc⟩ := exists_seedAccessNP hW hW0 hp.2.1 hr hc hsub hBh hscale
    (hdom he.1).choose_spec hhull hp.2.2.zero hδ hδ' hK hone hgeo'.collar hgeo'.current hseed b hb
  refine ⟨tt, hacc, ?_⟩
  by_cases hb0 : b = 0
  · exact Or.inl hb0
  right
  obtain ⟨hbJ, hbR⟩ := hword b hb hb0
  have htt0 : tt ≠ 0 := fun h => by
    rcases lt_or_gt_of_ne hb0 with hlt | hgt
    · exact (hneg hlt).ne h
    · exact (hpos hgt).ne' h
  have httδ : |tt| < P.1.1 := lt_of_le_of_lt htt hδ'
  -- the own force positions at the restart, from the record
  have hstate := histState_stopRec_killed hζ hcst (le_refl (F.start i))
  have hVL : ∀ j, ownVL S F i p j ≤ -(P.1.1 : ℝ) := fun j => by
    have h := hyP.2.2.2.1 j
    simp only [ownVLrec] at h
    rw [show rationalTime t.1 = F.start i from rfl, hy2, hstate] at h
    exact h
  have hVR : ∀ j, (P.1.1 : ℝ) ≤ ownVR S F i p j := fun j => by
    have h := hyP.2.2.2.2 j
    simp only [ownVRrec] at h
    rw [show rationalTime t.1 = F.start i from rfl, hy2, hstate] at h
    exact h
  refine ⟨hbJ, ?_, ?_⟩
  · rintro (h0 | ⟨j, hj⟩ | ⟨j, hj⟩)
    · exact htt0 h0
    · rw [abs_lt] at httδ; have := hVL j; rw [hj] at this; linarith
    · rw [abs_lt] at httδ; have := hVR j; rw [hj] at this; linarith
  · have hk : ((normSource C.toR1Restart C.hasChart).data i).κ = S.κ := V.kappa i
    rw [forceBoundaryData_of_gap (F := Ito.weightWord S.ρL S.ρR) hVL hVR httδ, hbR, hk]
    rcases lt_or_gt_of_ne hb0 with hlt | hgt
    · rw [ite_eq_left hlt, ite_eq_left (hneg hlt)]
    · rw [ite_eq_right (not_lt.2 hgt.le), ite_eq_right (not_lt.2 (hpos hgt).le)]

end InteractingSLE.Sec5.Aux61Cpt
