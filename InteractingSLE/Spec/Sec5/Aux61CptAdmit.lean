/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptCover
import InteractingSLE.Spec.Sec5.Aux61NjSeed
import InteractingSLE.Spec.Sec5.Aux61GWindow20All

/-!
# The family's admission: the actual record passes both tests

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a). `cptAdmission`: almost surely on the window event, for the source's
retained time and every nonzero chart landing `y`, the actual retained record passes a rational landing test around
`y` (GLUEINST's `Aux61GWindow20.ae_landing_admission_separated`, already for the test with its eastern conjunct) and a
rational seed test whose radius is below the landing interval's distance from `0`; every thin window admitting the
record is then installed by an index of `cptChoices S`.

The seed part: `exists_seed_conditions` is NOJUMP's `Aux61Nj.ae_seed_admission` argument at one sample, for a given
conformal chart with the source chart geometry (the restart-facts hypothesis of NOJUMP's statement is used there only
for these two facts, which GLUEINST's time source supplies directly); `seedRecords_of_conditions` converts the four
sample conditions to the record test through the transfer equalities (own driver on `[0, r]`, `retObs_eq_of_good`,
`recPhys_eq_of_mem_H`, `histState_stopRec_killed`). The own force-position gaps are strict by the deterministic route:
all own marks sit at the seed, so the positions are the base images, signed because `F̄_r(0)` is the tip in `ℍ`.

R48/R77 respected; nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu GlueCond Cond44Ref Aux61GWord Aux61Cmp LawUnique Aux61Restart MartChar.RealFlow
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61R1C Aux61Asm2 Aux61SlitWX Aux61GWindow17
open Aux61GR1F Aux61GInst Aux61FibData Aux61GWindow19 Aux61WndCap Aux61ULoc Restart.FlowStopIdentG
universe u

variable {S : SourceSetting.{u}}

/-- **The four seed conditions at one sample** (NOJUMP's `ae_seed_admission` argument, for a given conformal chart
with the source chart geometry and the restart tip off the counterflow hull). -/
theorem exists_seed_conditions {p : S.Ω × HistorySpace 0 0} (hgood : p.2 ∈ CfRegQ.goodCfSet)
    (hp : Aux50Hit.IsGoodPath S.own.W S.own.VL S.own.VR S.life p.1 ∧
      IsLoewnerTrace (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal) ∧
      IsProperArc (fun t : ℝ => S.path p.1 t.toNNReal))
    (hfor : ∀ t : ℝ≥0,
      (∀ i, S.own.VL i t p.1 - S.own.W t p.1 =
        Restart.FlowStopIdentCMI.geomL (fun v : ℝ => S.own.W v.toNNReal p.1) t (S.xL i)) ∧
      (∀ i, S.own.VR i t p.1 - S.own.W t p.1 =
        Restart.FlowStopIdentCMI.geomR (fun v : ℝ => S.own.W v.toNNReal p.1) t (S.xR i)))
    {c : Chart} (hc : c.IsConformal) {r₀ : ℝ≥0}
    (hgeo : SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) r₀ c)
    (htip : S.path p.1 r₀ ∉ cfHullQ (rationalTime S.s) p.2) :
    ∃ δ δ' ε d : ℚ, 0 < δ' ∧ δ' < δ ∧ 0 < ε ∧ 0 < d ∧
      (∀ z ∈ H ∩ ball (0 : ℂ) (δ : ℝ), (d : ℝ) ≤ infDist
        (fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) r₀ z) (H \ cfHullQ (rationalTime S.s) p.2)ᶜ) ∧
      (∀ ζ ∈ H ∩ ball (0 : ℂ) (ε : ℝ),
        ‖fwdMap (fun t : ℝ => S.own.W t.toNNReal p.1) r₀ (c.2.1 ζ)‖ ≤ (δ' : ℝ)) ∧
      (∀ j, S.own.VL j r₀ p.1 - S.own.W r₀ p.1 ≤ -(δ : ℝ)) ∧
      (∀ j, (δ : ℝ) ≤ S.own.VR j r₀ p.1 - S.own.W r₀ p.1) := by
  set W : ℝ → ℝ := fun t => S.own.W t.toNNReal p.1 with hWdef
  set η : ℝ → ℂ := fun t => S.path p.1 t.toNNReal with hηdef
  set r : ℝ := ((r₀ : ℝ≥0) : ℝ) with hrdef
  have hW : Continuous W := hp.1.continuous_rpath
  have hW0 : W 0 = 0 := by simpa only [hWdef, Real.toNNReal_zero] using hp.1.2.1
  have hr : 0 < r := NNReal.coe_pos.2 hgeo.start_pos
  have hηr : η r = S.path p.1 r₀ := by simp only [hηdef, hrdef, Real.toNNReal_coe]
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
  have hVL : ∀ j, S.own.VL j r₀ p.1 - S.own.W r₀ p.1 = gL := by
    intro j
    have h := (hfor r₀).1 j
    simp only [Restart.FlowStopIdentCMI.geomL, hxL j, neg_zero] at h
    simp only [h, hgLdef, hWdef, hrdef, Real.toNNReal_coe]
  have hVR : ∀ j, S.own.VR j r₀ p.1 - S.own.W r₀ p.1 = gR := by
    intro j
    have h := (hfor r₀).2 j
    simp only [Restart.FlowStopIdentCMI.geomR, hxR j] at h
    simp only [h, hgRdef, hWdef, hrdef, Real.toNNReal_coe]
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
  have hcolt : MapsTo (fwdMapInv W r) (ball 0 δt ∩ H) c.dom :=
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
  have hsub : (c.dom : Set ℂ) ⊆ H \ fwdHull W r := by
    rw [hhull]
    intro z hz
    exact ⟨(hgeo.retained hz).1, fun hP' => (hgeo.retained hz).2
      (Or.inr (image_mono Ioc_subset_Icc_self hP'))⟩
  have hBh := isHPHull_stripTargetHull c.dom.isOpen hgeo.simply hc.dom_subset hgeo.target
  obtain ⟨a, ξ, ha, hscale⟩ := hgeo.scale hW hW0 hp.2.1 hp.2.2 hc
  have hcur : Tendsto (fun z => c.1 (fwdMapInv W r z)) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 ((0 : ℝ) : ℂ)) := by
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
    have : (δ : ℝ) < gR := lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_right _ _))
    linarith

/-- **The record passes the seed test** when the four seed conditions hold at its sample, with the record chart. -/
theorem mem_seedRecords_of_conditions (t : GoodTime S) {p : S.Ω × HistorySpace 0 0}
    (hgood : p.2 ∈ CfRegQ.goodCfSet) (hp1 : Aux50Hit.IsGoodPath S.own.W S.own.VL S.own.VR S.life p.1)
    {y : SourceRecord S.nL S.nR} (hy1 : y.1 = stopRec (rationalTime S.s) p.2)
    (hy2 : y.2 = stopRec (rationalTime t.1) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1))
    (hcert : y ∈ certifiedRecords S t) {δ δ' ε d : ℚ} (hδ' : 0 < δ') (hδδ : δ' < δ) (hε : 0 < ε) (hd : 0 < d)
    (h1 : ∀ z ∈ H ∩ ball (0 : ℂ) (δ : ℝ), (d : ℝ) ≤ infDist
      (fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime t.1) z)
      (H \ cfHullQ (rationalTime S.s) p.2)ᶜ)
    (h2 : ∀ ζ ∈ H ∩ ball (0 : ℂ) (ε : ℝ), ‖fwdMap (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime t.1)
      ((recordChart S t y).2.1 ζ)‖ ≤ (δ' : ℝ))
    (h3 : ∀ j, S.own.VL j (rationalTime t.1) p.1 - S.own.W (rationalTime t.1) p.1 ≤ -(δ : ℝ))
    (h4 : ∀ j, (δ : ℝ) ≤ S.own.VR j (rationalTime t.1) p.1 - S.own.W (rationalTime t.1) p.1) :
    y ∈ seedRecords S t ⟨(δ, δ', ε, d), hδ', hδδ, hε, hd⟩ := by
  set W : ℝ → ℝ := fun s => S.own.W s.toNNReal p.1 with hWdef
  set r : ℝ := ((rationalTime t.1 : ℝ≥0) : ℝ) with hrdef
  have hζ := hp1.1
  have hcst : Continuous fun s => (S.own.W s p.1, fun j => S.own.VL j s p.1, fun j => S.own.VR j s p.1) := by
    have c1 : Continuous fun s => S.own.W s p.1 := by
      have := hp1.2.2.1; rw [hζ] at this; simpa [continuousOn_univ] using this
    have c2 : ∀ j, Continuous fun s => S.own.VL j s p.1 := fun j => by
      have := hp1.2.2.2.1 j; rw [hζ] at this; simpa [continuousOn_univ] using this
    have c3 : ∀ j, Continuous fun s => S.own.VR j s p.1 := fun j => by
      have := hp1.2.2.2.2 j; rw [hζ] at this; simpa [continuousOn_univ] using this
    exact c1.prodMk ((continuous_pi c2).prodMk (continuous_pi c3))
  have hW : Continuous W := hp1.continuous_rpath
  have hW0 : W 0 = 0 := by simpa only [hWdef, Real.toNNReal_zero] using hp1.2.1
  have hdrvEq : EqOn (ownDrv S t y) W (Icc 0 r) := by
    intro x hx
    have hxr : x.toNNReal ≤ rationalTime t.1 := Real.toNNReal_le_iff_le_coe.2 hx.2
    simp only [ownDrv, Ito.rpath, recU, hWdef]
    rw [hy2, frozenDrv_stopRec_killed hζ hcst, min_eq_left hxr]
  obtain ⟨hdc, hd0, -⟩ := ownDrv_facts S t hcert
  have hdc' : Continuous (ownDrv S t y) := hdc.comp continuous_real_toNNReal
  have hd0' : ownDrv S t y 0 = 0 := by simpa [ownDrv, Ito.rpath] using hd0
  have hr0 : (0 : ℝ) ≤ r := NNReal.coe_nonneg _
  have hinv : EqOn (fwdMapInv (ownDrv S t y) r) (fwdMapInv W r) H :=
    Sec7.fwdMapInv_eqOn_of_eqOn hdc' hd0' hW hW0 hr0 hdrvEq
  have hobs : Aux61Marks.retObs (rationalTime S.s) y = (H \ cfHullQ (rationalTime S.s) p.2)ᶜ :=
    Aux61Nj.retObs_eq_of_good S hgood y hy1 hcert.2.1
  have hstate := histState_stopRec_killed hζ hcst (le_refl (rationalTime t.1))
  have hratH : ∀ a b : ℚ, 0 < b → ratPt a b ∈ H := fun a b hb => by
    change (0 : ℝ) < (ratPt a b).im
    simp only [ratPt]
    exact_mod_cast hb
  refine ⟨hcert, ?_, ?_, ?_, ?_⟩
  · intro a b hb hab
    rw [hinv (hratH a b hb), hobs]
    exact h1 _ ⟨hratH a b hb, hab⟩
  · intro a b hb hab
    rw [recPhys_eq_of_mem_H S t hcert (hratH a b hb), Ito.fwdMap_congr_of_eqOn hdrvEq]
    exact h2 _ ⟨hratH a b hb, hab⟩
  · intro j
    simp only [ownVLrec]
    rw [hy2, hstate]
    exact h3 j
  · intro j
    simp only [ownVRrec]
    rw [hy2, hstate]
    exact h4 j

/-- **The family's admission at the source's retained time.** -/
theorem cptAdmission_at_time (S : SourceSetting.{u}) (t : GoodTime S) (ht : t.1 = S.t) :
    ∀ᵐ p ∂S.μ, S.windowEvent p → ∀ y : ℝ, y ≠ 0 →
      Tendsto (timePath S t p) (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)) →
      ∃ O : Set ℝ, IsOpen O ∧ 0 ∈ O ∧ y ∈ O ∧
        ∀ J : AllowedWindow,
          timeRecord S t p ∈ windowRecords S t J →
          (∀ z ∈ closure (outerBuffer J.1.1), z.im = 0 → z.re ∈ O) →
          ∃ i : (cptChoices S).Idx, (cptChoices S).q i.1 = t.1 ∧
            (cptChoices S).record i.1 p ∈ (cptChoices S).toR1Restart.selected i ∧
            bufferedWindow J.1.1 ⊆ ((cptChoices S).data i.1).V ∧
            y ∈ Ioo ((cptChoices S).left i.1) ((cptChoices S).right i.1) := by
  let C := baseChoices S t.1
  let i := baseIndex S t
  filter_upwards [Aux61SlitWZ.ae_window_good_record S, Aux61SlitWAB.ae_record_mem_certifiedSelection C i,
    canonicalFamily_geometry C i, S.physical_path, S.physical_forces, Aux61Asm2.ae_mem_goodCfSet S,
    Aux61Nj.ae_windowEvent_tip_notMem S, Aux61GWindow20.ae_landing_admission_separated S]
    with p hreg hcert hgeo hp hfor hgood htip hland hwin y hy0 hend
  have he : p ∈ (timeSource S t).event (timeIndex S t) := by
    change actRec S t.1 p ∈ univ ∩ goodSet (rationalTime S.s) t.1
    exact ⟨mem_univ _, by simpa only [ht] using hreg hwin⟩
  have hrec : timeRecord S t p ∈ certifiedRecords S t := hcert he
  have G : SourceChartGeometry (fun v : ℝ => S.own.W v.toNNReal p.1) (fun v => S.path p.1 v.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (rationalTime t.1) (recordChart S t (timeRecord S t p)) := hgeo he
  have hc : (recordChart S t (timeRecord S t p)).IsConformal := (recordChart_spec S t).conformal _
  have htip' : S.path p.1 (rationalTime t.1) ∉ cfHullQ (rationalTime S.s) p.2 := by
    rw [ht]; exact (htip hwin).2
  obtain ⟨δ, δ', ε, d, hδ', hδδ, hε, hd, c1, c2, c3, c4⟩ := exists_seed_conditions hgood hp hfor hc G htip'
  obtain ⟨εL, hεL, L, hyL, hLrec, hsep⟩ := hland hwin t ht y hy0 hend
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨ε'', hε''pos, hε''lt⟩ := exists_rat_btwn (lt_min hεR hεL)
  have hε''Q : (0 : ℚ) < ε'' := by exact_mod_cast hε''pos
  have hPrec : timeRecord S t p ∈ seedRecords S t ⟨(δ, δ', ε'', d), hδ', hδδ, hε''Q, hd⟩ :=
    mem_seedRecords_of_conditions t hgood hp.1 rfl rfl hrec hδ' hδδ hε''Q hd c1
      (fun ζ hζ => c2 ζ ⟨hζ.1, ball_subset_ball ((le_of_lt hε''lt).trans (min_le_left _ _)) hζ.2⟩) c3 c4
  set P : SeedParam := ⟨(δ, δ', ε'', d), hδ', hδδ, hε''Q, hd⟩ with hPdef
  have hrad : seedRad P = ε'' := rfl
  refine ⟨cptReal L P, isOpen_cptReal L P,
    Or.inl ⟨neg_neg_of_pos (seedRad_pos P), seedRad_pos P⟩, Or.inr (mem_landInterval_iff.2 hyL),
    fun J hJ hreal => ?_⟩
  have hside : seedRad P ≤ landLo L ∨ landHi L ≤ -seedRad P := by
    have hlt : seedRad P < εL := by rw [hrad]; exact lt_of_lt_of_le hε''lt (min_le_right _ _)
    rcases hsep with h | h
    · exact Or.inl (le_of_lt (lt_of_lt_of_le hlt h))
    · exact Or.inr (h.trans (neg_le_neg (le_of_lt hlt)))
  let k : CptIndex S := ⟨(t, J, L, P), hside, hreal⟩
  have hgoodk : ((cptChoices S).good k).Nonempty := ⟨timeRecord S t p, hrec.1.2⟩
  refine ⟨⟨k, hgoodk⟩, rfl, ⟨⟨hJ, hLrec, hPrec⟩, hrec.1.2⟩, Subset.rfl, ?_⟩
  change y ∈ Ioo (cptWord S k).left (cptWord S k).right
  rw [cptWord_left, cptWord_right]
  exact mem_landInterval_iff.2 hyL

/-- **`CptAdmission` PROVED**: the family's initial-record admission, with no input. -/
theorem cptAdmission (S : SourceSetting.{u}) : CptAdmission S := by
  have hall : ∀ᵐ p ∂S.μ, ∀ t : GoodTime S, t.1 = S.t → S.windowEvent p → ∀ y : ℝ, y ≠ 0 →
      Tendsto (timePath S t p) (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)) →
      ∃ O : Set ℝ, IsOpen O ∧ 0 ∈ O ∧ y ∈ O ∧
        ∀ J : AllowedWindow,
          timeRecord S t p ∈ windowRecords S t J →
          (∀ z ∈ closure (outerBuffer J.1.1), z.im = 0 → z.re ∈ O) →
          ∃ i : (cptChoices S).Idx, (cptChoices S).q i.1 = t.1 ∧
            (cptChoices S).record i.1 p ∈ (cptChoices S).toR1Restart.selected i ∧
            bufferedWindow J.1.1 ⊆ ((cptChoices S).data i.1).V ∧
            y ∈ Ioo ((cptChoices S).left i.1) ((cptChoices S).right i.1) := by
    refine ae_all_iff.2 fun t => ?_
    by_cases ht : t.1 = S.t
    · filter_upwards [cptAdmission_at_time S t ht] with p hp _ hw y hy0 hy
      exact hp hw y hy0 hy
    · exact ae_of_all _ fun _ h => (ht h).elim
  filter_upwards [hall] with p hp hw t ht y hy0 hy
  exact hp t ht hw y hy0 hy

/-- **The fibre leaf of Theorems 1.2–1.3, PROVED** (at every universe). -/
theorem cptFibreCover :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_cptAdmission cptAdmission

end InteractingSLE.Sec5.Aux61Cpt
