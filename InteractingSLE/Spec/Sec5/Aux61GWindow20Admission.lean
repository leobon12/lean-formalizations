/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow20Bounds
import InteractingSLE.Spec.Sec5.Aux61GWindow20Transition
import InteractingSLE.Spec.Sec5.Aux61GWindow20Landing
import InteractingSLE.Spec.Sec5.Aux61GWindow19Thin

/-! # Almost sure admission of the actual chart landing

The actual record passes CAPTURE's rational landing test on an interval
containing the actual chart landing. No access, height, branch, or
admission hypothesis is imposed.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H Hbar fwdHull)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow20
open WangWu Aux61SlitW Aux61R1C Aux61Asm2 Aux61GWindow17 Aux61GWindow19
open Aux61GInst Aux61FibData Aux61Restart Aux61Cpt Aux61Cmp LawUnique GlueCond
open Restart.FlowStopIdentG
universe u

/-- At the original source time, every actual real chart landing is
inside a rational landing interval whose Borel test accepts the actual
retained record. -/
theorem ae_landing_admission_at_time (S : SourceSetting.{u}) (t : GoodTime S) (ht : t.1 = S.t) :
    ∀ᵐ p ∂S.μ, S.windowEvent p → ∀ y : ℝ,
      Tendsto (timePath S t p) (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)) →
      ∃ L : LandParam, |y - L.1.1| < L.1.2.1 ∧ timeRecord S t p ∈ landRecords S t L := by
  let C := baseChoices S t.1
  let i := baseIndex S t
  have R := Aux61SlitWZ.readers C (fun _ => MeasurableSet.univ)
  filter_upwards [Aux61SlitWZ.ae_window_good_record S,
    Aux61SlitWAB.ae_record_mem_certifiedSelection C i,
    canonicalFamily_restartPoint C i, canonicalFamily_geometry C i, canonicalFamily_ae_domain C i,
    r1_contact_fields_of_tipOff C.toR1Restart C.hasChart R.tipOff i,
    ae_recordPath S, S.physical_path, Aux61Asm2.ae_mem_goodCfSet S, ae_cfW_trace S,
    ae_retained_window_landing S]
    with p hreg hcert hB hgeo hdom hcontact hversion hp hgood hcf hlanding hwin y hend
  have he : p ∈ (timeSource S t).event (timeIndex S t) := by
    change actRec S t.1 p ∈ univ ∩ goodSet (rationalTime S.s) t.1
    exact ⟨mem_univ _, by simpa only [ht] using hreg hwin⟩
  have hrec : timeRecord S t p ∈ certifiedRecords S t := hcert he
  let c := recordChart S t (timeRecord S t p)
  let r := rationalTime t.1
  let ρ := recordPath S r p
  let T := timeContact S t p
  let η : ℝ → ℂ := fun v => S.path p.1 v.toNNReal
  have B : Aux61SlitWX.RestartPoint c ρ T := hB he
  have G : SourceChartGeometry (fun v : ℝ => S.own.W v.toNNReal p.1) η
      (cfHullQ (rationalTime S.s) p.2) r c := hgeo he
  obtain ⟨b, hbdom⟩ := hdom he
  change (c.dom : Set ℂ) = restartComponent (cfHullQ (rationalTime S.s) p.2) η r b at hbdom
  have hK := cfHullQ_eq_cfW S hgood
  rw [hK] at hbdom
  have hr : (r : ℝ) = (S.t : ℝ) := by
    change (rationalTime t.1 : ℝ) = _
    rw [coe_rationalTime (by exact_mod_cast (goodTime_pos S t).le), ht]
  have hρ : ∀ v, ρ v = η ((r : ℝ) + (v : ℝ)) := by
    intro v
    simpa only [η, ← NNReal.coe_add, Real.toNNReal_coe] using (hversion r).1 v
  obtain ⟨e, x, hte, hx, hin, hland, hphys⟩ := hlanding hwin
  have hre : (r : ℝ) < e := hr ▸ hte
  have he0 : 0 < e := (by exact_mod_cast S.t_pos : (0 : ℝ) < S.t).trans hte
  have heH : η e ∈ H := hp.2.2.mem_H e he0
  obtain ⟨hw0, γ, hγ⟩ := hcf
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have heK : η e ∈ negInv '' fwdHull (cfW S p) (rationalTime S.s) := by
    rcases cfBdry_mem_hull_or_real hw hw0 hγ hs x with h | h
    · rwa [hphys] at h
    · have hpos : 0 < (η e).im := heH
      rw [hphys] at h
      exact (lt_irrefl (0 : ℝ) (h ▸ hpos)).elim
  have hT : T = ((e - r).toNNReal : ℝ≥0∞) := by
    have hct := (hcontact he).1
    change T = hitTime (recordPath S r) (fun p => (H \ cfHullQ (rationalTime S.s) p.2)ᶜ) p at hct
    rw [hct]
    change hitTime (fun _ : Unit => ρ)
      (fun _ => (H \ cfHullQ (rationalTime S.s) p.2)ᶜ) () = _
    rw [hK]
    have hstart : ρ 0 ∈ H \ cfHullQ (rationalTime S.s) p.2 := (hcontact he).2.2
    rw [hK] at hstart
    exact hitTime_shift_eq hre hρ hstart
      (by rw [hr]; exact hin) (fun h => h.2 heK)
  have hTpos : 0 < T := (hcontact he).2.1
  have hTfin : T < ⊤ := hT ▸ ENNReal.coe_lt_top
  have hTclock : (r : ℝ) + (T.toNNReal : ℝ) = e := by
    rw [hT, ENNReal.toNNReal_coe, Real.coe_toNNReal _ (sub_pos.2 hre).le]
    ring
  have hTNNpos : 0 < T.toNNReal := ENNReal.toNNReal_pos hTpos.ne' hTfin.ne
  have : (𝓝[<] T.toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hTNNpos⟩
  have hbefore : ∀ᶠ v : ℝ≥0 in 𝓝[<] T.toNNReal,
      0 < v ∧ (v : ℝ≥0∞) < T := by
    filter_upwards [Ioo_mem_nhdsLT hTNNpos] with v hv
    exact ⟨hv.1, (ENNReal.coe_toNNReal hTfin.ne) ▸ ENNReal.coe_lt_coe.2 hv.2⟩
  have hinside : ∀ᶠ v : ℝ≥0 in 𝓝[<] T.toNNReal, ρ v ∈ c.dom :=
    hbefore.mono fun v hv => B.inside v hv.1 hv.2
  have hsub : (c.dom : Set ℂ) ⊆ H \ negInv '' fwdHull (cfW S p) (rationalTime S.s) := by
    intro z hz
    have h := G.retained hz
    rw [hK] at h
    exact ⟨h.1, fun hzK => h.2 (Or.inl hzK)⟩
  have hcfLim : Tendsto (fun v : ℝ≥0 => revChart (cfW S p) (rationalTime S.s) (ρ v))
      (𝓝[<] T.toNNReal) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hinside.mono fun v hv => revChart_mem_H hw hs (hsub hv)⟩
    have hshift := tendsto_add_coe_nhdsLT r T.toNNReal
    rw [hTclock] at hshift
    exact (hland.comp hshift).congr fun v => by rw [hρ]; rfl
  have hunit : Tendsto (inPath (univ : Set Unit) (fun _ => c) (fun _ => ρ) (fun _ => T) ())
      (𝓝[<] T.toNNReal) (𝓝 (y : ℂ)) := by
    change Tendsto (inPath (univ : Set Unit)
      (fun _ => sourceChart (timeSource S t) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
      (fun _ => (timeSource S t).path i p) (fun _ => (timeSource S t).contact i p) ()) _ _
    rwa [Aux61SlitWAA.inPath_unit_eq he]
  have hchartLim : Tendsto (fun v => c.1 (ρ v)) (𝓝[<] T.toNNReal) (𝓝 (y : ℂ)) :=
    hunit.congr' (hbefore.mono fun v hv => B.unitSpec.inPath_eq_fwd (mem_univ ()) hv.1 hv.2)
  have hclosed : IsClosed (η '' Icc 0 (r : ℝ)) :=
    (isCompact_Icc.image_of_continuousOn (hp.2.2.cont.mono Icc_subset_Ici_self)).isClosed
  have hpre : η e ∉ η '' Icc 0 (r : ℝ) := by
    rintro ⟨v, hv, hve⟩
    have h := hp.2.2.inj hv.1 he0.le hve
    linarith only [hv.2, hre, h]
  have hone : η e ≠ 1 := by
    intro heq
    have hpos : 0 < (η e).im := heH
    rw [heq, Complex.one_im] at hpos
    exact lt_irrefl _ hpos
  have hBh := isHPHull_stripTargetHull c.dom.isOpen G.simply B.conformal.dom_subset G.target
  have hW0 : (fun v : ℝ => S.own.W v.toNNReal p.1) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hp.1.2.1
  obtain ⟨a, ξ, -, hscale⟩ := G.scale hp.1.continuous_rpath hW0 hp.2.1 hp.2.2 B.conformal
  have htrans := tendsto_transition_of_common_access hw hw0 hγ hs B.conformal hsub hBh hscale
    hbdom hclosed hx.ne' (hphys.symm ▸ heH) (hphys.symm ▸ hpre) (hphys.symm ▸ hone)
    hinside hcfLim hchartLim
  have hFy : boundedInverse c (y : ℂ) = cayley (η e) := by
    have h := Aux61SlitWAA.boundedInverse_eq_at_endpoint B.unitSpec (mem_univ ()) hTpos hTfin
      (recordChart_extension S t hrec).2 hunit
    rw [hρ, hTclock] at h
    exact h
  have hpole : boundedInverse c (y : ℂ) ≠ 1 := by
    rw [hFy]
    exact cayley_ne_one_of_Hbar (QuantumZipper.H_subset_Hbar heH)
  have hphysy : recPhys S t (timeRecord S t p) (y : ℂ) = η e := by
    rw [recPhys, hFy, cayleyInv_cayley_of_mem_Hbar (QuantumZipper.H_subset_Hbar heH)]
  have hprefix : recPrefix S t (timeRecord S t p) = η '' Icc 0 (r : ℝ) := by
    have hq : (t.1 : ℝ) = (r : ℝ) := (coe_rationalTime (by exact_mod_cast (goodTime_pos S t).le)).symm
    rw [recPrefix, hq]
    apply image_congr
    intro v hv
    change histTrace 0 (Aux61ULoc.stopRec r (killedHistory S.own.W S.own.VL S.own.VR S.life p.1))
      v.toNNReal = η v
    rw [Aux61Marks.histTrace_stopRec_of_le (Real.toNNReal_le_iff_le_coe.2 hv.2)]
    simpa only [recordPath, zero_add] using (hversion 0).1 v.toNNReal
  have hclear : 0 < infDist (recPhys S t (timeRecord S t p) (y : ℂ))
      (recPrefix S t (timeRecord S t p)) := by
    rw [hphysy, hprefix]
    exact (hclosed.notMem_iff_infDist_pos ⟨η 0, ⟨0, ⟨le_rfl, r.coe_nonneg⟩, rfl⟩⟩).1 hpre
  apply exists_landRecords_of_transition S t hrec hx hpole (hphysy.symm ▸ heH) hclear
  refine (htrans.mono_right nhdsWithin_le_nhds).congr'
    (eventually_nhdsWithin_of_forall fun z hz => ?_)
  dsimp only
  rw [cfW_eq_recDrv hgood (timeRecord S t p) rfl, recPhys_eq_of_mem_H S t hrec hz]

end InteractingSLE.Sec5.Aux61GWindow20
