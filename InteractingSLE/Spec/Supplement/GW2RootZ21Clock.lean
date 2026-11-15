/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootZ21Read
import InteractingSLE.Spec.Supplement.GW2RootM17Trace
import InteractingSLE.Spec.Supplement.GB6GaugeEClock

/-!
# The forward record reader is the actual intrinsic capacity clock

Packet PROVE-T14-GW2ROOT2. Original generating traces and live cutoffs
prove the domain restriction and the proper relative hull. The grid
reader therefore returns the literal intrinsic relative clock.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootZ21

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB

/-- A strictly live stopped record preserves the endpoint hull, even
when its original regular driver has only a finite lifetime. -/
theorem fwdHull_record_of_live {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < e.2) :
    QuantumZipper.fwdHull (rdrv (recOf (t : ℝ≥0∞) e)) t =
      QuantumZipper.fwdHull (Ito.rpath e.1) t := by
  have hg := isDrvGood_recOf_of_lt he ht
  have heq : EqOn (rdrv (recOf (t : ℝ≥0∞) e)) (Ito.rpath e.1) (Icc 0 (t : ℝ)) := by
    intro q hq
    apply rdrv_recOf_eq he hg
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
    simpa only [rtime_recOf_coe, min_eq_left ht.le, ENNReal.toNNReal_coe] using hq.2
  obtain ⟨B, htB, hBe⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ht
  have hcont : ContinuousOn (Ito.rpath e.1) (Icc 0 (B : ℝ)) :=
    he.1.comp continuous_real_toNNReal.continuousOn fun q hq =>
      (ENNReal.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hq.2)).trans_lt hBe
  exact LocalExt.fwdHull_congr_of_continuousOn (continuous_rdrv _).continuousOn
    hcont t.coe_nonneg (by exact_mod_cast htB) heq

/-- The total Borel forward capacity reader returns the intrinsic clock
before first contact, from the two original finite generating traces.
No relative trace, domain, hull or capacity equality is assumed. -/
theorem forwardCapacity_eq_relClock_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2) :
    forwardCapacity s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) e) =
      relClock (Ito.rpath (regW s W ζ · ω)) s (Ito.rpath e.1) t := by
  let U := Ito.rpath (regW s W ζ · ω)
  let r := cfRec s W ζ ω
  have hm : relMap (rdrv r) s = relMap U s := by
    apply relMap_eq_of_eqOn s.coe_nonneg
    intro q hq
    exact (GaugeE.record_prefix_eq s hW0 hW hs hq).trans
      (cfE_fst_of_lt s hW0 hW
        ((ENNReal.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hq.2)).trans_lt hs)).symm
  have hUK : QuantumZipper.fwdHull (rdrv r) s = QuantumZipper.fwdHull U s :=
    (GaugeE.record_hull_eq s hW0 hW hs).trans
      (RootG15.regW_fwdHull_eq W ζ ω hW hW0 hs).symm
  have hpiece := fwdHull_record_of_live he (lt_min_iff.mp ht).2
  have hH : QuantumZipper.fwdHull (Ito.rpath e.1) t ⊆ H := by
    rw [← hpiece]
    exact (isHPHull_fwdHull (continuous_rdrv _) t.coe_nonneg).1
  have hD : QuantumZipper.fwdHull (Ito.rpath e.1) t ⊆ relDomain (rdrv r) s := by
    intro z hz
    apply (mem_relDomain_iff _ _ _).mpr
    refine ⟨hH hz, ?_⟩
    rw [hUK]
    exact RootG15.inv_notMem_regW_fwdHull_before_contact W ζ ω hα hW hW0 hs
      hγ he.1 he.2.1 t ht z hz
  have hforward : forwardHull s t (r, recOf (t : ℝ≥0∞) e) =
      relMap U s '' QuantumZipper.fwdHull (Ito.rpath e.1) t := by
    unfold forwardHull
    rw [hpiece, inter_eq_left.mpr hD, hm]
  obtain ⟨B, V, Γ, htB, _, hV, _, _, ha0, hmono, _, hK⟩ :=
    RootM17.exists_regW_relative_trace_before_contact W ζ ω hα hW hW0 hs hsH
      hγ he.1 he.2.1 ht
  change relClock U s (Ito.rpath e.1) 0 = 0 at ha0
  change StrictMonoOn (fun t : ℝ≥0 => relClock U s (Ito.rpath e.1) t) (Icc 0 B) at hmono
  change ∀ t ∈ Icc 0 B, QuantumZipper.fwdHull (Ito.rpath V)
    (relClock U s (Ito.rpath e.1) t) =
      relMap U s '' QuantumZipper.fwdHull (Ito.rpath e.1) t at hK
  have ha : 0 ≤ relClock U s (Ito.rpath e.1) t := by
    have hh := hmono.monotoneOn (show (0 : ℝ≥0) ∈ Icc 0 B from ⟨le_rfl, zero_le⟩)
      (show t ∈ Icc 0 B from ⟨zero_le, htB.le⟩) (zero_le : (0 : ℝ≥0) ≤ t)
    simpa only [NNReal.coe_zero, ha0] using hh
  have hHull : IsHPHull (relMap U s '' QuantumZipper.fwdHull (Ito.rpath e.1) t) := by
    rw [← hK t ⟨zero_le, htB.le⟩]
    exact isHPHull_fwdHull (hV.comp continuous_real_toNNReal) ha
  change (WholeField.hcapHit (forwardHull s t (r, recOf (t : ℝ≥0∞) e))).toReal / 2 = _
  rw [hforward, WholeField.IsHPHull.hcapHit_eq hHull]
  let A : HPHull := ⟨relMap U s '' QuantumZipper.fwdHull (Ito.rpath e.1) t, hHull⟩
  change (ENNReal.ofReal (HPHull.hcap A)).toReal / 2 =
    ConformalImage.hcapSet (relMap U s '' QuantumZipper.fwdHull (Ito.rpath e.1) t) / 2
  rw [ENNReal.toReal_ofReal (HPHull.hcap_nonneg A), ConformalImage.hcapSet_eq hHull]

end InteractingSLE.Theorem14.GW2TipSystem.RootZ21
