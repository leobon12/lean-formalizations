/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootZ21Actual

/-!
# The observable clock on a full protected physical prefix

Packet PROVE-T14-GW2ROOT2. A later live record preserves every earlier
hull. Hence the actual clock's entire protected prefix, its continuity,
strict increase and attained levels are read from one retained record.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootZ21

open Exist Staged StagedLaw Restart Supp8.GB6

/-- Every hull before a strictly live recording cutoff is unchanged. -/
theorem fwdHull_record_of_le_of_live {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) {v : ℝ≥0} (hv : (v : ℝ≥0∞) < e.2)
    {t : ℝ≥0} (htv : t ≤ v) :
    QuantumZipper.fwdHull (rdrv (recOf (v : ℝ≥0∞) e)) t =
      QuantumZipper.fwdHull (Ito.rpath e.1) t := by
  have hg := isDrvGood_recOf_of_lt he hv
  have heq : EqOn (rdrv (recOf (v : ℝ≥0∞) e)) (Ito.rpath e.1) (Icc 0 (t : ℝ)) := by
    intro q hq
    apply rdrv_recOf_eq he hg
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
    simpa only [rtime_recOf_coe, min_eq_left hv.le, ENNReal.toNNReal_coe] using
      hq.2.trans (NNReal.coe_le_coe.mpr htv)
  obtain ⟨B, hvB, hBe⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hv
  have hcont : ContinuousOn (Ito.rpath e.1) (Icc 0 (B : ℝ)) :=
    he.1.comp continuous_real_toNNReal.continuousOn fun q hq =>
      (ENNReal.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hq.2)).trans_lt hBe
  exact LocalExt.fwdHull_congr_of_continuousOn (continuous_rdrv _).continuousOn
    hcont t.coe_nonneg (by exact_mod_cast (htv.trans_lt (ENNReal.coe_lt_coe.mp hvB))) heq

/-- Earlier forward capacity values use no information after their own
time, even when they are read from a later retained piece record. -/
theorem forwardCapacity_prefix_eq (s : ℝ≥0) (r : RecData)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) < e.2) {t : ℝ≥0} (htv : t ≤ v) :
    forwardCapacity s t (r, recOf (v : ℝ≥0∞) e) =
      forwardCapacity s t (r, recOf (t : ℝ≥0∞) e) := by
  unfold forwardCapacity forwardHull
  rw [fwdHull_record_of_le_of_live he hv htv,
    fwdHull_record_of_live he ((ENNReal.coe_le_coe.mpr htv).trans_lt hv)]

/-- The actual forward clock read from one retained record is normalized,
strictly increasing and continuous on the whole protected prefix. The
source traces supply every geometric and clock fact. -/
theorem forwardCapacity_regular_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ QuantumZipper.H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2) :
    let a := fun t => forwardCapacity s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    a 0 = 0 ∧ StrictMonoOn a (Icc 0 v) ∧ ContinuousOn a (Icc 0 v) := by
  let a := fun t => forwardCapacity s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let b := fun t : ℝ≥0 => relClock (Ito.rpath (regW s W ζ · ω)) s (Ito.rpath e.1) t
  have hab : EqOn a b (Icc 0 v) := by
    intro t ht
    rw [show a t = forwardCapacity s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) e) from
      forwardCapacity_prefix_eq s _ he (lt_min_iff.mp hv).2 ht.2]
    exact forwardCapacity_eq_relClock_before_contact W ζ ω hα hW hW0 hs hsH he hγ
      ((ENNReal.coe_le_coe.mpr ht.2).trans_lt hv)
  obtain ⟨B, _, _, hvB, _, _, _, _, hb0, hbm, hbc, _⟩ :=
    RootM17.exists_regW_relative_trace_before_contact W ζ ω hα hW hW0 hs hsH
      hγ he.1 he.2.1 hv
  have hsub : Icc 0 v ⊆ Icc 0 B := Icc_subset_Icc_right hvB.le
  change b 0 = 0 at hb0
  change StrictMonoOn b (Icc 0 B) at hbm
  change ContinuousOn b (Icc 0 B) at hbc
  refine ⟨(hab ⟨zero_le, zero_le⟩).trans hb0, ?_, ?_⟩
  · exact (hbm.mono hsub).congr hab.symm
  · exact (hbc.mono hsub).congr hab

/-- Every attained relative capacity level has exactly one physical
time on the protected prefix. In particular this applies to the unit
level in a scaled chart; continuity and strict increase are conclusions
of the original trace geometry, not assumptions on a clock. -/
theorem exists_unique_forwardCapacity_level_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ QuantumZipper.H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
    (u : ℝ≥0)
    (hu : (u : ℝ) ≤ forwardCapacity s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) :
    ∃! t : ℝ≥0, t ∈ Icc 0 v ∧
      forwardCapacity s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) = u := by
  obtain ⟨h0, hm, hc⟩ := forwardCapacity_regular_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv
  obtain ⟨t, ht, htu⟩ := GaugeE.exists_clock_eq hc h0 hu
  refine ⟨t, ⟨ht, htu⟩, ?_⟩
  rintro t' ⟨ht', htu'⟩
  exact hm.injOn ht' ht (htu'.trans htu.symm)

end InteractingSLE.Theorem14.GW2TipSystem.RootZ21
