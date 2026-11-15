/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR4Driver

/-!
# The actual physical driver is recovered from a GW2 relative buffer

The two original generating traces supply the relative chain, its clock,
inverse hulls and capacity. The total Borel driver reader therefore returns
the original physical driver at every available time. No inverse or capacity
identity is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR4

open Supp8.GB6 Exist.StagedLaw GW2TipSystem GW2JDetR3

/-- Every available physical driver prefix is a Borel function of the retained
counterflow record and any later live relative record. All reconstruction
identities are proved from the original source traces. -/
theorem exists_actual_physicalDriverRead {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hT : 0 < T) :
    let r := cfRec s W ζ ω
    let S := min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
    let a : ℝ≥0 → ℝ := fun t => relClock (rdrv r) s (Ito.rpath w) t
    let L := ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < S), ((a t).toNNReal : ℝ≥0∞)
    ∃ V : ℝ≥0 → ℝ, V 0 = 0 ∧ a 0 = 0 ∧
      StrictMonoOn a {t | (t : ℝ≥0∞) < S} ∧
      ContinuousOn a {t | (t : ℝ≥0∞) < S} ∧
      ContinuousOn V {q | (q : ℝ≥0∞) < L} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
        0 ≤ a t ∧ ((a t).toNNReal : ℝ≥0∞) < L ∧
        ∀ b : ℝ≥0, (a t).toNNReal < b → (b : ℝ≥0∞) < L →
          let p := (r, cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ())
          inverseHull s (a t).toNNReal p = fwdHull (Ito.rpath w) t ∧
            physicalCapacity s (a t).toNNReal p = t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
        ∀ b : ℝ≥0, (a t).toNNReal < b → (b : ℝ≥0∞) < L →
          let p := (r, cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ())
          (∀ u ≤ t, physicalHullRead s u p = fwdHull (Ito.rpath w) u) ∧
          (∀ u ≤ t, physicalDriverRead s u p = w u) := by
  dsimp only
  obtain ⟨V, hV0, ha0, hm, hc, hVc, hread⟩ :=
    exists_inverse_capacity_chain W ζ ω hα hW hW0 hs hsH hγ hw hw0 hT
  let r := cfRec s W ζ ω
  let S := min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
  let a : ℝ≥0 → ℝ := fun t => relClock (rdrv r) s (Ito.rpath w) t
  let L := ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < S), ((a t).toNNReal : ℝ≥0∞)
  change a 0 = 0 at ha0
  change StrictMonoOn a {t | (t : ℝ≥0∞) < S} at hm
  change ContinuousOn a {t | (t : ℝ≥0∞) < S} at hc
  change ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
    0 ≤ a t ∧ ((a t).toNNReal : ℝ≥0∞) < L ∧
    ∀ b : ℝ≥0, (a t).toNNReal < b → (b : ℝ≥0∞) < L →
      let p := (r, cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ())
      inverseHull s (a t).toNNReal p = fwdHull (Ito.rpath w) t ∧
        physicalCapacity s (a t).toNNReal p = t at hread
  refine ⟨V, hV0, ha0, hm, hc, hVc, hread, ?_⟩
  intro t ht b htb hb
  let p := (r, cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ())
  have hcut : ∀ u ≤ t, capacityCut s u p = ((a u).toNNReal : ℝ≥0∞) := by
    intro u hut
    have hu : (u : ℝ≥0∞) < S := (ENNReal.coe_le_coe.mpr hut).trans_lt ht
    have hu0 := (hread u hu).1
    have hub : (a u).toNNReal < b :=
      (Real.toNNReal_le_toNNReal (hm.monotoneOn hu ht hut)).trans_lt htb
    apply capacityCut_eq_of_local_inverse s u p hub
    intro q hqb
    have hqL : (q : ℝ≥0∞) < L := (ENNReal.coe_le_coe.mpr hqb.le).trans_lt hb
    obtain ⟨v, ⟨hv, hav⟩, _⟩ := existsUnique_time_of_lt_clockSup ha0 hm hc hqL
    have hcap := ((hread v hv).2.2 b
      (by simpa only [hav, Real.toNNReal_coe] using hqb) hb).2
    change physicalCapacity s (a v).toNNReal p = v at hcap
    rw [hav, Real.toNNReal_coe] at hcap
    rw [hcap]
    constructor
    · intro huv
      have h := hm hu hv (NNReal.coe_lt_coe.mp huv)
      rw [hav] at h
      apply NNReal.coe_lt_coe.mp
      rwa [Real.coe_toNNReal _ hu0]
    · intro hq
      have h := NNReal.coe_lt_coe.mpr hq
      rw [Real.coe_toNNReal _ hu0, ← hav] at h
      exact NNReal.coe_lt_coe.mpr ((hm.lt_iff_lt hu hv).mp h)
  have hHull : ∀ u ≤ t, physicalHullRead s u p = fwdHull (Ito.rpath w) u := by
    intro u hut
    have hu : (u : ℝ≥0∞) < S := (ENNReal.coe_le_coe.mpr hut).trans_lt ht
    unfold physicalHullRead
    rw [hcut u hut, ENNReal.toNNReal_coe]
    exact ((hread u hu).2.2 b
      ((Real.toNNReal_le_toNNReal (hm.monotoneOn hu ht hut)).trans_lt htb) hb).1
  refine ⟨hHull, ?_⟩
  obtain ⟨w', _, c, htc, hw', hw'0, _, hew, _⟩ :=
    RootF14.exists_complete_prefix_model hγ hw hw0 (lt_min_iff.mp ht).2
  intro u hut
  have huc : u < c := hut.trans_lt htc
  have hdriver : physicalDriverRead s u p = Ito.rpath w' u := by
    apply hullDriverRead_eq_of_prefix (hw'.comp continuous_real_toNNReal)
      (by simpa only [Function.comp_def, Real.toNNReal_zero] using hw'0)
    intro v hvu
    exact (hHull v (hvu.trans hut)).trans
      (RootF14.fwdHull_eq_of_prefix_eq hew (hvu.trans_lt huc)).symm
  have hdriver' : physicalDriverRead s u p = w' u := by
    simpa only [Ito.rpath, Real.toNNReal_coe] using hdriver
  exact hdriver'.trans (hew ⟨zero_le, huc.le⟩)

end InteractingSLE.Theorem14.GW2JDetR4
