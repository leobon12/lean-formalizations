/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR3Capacity
import InteractingSLE.Spec.Supplement.GW2RootJ16Clock

/-!
# Actual inverse-hull and capacity read-back before GW2 contact

The relative driver is constructed from the two source generating traces.
At every live physical time its recorded relative hull pulls back to the
original hull, and the Borel capacity readout equals physical time.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2JDetR3

open Supp8.GB6 Exist.StagedLaw GW2TipSystem

/-- An arbitrarily buffered relative record determines every pre-contact
physical hull and its original capacity time. No inverse, capacity or clock
identity is a premise: they are proved from the two generating traces. -/
theorem exists_inverse_capacity_chain {Ω : Type*}
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
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
        0 ≤ a t ∧ ((a t).toNNReal : ℝ≥0∞) < L ∧
        ∀ b : ℝ≥0, (a t).toNNReal < b → (b : ℝ≥0∞) < L →
          let p := (r, cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ())
          inverseHull s (a t).toNNReal p = fwdHull (Ito.rpath w) t ∧
            physicalCapacity s (a t).toNNReal p = t := by
  dsimp only
  let r := cfRec s W ζ ω
  let U := rdrv r
  let U' : ℝ → ℝ := fun q => regW s W ζ q.toNNReal ω
  have he : EqOn U U' (Icc 0 s) := by
    intro q hq
    have hqζ : (q.toNNReal : ℝ≥0∞) < ζ ω :=
      (ENNReal.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hq.2)).trans_lt hs
    exact (GaugeE.record_prefix_eq s hW0 hW hs hq).trans
      (cfE_fst_of_lt s hW0 hW hqζ).symm
  have hmap : relMap U s = relMap U' s := relMap_eq_of_eqOn s.coe_nonneg he
  have hclock : relClock U s (Ito.rpath w) = relClock U' s (Ito.rpath w) :=
    relClock_eq_of_eqOn s.coe_nonneg he (Ito.rpath w)
  obtain ⟨V, hV0, ha0, hm, hc, hVc, hK⟩ :=
    RootJ16.exists_regW_relative_chain_before_contact W ζ ω hα hW hW0 hs hsH
      hγ hw hw0 hT
  change relClock U' s (Ito.rpath w) 0 = 0 at ha0
  change StrictMonoOn (fun t : ℝ≥0 => relClock U' s (Ito.rpath w) t) _ at hm
  change ContinuousOn (fun t : ℝ≥0 => relClock U' s (Ito.rpath w) t) _ at hc
  change ContinuousOn V {q | (q : ℝ≥0∞) <
    ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < _),
      ((relClock U' s (Ito.rpath w) t).toNNReal : ℝ≥0∞)} at hVc
  rw [← hclock] at ha0 hm hc hVc
  refine ⟨V, hV0, ha0, hm, hc, hVc, ?_⟩
  intro t ht
  have ha : 0 ≤ relClock U s (Ito.rpath w) t := by
    have hz : ((0 : ℝ≥0) : ℝ≥0∞) < min
        (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
          ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T :=
      lt_of_le_of_lt bot_le ht
    have h := hm.monotoneOn hz ht (zero_le : (0 : ℝ≥0) ≤ t)
    simpa only [NNReal.coe_zero, ha0] using h
  have hlive := RootJ16.regW_relClock_lt_lifetime W ζ ω hα hW hW0 hs hsH
    hγ hw hw0 ht
  change ((relClock U' s (Ito.rpath w) t).toNNReal : ℝ≥0∞) <
    ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < _),
      ((relClock U' s (Ito.rpath w) t).toNNReal : ℝ≥0∞) at hlive
  rw [← hclock] at hlive
  refine ⟨ha, hlive, ?_⟩
  intro b htb hb
  change (relClock U s (Ito.rpath w) t).toNNReal < b at htb
  let L := ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T),
        ((relClock U s (Ito.rpath w) t).toNNReal : ℝ≥0∞)
  let rb := cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ()
  have hp : EqOn (rdrv rb) (Ito.rpath V) (Icc 0 b) :=
    GaugeE.record_prefix_eq b hV0 hVc hb
  have hkb : fwdHull (rdrv rb) (relClock U s (Ito.rpath w) t) =
      fwdHull (Ito.rpath V) (relClock U s (Ito.rpath w) t) := by
    apply fwdHull_eq_of_eqOn ha
      (show relClock U s (Ito.rpath w) t < b from by
        have h := NNReal.coe_lt_coe.mpr htb
        rwa [Real.coe_toNNReal _ ha] at h)
    intro q hq
    exact hp ⟨hq.1, hq.2⟩
  have hk := (hK t ht).1
  change fwdHull (Ito.rpath V) (relClock U' s (Ito.rpath w) t) =
    relMap U' s '' fwdHull (Ito.rpath w) t at hk
  rw [← hclock, ← hmap] at hk
  have hinv : inverseHull s (relClock U s (Ito.rpath w) t).toNNReal (r, rb) =
      fwdHull (Ito.rpath w) t := by
    unfold inverseHull
    rw [Real.coe_toNNReal _ ha, hkb, hk]
    exact relInv_image_relMap_before_contact W ζ ω hα hW hW0 hs hγ hw hw0 ht
  refine ⟨hinv, ?_⟩
  unfold physicalCapacity
  rw [hinv, hcapHit_fwdHull_of_live_trace hγ hw hw0 (lt_min_iff.mp ht).2,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) t.coe_nonneg)]
  ring

end InteractingSLE.Theorem14.GW2JDetR3
