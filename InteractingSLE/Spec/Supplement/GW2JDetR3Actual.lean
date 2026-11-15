/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR3Cut

/-!
# Exact geometric availability and physical stopping times

For the actual pre-contact relative chain, every live relative time has a
unique available physical time. The Borel capacity cutoff recovers the
relative time of every available physical cutoff, with any later live buffer.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2JDetR3

open Supp8.GB6 Exist.StagedLaw GW2TipSystem

/-- The inverse-clock availability and capacity stopping identities of the
actual relative chain, proved from the two original generating traces. -/
theorem exists_actual_capacity_cut {Ω : Type*}
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
    ∃ V : ℝ≥0 → ℝ, V 0 = 0 ∧ ContinuousOn V {q | (q : ℝ≥0∞) < L} ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < L ↔
        ∃! t : ℝ≥0, (t : ℝ≥0∞) < S ∧ a t = u) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < S →
        ∀ b : ℝ≥0, (a t).toNNReal < b → (b : ℝ≥0∞) < L →
          capacityCut s t
            (r, cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ()) =
              ((a t).toNNReal : ℝ≥0∞) := by
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
      inverseHull s (a t).toNNReal p = QuantumZipper.fwdHull (Ito.rpath w) t ∧
        physicalCapacity s (a t).toNNReal p = t at hread
  refine ⟨V, hV0, hVc, ?_, ?_⟩
  · intro u
    constructor
    · exact existsUnique_time_of_lt_clockSup ha0 hm hc
    · rintro ⟨t, ⟨ht, he⟩, _⟩
      change a t = u at he
      change (u : ℝ≥0∞) < L
      have h := (hread t ht).2.1
      simpa only [he, Real.toNNReal_coe] using h
  · intro t ht b htb hb
    apply capacityCut_eq_of_local_inverse s t _ htb
    intro q hqb
    have hqL : (q : ℝ≥0∞) < L := (ENNReal.coe_le_coe.mpr hqb.le).trans_lt hb
    obtain ⟨u, ⟨hu, hau⟩, _⟩ := existsUnique_time_of_lt_clockSup ha0 hm hc hqL
    have hqread := (hread u hu).2.2 b
      (by simpa only [hau, Real.toNNReal_coe] using hqb) hb
    have hcap : physicalCapacity s q
        (r, cfRec b (fun u (_ : Unit) => V u) (fun _ => L) ()) = u := by
      simpa only [hau, Real.toNNReal_coe] using hqread.2
    rw [hcap]
    have hat := (hread t ht).1
    constructor
    · intro htu
      have h := hm ht hu (NNReal.coe_lt_coe.mp htu)
      rw [hau] at h
      apply NNReal.coe_lt_coe.mp
      rwa [Real.coe_toNNReal _ hat]
    · intro hq
      have h := NNReal.coe_lt_coe.mpr hq
      rw [Real.coe_toNNReal _ hat, ← hau] at h
      exact NNReal.coe_lt_coe.mpr ((hm.lt_iff_lt ht hu).mp h)

end InteractingSLE.Theorem14.GW2JDetR3
