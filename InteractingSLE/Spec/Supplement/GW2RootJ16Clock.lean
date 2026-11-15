/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ16Chain

/-!
# Every live physical cutoff has a live intrinsic relative time

Packet PROVE-T14-GW2ROOT2. Strict increase of the constructed actual
regularized clock gives strict liveness at every pre-contact cutoff.
The relative lifetime is the supremum of its live clock values. No
liveness or clock regularity conclusion is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ16

open Supp8.GB6

/-- A physical cutoff before first contact and its generating lifetime
maps strictly below the intrinsic relative lifetime of the constructed chain. -/
theorem regW_relClock_lt_lifetime {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (fun t => W t ω) (ζ ω) α)
    (hW : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hW0 : W 0 ω = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
    {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    {v : ℝ≥0} (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T) :
    let S := min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
    let a : ℝ≥0 → ℝ := fun t =>
      relClock (fun q : ℝ => regW s W ζ q.toNNReal ω) s (fun q : ℝ => w q.toNNReal) t
    ((a v).toNNReal : ℝ≥0∞) <
      ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < S), ((a t).toNNReal : ℝ≥0∞) := by
  let S := min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) T
  let a : ℝ≥0 → ℝ := fun t =>
    relClock (fun q : ℝ => regW s W ζ q.toNNReal ω) s (fun q : ℝ => w q.toNNReal) t
  change ((a v).toNNReal : ℝ≥0∞) <
    ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < S), ((a t).toNNReal : ℝ≥0∞)
  have hvS : (v : ℝ≥0∞) < S := hv
  have hT : 0 < T := lt_of_le_of_lt bot_le (lt_min_iff.mp hv).2
  obtain ⟨_, _, ha0, hm, _, _, _⟩ :=
    exists_regW_relative_chain_before_contact W ζ ω hα hW hW0 hs hsH hγ hw hw0 hT
  change a 0 = 0 at ha0
  change StrictMonoOn a {t | (t : ℝ≥0∞) < S} at hm
  have hn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < S → 0 ≤ a t := by
    intro t ht
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < S := lt_of_le_of_lt bot_le ht
    have h := hm.monotoneOn h0 ht (zero_le : (0 : ℝ≥0) ≤ t)
    rwa [ha0] at h
  obtain ⟨B, hvB, hBS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hvS
  have hab : a v < a B := hm hvS hBS (ENNReal.coe_lt_coe.mp hvB)
  have hNN : (a v).toNNReal < (a B).toNNReal := by
    apply NNReal.coe_lt_coe.mp
    simpa only [Real.coe_toNNReal _ (hn v hvS), Real.coe_toNNReal _ (hn B hBS)] using hab
  exact (ENNReal.coe_lt_coe.mpr hNN).trans_le
    (le_iSup_of_le B (le_iSup_of_le hBS le_rfl))

end InteractingSLE.Theorem14.GW2TipSystem.RootJ16
