/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TtJunc
import InteractingSLE.Spec.Supplement.GW2SdpFlip
import InteractingSLE.Spec.Supplement.GW2SdzStruct
import InteractingSLE.Spec.Supplement.GW2RuStep
import InteractingSLE.Spec.Supplement.GW2WmFar

/-!
# Decision D37 (with D43): the decoded past of a stage and the lower, rightward structure

Packet PROVE-GW2-RELDET (round 32). The base word of a root-`x` stage is the root word flowed through the decoded past
`GW2Wm.pastOf cf R b N`: the records of the relative driver `R` between the stage boundaries `b`. Here:

* `pastFirst_pastOf_one`, **`pastDrift_pastOf`**: along `pastOf`, the cumulative displacement after the root piece is
  `R (b N) − R (b 1)` (ordered boundaries);
* `pastOf_one_snd`: the root piece's record is `recOf (b 1) (R, ⊤)`;
* `FarJunction`: the far-junction clause of the lower structure (`3√s ≤ junctionR`, or `3√s ≤ −junctionL` on the
  mirror);
* **`nearStructBot_stageWord`**: SDE's deterministic inputs of `nearStruct_stageWord_span` with the far junction in
  place of the span give `NearStructBot` in BOTH orientations (SDE's `nearStruct_of_sideInv`, bottom branches).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe v

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist.Staged Exist.StagedLaw GW2TipSystem.RootH10 GW2Sdp

/-! ### The decoded past -/

section Past

/-- The root piece of `pastOf`. -/
theorem pastFirst_pastOf_one (cf : RecData) (R : ℝ≥0 → ℝ) (b : ℕ → ℝ≥0) :
    ∀ n, pastFirst n (GW2Wm.pastOf cf R b (n + 1)) = GW2Wm.pastOf cf R b 1
  | 0 => rfl
  | n + 1 => pastFirst_pastOf_one cf R b n

/-- **The cumulative displacement after the root piece along `pastOf`** (ordered boundaries). -/
theorem pastDrift_pastOf (cf : RecData) {R : ℝ≥0 → ℝ} (hR : Continuous R) (b : ℕ → ℝ≥0) :
    ∀ n, (∀ j < n, b (j + 1) ≤ b (j + 2)) → pastDrift n (GW2Wm.pastOf cf R b (n + 1)) = R (b (n + 1)) - R (b 1)
  | 0, _ => by
    change (0 : ℝ) = R (b 1) - R (b 1)
    rw [sub_self]
  | n + 1, hb => by
    have ih := pastDrift_pastOf cf hR b n fun j hj => hb j (Nat.lt_succ_of_lt hj)
    change pastDrift n (GW2Wm.pastOf cf R b (n + 1)) +
      rdrv (recOf ((b (n + 2) - b (n + 1) : ℝ≥0) : ℝ≥0∞) (fun u => stgDrv R (b (n + 1)) u, ⊤))
        (rtime (recOf ((b (n + 2) - b (n + 1) : ℝ≥0) : ℝ≥0∞) (fun u => stgDrv R (b (n + 1)) u, ⊤))) =
      R (b (n + 2)) - R (b 1)
    rw [ih, GW2Ru.rdrv_rtime_stgRec hR (hb n (Nat.lt_succ_self n))]
    ring

/-- **The root piece's record** is the record of `R` up to the first boundary. -/
theorem pastOf_one_snd (cf : RecData) {R : ℝ≥0 → ℝ} (hR0 : R 0 = 0) {b : ℕ → ℝ≥0} (hb0 : b 0 = 0) :
    (GW2Wm.pastOf cf R b 1).2 = recOf ((b 1 : ℝ≥0) : ℝ≥0∞) (R, ⊤) := by
  change recOf ((b 1 - b 0 : ℝ≥0) : ℝ≥0∞) (fun u => stgDrv R (b 0) u, ⊤) = _
  rw [hb0, tsub_zero]
  congr 2
  funext u
  simp only [stgDrv, zero_add, hR0, sub_zero]

end Past

/-! ### The lower structure from the far junction -/

section Struct

variable {κ : ℝ} {S : Type v}

/-- **The far-junction clause of the lower structure**: the junction on the side read by the next (rightward) test
is at least `3√s` away (the right junction, or the left one on the mirror). -/
def FarJunction (s : ℝ≥0) (flip : Bool) {n : ℕ} (y : GW2JDetR5.Past S (n + 1)) : Prop :=
  (flip = false → 3 * Real.sqrt s ≤ junctionR (n + 1) y) ∧ (flip = true → 3 * Real.sqrt s ≤ -junctionL (n + 1) y)

/-- **The lower, rightward structure of a stage word** (both orientations), from SDE's deterministic inputs and the far
junction. -/
theorem nearStructBot_stageWord (hκ : 0 < κ) (hκ4 : κ < 4) (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (hθ : ∀ j, θ j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (n : ℕ) (x : GW2JDetR5.Past S (n + 1)) {s : ℝ≥0}
    (hs : s ≠ 0) (flip : Bool)
    (hformL : ∀ h ∈ rootHeightsL (W₀ (GW2Wm.pastRoot (n + 1) x)), h ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ h = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hformR : ∀ h ∈ rootHeightsR (W₀ (GW2Wm.pastRoot (n + 1) x)), h ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ h = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    (hfarL : GW2Wm.FarL (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) (-sleLambda (16 / κ) + Real.pi * chiC κ))
    (hfarR : GW2Wm.FarR (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) (sleLambda (16 / κ) - Real.pi * chiC κ))
    (hjL : junctionL (n + 1) x < 0) (hjR : 0 < junctionR (n + 1) x) (hfar : FarJunction s flip x) :
    GW2Sdy.NearStructBot κ s flip (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) := by
  have h := sideInv_stageWord hκ W₀ θ hθ (n + 1) x
  set c := GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x with hc
  cases flip with
  | false =>
    exact nearStructBot_of_sideInv hκ hκ4 hs h (hfar.1 rfl) hjL hformL (GW2Wm.farL_flowLine hκ hfarL)
      (GW2Wm.farR_flowLine hκ hfarR)
  | true =>
    have h' := h.srefl
    have hfL' : GW2Wm.FarL (FCPlumb.FCKerD.sreflWord c) (-sleLambda (16 / κ) + Real.pi * chiC κ) := by
      have := GW2Sdo.farL_sreflWord hfarR
      rwa [neg_sub, sub_eq_neg_add] at this
    have hfR' : GW2Wm.FarR (FCPlumb.FCKerD.sreflWord c) (sleLambda (16 / κ) - Real.pi * chiC κ) := by
      have := GW2Sdo.farR_sreflWord hfarL
      rwa [neg_add, neg_neg, ← sub_eq_add_neg] at this
    have hformL' : ∀ y ∈ Neg.neg '' rootHeightsR (W₀ (GW2Wm.pastRoot (n + 1) x)), y ∈ oldLeftHeights κ ∨
        ∃ S : ℝ, -2 < S ∧ y = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ := by
      rintro _ ⟨y, hy, rfl⟩
      rcases hformR y hy with ⟨α, hα, hαe⟩ | ⟨S, hS, hSe⟩
      · refine Or.inl ⟨-α, ⟨by linarith [hα.2], by linarith [hα.1]⟩, ?_⟩
        rw [← hαe]
        ring
      · exact Or.inr ⟨S, hS, by rw [hSe]; ring⟩
    exact GW2Sdz.nearStructBot_true_of (nearStructBot_of_sideInv hκ hκ4 hs h' (hfar.2 rfl) (by linarith)
      hformL' (GW2Wm.farL_flowLine hκ hfL') (GW2Wm.farR_flowLine hκ hfR'))

end Struct

end InteractingSLE.Theorem14.GW2Rd
