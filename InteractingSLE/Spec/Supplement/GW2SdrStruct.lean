/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdpFlip

/-!
# The near structure (N3): the stage-word structure from the first piece's junction SPAN

Packet PROVE-GW2-SDE (round 17). The span-based gap (`GW2Sdr.gapFam2`) bounds the root prefix's junction span, not
each junction; the structure lemma only needs the span (`GW2Sdp.nearStruct_of_sideInv`), which never shrinks:

* **`nearStruct_stageWord_span`**: every stage word, either orientation, has ROOT2's near structure at the scale `s`
  from the root-word side forms, the far heights, junctions strictly off the tip, and the first piece's junction span
  at least `6√s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe v

namespace InteractingSLE.Theorem14.GW2Sdr

open Restart Exist.Staged Exist.StagedLaw GW2TipSystem.RootH10 GW2Sdp

variable {κ : ℝ} {S : Type v}

/-- **The near structure of every stage word from the first piece's junction span.** -/
theorem nearStruct_stageWord_span (hκ : 0 < κ) (hκ4 : κ < 4) (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (hθ : ∀ j, θ j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (n : ℕ) (x : GW2JDetR5.Past S (n + 1)) {s : ℝ≥0}
    (hs : s ≠ 0) (flip : Bool)
    (hformL : ∀ h ∈ rootHeightsL (W₀ (GW2Wm.pastRoot (n + 1) x)), h ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ h = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hformR : ∀ h ∈ rootHeightsR (W₀ (GW2Wm.pastRoot (n + 1) x)), h ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ h = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    (hfarL : GW2Wm.FarL (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) (-sleLambda (16 / κ) + Real.pi * chiC κ))
    (hfarR : GW2Wm.FarR (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) (sleLambda (16 / κ) - Real.pi * chiC κ))
    (hjL : junctionL (n + 1) x < 0) (hjR : 0 < junctionR (n + 1) x)
    (hfirst : 6 * Real.sqrt s ≤ junctionR 1 (pastFirst n x) - junctionL 1 (pastFirst n x)) :
    GW2Sdy.NearStruct κ s flip (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) :=
  nearStruct_of_sideInv hκ hκ4 hs flip (sideInv_stageWord hκ W₀ θ hθ (n + 1) x) hformL hformR hfarL hfarR
    hjL hjR (hfirst.trans (junction_span n x))

end InteractingSLE.Theorem14.GW2Sdr
