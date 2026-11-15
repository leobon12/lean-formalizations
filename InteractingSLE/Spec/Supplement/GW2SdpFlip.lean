/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdpJoint
import InteractingSLE.Spec.Supplement.GW2SdoFar

/-!
# The near structure (N3), step E: both orientations

Packet PROVE-GW2-SDE (round 15). Odd histories read the mirror word (`nearDilWord s true c = dilW _ (sreflWord c)`).
The side invariant passes to the mirror with the junctions exchanged and negated, the old sides exchanged, and the
root heights negated:

* **`SideInv.srefl`**: `SideInv κ c aL aR HL HR → SideInv κ (sreflWord c) (−aR) (−aL) (−HR) (−HL)`;
* **`nearStruct_of_sideInv`**: for EITHER orientation, the side invariant with the root-word forms, the two far
  heights, junctions strictly off the tip and junction span at least `6√s` gives ROOT2's structure at the scale `s`;
* **`nearStruct_stageWord'`**: the same for every stage word, from the first piece's junctions beyond `3√s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe v

namespace InteractingSLE.Theorem14.GW2Sdp

open Restart Exist.Staged Exist.StagedLaw GW2TipSystem.RootH10

variable {κ : ℝ}

/-- **The side invariant of the mirror word.** -/
theorem SideInv.srefl {c : BoundaryWord} {aL aR : ℝ} {HL HR : Set ℝ} (h : SideInv κ c aL aR HL HR) :
    SideInv κ (FCPlumb.FCKerD.sreflWord c) (-aR) (-aL) (Neg.neg '' HR) (Neg.neg '' HL) where
  aL_nonpos := neg_nonpos.2 h.aR_nonneg
  aR_nonneg := neg_nonneg.2 h.aL_nonpos
  oldL z hz1 hz2 hzJ := by
    rw [FCPlumb.FCKerD.jumps_sreflWord] at hzJ
    rw [FCPlumb.FCKerD.fn_sreflWord_of_notMem hzJ]
    obtain ⟨α, hα, hαe⟩ := h.oldR (-z) (by linarith) (by linarith) fun hm => hzJ (Sec7.FlowReflect.mem_reflJumps.2 hm)
    refine ⟨-α, ⟨by linarith [hα.2], by linarith [hα.1]⟩, ?_⟩
    simp only [Sec7.FlowReflect.reflData, ← hαe]
    ring
  rootL z hz hzJ := by
    rw [FCPlumb.FCKerD.jumps_sreflWord] at hzJ
    rw [FCPlumb.FCKerD.fn_sreflWord_of_notMem hzJ]
    exact ⟨_, h.rootR (-z) (by linarith) fun hm => hzJ (Sec7.FlowReflect.mem_reflJumps.2 hm), rfl⟩
  oldR z hz1 hz2 hzJ := by
    rw [FCPlumb.FCKerD.jumps_sreflWord] at hzJ
    rw [FCPlumb.FCKerD.fn_sreflWord_of_notMem hzJ]
    obtain ⟨α, hα, hαe⟩ := h.oldL (-z) (by linarith) (by linarith) fun hm => hzJ (Sec7.FlowReflect.mem_reflJumps.2 hm)
    refine ⟨-α, ⟨by linarith [hα.2], by linarith [hα.1]⟩, ?_⟩
    simp only [Sec7.FlowReflect.reflData, ← hαe]
    ring
  rootR z hz hzJ := by
    rw [FCPlumb.FCKerD.jumps_sreflWord] at hzJ
    rw [FCPlumb.FCKerD.fn_sreflWord_of_notMem hzJ]
    exact ⟨_, h.rootL (-z) (by linarith) fun hm => hzJ (Sec7.FlowReflect.mem_reflJumps.2 hm), rfl⟩

/-- **ROOT2's structure in either orientation from the side invariant.** -/
theorem nearStruct_of_sideInv (hκ : 0 < κ) (hκ4 : κ < 4) {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool) {c : BoundaryWord}
    {aL aR : ℝ} {HL HR : Set ℝ} (h : SideInv κ c aL aR HL HR)
    (hformL : ∀ x ∈ HL, x ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ x = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hformR : ∀ x ∈ HR, x ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ x = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    (hfarL : GW2Wm.FarL c (-sleLambda (16 / κ) + Real.pi * chiC κ))
    (hfarR : GW2Wm.FarR c (sleLambda (16 / κ) - Real.pi * chiC κ))
    (haL : aL < 0) (haR : 0 < aR) (hspan : 6 * Real.sqrt s ≤ aR - aL) :
    GW2Sdy.NearStruct κ s flip c := by
  cases flip with
  | false =>
    by_cases hR3 : 3 * Real.sqrt s ≤ aR
    · exact Or.inr (nearStructBot_of_sideInv hκ hκ4 hs h hR3 haL hformL (GW2Wm.farL_flowLine hκ hfarL)
        (GW2Wm.farR_flowLine hκ hfarR))
    · exact Or.inl (nearStructTop_of_sideInv hκ hκ4 hs h (by linarith [not_le.1 hR3]) haR hformR
        (GW2Wm.farL_flowLine hκ hfarL) (GW2Wm.farR_flowLine hκ hfarR))
  | true =>
    have h' := h.srefl
    have hfL' : GW2Wm.FarL (FCPlumb.FCKerD.sreflWord c) (-sleLambda (16 / κ) + Real.pi * chiC κ) := by
      have := GW2Sdo.farL_sreflWord hfarR
      rwa [neg_sub, sub_eq_neg_add] at this
    have hfR' : GW2Wm.FarR (FCPlumb.FCKerD.sreflWord c) (sleLambda (16 / κ) - Real.pi * chiC κ) := by
      have := GW2Sdo.farR_sreflWord hfarL
      rwa [neg_add, neg_neg, ← sub_eq_add_neg] at this
    have hformL' : ∀ x ∈ Neg.neg '' HR, x ∈ oldLeftHeights κ ∨
        ∃ S : ℝ, -2 < S ∧ x = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ := by
      rintro _ ⟨x, hx, rfl⟩
      rcases hformR x hx with ⟨α, hα, hαe⟩ | ⟨S, hS, hSe⟩
      · refine Or.inl ⟨-α, ⟨by linarith [hα.2], by linarith [hα.1]⟩, ?_⟩
        rw [← hαe]
        ring
      · exact Or.inr ⟨S, hS, by rw [hSe]; ring⟩
    have hformR' : ∀ x ∈ Neg.neg '' HL, x ∈ oldRightHeights κ ∨
        ∃ S : ℝ, -2 < S ∧ x = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ := by
      rintro _ ⟨x, hx, rfl⟩
      rcases hformL x hx with ⟨α, hα, hαe⟩ | ⟨S, hS, hSe⟩
      · refine Or.inl ⟨-α, ⟨by linarith [hα.2], by linarith [hα.1]⟩, ?_⟩
        rw [← hαe]
        ring
      · exact Or.inr ⟨S, hS, by rw [hSe]; ring⟩
    by_cases hR3 : 3 * Real.sqrt s ≤ -aL
    · exact Or.inr (GW2Sdz.nearStructBot_true_of (nearStructBot_of_sideInv hκ hκ4 hs h' hR3 (by linarith)
        hformL' (GW2Wm.farL_flowLine hκ hfL') (GW2Wm.farR_flowLine hκ hfR')))
    · exact Or.inl (GW2Sdz.nearStructTop_true_of (nearStructTop_of_sideInv hκ hκ4 hs h'
        (by linarith [not_le.1 hR3]) (by linarith) hformR' (GW2Wm.farL_flowLine hκ hfL')
        (GW2Wm.farR_flowLine hκ hfR')))

variable {S : Type v}

/-- **The near structure of every stage word, either orientation**: from the root-word forms, the far heights,
junctions strictly off the tip and the first piece's junctions beyond `3√s`. -/
theorem nearStruct_stageWord' (hκ : 0 < κ) (hκ4 : κ < 4) (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (hθ : ∀ j, θ j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (n : ℕ) (x : GW2JDetR5.Past S (n + 1)) {s : ℝ≥0}
    (hs : s ≠ 0) (flip : Bool)
    (hformL : ∀ h ∈ rootHeightsL (W₀ (GW2Wm.pastRoot (n + 1) x)), h ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ h = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hformR : ∀ h ∈ rootHeightsR (W₀ (GW2Wm.pastRoot (n + 1) x)), h ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ h = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    (hfarL : GW2Wm.FarL (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) (-sleLambda (16 / κ) + Real.pi * chiC κ))
    (hfarR : GW2Wm.FarR (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) (sleLambda (16 / κ) - Real.pi * chiC κ))
    (hjL : junctionL (n + 1) x < 0) (hjR : 0 < junctionR (n + 1) x)
    (hfirst : 3 * Real.sqrt s ≤ -junctionL 1 (pastFirst n x) ∧ 3 * Real.sqrt s ≤ junctionR 1 (pastFirst n x)) :
    GW2Sdy.NearStruct κ s flip (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) := by
  have hspan := junction_span n x
  exact nearStruct_of_sideInv hκ hκ4 hs flip (sideInv_stageWord hκ W₀ θ hθ (n + 1) x) hformL hformR hfarL hfarR
    hjL hjR (by linarith [hfirst.1, hfirst.2])

end InteractingSLE.Theorem14.GW2Sdp
