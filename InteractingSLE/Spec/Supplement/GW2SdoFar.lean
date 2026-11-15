/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdzStruct
import InteractingSLE.Spec.Supplement.GW2WmMap

/-!
# The far clauses of the near structure from GEOM2's far heights of the base word

Packet PROVE-GW2-SDE (round 14). Input (N3) of the near words (`GW2Sdy.NearStruct` of the dilated base word
`nearDilWord s flip c`) has two far clauses: the height beyond the outermost left label is `−λ′ + πχ`, beyond the
outermost right label `λ′ − πχ`. GEOM2's word map (`GW2Wm.farL_baseWord`, `farR_baseWord`) gives these far heights for
the base word as `FarL`/`FarR`. This file carries them through the dilation and, on odd histories, the sorted mirror
word (which exchanges the sides and negates the heights, so the far heights are again `−λ′ + πχ` on the left and
`λ′ − πχ` on the right):

* `farL_dilW`, `farR_dilW`, `farL_sreflWord`, `farR_sreflWord`, `farL_nearDilWord`, `farR_nearDilWord`;
* **`nearFarL_of_base`**, **`nearFarR_of_base`**: the two far clauses of `NearStructTop`/`NearStructBot` for
  `nearDilWord s flip c`, at every near scale `s ≠ 0` and orientation, from `FarL c (−λ′ + πχ)` and
  `FarR c (λ′ − πχ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Sdo

open Restart GW2Sdy GW2Sdz GW2Wm

variable {c : BoundaryWord} {h : ℝ}

theorem farL_dilW {a : ℝ} (ha : 0 < a) (hf : FarL c h) : FarL (dilW a c) h := by
  obtain ⟨A, hA⟩ := hf
  refine ⟨a * A, fun y hy hyJ => ?_⟩
  rw [fn_dilW_apply ha]
  refine hA _ ?_ fun hm => hyJ ((mem_jumps_dilW_iff ha c y).2 hm)
  rw [div_lt_iff₀ ha, mul_comm]
  exact hy

theorem farR_dilW {a : ℝ} (ha : 0 < a) (hf : FarR c h) : FarR (dilW a c) h := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨a * B, fun y hy hyJ => ?_⟩
  rw [fn_dilW_apply ha]
  refine hB _ ?_ fun hm => hyJ ((mem_jumps_dilW_iff ha c y).2 hm)
  rw [lt_div_iff₀ ha, mul_comm]
  exact hy

/-- The mirror word's far-left height is minus the far-right height. -/
theorem farL_sreflWord (hf : FarR c h) : FarL (FCPlumb.FCKerD.sreflWord c) (-h) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨-B, fun y hy hyJ => ?_⟩
  rw [FCPlumb.FCKerD.jumps_sreflWord] at hyJ
  rw [FCPlumb.FCKerD.fn_sreflWord_of_notMem hyJ]
  simp only [Sec7.FlowReflect.reflData]
  rw [hB (-y) (by linarith) fun hm => hyJ (Sec7.FlowReflect.mem_reflJumps.2 hm)]

/-- The mirror word's far-right height is minus the far-left height. -/
theorem farR_sreflWord (hf : FarL c h) : FarR (FCPlumb.FCKerD.sreflWord c) (-h) := by
  obtain ⟨A, hA⟩ := hf
  refine ⟨-A, fun y hy hyJ => ?_⟩
  rw [FCPlumb.FCKerD.jumps_sreflWord] at hyJ
  rw [FCPlumb.FCKerD.fn_sreflWord_of_notMem hyJ]
  simp only [Sec7.FlowReflect.reflData]
  rw [hA (-y) (by linarith) fun hm => hyJ (Sec7.FlowReflect.mem_reflJumps.2 hm)]

variable {κ : ℝ}

theorem farL_nearDilWord {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool)
    (hL : FarL c (-sleLambda (16 / κ) + Real.pi * chiC κ)) (hR : FarR c (sleLambda (16 / κ) - Real.pi * chiC κ)) :
    FarL (nearDilWord s flip c) (-sleLambda (16 / κ) + Real.pi * chiC κ) := by
  have ha : 0 < (Real.sqrt s)⁻¹ := inv_pos.2 (sqrt_pos_of_ne hs)
  cases flip with
  | false => exact farL_dilW ha hL
  | true =>
    have := farL_dilW ha (farL_sreflWord hR)
    rwa [neg_sub, sub_eq_neg_add] at this

theorem farR_nearDilWord {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool)
    (hL : FarL c (-sleLambda (16 / κ) + Real.pi * chiC κ)) (hR : FarR c (sleLambda (16 / κ) - Real.pi * chiC κ)) :
    FarR (nearDilWord s flip c) (sleLambda (16 / κ) - Real.pi * chiC κ) := by
  have ha : 0 < (Real.sqrt s)⁻¹ := inv_pos.2 (sqrt_pos_of_ne hs)
  cases flip with
  | false => exact farR_dilW ha hR
  | true =>
    have := farR_dilW ha (farR_sreflWord hL)
    rwa [neg_add, neg_neg, ← sub_eq_add_neg] at this

/-- **The far-left clause of the near structure from the base word's far heights.** -/
theorem nearFarL_of_base (hκ : 0 < κ) {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool)
    (hL : FarL c (-sleLambda (16 / κ) + Real.pi * chiC κ)) (hR : FarR c (sleLambda (16 / κ) - Real.pi * chiC κ)) :
    ∀ y, y < flowLineXL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
      (GW2TipStage.lastL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) → y ∉ (nearDilWord s flip c).jumps →
        (nearDilWord s flip c).fn y = -sleLambda (16 / κ) + Real.pi * chiC κ :=
  farL_flowLine hκ (farL_nearDilWord hs flip hL hR)

/-- **The far-right clause of the near structure from the base word's far heights.** -/
theorem nearFarR_of_base (hκ : 0 < κ) {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool)
    (hL : FarL c (-sleLambda (16 / κ) + Real.pi * chiC κ)) (hR : FarR c (sleLambda (16 / κ) - Real.pi * chiC κ)) :
    ∀ y, flowLineXR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
      (GW2TipStage.lastR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) < y →
        y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y = sleLambda (16 / κ) - Real.pi * chiC κ :=
  farR_flowLine hκ (farR_nearDilWord hs flip hL hR)

end InteractingSLE.Theorem14.GW2Sdo
