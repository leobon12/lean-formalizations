/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2Induction
import InteractingSLE.Spec.Supplement.SBLemmaS5SideProof
import InteractingSLE.Spec.Supplement.S10Order

/-!
# SB3's finite geometric induction after erasure

Packet PROVE-T14-SBTAIL2, second continuation. Real connectors, the corrected
inside case, and S5's relative gluing case preserve S1. The finite-chain theorem
below performs this induction; it does not construct the conditional erasure law
or prove the relative ordered-completion input. Real translation handles SB3's
distinct upper seed without changing the retained original-real bridge.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Erase

/-- Real translation transports the closed right side, just as it transports
the closed left side in `Supp10.closedLeftSide_add_real`. -/
theorem closedRightSide_add_real (γ : ℝ≥0 → ℂ) (x : ℝ) :
    Supp9B.closedRightSide (fun t => γ t + x) =
      (· + (x : ℂ)) '' Supp9B.closedRightSide γ := by
  let Φ := Homeomorph.addRight (x : ℂ)
  have hS : Φ '' seedRayClosure γ = seedRayClosure (fun t => γ t + x) :=
    (Supp10.seedRayClosure_add_real γ x).symm
  have hC : Φ '' (seedRayClosure γ)ᶜ = (seedRayClosure (fun t => γ t + x))ᶜ := by
    rw [← hS]
    exact Φ.toEquiv.image_compl _
  have hp : Φ (γ 0 + 1 - Complex.I) = (fun t => γ t + (x : ℂ)) 0 + 1 - Complex.I := by
    change γ 0 + 1 - Complex.I + x = γ 0 + x + 1 - Complex.I
    ring
  unfold Supp9B.closedRightSide Supp9B.rightSide
  rw [image_union]
  congr 1
  · by_cases h : γ 0 + 1 - Complex.I ∈ (seedRayClosure γ)ᶜ
    · have he := Φ.image_connectedComponentIn h
      rw [hC, hp] at he
      exact he.symm
    · have h' : (fun t => γ t + (x : ℂ)) 0 + 1 - Complex.I ∉
          (seedRayClosure (fun t => γ t + x))ᶜ := by
        rw [← hp, ← hC]
        rintro ⟨z, hz, he⟩
        exact h (Φ.injective he ▸ hz)
      rw [connectedComponentIn_eq_empty h', connectedComponentIn_eq_empty h, image_empty]
  · exact hS.symm

/-- S1 is preserved by real translation, with exactly the same prefix length. -/
theorem isOneSided_add_real {A : Set ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0}
    (h : IsOneSided A β a) (x : ℝ) :
    IsOneSided ((· + (x : ℂ)) '' A) (fun t => β t + x) a := by
  obtain ⟨β', hβ', hA⟩ := h
  have hβ'x := Supp10.IsProperCompletion.sub_real hβ' (-x)
  simp only [neg_neg] at hβ'x
  refine ⟨_, hβ'x, ?_⟩
  rw [closedRightSide_add_real]
  exact image_mono hA

/-- Translating both a set and a curve does not change S1. -/
theorem isOneSided_add_real_iff {A : Set ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0} (x : ℝ) :
    IsOneSided ((· + (x : ℂ)) '' A) (fun t => β t + x) a ↔ IsOneSided A β a := by
  constructor
  · intro h
    have hx := isOneSided_add_real h (-x)
    simpa only [image_image, Complex.ofReal_neg, add_neg_cancel_right, image_id'] using hx
  · exact fun h => isOneSided_add_real h x

/-- One geometric step in the source's SB3 induction. No constructor asserts S1.
The relative case records the actual relative-prefix comparison needed by S5;
its construction from the conditional field remains separate mathematics. -/
inductive ErasureStep (β : ℝ≥0 → ℂ) (a : ℝ≥0) : Set ℂ → Set ℂ → Prop
  | real {A : Set ℂ} {T : Set ℝ}
      (h0 : (β 0).im = 0) (hT : ∀ x ∈ T, (β 0).re ≤ x) :
      ErasureStep β a A (A ∪ ((↑) : ℝ → ℂ) '' T)
  | inside {p : ℝ → ℂ} {B : Set ℂ}
      (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
      (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
      (hin : β '' Icc 0 a ⊆ hullK (p '' Icc 0 1))
      (hvisit : ∀ s : ℝ≥0, s < a → β s ≠ realMin (p '' Icc 0 1))
      (hB : B ⊆ closure (H \ fillH (p '' Icc 0 1))) :
      ErasureStep β a (p '' Icc 0 1) (p '' Icc 0 1 ∪ B)
  | relative {p : ℝ → ℂ} {c : Chart} {g : ℂ → ℂ}
      {tL a₁ : ℝ≥0} {aR bR : ℝ≥0 → ℂ} {w : ℝ}
      (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
      (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
      (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
      (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
      (hgf : ∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite)
      (ht : tL ≤ a) (hL : β tL = realMin (p '' Icc 0 1)) (hb0 : bR 0 = 0)
      (hrel : ∀ s : ℝ≥0, s ≤ a - tL → g (bR s) = β (tL + s))
      (hw : 0 ≤ w) (ha0 : aR 0 = w)
      (hord : HasOrderedProperCompletions aR a₁ bR (a - tL)) :
      ErasureStep β a (p '' Icc 0 1) (p '' Icc 0 1 ∪ g '' (aR '' Icc 0 a₁))

/-- Each source case propagates S1 from the entire old history to its enlargement. -/
theorem ErasureStep.isOneSided {β : ℝ≥0 → ℂ} {a : ℝ≥0} {A B : Set ℂ}
    (hstep : ErasureStep β a A B) (hA : IsOneSided A β a) : IsOneSided B β a := by
  cases hstep with
  | real h0 hT => exact hA.union_right_real h0 hT
  | inside hp hp0 hpH hβ0 hin hvisit hB =>
    exact s5InsideNoVisitStatement _ β a hp hp0 hpH hβ0 hA hin hvisit _ hB
  | relative hp hp0 hpH hβ0 hc hgc hgi hgf ht hL hb0 hrel hw ha0 hord =>
    exact s5Statement _ β a hp hp0 hpH hβ0 hA _ _ hc hgc hgi hgf _ _ _ _ _
      ht hL hb0 hrel hw ha0 hord

/-- Finite induction over connectors and actual relative ordinary pieces. The
proper completion may change at each stage; no union of separate S1 witnesses is used. -/
theorem isOneSided_of_erasureSteps {β : ℝ≥0 → ℂ} {a : ℝ≥0} {A B : Set ℂ}
    (hsteps : Relation.ReflTransGen (ErasureStep β a) A B) (hA : IsOneSided A β a) :
    IsOneSided B β a := by
  induction hsteps with
  | refl => exact hA
  | tail _ hstep ih => exact hstep.isOneSided ih

end InteractingSLE.Theorem14.SB.Erase
