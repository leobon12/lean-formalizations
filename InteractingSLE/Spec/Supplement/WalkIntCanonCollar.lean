/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCanonFamily

/-!
# Inherited zero limits along component collars

These are the two limit expressions in `IsPieceMatchRef` and
`IsRealMatchRef`, with physical hull gaps in place of lift assumptions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntCanon

/-- An untouched physical real collar has zero reference lift when read
through a conformal component chart. -/
theorem tendsto_lift_zero_comp {c d : Chart} (hc : c.IsConformal)
    (M : HullModel d) (hd : IsNormalized d) {x a ρ : ℝ} (hρ : 0 < ρ)
    (hgap : Disjoint (ball (a : ℂ) ρ) M.hull)
    (hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ))) :
    Tendsto (fun z => d.2.2 (c.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hphys : map c.2.1 (𝓝[H] (x : ℂ)) ≤ 𝓝[H] (a : ℂ) := by
    change Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝[H] (a : ℂ))
    refine tendsto_nhdsWithin_iff.2 ⟨hland, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hc.2.1 hz
  have hlim := M.tendsto_lift_zero hd hρ hgap hphys
  simpa only [Function.comp_def] using tendsto_map'_iff.1 hlim

/-- A nested retained hull preserves an own-prefix lift on a collar where
its transition hull is absent. The sign matches `IsPieceMatchRef`. -/
theorem tendsto_piece_lift_sub_comp {c dA dB : Chart}
    (A : HullModel dA) (B : HullModel dB)
    (hA : IsNormalized dA) (hB : IsNormalized dB) (hAB : A.hull ⊆ B.hull)
    {x y ρ : ℝ} (hρ : 0 < ρ)
    (hgap : Disjoint (ball ((y + A.shift : ℝ) : ℂ) ρ)
      ((fun z => dA.1 z + (A.shift : ℂ)) '' (B.hull \ A.hull)))
    (hdom : ∀ᶠ z in 𝓝[H] (x : ℂ), c.2.1 z ∈ dB.dom)
    (htrans : Tendsto (fun z => dA.1 (c.2.1 z))
      (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ))) :
    Tendsto (fun z => dA.2.2 (c.2.1 z) - dB.2.2 (c.2.1 z))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hphys : map c.2.1 (𝓝[H] (x : ℂ)) ≤ 𝓟 (H \ B.hull) := by
    refine le_principal_iff.2 ?_
    change ∀ᶠ z in 𝓝[H] (x : ℂ), c.2.1 z ∈ H \ B.hull
    exact hdom.mono fun z hz => by rwa [← B.dom_eq]
  have hq : Tendsto (fun z => dA.1 z + (A.shift : ℂ))
      (map c.2.1 (𝓝[H] (x : ℂ))) (𝓝[H] ((y + A.shift : ℝ) : ℂ)) := by
    apply tendsto_map'_iff.2
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [Function.comp_def, ofReal_add] using htrans.add_const (A.shift : ℂ)
    · filter_upwards [hdom] with z hz
      have hzB : c.2.1 z ∈ H \ B.hull := by rwa [← B.dom_eq]
      have hzA : c.2.1 z ∈ dA.dom := by
        change c.2.1 z ∈ (dA.dom : Set ℂ)
        rw [A.dom_eq]
        exact ⟨hzB.1, fun ha => hzB.2 (hAB ha)⟩
      have hH := hA.conformal.fwd_mem hzA
      simpa only [Function.comp_apply, QuantumZipper.H, mem_ofPred_eq,
        add_im, ofReal_im, add_zero] using hH
  have hlim := tendsto_lift_sub_of_nested A B hA hB hAB hphys hρ hgap hq
  have hneg := hlim.neg
  rw [neg_zero] at hneg
  have hcomp := tendsto_map'_iff.1 hneg
  simpa only [Function.comp_def, neg_sub] using hcomp

end InteractingSLE.Theorem14.WalkIntCanon
