/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootR18Path
import InteractingSLE.Spec.Supplement.GW2RootR18Safe
import InteractingSLE.Spec.Supplement.GW2RootE13Carrier
import InteractingSLE.Spec.Supplement.GB6PastStep

/-!
# The actual switched prefixes in the regularized joint chart

Packet PROVE-T14-GW2ROOT2. On the literal no-contact event for the original
counterflow trace and the canonical physical prefix, its joint-chart image
is the upper part of a continuous path from zero. The path, closed-hull
avoidance, boundedness and attachment are all constructed from the source
data. Real visits and killed canonical endings are retained.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootR18

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric
open Supp8.GB6 Supp8.GB6.CoordB

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens)
  (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
  (hb : IsPiecewiseConstantBoundaryData b jumps)
  (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
  (hh : IsGFFWithBoundaryData P h b jumps)
  (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
  (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
  (α : Ω → ℝ≥0 → ℂ) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (α ω))
  (s : ℝ≥0)

include h13 hβA hb hc₀J hc₀ hh hcf hζ hα

/-- The actual switched joint-chart prefix has a continuous carrier before
trace contact. No relative trace, chart geometry or clock premise is used. -/
theorem ae_exists_relative_prefix (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂P, Disjoint (α ω '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' (prefixSet hκ h12p βA b jumps c₀ h 0 l ω \ {0})) →
      ∃ Γ : ℝ≥0 → ℂ, ContinuousOn Γ (Icc 0 1) ∧ Γ 0 = 0 ∧
        prefixImage hκ h12p βA b jumps c₀ h (regW s W' ζ') s 0 l ω = Γ '' Icc 0 1 ∩ H := by
  filter_upwards [ae_exists_nnpath_prefixSet hκ h12p βA b jumps c₀ P h
    h13 hβA hb hc₀J hc₀ hh l, hα,
    GW2Later.ae_counterflow_regular h13 hκ hcf hζ, hζ]
    with ω hp hαω hreg hζω hsep
  obtain ⟨γ, hγc, hγ0, hγH, hset⟩ := hp
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  have he : (fun q : ℝ => regW s W' ζ' q.toNNReal ω) = Ito.rpath (fun t => W' t ω) := by
    funext q
    exact regW_eq s hζω hW0 hW q.toNNReal
  let U := Ito.rpath (fun t => W' t ω)
  have hU : Continuous U := hW.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simpa only [U, Ito.rpath, Real.toNNReal_zero] using hW0
  rw [hset] at hsep
  have hsafe := path_mem_relSafe_of_trace_disjoint hαω hW hW0
    (s := s) ENNReal.coe_lt_top hγc hγ0 hγH hsep
  let Γ : ℝ≥0 → ℂ := fun t => relBdry U s (γ t)
  refine ⟨Γ, (continuousOn_relBdry hU hU0 s.coe_nonneg).comp hγc hsafe, ?_, ?_⟩
  · change relBdry U s (γ 0) = 0
    rw [hγ0, relBdry_zero hU hU0 s.coe_nonneg]
  · have hγdom : ∀ t ∈ Icc (0 : ℝ≥0) 1, γ t ∈ H →
        -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U s := by
      intro t ht _ hbad
      exact (hsafe ht).2 (subset_closure ⟨-(γ t)⁻¹, hbad, neg_inv_neg_inv _⟩)
    rw [prefixImage, he, hset, RootE13.prefix_inter_jointDomain_eq hγdom]
    change relMap U s '' (γ '' Icc 0 1 ∩ H) = Γ '' Icc 0 1 ∩ H
    rw [← image_relBdry_inter_H hU hU0 s.coe_nonneg
      (show γ '' Icc 0 1 ⊆ relSafe U s from by rintro _ ⟨t, ht, rfl⟩; exact hsafe ht),
      image_image]

/-- Boundedness, attachment and a compact filling representative for the
literal switched image follow from the source trace data before contact. -/
theorem ae_prefixImage_geometry (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂P, Disjoint (α ω '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' (prefixSet hκ h12p βA b jumps c₀ h 0 l ω \ {0})) →
      let A := prefixImage hκ h12p βA b jumps c₀ h (regW s W' ζ') s 0 l ω
      Bornology.IsBounded A ∧ IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) ∧
        ∃ K : Set ℂ, IsCompact K ∧ fillH A = fillH K := by
  filter_upwards [ae_exists_relative_prefix hκ h12p βA b jumps c₀ P h
    h13 hβA hb hc₀J hc₀ hh W' ζ' hcf hζ α hα s l] with ω hω hsep
  obtain ⟨Γ, hc, h0, hImage⟩ := hω hsep
  dsimp only
  rw [hImage]
  obtain ⟨hK, hb, ha, hfill⟩ := RootD12.upper_prefix_geometry hc
    (show (Γ 0).im ≤ 0 by rw [h0]; exact le_rfl)
  exact ⟨hb, ha, Γ '' Icc 0 1, hK, hfill⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootR18
