/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RArc
import InteractingSLE.Spec.Sec7.StripWallInputsRefl

/-!
# SB4's mirrored sewing geometry: the left walk read in the reflected plane

Packet PROVE-T14-SB4LEAF. The second half of SB4's distinct-seed leaf compares an upper schedule from `v ≥ 0` with
the left side of the completed left walk (supplement p. 634: "Reflecting gives the upper-walk barrier"). Through the
reflection `ρ(z) = −z̄` (`Supp9B.refl`) the left walk becomes a right walk, its left side the right side of the
reflected walk, the launch chart `c` the reflected chart `ρ ∘ c ∘ ρ` and the new piece the reflected trace of the
negated driver. This file supplies the reflected objects:

* `reflChart_recenter`, `isLeftEntryChart_recenter`, `isRightEntryChart_reflChart`, `isLeftEntryChart_runChart`;
* `rightSideOf_refl_image`: `rightSideOf (ρ X) = ρ (leftSideOf X)`;
* `HasRelTailGeometry.refl_image` (the outer map absorbs the reflection);
* `negReal_subset_closedLeftSide`;
* `ae_chosenTrace_neg_eq`: the chosen trace of the negated driver is the reflected chosen trace.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B Lx Lu Ly Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw GW2Schedule

/-! ### Reflected charts -/

/-- Reflecting and recentring commute (the recentring sign flips). -/
theorem reflChart_recenter (c : Chart) (m : ℝ) : (reflChart c).recenter (-m) = reflChart (c.recenter m) := by
  refine Prod.ext (funext fun z => ?_) (Prod.ext (funext fun w => ?_) rfl)
  · show Supp9B.refl (c.1 (Supp9B.refl z)) - ((-m : ℝ) : ℂ) = Supp9B.refl (c.1 (Supp9B.refl z) - (m : ℂ))
    simp only [Supp9B.refl, map_sub, Complex.conj_ofReal, Complex.ofReal_neg, sub_neg_eq_add, neg_sub,
      neg_add_eq_sub]
  · show Supp9B.refl (c.2.1 (Supp9B.refl (w + ((-m : ℝ) : ℂ)))) =
      Supp9B.refl (c.2.1 (Supp9B.refl w + (m : ℂ)))
    simp only [Supp9B.refl, map_add, map_neg, Complex.conj_ofReal, Complex.ofReal_neg, neg_add, neg_neg]

/-- **A recentred domain chart with a left entry value is a left entry chart.** -/
theorem isLeftEntryChart_recenter {A : Set ℂ} {L a : ℝ} {c : Chart} (hD : IsDomainChart (H \ fillH A) c)
    (hv : IsLeftEntryValue c L a)
    (hcob : Tendsto c.1 (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (Bornology.cobounded ℂ))
    (hlift : ∀ x < L, Tendsto c.2.2 (𝓝[H] (x : ℂ)) (𝓝 0)) :
    IsLeftEntryChart A L (c.recenter a) := by
  obtain ⟨e, he, hlim⟩ := hv
  refine ⟨isDomainChart_recenter hD a, ⟨fun x => e x - a, fun x hx => ?_, ?_⟩, ?_, hlift⟩
  · have := (he x hx).sub_const (a : ℂ)
    push_cast
    exact this
  · simpa using hlim.sub_const a
  · have h := Lw.tendsto_add_cobounded (-(a : ℂ)) le_rfl
    exact (h.comp hcob).congr fun z => by simp [Chart.recenter, sub_eq_add_neg]

/-- **A left entry chart reflects to a right entry chart.** -/
theorem isRightEntryChart_reflChart {A : Set ℂ} {L : ℝ} {c : Chart} (hc : IsLeftEntryChart A L c) :
    IsRightEntryChart (refl '' A) (-L) (reflChart c) := by
  obtain ⟨hD, ⟨e, he, hlim⟩, hcob, hlift⟩ := hc
  have hdom : H \ fillH (refl '' A) = refl '' (H \ fillH A) := by
    rw [refl_eq_reflectC]; exact LP.H_diff_fillH_image_reflectC A
  refine ⟨hdom ▸ isDomainChart_reflChart hD, ⟨fun x => -e (-x), fun x hx => ?_, ?_⟩, ?_, fun x hx => ?_⟩
  · have hr := tendsto_refl_nhdsWithin_H (x : ℂ)
    rw [refl_ofReal] at hr
    have h1 := (he (-x) (by linarith)).comp hr
    have h2 := (continuous_refl.tendsto _).comp h1
    rw [refl_ofReal] at h2
    exact h2
  · have hn : Tendsto (fun x : ℝ => -x) (𝓝[>] (-L)) (𝓝[<] L) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x hx => ?_⟩
      · have := ((continuous_neg (G := ℝ)).tendsto (-L)).mono_left (nhdsWithin_le_nhds (s := Ioi (-L)))
        simpa using this
      · have : -L < x := hx
        show -x < L
        linarith
    have h1 := hlim.comp hn
    simpa using h1.neg
  · have hmaps : Tendsto refl (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH (refl '' A)))
        (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH A)) := by
      refine tendsto_inf.2 ⟨tendsto_refl_cobounded.mono_left inf_le_left,
        (tendsto_principal_principal.2 fun z hz => ?_).mono_left inf_le_right⟩
      rw [hdom] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rwa [refl_refl]
    exact tendsto_refl_cobounded.comp (hcob.comp hmaps)
  · have hr := tendsto_refl_nhdsWithin_H (x : ℂ)
    rw [refl_ofReal] at hr
    have h1 := (hlift (-x) (by linarith)).comp hr
    have h2 := h1.neg
    rw [neg_zero] at h2
    exact h2

open Exist.StagedLaw in
/-- **The recentred run chart is a left entry chart** at the smallest real point of a compact `A` with the prefix's
fill, when it has the left entry value `a` there. -/
theorem isLeftEntryChart_runChart {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {a : ℝ}
    (hv : IsLeftEntryValue (stChart (ExplState.run κ b jumps spec D n)) (realMin A) a) :
    IsLeftEntryChart A (realMin A) ((stChart (ExplState.run κ b jumps spec D n)).recenter a) := by
  have hD := Lw.isDomainChart_runChart spec D hreg n hnot
  rw [← hAf] at hD
  have hcob := Lw.tendsto_runChart_cobounded spec D hreg n hnot
  rw [← hAf] at hcob
  refine isLeftEntryChart_recenter hD hv hcob fun x hx => ?_
  refine Lw.tendsto_runChart_lift_zero spec D hreg n hnot hAc hAf fun y hy => lt_of_lt_of_le hx ?_
  refine csInf_le ?_ hy
  obtain ⟨M, hM⟩ := hAc.isBounded.exists_norm_le
  refine ⟨-M, fun z hz => ?_⟩
  have := hM _ hz
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  linarith [neg_abs_le z]

/-! ### Sides under the reflection -/

/-- The reflection maps components of `ℍ \ Y` to components of `ℍ \ ρ(Y)`. -/
theorem refl_image_connectedComponentIn {Y : Set ℂ} {z : ℂ} (hz : z ∈ H \ Y) :
    Supp9B.refl '' connectedComponentIn (H \ Y) z = connectedComponentIn (H \ Supp9B.refl '' Y) (Supp9B.refl z) := by
  have hHY : Supp9B.refl '' (H \ Y) = H \ Supp9B.refl '' Y := by
    rw [image_sdiff refl_injective, refl_image_H]
  have h := (Homeomorph.mk ⟨Supp9B.refl, Supp9B.refl, refl_refl, refl_refl⟩ continuous_refl
    continuous_refl).image_connectedComponentIn (s := H \ Y) (x := z) hz
  simpa [hHY] using h

/-- **The reflection exchanges the two frozen side conventions**: `rightSideOf (ρ X) = ρ (leftSideOf X)`. -/
theorem rightSideOf_refl_image (X : Set ℂ) : rightSideOf (Supp9B.refl '' X) = Supp9B.refl '' leftSideOf X := by
  ext z
  constructor
  · rintro ⟨⟨hzH, hzX⟩, x, hx, hxX, hxcl⟩
    have hz' : Supp9B.refl z ∉ X := fun h => hzX ⟨_, h, refl_refl z⟩
    have hxX' : ((-x : ℝ) : ℂ) ∉ X := fun h => hxX ⟨_, h, by rw [refl_ofReal, neg_neg]⟩
    have hcl : Supp9B.refl (x : ℂ) ∈ closure (connectedComponentIn (H \ X) (Supp9B.refl z)) := by
      have h1 := mem_closure_image continuous_refl.continuousAt hxcl
      rw [refl_image_connectedComponentIn ⟨hzH, hzX⟩, refl_image_refl_image] at h1
      exact h1
    rw [refl_ofReal] at hcl
    exact ⟨Supp9B.refl z, ⟨⟨refl_mem_H hzH, hz'⟩, -x, by linarith, hxX', hcl⟩, refl_refl z⟩
  · rintro ⟨w, ⟨⟨hwH, hwX⟩, x, hx, hxX, hxcl⟩, rfl⟩
    have hw' : Supp9B.refl w ∉ Supp9B.refl '' X := fun ⟨w', hw', he⟩ => hwX (refl_injective he ▸ hw')
    have hxX' : ((-x : ℝ) : ℂ) ∉ Supp9B.refl '' X := by
      rintro ⟨y, hy, he⟩
      have : y = (x : ℂ) := by
        have h2 := congrArg Supp9B.refl he
        rwa [refl_refl, refl_ofReal, neg_neg] at h2
      exact hxX (this ▸ hy)
    have hcl : Supp9B.refl (x : ℂ) ∈
        closure (connectedComponentIn (H \ Supp9B.refl '' X) (Supp9B.refl w)) := by
      have h1 := mem_closure_image continuous_refl.continuousAt hxcl
      rwa [refl_image_connectedComponentIn ⟨hwH, hwX⟩] at h1
    rw [refl_ofReal] at hcl
    exact ⟨⟨refl_mem_H hwH, hw'⟩, -x, by linarith, hxX', hcl⟩

/-- Negative real points are on the closed left side of a proper curve from `0`. -/
theorem negReal_subset_closedLeftSide {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0) (v : ℝ) :
    ((↑) : ℝ → ℂ) '' Icc (-v) 0 ⊆ closedLeftSide β₀ := by
  have h0 : (β₀ 0).im = 0 := by rw [hβ0]; rfl
  rintro _ ⟨y, ⟨-, hy0⟩, rfl⟩
  by_cases hyS : (y : ℂ) ∈ seedRayClosure β₀
  · exact Or.inr hyS
  rcases hy0.lt_or_eq with hy | rfl
  · refine Or.inl (ofReal_mem_leftSide hβ.2.2.1 h0 ?_ hyS)
    rw [hβ0]; simpa using hy
  · exact absurd (Or.inl ⟨0, by rw [hβ0]; simp⟩) hyS

/-! ### The sewing geometry under the reflection -/

/-- **The outer map of the sewing geometry absorbs the reflection.** -/
theorem _root_.InteractingSLE.Theorem14.SB.Leaf.HasRelTailGeometry.refl_image {A S Wrel : Set ℂ} {u : ℝ}
    {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hg : Leaf.HasRelTailGeometry A S Wrel u η ζ) :
    Leaf.HasRelTailGeometry (refl '' A) (refl '' S) Wrel u η ζ := by
  obtain ⟨p, β, γ, c, g, J, tL, hp, hp0, hpH, hβ, hβ0, hA, hc, hgc, hgi, hentry, hγ, hγ0, htail, hfree, hu,
    hη0, hηH, hW, hJ, hnew, hS⟩ := hg
  refine ⟨p, β, γ, c, g, fun z => refl (J z), tL, hp, hp0, hpH, hβ, hβ0, hA, hc, hgc, hgi, hentry, hγ, hγ0,
    htail, hfree, hu, hη0, hηH, hW, refl_injective.comp hJ, ?_, ?_⟩
  · rw [← image_image refl J]; exact image_mono hnew
  · rw [← image_image refl J]; exact image_mono hS

/-! ### The reflected trace -/

/-- **The chosen trace of the negated driver is the reflected chosen trace**, almost surely, through the available
lifetime. -/
theorem ae_chosenTrace_neg_eq (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {θ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {hl : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b J θ Q hl W ζ) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω →
      GW2aSingle.chosenTrace (-W) ζ ω t = refl (GW2aSingle.chosenTrace W ζ ω t) := by
  have hflR := Sec7.StripWall.isFlowLineDriver_reflect hb hfl
  filter_upwards [GW2aSingle.ae_chosenTrace h13 hκ hfl, GW2aSingle.ae_chosenTrace h13 hκ hflR,
    Supp8.GB6.ae_driver_zero_continuousOn hflR] with ω h1 h2 h3 t ht
  have hR := LP.isGeneratingTrace_reflect h1.1
  exact IsGeneratingTrace.eq_of_le h2.1 hR h3.2 h3.1 ht

end InteractingSLE.Theorem14.SB.Lf
