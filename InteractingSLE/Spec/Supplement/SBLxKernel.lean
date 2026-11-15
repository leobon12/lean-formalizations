/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLxStep
import InteractingSLE.Spec.Supplement.SBLwReg

/-!
# SB3's stage step under one retained conditional law

Packet PROVE-T14-SBLEAVES3. Under a probability measure `Q` (the walk's retained kernel at a launch, the measure of
`HasRelStageOrderingE`), almost surely S1 holds for the retained prefix `A = p([0, 1])` together with every finite
truncation of the next lower piece: `ae_isOneSided_stage`. The inputs are exactly the relative stage ordering with
SB2(1)'s entry (`HasRelStageOrderingE`, from `ae_hasRelStageOrderingE_of_sb2UpperLaunchEntry`), Theorem 1.3 (pathwise
regularity of the two relative flow lines, `Lw.ae_flowLine_regular`), the launch chart as a left entry chart at every
entry value (`isLeftEntryChart_shift_of_runChart_entry`), its boundary map, and the facts carried over from the
ambient law (S1 for `A`, the upper flow's continuity and start, the frozen past `L = min(A ∩ ℝ)`, a positive lower
lifetime).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lx

open Lv Lw

/-- **SB3's stage step under the retained law.** Under `Q`, with the relative stage ordering and SB2(1)'s entry
(`HasRelStageOrderingE` at the frozen `L₀ = min(A ∩ ℝ)`), almost surely S1 holds for `A ∪ g(α([0, d]))` and every
available upper stop `a`, for every available truncation `d` of the next lower piece `α` (the chosen trace of the staged
driver `(W, ζL)`), when that piece has positive lifetime. -/
theorem ae_isOneSided_stage (h13 : Exist.Theorem13Statement.{u}) {κ ψ u : ℝ} (hκ : 0 < κ) {Ω : Type u}
    [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens} {c : Chart}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {L : Ω → ℝ} {W : ℝ≥0 → Ω → ℝ} {ζL : Ω → ℝ≥0∞}
    {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = u) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hR : HasRelStageOrderingE κ ψ Q h c η ζ L (realMin (p '' Icc 0 1)) W ζL)
    (hc : ∀ m : ℝ, IsLeftEntryValue c (realMin (p '' Icc 0 1)) m →
      IsLeftEntryChart ((fun z => z - (u : ℂ)) '' (p '' Icc 0 1)) (realMin (p '' Icc 0 1) - u) (shiftChart c u m))
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hL : ∀ᵐ ω ∂Q, L ω = realMin (p '' Icc 0 1))
    (hη : ∀ᵐ ω ∂Q, ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω} ∧ η ω 0 = u)
    (hS1 : ∀ᵐ ω ∂Q, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (p '' Icc 0 1) (η ω) a)
    (hζL : ∀ᵐ ω ∂Q, 0 < ζL ω) :
    ∀ᵐ ω ∂Q, ∀ d a : ℝ≥0, (d : ℝ≥0∞) ≤ ζL ω → (a : ℝ≥0∞) ≤ ζ ω →
      IsOneSided (p '' Icc 0 1 ∪ g '' (GW2aSingle.chosenTrace W ζL ω '' Icc 0 d)) (η ω) a := by
  obtain ⟨b', jumps', h', m, ηr, ζr, -, -, -, hm, hent, hα, hηr, hlink, hord⟩ := hR
  have hcm := hc m hent
  filter_upwards [ae_flowLine_regular h13 hκ hα, ae_flowLine_regular h13 hκ hηr, hlink, hord, hL, hη, hS1, hζL]
    with ω hαω hηrω hlinkω hordω hLω hηω hS1ω hζLω
  intro d a hd ha
  obtain ⟨-, hα0, hαH, -, -⟩ := hαω
  obtain ⟨hηrc, hηr0, hηrH, hηrd, hηrt⟩ := hηrω
  rw [hLω] at hlinkω
  exact isOneSided_union_of_link hp hp0 hpf hpH hηω.2 hηω.1 ha (hS1ω) hcm hgc hgi hηrc hηr0 hηrH hηrd hηrt hlinkω
    hm hα0 (fun t ht => hαH t ((ENNReal.coe_le_coe.2 ht).trans hd)) hd hζLω hordω

end InteractingSLE.Theorem14.SB.Lx
