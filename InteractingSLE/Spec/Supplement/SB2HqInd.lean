/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2HqAe
import InteractingSLE.Spec.Supplement.SB2JxShift

/-!
# SB2(1)'s late (S) line mean, part 13: FIN's `hind₁` in its final form, and the chart inverse off the retained set

Packet PROVE-T14-SB2DRV (round 11):

* **`shift_inv_mem_sdiff`**: when a conformal chart has domain `ℍ \ X`, its seed-shifted inverse maps `ℍ` into
  `ℍ \ (X − u)` (FIN's `hlift` reads the configuration's `EqOn` there);
* **`ae_hind₁_line`** (FIN's `hind₁`): almost surely on the launch event and a type cell, for ANY `LΨ` whose imaginary
  part is the seed-shifted chart's lift off the translated walk fill and ANY bounded harmonic extension `G₀` of the
  typed cell word, every harmonic representative `w₁` of the translated walk-fill mean satisfies
  `w₁ + u₀' = G₀ ∘ Ψ − χ Im LΨ` off the translated walk fill, `Ψ` the seed-shifted chart (`ae_walkFill_translate_rep`
  + `eqOn_bhe_typed_word` + `Ψ z = c.1 (z + u)`, `Im LΨ z = c.2.2 (z + u)`).

**R48.** Theorems 1.2–1.3 appear only as hypotheses (through `ae_walkFill_translate_rep`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets Sec6
open Supp8.Q3Chain (initJumps)

/-- **The seed-shifted chart inverse maps `ℍ` off the translated retained set.** -/
theorem shift_inv_mem_sdiff {c : Chart} (hc : c.IsConformal) {X : Set ℂ} (hdom : (c.dom : Set ℂ) = H \ X) (u : ℝ)
    {y : ℂ} (hy : y ∈ H) : (Lw.shiftChart c u 0).2.1 y ∈ H \ (fun z : ℂ => z + (-u : ℝ)) '' X := by
  rw [← image_translate_H_sdiff, ← hdom, hc.coe_dom]
  refine ⟨c.2.1 (y + ((0 : ℝ) : ℂ)), ⟨y + ((0 : ℝ) : ℂ), by simpa using hy, rfl⟩, rfl⟩

section Ind

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **FIN's `hind₁` in its final form** (Theorems 1.2–1.3 as hypotheses). -/
theorem ae_hind₁_line (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {A' : Ω → Set ℂ} (hA'H : ∀ ω, A' ω ⊆ H)
    (hA'm : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U})
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω)
    {u₀' : ℂ → ℝ} (hrel : EqOn u₀' (fun z => u₀ (z + u) + ψ * chiC κ) H)
    {gW : Ω → DistOn upperHalfPlaneOpens}
    (hgW : IsLocalSetMean (walkFill κ b jumps E k A') (WholeField.centredField h u₀) P gW) (F : Set Ω)
    (wt : WordType) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → ω ∈ wordTypeCell κ ψ I.word F wt →
      ∀ (LΨ : ℂ → ℂ) (G₀ : ℂ → ℝ),
      EqOn (Lw.shiftChart (I.chart ω) u 0).2.2 (fun z => (LΨ z).im)
        (H \ (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω) →
      IsBoundedHarmonicExtension (forceBoundaryData κ (typedRhoL wt) (typedRhoR wt) (cellXL κ ψ I.word wt ω)
        (cellXR κ ψ I.word wt ω)) (initJumps (cellXL κ ψ I.word wt ω) (cellXR κ ψ I.word wt ω)) G₀ →
      ∀ w₁ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₁ (H \ (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω) →
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω →
        Exist.flowField (-(-u)) 0 (gW ω) φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀' z)
        (fun z => G₀ ((Lw.shiftChart (I.chart ω) u 0).1 z) - chiC κ * (LΨ z).im)
        (H \ (fun z : ℂ => z + (-u : ℝ)) '' walkFill κ b jumps E k A' ω) := by
  filter_upwards [ae_walkFill_translate_rep h12p h13 HP I hu₀ hA'H hA'm hA'ae hrel hgW,
    ae_dom_eq_H_sdiff_walkFill HP I hA'ae, I.field] with ω hrepω hdomω hf hl hcell LΨ G₀ hEq hG₀ w₁ hw₁ hrep z hz
  have hpc := (hf hl).1
  have hc := isConformal_chart I ω
  have e1 := hrepω hl w₁ hw₁ hrep hz
  have hzu : z + (u : ℂ) ∈ ((I.chart ω).dom : Set ℂ) := by
    rw [hdomω hl]
    refine ⟨?_, fun hW => hz.2 ⟨z + u, hW, by push_cast; ring⟩⟩
    show 0 < (z + (u : ℂ)).im
    have : 0 < z.im := hz.1
    simpa using this
  rw [hc.coe_dom] at hzu
  obtain ⟨y, hy, hyz⟩ := hzu
  have hΨ : (Lw.shiftChart (I.chart ω) u 0).1 z = (I.chart ω).1 (z + u) := by
    show (I.chart ω).1 (z + u) - ((0 : ℝ) : ℂ) = _
    simp
  have hΨH : (I.chart ω).1 (z + u) ∈ H := by rw [← hyz, hc.2.2 y hy]; exact hy
  have hG₀' : IsBoundedHarmonicExtension (forceBoundaryData κ (typedRhoL wt) (typedRhoR wt)
      (FCDet.typeXL κ ψ wt.1 wt.2.1 (typedRhoL wt) (typedRhoR wt) (I.word ω))
      (FCDet.typeXR κ ψ wt.1 wt.2.1 (typedRhoL wt) (typedRhoR wt) (I.word ω)))
      (forceJumpSet (FCDet.typeXL κ ψ wt.1 wt.2.1 (typedRhoL wt) (typedRhoR wt) (I.word ω))
        (FCDet.typeXR κ ψ wt.1 wt.2.1 (typedRhoL wt) (typedRhoR wt) (I.word ω))) G₀ := by
    rw [← Supp8.Q3Chain.coe_initJumps]
    exact hG₀
  have hG := eqOn_bhe_typed_word HP.kappa_pos (mem_typeSet_of_mem_wordTypeCell hcell) hpc hG₀' _ hΨH
  have hL : (LΨ z).im = (I.chart ω).2.2 (z + u) := (hEq hz).symm
  show w₁ z + u₀' z = G₀ ((Lw.shiftChart (I.chart ω) u 0).1 z) - chiC κ * (LΨ z).im
  rw [hΨ, hG, hL]
  exact e1

end Ind

end InteractingSLE.Theorem14.SB.Lv
