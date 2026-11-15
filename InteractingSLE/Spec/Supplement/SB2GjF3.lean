/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CyF3

/-!
# F3's mean identity at the root in the version's chart, from the premise on the base region

Packet PROVE-GW2-GEOM2, round 17 (decision D79). **`hF3_of_premiseB`** is CONDFIN's `Cy.hF3_of_premise` (the `hF3`
input of `Cy.hmean_root_obj`) from F3's mean premise read only on the base region `stageEvent ℓ ∩ {ℓ ≤ relOff}`, which
is NOJUMP's `Nf.SB2LowerRootVersionStatement9F` premise: the live event `FB` lies in that region. CONDFIN's proof.

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Gj

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

omit [StandardBorelSpace Ω] in
/-- **F3's mean identity in the version's chart** from the premise of NOJUMP's root statement. -/
theorem hF3_of_premiseB (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} (hℓ : ℓ ≤ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {A₁ : ℝ≥0 → Ω → Set ℂ}
    (hA₁m : ∀ t, Measurable[mΩ, hittingSigma] (A₁ t)) (hA₁c : ∀ t ω, A₁ t ω ⊆ H ∧ IsOpen (H \ A₁ t ω))
    (hl₁ : ∀ t, IsLocalSet (A₁ t) (WholeField.centredField h u₀) P)
    (hA₁f : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω)
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {β₁ : Ω → BoundaryWord} {Fr FB : Set Ω} (hFrB : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ FB)
    (hFB : ∀ᵐ ω ∂P, ω ∈ FB → fillH (K ω) = A₁ 0 ω)
    (hFBs : ∀ᵐ ω ∂P, ω ∈ FB → ω ∈ Ms.stageEvent κ b jumps E u l k ℓ ∧
      ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))
    (hP8 : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
        ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
            (H \ A₁ 0 ω)) :
    ∀ t, ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ t) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ Fr → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ t ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ t ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
        EqOn (fun z => w₁ z + u₀ z)
          (fun z => (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).mean ((Mo.hullChart (fillH (K ω)) (x₀ ω)).1 z) -
            chiC κ * (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.2 z) (H \ A₁ t ω) := by
  intro t g₁ hg₁
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- the retained set does not depend on the cap
  have hA₁eq : ∀ᵐ ω ∂P, A₁ t ω = A₁ 0 ω := by
    filter_upwards [hA₁f t, hA₁f 0] with ω ht h0
    rw [ht, h0]
    congr 1
    funext ω'
    rw [WalkInf.stageSet_capSpec_of_le hℓ ω' le_rfl, WalkInf.stageSet_capSpec_of_le hℓ ω' le_rfl]
  obtain ⟨g₀, hg₀⟩ := IsLocalSet.exists_isLocalSetMean hh0 (hA₁m 0) (hl₁ 0)
  have hgg := GW4Fix.ae_localSetMean_eq_of_ae_set_eq hh0 (hA₁m t) (hA₁m 0)
    (Eventually.of_forall fun ω => (hA₁c t ω).2) (Eventually.of_forall fun ω => (hA₁c 0 ω).2) hA₁eq hg₁ hg₀
  filter_upwards [hP8 g₀ hg₀, hgg, hA₁eq, hFrB, hFB, hFBs] with ω h8 hg hAt hfr hfb hfs hω w₁ hw₁ hφ
  have hFBω := hfr hω
  rw [hAt] at hw₁ hφ ⊢
  have h8' := h8 (hfs hFBω).1 (hfs hFBω).2 w₁ hw₁ fun φ hφs => by rw [← hg]; exact hφ φ hφs
  intro z hz
  rw [h8' hz, hfb hFBω]
  show _ = (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).mean ((Mo.hullChart (A₁ 0 ω) (x₀ ω)).1 z) -
    chiC κ * (Mo.hullChart (A₁ 0 ω) (x₀ ω)).2.2 z
  rw [RLC.OrdDet.mean_shiftW]
  simp only [Mo.hullChart, Complex.ofReal_zero, sub_zero, sub_add_cancel]

end InteractingSLE.Theorem14.SB.Gj
