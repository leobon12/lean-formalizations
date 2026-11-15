/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CyRoot
import InteractingSLE.Spec.Supplement.OrdFstShift
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaVersions
import InteractingSLE.Spec.Supplement.WalkInfLaunch

/-!
# F3's mean identity at the root, read in the version's chart

Packet PROVE-SB2-CONDFIN, round 13 (D74, item 1). `Cy.hmean_root_obj` takes F3's mean identity of the retained set
`A₁ t` in the version's chart `Mo.hullChart (fill K) x₀` with the version's word `shiftW x₀ β₁`, on the root event.
NOJUMP's `Ne.SB2LowerRootVersionStatement8` takes it as a premise in the offset-`0` chart of `A₁ 0` with the word
`β₁`, on the stage event. **`hF3_of_premise`** turns the second into the first: `A₁ t = A₁ 0` almost surely (the
capped program's explored set before `ℓ` does not see the cap, `WalkInf.stageSet_capSpec_of_le`), the two local-set
means then agree almost surely (`GW4Fix.ae_localSetMean_eq_of_ae_set_eq`), on the root event `fill K = A₁ 0`, and
the chart and word shift by `x₀` together (`RLC.OrdDet.mean_shiftW`). So the root line mean's only inputs besides
Theorems 1.2–1.3 are the premises and outputs of NOJUMP's statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cy

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

omit [StandardBorelSpace Ω] in
/-- **F3's mean identity in the version's chart** from the premise of NOJUMP's root statement. -/
theorem hF3_of_premise (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
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
    (hFBs : ∀ᵐ ω ∂P, ω ∈ FB → ω ∈ Ms.stageEvent κ b jumps E u l k ℓ)
    (hP8 : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
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
  have h8' := h8 (hfs hFBω) w₁ hw₁ fun φ hφs => by rw [← hg]; exact hφ φ hφs
  intro z hz
  rw [h8' hz, hfb hFBω]
  show _ = (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).mean ((Mo.hullChart (A₁ 0 ω) (x₀ ω)).1 z) -
    chiC κ * (Mo.hullChart (A₁ 0 ω) (x₀ ω)).2.2 z
  rw [RLC.OrdDet.mean_shiftW]
  simp only [Mo.hullChart, Complex.ofReal_zero, sub_zero, sub_add_cancel]

end InteractingSLE.Theorem14.SB.Cy
