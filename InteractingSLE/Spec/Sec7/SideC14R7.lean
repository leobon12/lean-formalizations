/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5WallCover
import InteractingSLE.Spec.Sec7.R5EnlMean
import InteractingSLE.Spec.Sec2.MartingaleCoupling

/-!
# General initial pocket means supply R.7's initial heights

PROVE-SIDE-COLLAR2. Use one actual exterior mean's interior word formula
on a general pocket, then conditional-mean uniqueness and the bounded
harmonic extension to obtain the limits for every version. There is no
restriction on the physical landing or the exceptional selector.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.SideC14

open LocalSets PocketStop PocketStopSide Aux119Heights

/-- One exterior mean with the interior force-word formula gives all
versions of R.7's initial heights, for any change-pocket/traversal data. -/
theorem r7InitialHeights_of_initialWordFormula
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C : Ω → Set ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {a : ℝ} {h₀ G : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hBm : Measurable[mΩ, hittingSigma] (liveExt A γ C (fun _ => ∅) 0))
    (hhm : Measurable h₀)
    (hc : ∀ ω ∈ A, IsDomainChart (C ω) (c ω))
    (hG : IsLocalSetMean (liveExt A γ C (fun _ => ∅) 0) h₀ P G)
    (hFormula : ∀ᵐ ω ∂P, ω ∈ A → ∀ z ∈ C ω,
      harmRep (G ω) (H \ liveExt A γ C (fun _ => ∅) 0 ω) z + u z +
          chiC κ * (c ω).2.2 z =
        MartChar.meanExt κ ρL ρR 0 (xL ω) (xR ω) ((c ω).1 z) - a)
    (X₀ : Ω → Set ℂ) :
    R5Wall.R7InitialHeights κ ρL ρR P A γ C xL xR c a h₀ u X₀ := by
  intro g₀ hg₀
  have heq : g₀ =ᵐ[P] G := R5Enl.ae_eq_of_isCondZeroBoundaryGFF_of_le le_rfl
    (germSigma_le hBm hhm) hhm hg₀.1 hG.1 hg₀.2.2 hG.2.2
  filter_upwards [heq, hFormula] with ω heqω hFormulaω hω x hx _hX
  have hu := MartChar.isBoundedHarmonicExtension_meanExt κ ρL ρR 0 (xL ω) (xR ω)
  simp only [sub_zero] at hu
  have hlim := (hu.2.2 x hx).sub_const a
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hCy : (c ω).2.1 y ∈ C ω := (hc ω hω).inv_mem hy
  rw [heqω, hFormulaω hω _ hCy, (hc ω hω).fwd_inv hy]

end InteractingSLE.Sec7.SideC14
