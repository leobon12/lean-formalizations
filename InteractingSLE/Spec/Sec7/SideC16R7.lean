/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC14R7
import InteractingSLE.Spec.Sec7.SideC15Installed
import InteractingSLE.Spec.Sec7.SideC9InitialWord

/-! # General pocket-mean producers supply R.7's initial heights

PROVE-SIDE-COLLAR2. The first theorem is independent of side tests,
strip indices and pocket shape. It consumes the proved mean producer,
using the tested mean itself to supply existence. The second theorem
specializes it to a ready test's literal native word, including its
unclamped marks. No initial mean existence assumption is needed.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.SideC16
open LocalSets PocketStop PocketStopSide Aux119Heights

/-- A general pocket-mean producer gives R.7's `hInit` for every version,
for either traversal and any exceptional selector. The test's own mean
provides the input to the producer; no separate existence premise enters. -/
theorem r7InitialHeights_of_initialWordProducer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {C : Ω → Set ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {c : Ω → Chart} {a : ℝ} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    (hBm : Measurable[mΩ, hittingSigma] (liveExt A γ C (fun _ => ∅) 0))
    (hhm : Measurable h₀) (hc : ∀ ω ∈ A, IsDomainChart (C ω) (c ω))
    (hMean : ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (liveExt A γ C (fun _ => ∅) 0) h₀ P g₀ →
      ∃ G : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (liveExt A γ C (fun _ => ∅) 0) h₀ P G ∧
        ∀ᵐ ω ∂P, ω ∈ A → ∀ z ∈ C ω,
          harmRep (G ω) (H \ liveExt A γ C (fun _ => ∅) 0 ω) z + u z + chiC κ * (c ω).2.2 z =
            MartChar.meanExt κ ρL ρR 0 (xL ω) (xR ω) ((c ω).1 z) - a)
    (X₀ : Ω → Set ℂ) : R5Wall.R7InitialHeights κ ρL ρR P A γ C xL xR c a h₀ u X₀ := by
  intro g₀ hg₀
  obtain ⟨G, hG, hFormula⟩ := hMean g₀ hg₀
  exact SideC14.r7InitialHeights_of_initialWordFormula hBm hhm hc hG hFormula X₀ g₀ hg₀

end InteractingSLE.Sec7.SideC16

namespace InteractingSLE.Wire.Current.SideTest
open LocalSets Sec7 Sec7.SideC16 Sec7.PocketStop Sec7.PocketTraversal
  Sec7.PocketStopSide Sec7.PocketAdapt Sec7.Aux119Heights

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- R.7's exact initial-height predicate at the test's native word size.
The two cases select `nL = 0` or `nL = 1`; both have `nR = 1` in
`R7InitialHeights`'s convention of `nL + 1` and `nR + 1` marks. -/
def r7InitialHeights (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (a : ℝ) (X₀ : Ω → Set ℂ) : Prop :=
  match j with
  | ⟨seed, G, A, ψ, inf, false⟩ =>
    let j : SideTest Ω := ⟨seed, G, A, ψ, inf, false⟩
    let t := j.target i d
    R5Wall.R7InitialHeights (nL := 0) (nR := 1) t.kappa t.rhoL t.rhoR d.measure
      t.event t.curve t.domain t.marksL t.marksR t.baseChart a t.zeroField t.harmonic X₀
  | ⟨seed, G, A, ψ, inf, true⟩ =>
    let j : SideTest Ω := ⟨seed, G, A, ψ, inf, true⟩
    let t := j.target i d
    R5Wall.R7InitialHeights (nL := 1) (nR := 1) t.kappa t.rhoL t.rhoR d.measure
      t.event t.curve t.domain t.marksL t.marksR t.baseChart a t.zeroField t.harmonic X₀

/-- The native producer on a ready test supplies R.7's initial heights
at the original (unclamped) marks. This is the exact `R7InitialHeights`
interface, independent of whether the traversal is finite or infinite. -/
theorem r7InitialHeights_of_nativeMeanProducer
    {i : BothLow} {d : WordObjects Ω} [IsProbabilityMeasure d.measure]
    {j : SideTest Ω} (hj : j.Ready d) (a : ℝ)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hBm : Measurable[mΩ, hittingSigma]
      (liveExt (j.target i d).event (j.target i d).curve (j.target i d).domain (fun _ => ∅) 0))
    (hhm : Measurable (j.target i d).zeroField)
    (hMean : ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure g₀ →
      ∃ G : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure G ∧
        ∀ᵐ ω ∂d.measure, ω ∈ j.event → ∀ z ∈ (j.target i d).domain ω,
          harmRep (G ω) (H \ j.capacityReference i d 0 ω) z + (j.target i d).harmonic z +
            chiC (j.target i d).kappa * ((j.target i d).baseChart ω).2.2 z =
          j.initialWordExtension i d ω (((j.target i d).baseChart ω).1 z) - a)
    (X₀ : Ω → Set ℂ) :
    j.r7InitialHeights i d a X₀ := by
  have hSet : liveExt (j.target i d).event (j.target i d).curve (j.target i d).domain
      (fun _ => ∅) 0 = j.capacityReference i d 0 := by
    rw [Sec7.PocketStopSide.liveExt_zero_eq_eventFilled (j.isDrivenCurve_target hj)]
    rw [capacityReference, original_filling_zero, target_event]
  have hc : ∀ ω ∈ (j.target i d).event, IsDomainChart ((j.target i d).domain ω)
      ((j.target i d).baseChart ω) := fun _ hω => j.isDomainChart_baseChart hj hRc hLc hω
  have hMean' : ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (liveExt (j.target i d).event (j.target i d).curve (j.target i d).domain
        (fun _ => ∅) 0) (j.target i d).zeroField d.measure g₀ →
      ∃ G : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (liveExt (j.target i d).event (j.target i d).curve (j.target i d).domain
          (fun _ => ∅) 0) (j.target i d).zeroField d.measure G ∧
        ∀ᵐ ω ∂d.measure, ω ∈ (j.target i d).event → ∀ z ∈ (j.target i d).domain ω,
          harmRep (G ω) (H \ liveExt (j.target i d).event (j.target i d).curve (j.target i d).domain
            (fun _ => ∅) 0 ω) z + (j.target i d).harmonic z +
            chiC (j.target i d).kappa * ((j.target i d).baseChart ω).2.2 z =
          MartChar.meanExt (j.target i d).kappa (j.target i d).rhoL (j.target i d).rhoR 0
            ((j.target i d).marksL ω) ((j.target i d).marksR ω) (((j.target i d).baseChart ω).1 z) - a := by
    intro g₀ hg₀
    rw [hSet] at hg₀
    obtain ⟨G, hG, hFormula⟩ := hMean g₀ hg₀
    refine ⟨G, hSet.symm ▸ hG, ?_⟩
    rw [hSet]
    filter_upwards [hFormula] with ω hω hA z hz
    have hA' : ω ∈ j.event := by simpa only [target_event] using hA
    have hWord := j.initialWordExtension_eq_raw_of_signed_marks hj hA
      (j.initial_marks_signed_of_ready hj hA).1 (j.initial_marks_signed_of_ready hj hA).2
    rw [hω hA' z hz, hWord]
  rcases j with ⟨seed, G, A, ψ, inf, two⟩
  cases two <;> exact r7InitialHeights_of_initialWordProducer hBm hhm hc hMean' X₀

end InteractingSLE.Wire.Current.SideTest
