/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FpBase
import InteractingSLE.Spec.Supplement.SB2NeRoot

/-!
# The root of `hL`: D34's clause at `R` and the offset bridge

Worker PROVE-SB2-F3LAW (round 4).

* **`ae_heightClause_root`**: for a local set `A₁` (the retained hull `A₁ 0` of B's stage `ℓ`) and a sorted word with
  F3's mean identity (the premise of NOJUMP's `Ne.SB2LowerRootVersionStatement9E`), D34's `Nb.HeightClause` at
  `R = realMax (upperPrefix …)` holds almost surely on the root event `Ne.rootEv … ℓ`, as soon as the root facts
  (hull, free ray right of `R`, admissible heights left of `R`'s entry) hold on an event covering
  `stageEvent ℓ ∩ {ℓ ≤ relOff}` — which `Fp.SB2LowerBaseWordStatement` gives for the base word. This is 9E's heights
  premise.
* **`ae_le_entry_of_entryRead`** (D63): the offset clause `x₀ = Nc.entryRead (fill K) p` of SB2LIFT's
  `Cz.SB2LowerStageVersionStatement6E` (`p = stPt (run ℓ)`) and of NOJUMP's `Ne.SB2LowerRootVersionStatement9E`
  (`p = R`), with the free ray right of `p`, gives `hx₀le : x₀ ≤ Fm.entry (fill K) p` of `Fo.ae_leftAdm_succ_succ`
  (through `Fo.entryRead_eq_entry`).

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Fp

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide Fm

/-- **The offset bridge (D63)**: the offset identity `x₀ = Nc.entryRead (fill K) p` with the free ray right of `p`
gives `x₀ = Fm.entry (fill K) p`, hence the step's `hx₀le`. -/
theorem ae_le_entry_of_entryRead {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω} {K : Ω → Set ℂ}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {x₀ p : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, ω ∈ F → x₀ ω = Nc.entryRead (fillH (K ω)) (p ω))
    (hp : ∀ᵐ ω ∂P, ω ∈ F → FreeRight (fillH (K ω)) (p ω)) :
    ∀ᵐ ω ∂P, ω ∈ F → x₀ ω ≤ entry (fillH (K ω)) (p ω) := by
  filter_upwards [hx, hp] with ω hxω hpω hωF
  rw [hxω hωF, Fo.entryRead_eq_entry (Mo.isHPHull_fillH hKc hKp ω) (hpω hωF)]

open LQGMetric (DistOn TestOn) in
/-- **D34's clause at `R` on the root event** (9E's heights premise), from the root facts. See the module docstring. -/
theorem ae_heightClause_root.{u} {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} (k ℓ : ℕ)
    {A₁ : Ω → Set ℂ} {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hAm : Measurable[mΩ, hittingSigma] A₁) (hloc : IsLocalSet A₁ (WholeField.centredField h u₀) P)
    {β₁ : Ω → BoundaryWord} (hβs : ∀ ω, (β₁ ω).IsSorted)
    (hmean : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens,
      LocalSets.IsLocalSetMean A₁ (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ ω) 0).1 z) -
                QuantumZipper.chiC κ * (Mo.hullChart (A₁ ω) 0).2.2 z) (H \ A₁ ω))
    {G : Set Ω}
    (hroot : ∀ᵐ ω ∂P, ω ∈ G → IsHPHull (A₁ ω) ∧ FreeRight (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω)) ∧
      LeftAdm κ (β₁ ω) (entry (A₁ ω) (realMax (upperPrefix κ b jumps E u l k ω))))
    (hcov : ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      ℓ ≤ Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) → ω ∈ G) :
    ∀ᵐ ω ∂P, ω ∈ Ne.rootEv κ b jumps E u l k ℓ →
      Nb.HeightClause κ b jumps (A₁ ω) ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) (β₁ ω) := by
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨g₁, hg₁⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 hAm hloc
  filter_upwards [Sec7.IsLocalSetMean.ae_tendsto_zero_of_real hh0 hAm hloc hg₁, hmean g₁ hg₁, hg₁.2.1, hroot, hcov]
    with ω hw hid hharm hrω hcovω hωr
  obtain ⟨hev, hoff, -, -⟩ := hωr
  obtain ⟨hHP, hfree, hL⟩ := hrω (hcovω hev hoff.ge)
  obtain ⟨v, hv, hrep⟩ := hharm
  exact heightClause_of_meanIdentity hκ hHP hfree (hβs ω) hu₀ (hid hev v hv hrep) (hw v hv hrep) hL

end InteractingSLE.Theorem14.SB.Fp
