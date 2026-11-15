/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovTop
import InteractingSLE.Spec.Sec7.R5FreshBase

/-!
# The late seed-interval landings from the counterflow's no-return

Packet PROVE-COLLAR-COVER. PROVE-R5-FRESHTIP reduced its seed-interval landing input `R5Fresh.R7SeedLand(Inf)` to the
counterflow's no-return (`R5Fresh.r7SeedLand(Inf)_of_noReturn`: almost surely the counterflow does not come back to its
start `0` at a positive time). At the late pockets:

* **`lateSeedLand_of_noReturn`**: `ColCov.LateSeedLand i d` from `∀ᵐ ω, ∀ t > 0, d.curve ω t ≠ 0`;
* **`colCovSeedInput_of_noReturn`**: the tops' `ColCovSeedInput` from the no-return of every word's counterflow.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses (the no-return is to be supplied by `GW4Ident.CounterflowNoReturnStatement` through
`CfNoReturn.SeedGermStatement`, never through Theorem 1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest R5Fresh

/-- **`LateSeedLand` from the counterflow's no-return** (FRESHTIP's `r7SeedLand(Inf)_of_noReturn` at the late
pockets). -/
theorem lateSeedLand_of_noReturn {Ω : Type} [MeasurableSpace Ω] {i : BothLow} {d : WordObjects Ω}
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hnr : ∀ᵐ ω ∂d.measure, ∀ t : ℝ, 0 < t → d.curve ω t ≠ 0) : LateSeedLand i d := by
  intro j hj q _
  have hnr' : ∀ᵐ ω ∂d.measure, ω ∈ j.event → ∀ t : ℝ, 0 < t → d.curve ω t ≠ 0 := by
    filter_upwards [hnr] with ω hω _
    exact hω
  refine ⟨fun hIf => ?_, fun hIf => ?_⟩
  · obtain ⟨hcfg, hψ, hc, hdom, heq⟩ := ready_bounded_facts (i := i) hj hRc (hLc j.seed) hIf
    exact r7SeedLand_of_noReturn (W' := d.driver) hcfg hψ hc hdom heq (fun _ => rfl) (fun _ => rfl) hnr'
  · obtain ⟨hcfg, hψ, hc, hdom, heq⟩ := ready_inf_facts (i := i) hj hRc (hLc j.seed) hIf
    exact r7SeedLandInf_of_noReturn (W' := d.driver) hcfg hψ hc hdom heq (fun _ => rfl) (fun _ => rfl) hnr'

/-- **The tops' `ColCovSeedInput` from the no-return of every word's counterflow** (walls' continuity from the word
context's wall versions). -/
theorem colCovSeedInput_of_noReturn
    (hnr : ∀ (Ωw : BothLow → Type) [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
      (baseWord : ∀ i, Now.StripObjects (Ωw i)) [∀ i, IsProbabilityMeasure (baseWord i).measure]
      (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
      (_ : T12Asm3.PhysCtx Ωw baseWord hWordb) (index : BothLow),
      ∀ᵐ ω ∂(Relay.words T12Asm2.cond44Holds baseWord hWordb index).measure, ∀ t : ℝ, 0 < t →
        (Relay.words T12Asm2.cond44Holds baseWord hWordb index).curve ω t ≠ 0) :
    ColCovSeedInput := by
  intro Ωw _ _ baseWord _ hWordb hC index
  exact lateSeedLand_of_noReturn (hC.hWordvα index).continuous (fun q => (hC.hWordvL index q).continuous)
    (hnr Ωw baseWord hWordb hC index)

end InteractingSLE.Sec7.ColCov
