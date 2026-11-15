/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15ReadyLeft
import InteractingSLE.Spec.Sec7.SideC16Laws
import InteractingSLE.Spec.Sec7.SideC16Avoid

/-! # The physical word context supplies the pocket-side facts

PROVE-SIDE-COLLAR2. Derive the outer frontier, common prefix and
counterflow avoidance from the landed two-angle results. Prop. 4.11
comes from Part A and Lemma 4.7Q, independently of Theorems 1.2/1.3.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Ctx
open Current Sec7 Sec7.StripWall Sec7.PocketWordIn Sec7.PocketCoord
  Sec7.PocketCoupling Sec7.Lemma71I

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The complete physical context supplies the side of every ready change
pocket. All three frontier premises of C15 are conclusions here. -/
theorem ae_changePocket_left_of_physical_context
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
    (hθL : x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
    (hvL : ∀ q, IsWallVersion x.measure
      (x.experiment (StripSys.betaSpec (StripSys.rt (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
    (hβc : ∀ ω, Continuous (x.outerWall ω))
    (hβ0 : ∀ ω, x.outerWall ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂x.measure,
      IsGeneratingTrace (x.experiment StripSys.leftExtremalSpec 0 ω).1 ⊤ (x.outerWall ω))
    (hηc : ∀ ω, ContinuousOn (x.curve ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂x.measure,
      IsGeneratingTrace (fun t => x.driver t ω) ⊤ (fun t : ℝ≥0 => x.curve ω t)) :
    let d := wordSafeObjects i x hS
    ∀ j : SideTest Ω, j.Ready d → ∀ᵐ ω ∂x.measure, ω ∈ j.event →
      changePocket (x.rightWall ω) (x.leftWall j.seed ω) (StripSys.rt j.seed) ⊆
        leftSideOf (range (x.rightWall ω)) := by
  dsimp only
  let d := wordSafeObjects i x hS
  have hreg := WordSafe.isTwoAngle_regTwo hS hcumL hcumR
  obtain ⟨he, hEe⟩ := WordSafe.regTwo_leftExtremal hS hcumL hcumR
  have hβtr' : ∀ᵐ ω ∂x.measure,
      IsGeneratingTrace (WordSafe.regTwo (16 / i.kappa) x.boundary x.jumps x.measure x.experiment
        StripSys.leftExtremalSpec 0 ω).1 ⊤ (x.outerWall ω) := by
    filter_upwards [hβtr, hEe] with ω ht heq
    rwa [heq]
  have hβ := WordSafe.ae_isSimpleProper_leftExtremal hreg hcumL hcumR he hβc hβ0 hβtr'
  have hav := WordSafe.ae_avoidance prop411_for_initial_pockets hS hcumL hcumR hβtr hηtr
  intro j hj
  have hvLp : IsWallVersion x.measure
      (x.experiment (StripSys.betaSpec (StripSys.rt j.seed) x.thetaL))
      (StripSys.rt j.seed) (x.leftWall j.seed) := by
    simpa only [positiveSeed_of_pos hj.1] using hvL j.seed
  have hvLp' := WordSafe.isWallVersion_regTwo hS hcumL hcumR
    StripSys.pi_div_two_mem_Icc (Ioc_subset_Icc_self hθL) hvLp
  have hjoin := WordSafe.ae_eq_leftExtremal_of_le cond44 hreg hcumL hcumR
    (Ioc_subset_Icc_self hθL) (StripSys.rt j.seed)
    (WordSafe.isRegularDriver_regTwo_twoAngle _ _ _ 0)
    hvLp'.ae_isGeneratingTrace hβtr'
  have hLβ : ∀ᵐ ω ∂x.measure,
      x.leftWall j.seed ω (StripSys.rt j.seed) = x.outerWall ω (StripSys.rt j.seed) :=
    hjoin.mono fun _ h => h _ le_rfl
  exact j.ae_changePocket_subset_leftSideOf_of_ready (d := d) hj hβ hLβ hηc hav

end InteractingSLE.Wire.T12Ctx
