/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkLeafLaunch
import InteractingSLE.Spec.Supplement.WalkUnionMeanAE
import InteractingSLE.Spec.Exist.Param12Canonical

/-!
# Theorem 1.4's walk leaves: consequences of the launch locality

Packet PROVE-T14-WALK. With the launch-locality leaves proved (`WalkLeafLaunch`), the per-stage kernel input, the R58
walk statement and the marked union of the two walks follow from Theorems 1.2–1.3 alone (R48 allows them for Theorem
1.4):

* **`walkStageLaunchLocalStatement_right_of_roots`**, `…_left_of_roots`: the two leaves from the per-word frozen-form
  roots `Exist.Theorem12Statement`, `Exist.Theorem13Statement` of the expanded wiring (`Wire/Thm1415Current14`), through
  `Exist.Param12.theorem12ParamStatement_of_thm12_thm13`;
* **`walkMarkedLocalRegAEStatement_of_thm12_thm13`**: each walk's retained past is a marked local set (R58 form);
* **`gw3UnionLawBetweenRegStatement_of_unionMean`**: GW3's union law on the between components from Theorems 1.2–1.3
  and the single remaining walk-law leaf `WalkLaw.WalkUnionMeanRegAEStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

universe u

namespace InteractingSLE.Theorem14.WalkLeaf

open Exist.Staged

/-- The right walk's launch leaf from the wiring's roots. -/
theorem walkStageLaunchLocalStatement_right_of_roots (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : WalkLaw.WalkStageLaunchLocalStatement.{u} (-(Real.pi / 2)) true :=
  walkStageLaunchLocalStatement_right_of_thm12_thm13 (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)
    h13

/-- The left walk's launch leaf from the wiring's roots. -/
theorem walkStageLaunchLocalStatement_left_of_roots (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : WalkLaw.WalkStageLaunchLocalStatement.{u} (Real.pi / 2) false :=
  walkStageLaunchLocalStatement_left_of_thm12_thm13 (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)
    h13

/-- **Each walk's retained past is a marked local set** (R58 form), from Theorems 1.2–1.3. -/
theorem walkMarkedLocalRegAEStatement_of_thm12_thm13 (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) :
    WalkLaw.WalkMarkedLocalRegAEStatement.{u} θ right :=
  WalkLaw.walkMarkedLocalRegAEStatement_of_kernel hθ (WalkLaw.pastDetRegStatement_of_thm12_thm13 h12p h13)
    (WalkLaw.walkStageKernelLocalStatement_of_launch hθ
      (walkStageLaunchLocalStatement_of_thm12_thm13 h12p h13 hθ right))

/-- **GW3's union law on the between components from Theorems 1.2–1.3 and the union mean** (the launch-locality
leaves are discharged). -/
theorem gw3UnionLawBetweenRegStatement_of_unionMean (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hM : WalkLaw.WalkUnionMeanRegAEStatement.{u}) :
    GW3Between.GW3UnionLawBetweenRegStatement.{u} :=
  WalkLaw.gw3UnionLawBetweenRegStatement_of_kernel h12p h13
    (WalkLaw.walkStageKernelLocalStatement_right_of_launch
      (walkStageLaunchLocalStatement_right_of_thm12_thm13 h12p h13))
    (WalkLaw.walkStageKernelLocalStatement_left_of_launch
      (walkStageLaunchLocalStatement_left_of_thm12_thm13 h12p h13))
    hM

end InteractingSLE.Theorem14.WalkLeaf
