/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkInfChart
import InteractingSLE.Spec.Supplement.WalkInfLocal
import InteractingSLE.Spec.Exist.Param12Canonical

/-!
# Theorem 1.4: verified specializations of the walk-prefix inputs

Packet PROVE-T14-WALKSIDE2. The chart-version inputs follow directly from `WalkInf`.
The locality results below use the distinct `WalkInf.PrefixMarkedLocalOnStatement`:
they apply at unstopped flow instructions, exactly as required by the existing
`WalkInf.walkPrefixSideStatement_of_on` consumer. They do not assert the unrestricted
`WalkSide.PrefixMarkedLocalStatement`; that statement also quantifies over continuation
instructions and indices beyond the walk. See the packet handoff for the scope obstruction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Theorem14.WalkSide2

/-- The right walk's exact prefix-chart version input. -/
theorem prefixChartVersionStatement_right :
    WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true :=
  WalkInf.prefixChartVersionStatement_of_mem
    ⟨le_rfl, by linarith only [Real.pi_pos]⟩ true

/-- The left walk's exact prefix-chart version input. -/
theorem prefixChartVersionStatement_left :
    WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false :=
  WalkInf.prefixChartVersionStatement_of_mem
    ⟨by linarith only [Real.pi_pos], le_rfl⟩ false

/-- Prefix locality at the right walk's flow instructions, from Theorems 1.2–1.3.
This is the restricted `On` statement, with its original name and conditions preserved. -/
theorem prefixMarkedLocalOnStatement_right_of_thm12_thm13
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    WalkInf.PrefixMarkedLocalOnStatement.{u} (-(Real.pi / 2)) true :=
  WalkInf.prefixMarkedLocalOnStatement_of_thm12_thm13
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
    ⟨le_rfl, by linarith only [Real.pi_pos]⟩ true

/-- Prefix locality at the left walk's flow instructions, from Theorems 1.2–1.3.
This is the restricted `On` statement, with its original name and conditions preserved. -/
theorem prefixMarkedLocalOnStatement_left_of_thm12_thm13
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    WalkInf.PrefixMarkedLocalOnStatement.{u} (Real.pi / 2) false :=
  WalkInf.prefixMarkedLocalOnStatement_of_thm12_thm13
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
    ⟨by linarith only [Real.pi_pos], le_rfl⟩ false

end InteractingSLE.Theorem14.WalkSide2
