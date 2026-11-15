/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3DwEntr
import InteractingSLE.Spec.Supplement.SBS3DwVmSafe
import InteractingSLE.Spec.Supplement.SBS3DxDrvLineIfaceR
import InteractingSLE.Spec.Supplement.SBS3DxWdFinal
import InteractingSLE.Spec.Supplement.SBS3DxSBLuAmb
import InteractingSLE.Spec.Supplement.SBS3DzSB4RSymTop
import InteractingSLE.Spec.Supplement.SB2YtFin
import InteractingSLE.Spec.Wire.T14Asm6

/-!
# Decision D22 wired: SB2(1), SB3 and Theorem 1.4 with upper angles `ψ ≤ π/2`

Worker PROVE-R6-CORNER (round 8, ruling R121). The successor chain (`SBS3Dw*`, `SBS3Dx*`, `SBS3Dy*`, `SBS3Dz*`)
threads `ψ ≤ π/2` from Lemma S3 in SB2(1)'s form through SB2(1)'s statements, SB3, the relative SB3 instances and
SB4's leaves. Here:

* **bridges**: each all-angle statement gives its bounded successor (`…LeStatement_of_all`), so every all-angle
  result already proved still applies;
* **`Vm.sb2LineVersionRLeStatement_of_thm`**: SB2(1)'s version half (bounded) from Theorems 1.2–1.3 and
  PROVE-AUX61-NOJUMP's two remaining inputs `Vh.SB2RemainderLifeLeStatement`, `Vk.SB2RelEndpointLeStatement`;
  Lemma S3 enters as **`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`** (round 6's
  `S3.Asm.ae_entranceNoCommonArc_of_le`, so the wide-angle residual `SB2EntranceWideAngleStatement` is not used);
* **`Lv.sb2UpperLaunchEntryLAmbLeStatement_of_thm`**: SB2(1) (bounded) from the same inputs; route A
  (`…_of_entranceK2NLe`) as well;
* **`Wire.theorem14Statement_assembled4Le`**, **`theorem14Statement_of_sb2Lift_freeLe`**,
  **`theorem14Statement_assembled6Le_of_rootTests`**, **`theorem14Statement_assembled6Le`**: Theorem 1.4's tops with
  the bounded SB3 (`Ly.SB3InductionGenRLeStatement`) and the bounded distinct-seed leaf
  (`Ly.SB4DistinctSeedLaunchTailRLeStatement`, the mirrored half with the reflected bound); in the last two SB2(1)
  enters through NOJUMP's version half instead of route A's `SB2EntranceK2NStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Theorem14.SB

/-! ### All-angle statements give the bounded ones -/

/-- NOJUMP's remainder-life input, all angles ⇒ bounded. -/
theorem Vh.sb2RemainderLifeLeStatement_of_all (h : Vh.SB2RemainderLifeStatement.{u}) :
    Vh.SB2RemainderLifeLeStatement.{u} :=
  fun κ b jumps _ _ _ P _ h' E k u ψ η ζ HP _ I u₀ D w hw => h κ b jumps P h' E k u ψ η ζ HP I u₀ D w hw

/-- NOJUMP's endpoint input, all angles ⇒ bounded. -/
theorem Vk.sb2RelEndpointLeStatement_of_all (h : Vk.SB2RelEndpointStatement.{u}) :
    Vk.SB2RelEndpointLeStatement.{u} :=
  fun κ b jumps _ _ _ P _ h' E k u ψ η ζ HP _ => h κ b jumps P h' E k u ψ η ζ HP

/-- SB2(1)'s version half, all angles ⇒ bounded. -/
theorem Lv.sb2LineVersionRLeStatement_of_all (h : Lv.SB2LineVersionRStatement.{u}) :
    Lv.SB2LineVersionRLeStatement.{u} :=
  fun κ b jumps _ _ _ P _ h' E k u ψ η ζ HP _ I u₀ hu₀ D => h κ b jumps P h' E k u ψ η ζ HP I u₀ hu₀ D

/-- Route A's input, all angles ⇒ bounded. -/
theorem Lv.sb2EntranceK2NLeStatement_of_all (h : Lv.SB2EntranceK2NStatement.{u}) :
    Lv.SB2EntranceK2NLeStatement.{u} :=
  fun κ b jumps _ _ _ P _ h' E k u ψ η ζ H _ I => h κ b jumps P h' E k u ψ η ζ H I

/-- SB2(1) in GW1's ambient setting, all angles ⇒ bounded. -/
theorem Ly.sb2UpperLaunchEntryLAmbLeStatement_of_all (h : Ly.SB2UpperLaunchEntryLAmbStatement.{u}) :
    Ly.SB2UpperLaunchEntryLAmbLeStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h' hh hadm E hE hreg k u ψ hu hψ _ hL hH η ζ hη hS1 =>
    h κ hκ hκ4 b jumps hb P h' hh hadm E hE hreg k u ψ hu hψ hL hH η ζ hη hS1

/-- R95's amended SB3, all angles ⇒ bounded. -/
theorem Ly.sb3InductionGenRLeStatement_of_all (h : Ly.SB3InductionGenRStatement.{u}) :
    Ly.SB3InductionGenRLeStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h' hh hadm E hE hreg u ψ hu hψ _ hL hH η ζ hη hζ =>
    h κ hκ hκ4 b jumps hb P h' hh hadm E hE hreg u ψ hu hψ hL hH η ζ hη hζ

/-! ### SB2(1) with the bound -/

/-- **SB2(1)'s version half with `ψ ≤ π/2`** from Theorems 1.2–1.3 (R48) and NOJUMP's two remaining inputs (bounded
forms); Lemma S3 is `Tc.sb2EntranceNoCommonArcLeStatement_of_thm`. -/
theorem Vm.sb2LineVersionRLeStatement_of_thm (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hE7 : Vh.SB2RemainderLifeLeStatement.{u})
    (hEnd : Vk.SB2RelEndpointLeStatement.{u}) : Lv.SB2LineVersionRLeStatement.{u} :=
  Vm.sb2LineVersionRStatement_of_endpointLe h13 (Tc.sb2EntranceNoCommonArcLeStatement_of_thm h12p h13 h12p₀ h13₀) hE7
    hEnd

/-- **SB2(1) in GW1's ambient setting, `ψ ≤ π/2`**, from the bounded version half (Theorems 1.2–1.3; the kernel half
is `Lv.sb2LineKernelRStatement_proved`). -/
theorem Lv.sb2UpperLaunchEntryLAmbLeStatement_of_versionRLe (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hV : Lv.SB2LineVersionRLeStatement.{u}) :
    Ly.SB2UpperLaunchEntryLAmbLeStatement.{u} :=
  Lv.sb2UpperLaunchEntryLAmbStatement_of_driverLinkLe h13
    (Lv.sb2DriverLinkAmbStatement_of_halvesRLe h12p h13 hV (Lv.sb2LineKernelRStatement_proved h12p h13))

/-- **SB2(1) in GW1's ambient setting, `ψ ≤ π/2`, route A** (SB2DRV's `SB2EntranceK2NStatement`, bounded). -/
theorem Lv.sb2UpperLaunchEntryLAmbLeStatement_of_entranceK2NLe (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hN : Lv.SB2EntranceK2NLeStatement.{u}) :
    Ly.SB2UpperLaunchEntryLAmbLeStatement.{u} :=
  Lv.sb2UpperLaunchEntryLAmbStatement_of_driverLinkLe h13 (Lv.sb2DriverLinkAmbStatement_of_entranceK2NLe h12p h13 hN)

/-- **SB2(1) in GW1's ambient setting, `ψ ≤ π/2`**, from Theorems 1.2–1.3 (universes `u` and `0`) and NOJUMP's two
remaining inputs (bounded forms). -/
theorem Lv.sb2UpperLaunchEntryLAmbLeStatement_of_thm (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hE7 : Vh.SB2RemainderLifeLeStatement.{u}) (hEnd : Vk.SB2RelEndpointLeStatement.{u}) :
    Ly.SB2UpperLaunchEntryLAmbLeStatement.{u} :=
  Lv.sb2UpperLaunchEntryLAmbLeStatement_of_versionRLe (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)
    h13 (Vm.sb2LineVersionRLeStatement_of_thm (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hE7 hEnd)

end InteractingSLE.Theorem14.SB

namespace InteractingSLE.Wire

open MeasureTheory Theorem14

/-! ### Theorem 1.4's tops with the bound -/

/-- **Theorem 1.4 (all four clauses), `theorem14Statement_assembled4` with the bounded SB3 and the bounded
distinct-seed leaf.** -/
theorem theorem14Statement_assembled4Le
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.Ly.SB3InductionGenRLeStatement.{u})
    (hDS : SB.Ly.SB4DistinctSeedLaunchTailRLeStatement.{u})
    (hIA : SB.Ly.SB4InitialArcLaunchTailRStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  obtain ⟨hDS', hIA'⟩ := SB.Ly.sb4RetainedTailStatements_of_launchRLe hSB3 h12 h13 hDS hIA
  have hDSreg := SB.sb4DistinctSeedRegStatement_of_retainedTail hDS'
  have hIAreg := SB.sb4InitialArcRegStatement_of_retainedTail hIA'
  have hArc := WalkIntRunChron.walkPairArcDataStatement h13 h13₀
  exact theorem14Statement_of_sb4Reg_arcData h12 h13 h12₀ h13₀ hTests hDSreg hIAreg
    (walkNormChartStatement_of_sb4Reg_arcData_loc h12 h13 h12₀ h13₀ hTests hDSreg hIAreg hArc
      (walkNormChartLocStatement_of_sb4Reg h12 h13 h12₀ h13₀ hTests hDSreg hIAreg)) hArc hRep

/-- **Theorem 1.4 from SB2(2)'s combined target and the free real point, bounded SB3**
(`theorem14Statement_of_sb2Lift_free` with `ψ ≤ π/2`). -/
theorem theorem14Statement_of_sb2Lift_freeLe
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.Ly.SB3InductionGenRLeStatement.{u})
    (hC : SB.Lh.SB2LowerLaunchLiftStatement.{u}) (hfree : SB.Lh.LowerWalkLeftFreeStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  obtain ⟨hPR, hPL⟩ := walkProperRegStatements_of_thm12_thm13 h12 h13 h12₀ h13₀
  exact theorem14Statement_assembled4Le h12 h13 h12₀ h13₀ hTests hSB3
    (sb4DistinctSeedLaunchTailRStatement_of_sb2LiftLe h12 h13 h13₀ hC hPR hPL)
    (sb4InitialArcLaunchTailRStatement_of_arcLift (SB.Lf.sb2ArcLaunchLiftStatement_of_lower h12 h13 h12₀ h13₀ hC hfree)
      hPR h13) hRep

/-- **Theorem 1.4 from GW2's root tests, D22 form**: `theorem14Statement_assembled6_of_rootTests` with SB2(1) through
NOJUMP's version half with `ψ ≤ π/2` (inputs `hE7`, `hEnd`, bounded) in place of route A's
`SB2EntranceK2NStatement`; Lemma S3 is proved (`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). -/
theorem theorem14Statement_assembled6Le_of_rootTests
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hE7 : SB.Vh.SB2RemainderLifeLeStatement.{u}) (hEnd : SB.Vk.SB2RelEndpointLeStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Theorem14Statement.{u} :=
  theorem14Statement_of_sb2Lift_freeLe h12 h13 h12₀ h13₀ hTests
    (SB.LuM.sb3InductionGenRStatement_of_sb2Le
      (SB.Lv.sb2UpperLaunchEntryLAmbLeStatement_of_thm h12 h13 h12₀ h13₀ hE7 hEnd) h12 h13 h12₀ h13₀ hDy hDy₀)
    (SB.Lk.sb2LowerLaunchLiftStatement_of_split h12 h13 h12₀ h13₀ hgeo hcond)
    (SB.Lk.lowerWalkLeftFreeStatement_of_thm12_thm13 h12 h13 h12₀ h13₀)
    (GW4Fix.gw4ComponentRepAStatement h12 h13)

/-- **Theorem 1.4, main top, D22 form**: `theorem14Statement_assembled6` (COVER's scaled root cover and ROOT2's three
C24 assertions) with SB2(1) through NOJUMP's bounded version half (`hE7`, `hEnd`). -/
theorem theorem14Statement_assembled6Le
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (D : GW2TipSystem.RootC24.ConstructionFamily.{u}) (gap : GW2TipSystem.RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : GW2TipSystem.RootC24.SourceData Ω)
      (r : GW2TipSystem.ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : GW2TipSystem.RootC24.SourceData Ω)
      (x : GW2TipSystem.RootIdx c.Θ c.Q),
      ∀ᵐ ω ∂c.P, ω ∈ GW2TipSystem.RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : GW2TipSystem.RootC24.RootGeometryStatement (GW2TipSystem.RootCv.withScaledCover D gap))
    (hNear : GW2TipSystem.RootC24.RetainedNearModelsStatement (GW2TipSystem.RootCv.withScaledCover D gap))
    (hSlow : GW2TipSystem.RootC24.RetainedSlowComparisonsStatement (GW2TipSystem.RootCv.withScaledCover D gap))
    (hE7 : SB.Vh.SB2RemainderLifeLeStatement.{u}) (hEnd : SB.Vk.SB2RelEndpointLeStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled6Le_of_rootTests h12 h13 h12₀ h13₀
    (GW2TipSystem.RootCv.gw2RootTestStatement_of_scaledCover h13 h13₀ D gap hgap hpos hGeometry hNear hSlow)
    hE7 hEnd hgeo hcond hDy hDy₀

end InteractingSLE.Wire
