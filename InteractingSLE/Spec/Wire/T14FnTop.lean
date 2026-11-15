/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ByTopG
import InteractingSLE.Spec.Supplement.SB2RvVisit
import InteractingSLE.Spec.Supplement.SB2CbInv
import InteractingSLE.Spec.Supplement.GW2UbStage
import InteractingSLE.Spec.Supplement.GW2RjShell
import InteractingSLE.Spec.Supplement.GW2JDetR10Evolution

/-!
# The seal-ready Theorem 1.4 top: one binder, `hcan`

Packet PROVE-T14-ASSEMBLE7 (round 4). BUF's `Wire.theorem14Statement_oneG_nearImgC K₀ hcan hdet` (1767ee8bb) has
`hnearImg` with no open input, for every base package `K₀`. ROOTX's `SB.Ro.sb2LowerRootDetWStatement_closed`
(2747b146a) is `hdet` with no hypotheses. This file supplies the last piece of data, a **closed base package**
`T14Fn.pkg₀`, and states the top with exactly one binder.

* **`T14Fn.degenFam hκ hκ4`**: a near crossing family for every `0 < κ < 4`. It has two force points per side
  (`xL = (0, −3)`, `xR = (0, 1)`), weights `(0, κ − 4)` and `(0, κ/2 − 2)` (constant in `m`), and the reference
  evolutions of `GW2JDetR10.referenceEvolution`. The DS1 bounds hold with `Rw = 4`, `ε = 1`; the orientation clause
  holds going left.
* **`T14Fn.pkg₀`**: the package with the trivial instance, zero stops (`GW2Rd.zeroStop`), the trivial shells
  (`GW2Rj.trivShell 0`) and `degenFam` as near family. BUF's `hnearImg` holds for every base package, so this choice
  costs nothing. In ROOTX's `pkgOneG`, the base package's near family is the fallback of BUF's selection and its near
  stop is used off the good roots.
* **`T14Fn.gw2RootTestStatement_closed`**: GW2's root tests with **no hypotheses**.
* **`Wire.theorem14Statement_closedS hcan`**: Theorem 1.4 from `hcan : Mz.SB2LowerStageCanonStatement h12p`
  alone (CANON's `…_of_lawU` / `…_of_step` route delivers it). `Wire.theorem14Statement_of_step` is the same top from
  CANON's induction step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire.T14Fn

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.RootC24 Theorem14.GW2TipSystem.RootN4

/-- The left force positions `(0, −3)`. -/
def xL2 : Fin 2 → ℝ := ![0, -3]

/-- The right force positions `(0, 1)`. -/
def xR2 : Fin 2 → ℝ := ![0, 1]

/-- The left weights `(0, κ − 4)`. -/
def ρL2 (κ : ℝ) : Fin 2 → ℝ := ![0, κ - 4]

/-- The right weights `(0, κ/2 − 2)`. -/
def ρR2 (κ : ℝ) : Fin 2 → ℝ := ![0, κ / 2 - 2]

theorem isOrderedForceWord_two : IsOrderedForceWord xL2 xR2 := by
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [xL2]
  · fin_cases i <;> simp [xL2]
  · fin_cases i <;> fin_cases j <;> simp_all [xR2]
  · fin_cases i <;> simp [xR2]

theorem isDS1Word_two {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    Supp12.DS2.IsDS1Word 1 1 4 1 xL2 xR2 (ρL2 κ) (ρR2 κ) := by
  refine ⟨isOrderedForceWord_two, fun i => ?_, fun j => ?_, fun i hi => ?_, fun j hj => ?_⟩
  · fin_cases i
    · simp [ρL2]
    · show |κ - 4| ≤ 4
      exact abs_le.2 ⟨by linarith, by linarith⟩
  · fin_cases j
    · simp [ρR2]
    · show |κ / 2 - 2| ≤ 4
      exact abs_le.2 ⟨by linarith, by linarith⟩
  · have hi0 : i = 0 := Fin.ext (by simpa using hi)
    subst hi0
    have : (Finset.univ.filter fun l : Fin 2 => l ≤ 0) = {0} := by decide
    rw [this, Finset.sum_singleton]
    simp [ρL2]
  · have hj0 : j = 0 := Fin.ext (by simpa using hj)
    subst hj0
    have : (Finset.univ.filter fun l : Fin 2 => l ≤ 0) = {0} := by decide
    rw [this, Finset.sum_singleton]
    simp [ρR2]

/-- **A near crossing family for every `0 < κ < 4`** (degenerate: constant weights, reference evolutions). -/
def degenFam {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) : NearCrossingFamily.{u} κ where
  nL := 2
  nR := 2
  hnL := by norm_num
  hnR := by norm_num
  xL := xL2
  xR := xR2
  ρLs := fun _ => ρL2 κ
  ρRs := fun _ => ρR2 κ
  ρL₀ := ρL2 κ
  ρR₀ := ρR2 κ
  sequence := fun _ => GW2JDetR10.referenceEvolution.{u} hκ (ρL2 κ) (ρR2 κ) isOrderedForceWord_two
  limit := GW2JDetR10.referenceEvolution.{u} hκ (ρL2 κ) (ρR2 κ) isOrderedForceWord_two
  mL := 1
  mR := 1
  Rw := 4
  ε := 1
  η := 1
  goLeft := true
  hε := one_pos
  hη := one_pos
  hxL0 := by simp [xL2]
  hxR0 := by simp [xR2]
  hxL := fun i hi => by fin_cases i <;> simp_all [xL2]
  hxR := fun j hj => by fin_cases j <;> simp_all [xR2]
  hw := fun _ => isDS1Word_two hκ hκ4
  hw₀ := isDS1Word_two hκ hκ4
  hρL := tendsto_const_nhds
  hρR := tendsto_const_nhds
  hE := fun _ => GW2JDetR10.referenceEvolution_isEvolution hκ _ _ _
  hE₀ := GW2JDetR10.referenceEvolution_isEvolution hκ _ _ _
  horientation := by
    refine Or.inl ⟨rfl, rfl, ?_, ?_, fun i hi => ?_, ?_, ?_⟩
    · simp [xR2]
    · simp [xL2]
    · fin_cases i
      · exact absurd hi (by decide)
      · simp [xL2]
    · simp [ρL2, Fin.sum_univ_two]
    · simp [ρR2, Fin.sum_univ_two]

/-- The trivial stage instance. -/
def trivInst {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) : GW2Sde.StageInst Ω where
  W := fun _ _ => 0
  γ := fun _ _ => 0
  GT := ∅
  R := fun _ _ => 0
  V := fun _ => 0
  ρ := fun _ => 0
  ρs := fun _ _ => 0
  T := 0
  β := fun _ => c.c₀
  E := ∅
  Hr := fun _ => 0
  σa := 0
  kc := 0
  u₀ := fun _ => 0
  ℋ := fun _ => ⊥
  B := fun _ _ => ∅

/-- **A closed base package** (trivial instance, zero stops, trivial shells, the degenerate near family). -/
def pkg₀ : GW2Sde.PkgFamily.{u} := fun Ω _ _ c _ =>
  { inst := fun _ _ => trivInst c
    nearStop := fun _ _ _ _ => GW2Rd.zeroStop Ω
    slowStop := fun _ _ => GW2Rd.zeroStop Ω
    nearFamily := fun _ _ => degenFam c.hκ c.hκ4
    nearCandidate := fun _ _ _ _ => 0
    slowShell := fun _ _ _ => GW2Rj.trivShell 0 }

/-- **GW2's root tests, with no hypotheses**: ROOTX's guarded stop package on `pkg₀` with BUF's choices and BUF's
`hnearImg` (`T14By.hnearImg_oneGC`). -/
theorem gw2RootTestStatement_closed : GW2RootTestStatement.{u} :=
  T14Re.gw2RootTestStatement_oneG (GW2Bh.psiGoodS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) T14Re.chG)
    GW2Bh.exitB pkg₀ (GW2Bh.kSelBS T14Asm7.h13 (GW2Nx.schedVerXStopFamily T14Asm7.h13) T14Re.chG pkg₀)
    (fun Ω _ _ c r l n a => GW2Bh.exitB_spec Ω c r l n a) (T14By.hnearImg_oneGC pkg₀)

end InteractingSLE.Wire.T14Fn

namespace InteractingSLE.Wire

open Theorem14

/-- **Theorem 1.4, seal-ready top** (one binder): BUF's `theorem14Statement_oneG_nearImgC` at the closed base package
`T14Fn.pkg₀`, with ROOTX's closed `hdet`. The binder `hcan` is CANON's `Mz.SB2LowerStageCanonStatement` (delivered by
`Cz.sb2LowerStageCanonStatement_of_lawU` / `…_of_step`). -/
theorem theorem14Statement_closedS
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  theorem14Statement_oneG_nearImgC T14Fn.pkg₀ hcan SB.Ro.sb2LowerRootDetWStatement_closed

/-- **Theorem 1.4 from CANON's induction step** (`Cz.SB2LowerStageStepStatement`; the base stage and K2 at the tails
proved). -/
theorem theorem14Statement_of_step (hstep : SB.Cz.SB2LowerStageStepStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_closedS
    (SB.Cz.sb2LowerStageCanonStatement_of_step T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ hstep)

end InteractingSLE.Wire
