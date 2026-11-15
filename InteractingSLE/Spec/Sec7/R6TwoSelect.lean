/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TwoArcInf
import InteractingSLE.Spec.Sec7.R6SafeMeetInf

/-!
# R.6: rational inner times with a common point and inclusion

PROVE-R6-TWO. The common-point construction is specialized to the actual
branch-shifted initial charts. The landed frontier and avoidance lemmas
then give inclusion of the two actual current domains. This supplies the
geometric hypotheses used by the shared-wall witnesses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Two

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField
open HOuter PocketWordAssembly PocketSeedOpen R6Safe

/-- The actual branch-shifted current chart of a bounded pocket. -/
abbrev currentChart {Ω : Type*} (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (n : Ω → ℤ) (q : ℝ≥0) (ω : Ω) : Chart :=
  relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
    (travAll R L r η ψ) q ω

/-- The corresponding current chart of a seed-opening pocket. -/
abbrev currentChartInf {Ω : Type*} (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (n : Ω → ℤ) (q : ℝ≥0) (ω : Ω) : Chart :=
  relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
    (travAllInf R L r η ψ) q ω

section Bounded

variable {Ω : Type*} {A A' : Set Ω} {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0}
  {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- Rational inner times arbitrarily close above the visited inner
capacity have ordered stops, a common point and current-domain inclusion.
Both pockets here are outer; no full-complement identity is assumed. -/
theorem exists_rat_meet_near_tip_two
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfg (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω)) (hω' : ω ∈ A')
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (htip : η ω (outerFibreEnd R L r η ψ q ω) ∈ cfPocket (R' ω) (L' ω) r') {ε : ℝ} (hε : 0 < ε) :
    ∃ q' : ℚ, innerRelCap R' L' r' η ψ' (outerFibreEnd R L r η ψ q ω) ω < q' ∧
      (q' : ℝ) < innerRelCap R' L' r' η ψ' (outerFibreEnd R L r η ψ q ω) ω + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAll R' L' r' η ψ' ω) ∧
      outerFibreEnd R L r η ψ q ω < PocketStopWallsFin.ambTime0 (η ω) (cfPocket (R' ω) (L' ω) r')
        (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1)) (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0))
        (ψ' ω) (StripSys.rt q') ∧
      (((currentChart A' R' L' r' η ψ' n' (StripSys.rt q') ω).dom : Set ℂ) ∩
        (currentChart A R L r η ψ n q ω).dom).Nonempty ∧
      ((currentChart A' R' L' r' η ψ' n' (StripSys.rt q') ω).dom : Set ℂ) ⊆
        (currentChart A R L r η ψ n q ω).dom := by
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    (hcfg ω hω).toPocket (hψ ω hω) |>.erase.isOpen
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    ((hcfg ω hω).toPocket (hψ ω hω)).subset_H
  have hVo : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    (hcfg' ω hω).toPocket (hψ' ω hω) |>.erase.isOpen
  have hVH : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    ((hcfg' ω hω).toPocket (hψ' ω hω)).subset_H
  obtain ⟨hBC, hBCdom, hBCfwd⟩ := R5Phase.shiftChart_dom_facts hCo hCH
    (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  obtain ⟨hBV, hBVdom, hBVfwd⟩ := R5Phase.shiftChart_dom_facts hVo hVH
    (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  obtain ⟨q', hlo, hhi, hlive, htime, hmeet⟩ := exists_rat_relCharts_meet_two
    ((hcfg ω hω).toPocket (hψ ω hω)) ((hcfg' ω hω').toPocket (hψ' ω hω'))
    hq hsub hBC hBCdom hBCfwd hBV hBVdom hBVfwd htip hε
  have hincl := inner_dom_subset_outer_dom_two (n := n) (n' := n') hcfg hψ hω hq
    hcfg' hψ' hω' hlive hsub htime.le hmeet
  exact ⟨q', hlo, hhi, hlive, htime, hmeet, hincl⟩

end Bounded

section SeedOpening

variable {Ω : Type*} {A A' : Set Ω} {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0}
  {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- Rational inner times arbitrarily close above the visited inner
capacity have ordered stops, a common point and current-domain inclusion.
The outer pocket opens at the seed; the inner pocket is bounded; no full-complement identity is assumed. -/
theorem exists_rat_meet_near_tip_twoInf
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfg (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω)) (hω' : ω ∈ A')
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R' ω) (L' ω) r') {ε : ℝ} (hε : 0 < ε) :
    ∃ q' : ℚ, innerRelCap R' L' r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω < q' ∧
      (q' : ℝ) < innerRelCap R' L' r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAll R' L' r' η ψ' ω) ∧
      outerFibreEndInf R L r η ψ q ω < PocketStopWallsFin.ambTime0 (η ω) (cfPocket (R' ω) (L' ω) r')
        (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1)) (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0))
        (ψ' ω) (StripSys.rt q') ∧
      (((currentChart A' R' L' r' η ψ' n' (StripSys.rt q') ω).dom : Set ℂ) ∩
        (currentChartInf A R L r η ψ n q ω).dom).Nonempty ∧
      ((currentChart A' R' L' r' η ψ' n' (StripSys.rt q') ω).dom : Set ℂ) ⊆
        (currentChartInf A R L r η ψ n q ω).dom := by
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    (hcfg ω hω).toPocketInf (hψ ω hω) |>.erase.isOpen
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    ((hcfg ω hω).toPocketInf (hψ ω hω)).subset_H
  have hVo : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    (hcfg' ω hω).toPocket (hψ' ω hω) |>.erase.isOpen
  have hVH : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    ((hcfg' ω hω).toPocket (hψ' ω hω)).subset_H
  obtain ⟨hBC, hBCdom, hBCfwd⟩ := R5Phase.shiftChart_dom_facts hCo hCH
    (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  obtain ⟨hBV, hBVdom, hBVfwd⟩ := R5Phase.shiftChart_dom_facts hVo hVH
    (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  obtain ⟨q', hlo, hhi, hlive, htime, hmeet⟩ := exists_rat_relCharts_meet_twoInf
    ((hcfg ω hω).toPocketInf (hψ ω hω)) ((hcfg' ω hω').toPocket (hψ' ω hω'))
    hq hsub hBC hBCdom hBCfwd hBV hBVdom hBVfwd htip hε
  obtain ⟨hIc, hIsub, hIavoid⟩ := outer_chart_facts (n := n') hcfg' hψ' hω' hlive
  have hincl := dom_subset_of_avoid hIc (hIsub.trans hsub)
    (outer_frontier_subset_traceInf (n := n) hcfg hψ hω hq) (hIavoid _ htime.le) hmeet
  exact ⟨q', hlo, hhi, hlive, htime, hmeet, hincl⟩

end SeedOpening

section BothSeedOpening

variable {Ω : Type*} {A A' : Set Ω} {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0}
  {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- Rational inner times arbitrarily close above the visited inner
capacity have ordered stops, a common point and current-domain inclusion.
Both pockets open at the seed; no full-complement identity is assumed. -/
theorem exists_rat_meet_near_tip_twoInfInf
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfgInf (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordanInf (R' ω) (L' ω) r' (ψ' ω)) (hω' : ω ∈ A')
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R' ω) (L' ω) r') {ε : ℝ} (hε : 0 < ε) :
    ∃ q' : ℚ, innerRelCapInf R' L' r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω < q' ∧
      (q' : ℝ) < innerRelCapInf R' L' r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAllInf R' L' r' η ψ' ω) ∧
      outerFibreEndInf R L r η ψ q ω < PocketStopWallsFin.ambTime0Inf (η ω) (cfPocket (R' ω) (L' ω) r')
        (firstHit (η ω) (cfArcRInf (R' ω) (L' ω) r' 0))
        (ψ' ω) (StripSys.rt q') ∧
      (((currentChartInf A' R' L' r' η ψ' n' (StripSys.rt q') ω).dom : Set ℂ) ∩
        (currentChartInf A R L r η ψ n q ω).dom).Nonempty ∧
      ((currentChartInf A' R' L' r' η ψ' n' (StripSys.rt q') ω).dom : Set ℂ) ⊆
        (currentChartInf A R L r η ψ n q ω).dom := by
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    (hcfg ω hω).toPocketInf (hψ ω hω) |>.erase.isOpen
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    ((hcfg ω hω).toPocketInf (hψ ω hω)).subset_H
  have hVo : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    (hcfg' ω hω).toPocketInf (hψ' ω hω) |>.erase.isOpen
  have hVH : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    ((hcfg' ω hω).toPocketInf (hψ' ω hω)).subset_H
  obtain ⟨hBC, hBCdom, hBCfwd⟩ := R5Phase.shiftChart_dom_facts hCo hCH
    (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  obtain ⟨hBV, hBVdom, hBVfwd⟩ := R5Phase.shiftChart_dom_facts hVo hVH
    (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  obtain ⟨q', hlo, hhi, hlive, htime, hmeet⟩ := exists_rat_relCharts_meet_twoInfInf
    ((hcfg ω hω).toPocketInf (hψ ω hω)) ((hcfg' ω hω').toPocketInf (hψ' ω hω'))
    hq hsub hBC hBCdom hBCfwd hBV hBVdom hBVfwd htip hε
  obtain ⟨hIc, hIsub, hIavoid⟩ := outer_chart_factsInf (n := n') hcfg' hψ' hω' hlive
  have hincl := dom_subset_of_avoid hIc (hIsub.trans hsub)
    (outer_frontier_subset_traceInf (n := n) hcfg hψ hω hq) (hIavoid _ htime.le) hmeet
  exact ⟨q', hlo, hhi, hlive, htime, hmeet, hincl⟩

end BothSeedOpening

end InteractingSLE.Sec7.R6Two
