/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovLift
import InteractingSLE.Spec.Sec7.R5FreshSide

/-!
# The late lift geometry from the R.7 inputs at the late pockets

Packet PROVE-COLLAR-COVER. A late side test's pocket is an R.7 change pocket (walls `d.rightWall`,
`d.leftWall j.seed`, parameter `rt j.seed`, counterflow `d.curve`, Jordan coordinate `j.chart`, base chart
`(j.target i d).baseChart`, test event `j.event`, seeds at `0`). The late lift geometry is therefore the R.7 lift
geometry at these objects:

* `seedMarks` (abbrev): the single seed mark `![0]`;
* `LateSeedLand` (def, **named input**): PROVE-R5-FRESHTIP's `R5Fresh.R7SeedLand` / `R7SeedLandInf` at the late
  pocket of every ready test and every positive capacity — the seed-interval landings lie in `ℍ` (base-point (G5);
  R5-LIFT2's fact (ii), a fresh tip at the left stop, is not needed: FRESHTIP's pathwise side agreement);
* **`lateSeedLand_of_corner_mem_H`**: `LateSeedLand` holds whenever the pocket's corner is not real (FRESHTIP's
  `r7SeedLand(Inf)_of_corner_mem_H`);
* `LateOuterRefl` (def, **named input**): `R5Lift.R7OuterRefl` / `R7OuterReflInf` at the late pockets — the outer
  collars' old landings lie in `K_s` (PROVE-WALL-ORDER's target (3), the one-sided reverse wall visits);
* **`lateLiftCurGeom_of_seedLand`**: `R5Lift.LateLiftCurGeom` from `LateSeedLand`;
* **`lateOuterLiftGeom_of_seedLand`**: `ColCov.LateOuterLiftGeom` from `LateSeedLand` and `LateOuterRefl`.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest
open PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PocketWordAssembly
  PocketSeedOpen PocketCoord PocketJordan PocketStopField PocketStopWallsFin R5Phase R5Ref R5Lift R5Fresh
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type} [MeasurableSpace Ω]

/-- The single seed mark at `0`. -/
abbrev seedMarks : Ω → Fin (0 + 1) → ℝ := fun _ => ![0]

/-- **The seed-interval landings at the late pockets** (named input, PROVE-R5-FRESHTIP's `R5Fresh.R7SeedLand`): on
every ready late test and at every positive relative capacity, `R7SeedLand` (bounded pocket) or `R7SeedLandInf`
(pocket opening at the flow seed) of the test's pocket. -/
def LateSeedLand (i : BothLow) (d : WordObjects Ω) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q →
    (j.infinite = false → R7SeedLand d.measure j.event d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve
      j.chart seedMarks seedMarks (j.target i d).baseChart q) ∧
    (j.infinite = true → R7SeedLandInf d.measure j.event d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed)
      d.curve j.chart seedMarks seedMarks (j.target i d).baseChart q)

/-- **The outer collars' `K_s`-landing at the late pockets** (named input, PROVE-WALL-ORDER's target (3)): on every
ready late test and at every positive relative capacity, `R5Lift.R7OuterRefl` (bounded pocket) or `R7OuterReflInf`
(pocket opening at the flow seed) of the test's pocket, with the exceptional set `X j q`. -/
def LateOuterRefl (i : BothLow) (d : WordObjects Ω) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) : Prop :=
  ∀ j : SideTest Ω, j.Ready d → ∀ q : ℝ≥0, 0 < q →
    (j.infinite = false → R7OuterRefl d.measure j.event d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve
      j.chart seedMarks seedMarks (j.target i d).baseChart d.driver d.lifetime (X j q) q) ∧
    (j.infinite = true → R7OuterReflInf d.measure j.event d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed)
      d.curve j.chart seedMarks seedMarks (j.target i d).baseChart d.driver d.lifetime (X j q) q)

/-- **A ready bounded late test is an R.7 bounded change pocket on its event.** -/
theorem ready_bounded_facts {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hI : j.infinite = false) :
    (∀ ω ∈ j.event, IsCfPocketConfig (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)
      (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω)) ∧
    (∀ ω ∈ j.event, IsCfJordan (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) (j.chart ω)) ∧
    (∀ ω ∈ j.event, ((j.target i d).baseChart ω).IsConformal) ∧
    (∀ ω ∈ j.event, (((j.target i d).baseChart ω).dom : Set ℂ) =
      cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)) ∧
    (∀ ω ∈ j.event, EqOn ((j.target i d).baseChart ω).1 (j.chart ω)
      (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))) := by
  have hpc := fun ω (hω : ω ∈ j.event) =>
    (isPocketChartOn hj hRc hLc (i := i)).1 ω (by rwa [target_event])
  obtain ⟨-, -, -, -, -, hcfgP, -, -, hAG, -, hJ, -⟩ := hj
  simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG hJ
  refine ⟨fun ω hω => hcfgP ω (hAG hω).1 (hAG hω).2, hJ, fun ω hω => (hpc ω hω).1, fun ω hω => ?_,
    fun ω hω => ?_⟩
  · have h := (hpc ω hω).2.1
    rw [target_domain] at h
    exact h
  · have h := (hpc ω hω).2.2.1
    rw [target_domain, target_chart] at h
    exact h

/-- **A ready late test opening at the flow seed is an R.7 change pocket opening at the flow seed on its event.** -/
theorem ready_inf_facts {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hI : j.infinite = true) :
    (∀ ω ∈ j.event, IsCfPocketConfigInf (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)
      (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω)) ∧
    (∀ ω ∈ j.event, IsCfJordanInf (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) (j.chart ω)) ∧
    (∀ ω ∈ j.event, ((j.target i d).baseChart ω).IsConformal) ∧
    (∀ ω ∈ j.event, (((j.target i d).baseChart ω).dom : Set ℂ) =
      cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)) ∧
    (∀ ω ∈ j.event, EqOn ((j.target i d).baseChart ω).1 (j.chart ω)
      (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))) := by
  have hpc := fun ω (hω : ω ∈ j.event) =>
    (isPocketChartOn hj hRc hLc (i := i)).1 ω (by rwa [target_event])
  obtain ⟨-, -, -, hG, -, -, hcfgI, -, hAG, -, hJ, -⟩ := hj
  simp only [hI, ↓reduceIte] at hAG hJ
  refine ⟨fun ω hω => hcfgI ω (hAG hω).1
      (le_antisymm (not_lt.1 (hAG hω).2) ((hG ω (hAG hω).1).1.changeCorner_props.1.1)), hJ,
    fun ω hω => (hpc ω hω).1, fun ω hω => ?_, fun ω hω => ?_⟩
  · have h := (hpc ω hω).2.1
    rw [target_domain] at h
    exact h
  · have h := (hpc ω hω).2.2.1
    rw [target_domain, target_chart] at h
    exact h

/-- **`LateSeedLand` where the pocket corner is not real** (FRESHTIP's `r7SeedLand(Inf)_of_corner_mem_H`; the input
is genuine only for pockets closing at the flow target). -/
theorem lateSeedLand_of_corner_mem_H {i : BothLow} {d : WordObjects Ω} (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hcorner : ∀ j : SideTest Ω, j.Ready d → ∀ ω ∈ j.event,
      (j.infinite = false → cfArcR (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 1 ∈ H) ∧
      (j.infinite = true → cfArcRInf (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) 0 ∈ H)) :
    LateSeedLand i d := by
  intro j hj q _
  refine ⟨fun hIf => ?_, fun hIf => ?_⟩
  · obtain ⟨hcfg, hψ, hc, hdom, heq⟩ := ready_bounded_facts (i := i) hj hRc (hLc j.seed) hIf
    exact r7SeedLand_of_corner_mem_H (W' := d.driver) hcfg hψ hc hdom heq fun ω hω => (hcorner j hj ω hω).1 hIf
  · obtain ⟨hcfg, hψ, hc, hdom, heq⟩ := ready_inf_facts (i := i) hj hRc (hLc j.seed) hIf
    exact r7SeedLandInf_of_corner_mem_H (W' := d.driver) hcfg hψ hc hdom heq fun ω hω => (hcorner j hj ω hω).2 hIf

/-- **`R5Lift.LateLiftCurGeom` from the seed-interval landings at the late pockets** (FRESHTIP's pathwise side
agreement). -/
theorem lateLiftCurGeom_of_seedLand {i : BothLow} {d : WordObjects Ω} (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω)) (h : LateSeedLand i d) : LateLiftCurGeom i d := by
  intro j hj q hq
  cases hIf : j.infinite
  · obtain ⟨hcfg, hψ, hc, hdom, heq⟩ := ready_bounded_facts (i := i) hj hRc (hLc j.seed) hIf
    have hG := r7LiftCurGeom_of_seedLand (W' := d.driver) hcfg hψ hc hdom heq (fun _ => rfl) (fun _ => rfl)
      ((h j hj q hq).1 hIf)
    filter_upwards [hG] with ω hω hE hlive u hu
    have hE' : ω ∈ j.event := by rwa [target_event] at hE
    have hcurve : (j.target i d).curve =
        travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
      simp only [target_curve, hIf, Bool.false_eq_true, ↓reduceIte]
    have hT : lateLeftStop j d q ω =
        leftStop d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω := by
      simp only [lateLeftStop, hIf, Bool.false_eq_true, ↓reduceIte]
    rw [hcurve] at hlive hu ⊢
    rw [late_seed_interval_eq] at hu
    rw [hT, target_domain]
    exact hω hE' hlive u hu
  · obtain ⟨hcfg, hψ, hc, hdom, heq⟩ := ready_inf_facts (i := i) hj hRc (hLc j.seed) hIf
    have hG := r7LiftCurGeomInf_of_seedLand (W' := d.driver) hcfg hψ hc hdom heq (fun _ => rfl) (fun _ => rfl)
      ((h j hj q hq).2 hIf)
    filter_upwards [hG] with ω hω hE hlive u hu
    have hE' : ω ∈ j.event := by rwa [target_event] at hE
    have hcurve : (j.target i d).curve =
        travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
      simp only [target_curve, hIf, ↓reduceIte]
    have hT : lateLeftStop j d q ω =
        leftStopInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω := by
      simp only [lateLeftStop, hIf, ↓reduceIte]
    rw [hcurve] at hlive hu ⊢
    rw [late_seed_interval_eq] at hu
    rw [hT, target_domain]
    exact hω hE' hlive u hu

/-- The single-seed jump set is contained in the late jump set. -/
theorem notMem_seed_jumps {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (W : ℝ≥0 → Ω → ℝ) (q : ℝ≥0) (ω : Ω)
    (c : ℝ) {ξ : ℝ}
    (h : ξ ∉ forceJumpSet (fun a => geomLW W (j.target i d).marksL a q ω - c)
      (fun a => geomRW W (j.target i d).marksR a q ω - c)) :
    ξ ∉ forceJumpSet (fun a => geomLW W (seedMarks (Ω := Ω)) a q ω - c)
      (fun a => geomRW W (seedMarks (Ω := Ω)) a q ω - c) := by
  obtain ⟨hmL, hmR⟩ := target_seed_marks j i d ω
  rintro (h0 | ⟨a, ha⟩ | ⟨b, hb⟩)
  · exact h (Or.inl h0)
  · refine h (Or.inr (Or.inl ⟨Late.leftZero i d j, ?_⟩))
    rw [← ha, Fin.fin_one_eq_zero a]
    simp only [geomLW, hmL, Matrix.cons_val_zero]
  · refine h (Or.inr (Or.inr ⟨Late.rightZero i d j, ?_⟩))
    rw [← hb, Fin.fin_one_eq_zero b]
    simp only [geomRW, hmR, Matrix.cons_val_zero]

/-- **`ColCov.LateOuterLiftGeom` from the seed-interval landings and the outer collars' `K_s`-landing at the late
pockets**: the side at every seed-interval coordinate from FRESHTIP's `R5Fresh.ae_curSide(Inf)_of_seedLand`,
the reflection from `LateOuterRefl` (the pair events hold a.s. by the regularized hulls `ae_regHull_eq`). -/
theorem lateOuterLiftGeom_of_seedLand {i : BothLow} {d : WordObjects Ω} (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤) (h : LateSeedLand i d) (hr : LateOuterRefl i d X) :
    LateOuterLiftGeom i d X := by
  intro j hj q hq
  cases hIf : j.infinite
  · obtain ⟨hcfg, hψ, hc, hdom, heq⟩ := ready_bounded_facts (i := i) hj hRc (hLc j.seed) hIf
    have hSide := ae_curSide_of_seedLand (W' := d.driver) hcfg hψ hc hdom heq (fun _ => rfl) (fun _ => rfl)
      ((h j hj q hq).1 hIf)
    filter_upwards [hSide, (hr j hj q hq).1 hIf, ae_regHull_eq hCoupling hLife] with ω hS hRω hHull hE hlive ξ hξ
      hX hI hC
    have hE' : ω ∈ j.event := by rwa [target_event] at hE
    have hcurve : (j.target i d).curve =
        travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
      simp only [target_curve, hIf, Bool.false_eq_true, ↓reduceIte]
    have hT : lateLeftStop j d q ω =
        leftStop d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω := by
      simp only [lateLeftStop, hIf, Bool.false_eq_true, ↓reduceIte]
    have hvc : ∀ t, j.visitCapacity d ω t =
        visitCap d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t := by
      intro t
      simp only [SideTest.visitCapacity, hIf, Bool.false_eq_true, ↓reduceIte]
      rfl
    have href : ∀ t, j.referenceVisitChart i d ω t = relChart (j.target i d).baseChart
        (travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (visitCap d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t).toNNReal ω := by
      intro t
      rw [SideTest.referenceVisitChart, hcurve, hvc]
    have hξ' := notMem_seed_jumps (j := j) (i := i) _ q ω _ hξ
    rw [hcurve] at hlive hξ' hX hI hC ⊢
    rw [late_seed_interval_eq] at hI
    rw [target_domain] at hC ⊢
    simp only [href, hvc, hT]
    refine ⟨hS hE' hlive ξ hI, fun r x ε hv hcap hcol hpK => ?_⟩
    have hM : ω ∈ refEvent j.event d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed)
        (fun ω (s : ℝ) => d.driver s.toNNReal ω) d.curve j.chart (refHull d.driver d.lifetime) q r :=
      ⟨hE', hlive, Or.inl hv, hcap, hHull (rationalOriginalTime r)⟩
    exact hRω hE' hlive ξ hξ' hX ⟨fun h => h hI, hC⟩ r x ε hM hv hcol hpK
  · obtain ⟨hcfg, hψ, hc, hdom, heq⟩ := ready_inf_facts (i := i) hj hRc (hLc j.seed) hIf
    have hSide := ae_curSideInf_of_seedLand (W' := d.driver) hcfg hψ hc hdom heq (fun _ => rfl) (fun _ => rfl)
      ((h j hj q hq).2 hIf)
    filter_upwards [hSide, (hr j hj q hq).2 hIf, ae_regHull_eq hCoupling hLife] with ω hS hRω hHull hE hlive ξ hξ
      hX hI hC
    have hE' : ω ∈ j.event := by rwa [target_event] at hE
    have hcurve : (j.target i d).curve =
        travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart := by
      simp only [target_curve, hIf, ↓reduceIte]
    have hT : lateLeftStop j d q ω =
        leftStopInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart q ω := by
      simp only [lateLeftStop, hIf, ↓reduceIte]
    have hvc : ∀ t, j.visitCapacity d ω t =
        visitCapInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t := by
      intro t
      simp only [SideTest.visitCapacity, hIf, ↓reduceIte]
      rfl
    have href : ∀ t, j.referenceVisitChart i d ω t = relChart (j.target i d).baseChart
        (travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart)
        (visitCapInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart ω t).toNNReal ω := by
      intro t
      rw [SideTest.referenceVisitChart, hcurve, hvc]
    have hξ' := notMem_seed_jumps (j := j) (i := i) _ q ω _ hξ
    rw [hcurve] at hlive hξ' hX hI hC ⊢
    rw [late_seed_interval_eq] at hI
    rw [target_domain] at hC ⊢
    simp only [href, hvc, hT]
    refine ⟨hS hE' hlive ξ hI, fun r x ε hv hcap hcol hpK => ?_⟩
    have hM : ω ∈ refEventInf j.event d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed)
        (fun ω (s : ℝ) => d.driver s.toNNReal ω) d.curve j.chart (refHull d.driver d.lifetime) q r :=
      ⟨hE', hlive, Or.inl hv, hcap, hHull (rationalOriginalTime r)⟩
    exact hRω hE' hlive ξ hξ' hX ⟨fun h => h hI, hC⟩ r x ε hM hv hcol hpK

end InteractingSLE.Sec7.ColCov
