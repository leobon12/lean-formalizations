/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlFwdR7Inf
import InteractingSLE.Spec.Sec7.R5EnlLate
import InteractingSLE.Spec.Sec7.SideC5Data
import InteractingSLE.Spec.Sec7.PocketSideInTailActual
import InteractingSLE.Spec.Sec7.PocketSideInInstGerm
import InteractingSLE.Spec.Sec7.R5EnlTwin

/-!
# The late side tests' conditioned increment laws for the visit references

Packet PROVE-R5-ENLARGED (continued). PROVE-SIDE-COLLAR2's late collar
(`Wire.lateSideCollarExc_visitReferences_of_initialMeanFormulaOn`) takes R.5's conditioned increment laws on the late
side tests for the installed visit references:

`LateSideIncrementLawsOn i d (fun j => (side j).withVisitReferences …)
  (fun j r ω => j.referenceVisitChart i d ω (s j r)) (fun j q r => j.referenceVisitEvent i d (s j r) q)`.

A late side test is an R.7 test: its event, traversal, pocket, base chart (`pChart`) and zero field are those of the
change pocket of the right wall and the `seed`-th left wall (`SideTest.target`), bounded (`infinite = false`) or opening
at the flow seed (`infinite = true`); the visit reference at the original time `s` is the relative chart at the capacity
reached at `s` (`referenceVisitChart`), and its pair event is a visit window (`referenceVisitEvent`). Here:

* `pChart_cfPocket_facts` — the base chart of a test is conformal, with the pocket as domain and the Jordan coordinate
  as forward map;
* **`lateSideIncrementLawsOn_visitReferences`** — the late laws, from the walls' and coupling's data of the word objects
  and the counterflow's measurability, by `R5Enl.r7HasOldChartIncrementLawOn_visit(Inf)` on each test;
* **`lateSideCollarExc_visitReferences_of_initialMeanFormula_walls`** — SIDE-COLLAR2's late collar
  (`lateSideCollarExc_visitReferences_of_initialMeanFormulaOn`) with `hLaw` discharged.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets Sec7.PocketStopField Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketAdapt
  Sec7.Lemma71C Sec7.PocketStopSide Sec7.PocketCoupling Sec7.PocketWordPerQ Sec7.PocketWordAssembly
  Sec7.PocketSeedOpen Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketCoord Sec7.PocketJordan Sec7.R5Enl
  WholeField

/-- **The base chart of a test** (`pChart` of a Jordan coordinate of an open pocket in `ℍ`): on the event it is
conformal, has the pocket as domain and the coordinate as forward map. -/
theorem pChart_cfPocket_facts {Ω : Type*} {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) :
    ∀ ω ∈ A, (pChart A C ψ ω).IsConformal ∧ ((pChart A C ψ ω).dom : Set ℂ) = C ω ∧
      EqOn (pChart A C ψ ω).1 (ψ ω) (C ω) := by
  intro ω hω
  have hprops := pChart_props hCo hCH hψ ω
  refine ⟨hprops.2.2.1, ?_, fun z _ => ?_⟩
  · rw [hprops.2.2.2]
    ext z
    simp only [mem_ofPred_eq, hω, true_and, not_true_eq_false, false_and, or_false]
  · change pFwd A ψ ω z = _
    rw [pFwd_of_mem hω]

/-- **R.5's conditioned increment laws on the late side tests for the installed visit references** (both pocket
shapes): every late side test is an R.7 test, and on it the law at the visit reference of the original time `s j r`
is `R5Enl.r7HasOldChartIncrementLawOn_visit` (bounded pocket) or `R5Enl.r7HasOldChartIncrementLawOn_visitInf`
(pocket opening at the flow seed), with the test's configuration, Jordan coordinate and its point measurability, and
the infinite lifetime read off `SideTest.Ready`. -/
theorem lateSideIncrementLawsOn_visitReferences {Ω : Type} [mΩ : MeasurableSpace Ω] (i : BothLow)
    (d : WordObjects Ω) [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime) (s : SideTest Ω → ℕ → ℝ≥0)
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hC : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration d.driver d.forceL d.forceR
      d.brownian d.lifetime d.translatedField)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR) (forceJumpSet d.xL d.xR)
      d.coupledMean)
    (hζ : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t) (hLm : ∀ q t, Measurable fun ω => d.leftWall q ω t)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ q ω, Continuous (d.leftWall q ω))
    (hR0 : ∀ ω, d.rightWall ω 0 = 0) (hL0 : ∀ q ω, d.leftWall q ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => d.curve ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hdetL : ∀ q t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall q ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field d.originalMean) d.measure)
    (hlocL : ∀ q, Sec6.IsEntranceHistoryLocal (d.leftWall q) (centredField d.field d.originalMean) d.measure) :
    LateSideIncrementLawsOn i d (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r)) (fun j q r => j.referenceVisitEvent i d (s j r) q) := by
  have hκ : 0 < i.kappa := by linarith [i.kappa_gt_four]
  rintro ⟨seed, G, A, ψ, inf, two⟩ hj
  obtain ⟨-, -, -, hGc, hGlife, hcfg, hcfgI, hAm, hAG, -, hJ, hψm, -⟩ := hj
  dsimp only
  intro q gB hgB g hg r
  cases inf with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hAG hJ hψm
    have hcfgA : ∀ ω ∈ A, IsCfPocketConfig (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)
        (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) := fun ω hω => hcfg ω (hAG hω).1 (hAG hω).2
    have hfacts := pChart_cfPocket_facts (A := A) (C := fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω)
      (StripSys.rt seed)) (ψ := ψ)
      (fun ω hω => (R5Ref.pocket_of_cfg (W := fun ω (s : ℝ) => d.driver s.toNNReal ω) (hcfgA ω hω) (hJ ω hω)).1.isOpen)
      (fun ω hω => WangWu.image_negInv_subset_H (hcfgA ω hω).conf.changePocket_subset_H)
      (fun ω hω => (hJ ω hω).2.2.2.1)
    cases two <;>
    exact r7HasOldChartIncrementLawOn_visit (R := d.rightWall) (L := d.leftWall seed) (r := StripSys.rt seed)
      (η := d.curve) (ψ := ψ) (A := A) (G := A) (W' := d.driver) (ζ' := d.lifetime)
      (c := pChart A (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)) ψ)
      hT' hTr hu₀ hh hC hκ hu₀' hKilled hζ hRc (hLc seed) hR0 (hL0 seed) hRm (hLm seed) hdetR (hdetL seed) hlocR
      (hlocL seed) hAm (fun ω hω => (hGc ω (hAG hω).1).1) hAm Subset.rfl hcfgA (fun ω hω => hGlife ω (hAG hω).1) hJ
      (fun A' hA' hA'A p hp hpC => hψm A' hA' (fun ω hω => hAG (hA'A hω)) p hp hpC) hηm
      (fun ω hω => (hfacts ω hω).1) (fun ω hω => (hfacts ω hω).2.1) (fun ω hω => (hfacts ω hω).2.2) q (s _ r)
      (fun ω hω => ⟨hω.1, hω.2.1, Or.inl hω.2.2.1, hω.2.2.2.1⟩) (gB r) (hgB r) g hg
  | true =>
    simp only [↓reduceIte] at hAG hJ hψm
    have hcfgA : ∀ ω ∈ A, IsCfPocketConfigInf (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)
        (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) := fun ω hω =>
      hcfgI ω (hAG hω).1 (le_antisymm (le_of_not_gt (hAG hω).2) (hGc ω (hAG hω).1).1.changeCorner_props.1.1)
    have hfacts := pChart_cfPocket_facts (A := A) (C := fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω)
      (StripSys.rt seed)) (ψ := ψ)
      (fun ω hω => (R5Ref.pocket_of_cfgInf (W := fun ω (s : ℝ) => d.driver s.toNNReal ω) (hcfgA ω hω)
        (hJ ω hω)).1.isOpen)
      (fun ω hω => (R5Ref.pocket_of_cfgInf (W := fun ω (s : ℝ) => d.driver s.toNNReal ω) (hcfgA ω hω)
        (hJ ω hω)).1.subset_H)
      (fun ω hω => (hJ ω hω).2.2.2.1)
    cases two <;>
    exact r7HasOldChartIncrementLawOn_visitInf (R := d.rightWall) (L := d.leftWall seed) (r := StripSys.rt seed)
      (η := d.curve) (ψ := ψ) (A := A) (G := A) (W' := d.driver) (ζ' := d.lifetime)
      (c := pChart A (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)) ψ)
      hT' hTr hu₀ hh hC hκ hu₀' hKilled hζ hRc (hLc seed) hR0 (hL0 seed) hRm (hLm seed) hdetR (hdetL seed) hlocR
      (hlocL seed) hAm (fun ω hω => (hGc ω (hAG hω).1).1) hAm Subset.rfl hcfgA (fun ω hω => hGlife ω (hAG hω).1) hJ
      (fun A' hA' hA'A p hp hpC => hψm A' hA' (fun ω hω => hAG (hA'A hω)) p hp hpC) hηm
      (fun ω hω => (hfacts ω hω).1) (fun ω hω => (hfacts ω hω).2.1) (fun ω hω => (hfacts ω hω).2.2) q (s _ r)
      (fun ω hω => ⟨hω.1, hω.2.1, Or.inl hω.2.2.1, hω.2.2.2.1⟩) (gB r) (hgB r) g hg

/-- **The late side collar for the installed visit references, with R.5's increment laws discharged**
(`lateSideCollarExc_visitReferences_of_initialMeanFormulaOn` with `hLaw := lateSideIncrementLawsOn_visitReferences`):
the remaining inputs are the zero reference time, the height cover and the initial mean formula. -/
theorem lateSideCollarExc_visitReferences_of_initialMeanFormula_walls {Ω : Type} [mΩ : MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime) (s : SideTest Ω → ℕ → ℝ≥0)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) (hZero : ∀ j, ∃ r, s j r = 0)
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hC : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration d.driver d.forceL d.forceR
      d.brownian d.lifetime d.translatedField)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR) (forceJumpSet d.xL d.xR)
      d.coupledMean)
    (hζ : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t) (hLm : ∀ q t, Measurable fun ω => d.leftWall q ω t)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ q ω, Continuous (d.leftWall q ω))
    (hR0 : ∀ ω, d.rightWall ω 0 = 0) (hL0 : ∀ q ω, d.leftWall q ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => d.curve ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hdetL : ∀ q t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall q ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field d.originalMean) d.measure)
    (hlocL : ∀ q, Sec6.IsEntranceHistoryLocal (d.leftWall q) (centredField d.field d.originalMean) d.measure)
    (hCover : VisitReferenceHeightCoverPosExc i d side s X)
    (hFormula : InitialPocketMeanFormula i d side G) :
    LateSideCollarExc i d (fun j => (side j).withVisitReferences i j d hKilled (s j)) X :=
  lateSideCollarExc_visitReferences_of_initialMeanFormulaOn i d side G hKilled s X hZero hRc hLc hRm hLm hC hζ
    (lateSideIncrementLawsOn_visitReferences i d side hKilled s hT' hTr hu₀ hh hC hu₀' hζ hRm hLm hRc hLc hR0 hL0
      hηm hdetR hdetL hlocR hlocL) hCover hFormula

end InteractingSLE.Wire
