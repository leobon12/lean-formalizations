/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Asm2Build

/-!
# Choosing R1's chart with its complete normalization certificate

The new choice retains the physical derivative branch, the original target
limit and the current access limit. No landed chart choice is modified.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWX
open Aux61SlitW Aux61Asm2 Aux61Restart Aux61FibData Aux61ULoc LawUnique
universe u
variable {S : SourceSetting.{u}} (D : R1Restart S)

/-- All the R1 chart facts needed after choosing a measurable witness. -/
structure ChartFacts (i : D.ι) (b : SourceRecord S.nL S.nR → ℂ)
    (c : SourceRecord S.nL S.nR → Chart) : Prop where
  base_measurable : Measurable b
  base_mem : ∀ y, b y ∈ retainedDomain (historyHull (rationalTime S.s) (D.Y i) y) (D.η i y) (D.q i)
  measurable : IsMeasChart c
  conformal : ∀ y, (c y).IsConformal
  domain : ∀ y, ((c y).dom : Set ℂ) =
    restartComponent (historyHull (rationalTime S.s) (D.Y i) y) (D.η i y) (D.q i) (b y)
  target : ∀ y, (1 : ℂ) ∈ closure ((c y).dom : Set ℂ)
  continuous_lift : ∀ y, ContinuousOn (c y).2.2 (c y).dom
  lift : ∀ y z, z ∈ (c y).dom →
    (c y).2.2 z = (physicalRestartLog (stripTargetHull (c y).dom) z).im
  current : ∀ y, Tendsto ((c y).1 ∘ (ownHistoryChart (D.U i) (D.r i) y).2.1) (𝓝[H] 0) (𝓝 0)
  infty : ∀ y, Tendsto (fun z : ℂ => ‖(c y).1 (z + 1)‖) (𝓝[H] 0) atTop

/-- Extract the complete witness, before making any weaker chart choice. -/
theorem exists_chartFacts (h : D.HasChart) (i : D.ι) :
    ∃ p : (SourceRecord S.nL S.nR → ℂ) × (SourceRecord S.nL S.nR → Chart), ChartFacts D i p.1 p.2 := by
  obtain ⟨N, hN, hb, htarget, c, hc, hdom, -, hd, hf, hl, hcont, hphase, hlimits⟩ := h i
  refine ⟨(fun y => D.e (N y), c), ?_⟩
  have hdomain : ∀ y, ((c y).dom : Set ℂ) =
      historyComponent (rationalTime S.s) (D.q i) (D.Y i) (D.η i) (fun y => D.e (N y)) y := hdom
  refine ⟨measurable_from_nat.comp hN, hb, ⟨hd, hf, hl⟩, hc, hdomain, ?_, hcont, ?_,
    fun y => (hlimits y).1, fun y => (hlimits y).2⟩
  · intro y
    rw [hdomain y]
    exact htarget y
  · intro y z hz
    have h := hphase y z ((hdomain y) ▸ hz)
    simpa only [← hdomain y] using h

/-- The base point and chart chosen together with their full R1 certificate. -/
def chartWitness (h : D.HasChart) (i : D.ι) :
    (SourceRecord S.nL S.nR → ℂ) × (SourceRecord S.nL S.nR → Chart) :=
  Classical.choose (exists_chartFacts D h i)

def chart (h : D.HasChart) (i : D.ι) : SourceRecord S.nL S.nR → Chart :=
  (chartWitness D h i).2

def base (h : D.HasChart) (i : D.ι) : SourceRecord S.nL S.nR → ℂ :=
  (chartWitness D h i).1

theorem chart_spec (h : D.HasChart) (i : D.ι) : ChartFacts D i (base D h i) (chart D h i) :=
  Classical.choose_spec (exists_chartFacts D h i)

/-- The original restart data, with the fully certified chart choice. -/
def source (h : D.HasChart) : SourceRestartData S.Ω S.nL S.nR :=
  { D.src h with chart := chart D h }

end InteractingSLE.Sec5.Aux61SlitWX
